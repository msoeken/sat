use std::ops::Not;

use crate::{Lit, Solver, Var};

pub struct DPLLSolver {
    num_vars: u32,
    num_clauses: u32,
    cls_counter: u32,
    lits: Vec<Lit>,
    start: Vec<usize>,
    link: Vec<usize>,
    watch: Vec<usize>,
    next: Vec<u32>,
}

impl DPLLSolver {
    fn is_unit(&self, l: Lit, x: &[i32]) -> bool {
        let mut j = self.watch[l.index as usize];

        // loop over clauses watched by l
        while j != 0 {
            // (i)
            let mut p = self.start[j] + 1;

            // loop over literals in clause
            loop {
                // (ii)
                if p == self.start[j - 1] {
                    return true;
                }

                // (iii) if L(p) is false
                if x[self.lits[p].var_index() as usize] == (self.lits[p].index & 1) as i32 {
                    p += 1;
                } else {
                    break;
                }
            }

            // (iv)
            j = self.link[j];
        }

        false
    }

    #[allow(dead_code)]
    fn debug(&self) {
        print!("  p  =");
        for i in 0..self.lits.len() {
            print!("{:3}", i);
        }
        println!();

        print!("L(p) =");
        for lit in self.lits.iter() {
            print!("{:3}", lit.index);
        }
        println!();
        println!();

        print!("      i  =");
        for i in 0..self.start.len() {
            print!("{:3}", i);
        }
        println!();

        print!("START(i) =");
        for s in self.start.iter() {
            print!("{:3}", s);
        }
        println!();
    }
}

impl Solver for DPLLSolver {
    fn new(num_vars: u32, num_clauses: u32) -> Self {
        Self {
            num_vars,
            num_clauses,
            cls_counter: num_clauses,
            lits: Vec::new(),
            start: vec![0; num_clauses as usize + 1],
            link: vec![0; num_clauses as usize + 1],
            watch: vec![0; 2 * (num_vars + 1) as usize],
            next: vec![0; (num_vars + 1) as usize],
        }
    }

    fn num_vars(&self) -> u32 {
        self.num_vars
    }

    fn num_clauses(&self) -> u32 {
        self.num_clauses
    }

    fn add_clause(&mut self, clause: &[Lit]) {
        self.start[self.cls_counter as usize] = self.lits.len();

        for &l in clause.iter() {
            self.lits.push(l);
        }

        if self.watch[clause[0].index as usize] == 0 {
            // first watch?
            self.watch[clause[0].index as usize] = self.cls_counter as usize;
        } else {
            // new watch?
            let w = self.watch[clause[0].index as usize];
            self.watch[clause[0].index as usize] = self.cls_counter as usize;
            self.link[self.cls_counter as usize] = w;
        }

        self.cls_counter -= 1;
    }

    #[allow(clippy::many_single_char_names)]
    fn solve(&mut self) -> bool {
        assert_eq!(self.cls_counter, 0);
        self.start[0] = self.lits.len();

        enum Steps {
            Step2,
            Step3,
            Step4,
            Step5,
            Step6,
            Step7,
            Step8,
        }

        // D1. [Init.]
        let mut hs = vec![0u32; self.num_vars as usize + 1];
        let mut m = vec![0u32; self.num_vars as usize + 1];
        let mut x = vec![-1i32; self.num_vars as usize + 1];

        let mut d = 0_u32;
        let mut h = 0_u32;
        let mut t = 0_u32;
        let mut k = 0_u32;

        for k in (1..=self.num_vars).rev() {
            x[k as usize] = -1;
            if self.watch[2 * k as usize] != 0 || self.watch[2 * k as usize + 1] != 0 {
                self.next[k as usize] = h;
                h = k;
                if t == 0 {
                    t = k;
                }
            }
        }
        if t != 0 {
            self.next[t as usize] = h;
        }

        let mut next = Steps::Step2;

        loop {
            next = match next {
                Steps::Step2 => {
                    if t == 0 {
                        return true;
                    }
                    k = t;
                    Steps::Step3
                }
                Steps::Step3 => {
                    h = self.next[k as usize];

                    let f: u32 = if self.is_unit(Lit::pos(Var::new(h)), &x) {
                        1
                    } else {
                        0
                    } + if self.is_unit(Lit::neg(Var::new(h)), &x) {
                        2
                    } else {
                        0
                    };

                    if f == 3 {
                        Steps::Step7
                    } else if f >= 1 {
                        assert!(f == 1 || f == 2);
                        m[d as usize + 1] = f + 3;
                        t = k;
                        Steps::Step5
                    } else if h != t {
                        k = h;
                        Steps::Step3
                    } else {
                        Steps::Step4
                    }
                }
                Steps::Step4 => {
                    h = self.next[t as usize];
                    m[d as usize + 1] =
                        if self.watch[2 * h as usize] == 0 || self.watch[2 * h as usize + 1] != 0 {
                            1
                        } else {
                            0
                        };
                    Steps::Step5
                }
                Steps::Step5 => {
                    d += 1;
                    hs[d as usize] = h;
                    k = h;

                    if t == k {
                        t = 0;
                    } else {
                        self.next[t as usize] = self.next[k as usize];
                        h = self.next[k as usize];
                    }

                    Steps::Step6
                }
                Steps::Step6 => {
                    let b = (m[d as usize] + 1) % 2;
                    x[k as usize] = b as i32;
                    // clear watch list for ~x[k]

                    let l = Lit {
                        index: (k << 1) + b,
                    };
                    let mut j = self.watch[l.index as usize];
                    self.watch[l.index as usize] = 0;

                    while j != 0 {
                        // (i)
                        let jj = self.link[j];
                        let i = self.start[j];
                        let mut p = i + 1;
                        // (ii) while L(p) is false
                        while x[self.lits[p].var_index() as usize]
                            == (self.lits[p].index & 1) as i32
                        {
                            p += 1;
                        }
                        // (iii)
                        let ll = self.lits[p];
                        self.lits[p] = l;
                        self.lits[i] = ll;
                        // (iv)
                        p = self.watch[ll.index as usize];
                        let q = self.watch[ll.not().index as usize];

                        if !(p != 0 || q != 0 || x[ll.var_index() as usize] >= 0) {
                            // (v)
                            if t == 0 {
                                t = ll.var_index();
                                h = ll.var_index();
                                self.next[t as usize] = h;
                            } else {
                                self.next[ll.var_index() as usize] = h;
                                h = ll.var_index();
                                self.next[t as usize] = h;
                            }
                        }

                        // (vi)
                        self.link[j] = p;
                        self.watch[ll.index as usize] = j;

                        // (vii)
                        j = jj;
                    }
                    Steps::Step2
                }
                Steps::Step7 => {
                    t = k;
                    while m[d as usize] >= 2 {
                        k = hs[d as usize];
                        x[k as usize] = -1;
                        if self.watch[2 * k as usize] != 0 || self.watch[2 * k as usize + 1] != 0 {
                            self.next[k as usize] = h;
                            h = k;
                            self.next[t as usize] = h;
                        }
                        d -= 1;
                    }
                    Steps::Step8
                }
                Steps::Step8 => {
                    if d > 0 {
                        m[d as usize] = 3 - m[d as usize];
                        k = hs[d as usize];
                        Steps::Step6
                    } else {
                        return false;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::problems::waerden;

    use super::*;

    #[test]
    fn rbar_is_satisfiable() {
        let mut solver = DPLLSolver::new(4, 7);

        solver.add_clause_from_ints(&[-3, -4, -1]);
        solver.add_clause_from_ints(&[-2, -3, 4]);
        solver.add_clause_from_ints(&[-1, -2, 3]);
        solver.add_clause_from_ints(&[4, -1, 2]);
        solver.add_clause_from_ints(&[3, 4, 1]);
        solver.add_clause_from_ints(&[2, 3, -4]);
        solver.add_clause_from_ints(&[1, 2, -3]);

        assert!(solver.solve());
    }

    #[test]
    fn r_is_unsatisfiable() {
        let mut solver = DPLLSolver::new(4, 8);

        solver.add_clause_from_ints(&[-4, 1, -2]);
        solver.add_clause_from_ints(&[-3, -4, -1]);
        solver.add_clause_from_ints(&[-2, -3, 4]);
        solver.add_clause_from_ints(&[-1, -2, 3]);
        solver.add_clause_from_ints(&[4, -1, 2]);
        solver.add_clause_from_ints(&[3, 4, 1]);
        solver.add_clause_from_ints(&[2, 3, -4]);
        solver.add_clause_from_ints(&[1, 2, -3]);

        assert!(!solver.solve());
    }

    fn test_waerden(j: usize, k: usize, n: usize, sat: bool) {
        let clauses = waerden(j, k, n);

        let mut solver = DPLLSolver::new(n as u32, clauses.len() as u32);

        for clause in clauses.iter() {
            solver.add_clause_from_ints(clause);
        }

        assert_eq!(solver.solve(), sat);
    }

    #[test]
    fn waerden338() {
        test_waerden(3, 3, 8, true);
    }

    #[test]
    fn waerden339() {
        test_waerden(3, 3, 9, false);
    }
}
