use std::ops::Not;

use crate::{Lit, Solver};

struct WatchingSolver {
    num_vars: u32,
    num_clauses: u32,
    cls_counter: u32,
    lits: Vec<Lit>,
    start: Vec<usize>,
    link: Vec<usize>,
    watch: Vec<usize>,
}

impl Solver for WatchingSolver {
    fn new(num_vars: u32, num_clauses: u32) -> Self {
        Self {
            num_vars,
            num_clauses,
            cls_counter: num_clauses,
            lits: Vec::new(),
            start: vec![0; num_clauses as usize + 1],
            link: vec![0; num_clauses as usize + 1],
            watch: vec![0; 2 * (num_vars + 1) as usize],
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
            todo!();
        }

        self.cls_counter -= 1;
    }

    fn solve(&mut self) -> bool {
        assert_eq!(self.cls_counter, 0);
        self.start[0] = self.lits.len();

        // B1. [Initialize.]
        let mut d = 1_u32;
        let mut m = vec![0u32; self.num_vars as usize + 1];

        loop {
            // B2. [Rejoice or choose.]
            if d > self.num_vars {
                return true;
            }

            m[d as usize] =
                if self.watch[2 * d as usize] == 0 || self.watch[2 * d as usize + 1] != 0 {
                    1
                } else {
                    0
                };
            let mut l = Lit {
                index: 2 * d + m[d as usize],
            };

            // B3. [Remove !l if possible.]
            let mut cont = true;

            while cont {
                cont = false;

                let mut j = self.watch[l.not().index as usize];
                while j != 0 {
                    let i = self.start[j];
                    let ii = self.start[j - 1];
                    let jj = self.link[j];
                    let mut k = i + 1;
                    while k < ii {
                        let ll = self.lits[k];
                        if (ll.var_index() > d) || (ll.index + m[ll.var_index() as usize]) % 2 == 0
                        {
                            self.lits[i] = ll;
                            self.lits[k] = l.not();
                            self.link[j] = self.watch[ll.index as usize];
                            self.watch[ll.index as usize] = j;
                            j = jj;
                            break;
                        }
                        k += 1;
                        if k == ii {
                            break;
                        }
                    }
                    if k == ii {
                        self.watch[l.not().index as usize] = j;

                        // B5. [Try again.]
                        loop {
                            if m[d as usize] < 2 {
                                m[d as usize] = 3 - m[d as usize];
                                l = Lit {
                                    index: 2 * d + (m[d as usize] & 1),
                                };
                                break;
                            } else {
                                // B6. [Backtrack.]
                                if d == 1 {
                                    return false;
                                } else {
                                    d -= 1;
                                }
                            }
                        }

                        cont = true;
                        break;
                    }
                }
            }

            // B4. [Advance.]
            self.watch[l.not().index as usize] = 0;
            d += 1;

            // goto B2.
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rbar_is_satisfiable() {
        let mut solver = WatchingSolver::new(4, 7);

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
        let mut solver = WatchingSolver::new(4, 8);

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
}
