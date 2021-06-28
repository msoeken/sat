use crate::{Lit, Solver, Var};

struct WatchList {
    /// matches a clause to another clause in the linked list
    link_: Vec<usize>,

    /// maps literals to clause index (0 means no clause)
    watch_: Vec<usize>,
}

impl WatchList {
    /// creates a new watch list
    pub fn new(num_vars: usize, num_clauses: usize) -> Self {
        Self {
            link_: vec![0; num_clauses + 1],
            watch_: vec![0; 2 * (num_vars + 1)],
        }
    }

    /// insert a new entry to the watch list
    pub fn create_or_insert(&mut self, lit: Lit, clause_index: usize) {
        let w = &mut self.watch_[lit.index as usize];

        if *w == 0 {
            // first watch?
            *w = clause_index;
        } else {
            // new watch?
            self.link_[clause_index] = *w;
            *w = clause_index;
        }
    }

    /// insert a new clause being watched by lit
    pub fn insert(&mut self, lit: Lit, clause_index: usize) {
        let w = &mut self.watch_[lit.index as usize];

        self.link_[clause_index] = *w;
        *w = clause_index;
    }

    /// make literal watch a specific clause (without changing linked lists)
    pub fn watch(&mut self, lit: Lit, clause_index: usize) {
        self.watch_[lit.index as usize] = clause_index;
    }

    /// returns the watched clause by lit
    pub fn watchee(&self, lit: Lit) -> usize {
        self.watch_[lit.index as usize]
    }

    /// returns the next clause in the linked list (or 0 if last clause)
    pub fn link(&self, clause_index: usize) -> usize {
        self.link_[clause_index]
    }

    /// stops watching clauses for a literal
    pub fn remove(&mut self, lit: Lit) {
        self.watch_[lit.index as usize] = 0;
    }

    /// checks whether a literal is watching a clause
    pub fn is_watching(&self, lit: Lit) -> bool {
        self.watch_[lit.index as usize] != 0
    }
}

pub struct WatchingSolver {
    num_vars: u32,
    num_clauses: u32,
    cls_counter: usize,
    lits: Vec<Lit>,
    start: Vec<usize>,
    watch_list: WatchList,
}

impl Solver for WatchingSolver {
    fn new(num_vars: u32, num_clauses: u32) -> Self {
        Self {
            num_vars,
            num_clauses,
            cls_counter: num_clauses as usize,
            lits: Vec::new(),
            start: vec![0; num_clauses as usize + 1],
            watch_list: WatchList::new(num_vars as usize, num_clauses as usize),
        }
    }

    fn num_vars(&self) -> u32 {
        self.num_vars
    }

    fn num_clauses(&self) -> u32 {
        self.num_clauses
    }

    fn add_clause(&mut self, clause: &[Lit]) {
        self.start[self.cls_counter] = self.lits.len();

        for &l in clause.iter() {
            self.lits.push(l);
        }

        self.watch_list
            .create_or_insert(clause[0], self.cls_counter);

        self.cls_counter -= 1;
    }

    #[allow(clippy::many_single_char_names)]
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

            m[d as usize] = (!self.watch_list.is_watching(Lit::pos(Var::new(d)))
                || self.watch_list.is_watching(Lit::neg(Var::new(d))))
            .into();
            let mut l = Lit {
                index: 2 * d + m[d as usize],
            };

            // B3. [Remove !l if possible.]
            let mut cont = true;

            while cont {
                cont = false;

                let mut j = self.watch_list.watchee(!l);
                while j != 0 {
                    let i = self.start[j];
                    let ii = self.start[j - 1];
                    // remember where j links to, as we may change this later
                    let jj = self.watch_list.link(j);
                    let mut k = i + 1;
                    while k < ii {
                        let ll = self.lits[k];
                        // if ll has not been assigned yet...
                        if (ll.var_index() > d) || (ll.index + m[ll.var_index() as usize]) % 2 == 0
                        {
                            self.lits[i] = ll;
                            self.lits[k] = !l;
                            // Now ll watches clause j
                            self.watch_list.insert(ll, j);
                            j = jj;
                            break;
                        }
                        k += 1;
                        if k == ii {
                            break;
                        }
                    }
                    if k == ii {
                        self.watch_list.watch(!l, j);

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
            self.watch_list.remove(!l);
            d += 1;

            // goto B2.
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::problems::waerden;

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

    fn test_waerden(j: usize, k: usize, n: usize, sat: bool) {
        let clauses = waerden(j, k, n);

        let mut solver = WatchingSolver::new(n as u32, clauses.len() as u32);

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
