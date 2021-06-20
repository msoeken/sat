use std::cmp::min;

use crate::{Lit, Solver, Var};

#[derive(Default)]
struct Cell {
    lit: Lit,
    fwd: u32,
    bwd: u32,
    cls: u32,
}

pub struct BacktrackingSolver {
    num_vars: u32,
    num_clauses: u32,
    cls_counter: u32,
    cells: Vec<Cell>,
    start: Vec<usize>,
    size: Vec<usize>,
}

impl BacktrackingSolver {
    fn init_cells(num_vars: u32) -> Vec<Cell> {
        let mut cells = Vec::with_capacity(2 * (num_vars as usize + 1));

        // two empty ones
        cells.push(Cell::default());
        cells.push(Cell::default());

        for i in 1..=num_vars {
            cells.push(Cell {
                lit: Lit::default(),
                bwd: 2 * i,
                fwd: 2 * i,
                cls: 0,
            });
            cells.push(Cell {
                lit: Lit::default(),
                bwd: 2 * i + 1,
                fwd: 2 * i + 1,
                cls: 0,
            });
        }

        cells
    }

    fn remove_lit(&mut self, lit: Lit) -> bool {
        let mut p = self.cells[lit.index as usize].fwd;

        while p >= 2 * self.num_vars + 2 {
            let i = &mut self.size[self.cells[p as usize].cls as usize];

            if *i > 1 {
                *i -= 1;
                p = self.cells[p as usize].fwd;
            } else {
                p = self.cells[p as usize].bwd;

                while p >= 2 * self.num_vars + 2 {
                    self.size[self.cells[p as usize].cls as usize] += 1;
                    p = self.cells[p as usize].bwd;
                }

                return true;
            }
        }

        false
    }

    fn unremove_lit(&mut self, lit: Lit) {
        let mut p = self.cells[lit.index as usize].fwd;

        while p >= 2 * self.num_vars + 2 {
            self.size[self.cells[p as usize].cls as usize] += 1;
            p = self.cells[p as usize].fwd;
        }
    }

    #[allow(clippy::many_single_char_names)]
    fn deactivate(&mut self, lit: Lit) {
        let mut p = self.cells[lit.index as usize].fwd;

        while p >= 2 * self.num_vars + 2 {
            let j = self.cells[p as usize].cls;
            let i = self.start[j as usize];
            p = self.cells[p as usize].fwd;

            for s in i..i + self.size[j as usize] - 1 {
                // remove s from linked list
                let q = self.cells[s].fwd;
                let r = self.cells[s].bwd;
                self.cells[q as usize].bwd = r;
                self.cells[r as usize].fwd = q;

                let l = self.cells[s].lit;
                self.cells[l.index as usize].cls -= 1;
            }
        }
    }

    #[allow(clippy::many_single_char_names)]
    fn reactivate(&mut self, lit: Lit) {
        let mut p = self.cells[lit.index as usize].bwd;

        while p >= 2 * self.num_vars + 2 {
            let j = self.cells[p as usize].cls;
            let i = self.start[j as usize];
            p = self.cells[p as usize].bwd;

            for s in i..i + self.size[j as usize] - 1 {
                // insert s back into linked list
                let q = self.cells[s].fwd;
                let r = self.cells[s].bwd;
                self.cells[q as usize].bwd = s as u32;
                self.cells[r as usize].fwd = s as u32;

                let l = self.cells[s].lit;
                self.cells[l.index as usize].cls += 1;
            }
        }
    }

    pub fn debug(&self) {
        print!("  p  =");
        for i in 0..self.cells.len() {
            print!("{:3}", i);
        }
        println!();

        print!("L(p) =");
        for c in self.cells.iter() {
            print!("{:3}", c.lit.index);
        }
        println!();

        print!("F(p) =");
        for c in self.cells.iter() {
            print!("{:3}", c.fwd);
        }
        println!();

        print!("B(p) =");
        for c in self.cells.iter() {
            print!("{:3}", c.bwd);
        }
        println!();

        print!("C(p) =");
        for c in self.cells.iter() {
            print!("{:3}", c.cls);
        }
        println!();
    }
}

impl Solver for BacktrackingSolver {
    fn new(num_vars: u32, num_clauses: u32) -> Self {
        Self {
            num_vars,
            num_clauses,
            cls_counter: num_clauses,
            cells: Self::init_cells(num_vars),
            start: vec![0; num_clauses as usize + 1],
            size: vec![0; num_clauses as usize + 1],
        }
    }

    fn num_vars(&self) -> u32 {
        self.num_vars
    }

    fn num_clauses(&self) -> u32 {
        self.num_clauses
    }

    fn add_clause(&mut self, clause: &[Lit]) {
        let mut copy = clause.to_vec();
        copy.sort();
        copy.reverse();

        self.start[self.cls_counter as usize] = self.cells.len();
        self.size[self.cls_counter as usize] = copy.len();

        for &l in copy.iter() {
            self.cells.push(Cell {
                lit: l,
                fwd: self.cells[l.index as usize].fwd,
                bwd: l.index,
                cls: self.cls_counter,
            });

            let f = self.cells[l.index as usize].fwd as usize;
            self.cells[l.index as usize].fwd = self.cells.len() as u32 - 1;
            self.cells[f].bwd = self.cells.len() as u32 - 1;
            self.cells[l.index as usize].cls += 1;
        }

        self.cls_counter -= 1;
    }

    fn solve(&mut self) -> bool {
        // A1. [Initialize.]
        let mut a = self.num_clauses;
        let mut d = 1_u32;
        let mut m = vec![0_u32; self.num_vars() as usize + 1];

        loop {
            // A2. [Choose.]
            let mut l = if self.cells[2 * d as usize].cls <= self.cells[2 * d as usize + 1].cls {
                Lit::neg(Var::new(d))
            } else {
                Lit::pos(Var::new(d))
            };

            m[d as usize] = (l.index & 1) + 4 * min(self.cells[l.index as usize].cls, 1);

            if self.cells[l.index as usize].cls == a {
                return true;
            }

            // A3. [Remove ~l.]
            loop {
                if self.remove_lit(!l) {
                    // A5. [Try again.]
                    loop {
                        if m[d as usize] < 2 {
                            m[d as usize] = 3 - m[d as usize];
                            l = Lit {
                                index: 2 * d + (m[d as usize] & 1),
                            };
                            break; // go to A3.
                        }

                        // A6. [Backtrack.]
                        if d == 1 {
                            return false;
                        }
                        d -= 1;
                        l = Lit {
                            index: 2 * d + (m[d as usize] & 1),
                        };

                        // A7. [Reactivates l's clauses.]
                        a += self.cells[l.index as usize].cls;
                        self.reactivate(l);

                        // A8. [Unremove ~l.]
                        self.unremove_lit(!l);

                        // go back to A5.
                    }
                    continue; // go to A3.
                } else {
                    break;
                }
            }

            // A4. [Deactivate l's clauses.]
            self.deactivate(l);
            a -= self.cells[l.index as usize].cls;
            d += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Result;
    use std::ops::Not;

    use super::*;

    #[test]
    fn rbar_is_satisfiable() -> Result<()> {
        let mut solver = BacktrackingSolver::new(4, 7);

        // ~3 ~4 ~1
        solver.add_clause(&[
            solver.var(3)?.not(),
            solver.var(4)?.not(),
            solver.var(1)?.not(),
        ]);

        // ~2 ~3 4
        solver.add_clause(&[
            solver.var(2)?.not(),
            solver.var(3)?.not(),
            solver.var(4)?.into(),
        ]);

        // ~1 ~2 3
        solver.add_clause(&[
            solver.var(1)?.not(),
            solver.var(2)?.not(),
            solver.var(3)?.into(),
        ]);

        // 4 ~1 2
        solver.add_clause(&[
            solver.var(4)?.into(),
            solver.var(1)?.not(),
            solver.var(2)?.into(),
        ]);

        // 3 4 1
        solver.add_clause(&[
            solver.var(3)?.into(),
            solver.var(4)?.into(),
            solver.var(1)?.into(),
        ]);

        // 2 3 ~4
        solver.add_clause(&[
            solver.var(2)?.into(),
            solver.var(3)?.into(),
            solver.var(4)?.not(),
        ]);

        // 1 2 ~3
        solver.add_clause(&[
            solver.var(1)?.into(),
            solver.var(2)?.into(),
            solver.var(3)?.not(),
        ]);

        assert!(solver.solve());

        Ok(())
    }

    #[test]
    fn r_is_unsatisfiable() -> Result<()> {
        let mut solver = BacktrackingSolver::new(4, 8);

        // ~4 1 ~2
        solver.add_clause(&[
            solver.var(4)?.not(),
            solver.var(1)?.into(),
            solver.var(2)?.not(),
        ]);

        // ~3 ~4 ~1
        solver.add_clause(&[
            solver.var(3)?.not(),
            solver.var(4)?.not(),
            solver.var(1)?.not(),
        ]);

        // ~2 ~3 4
        solver.add_clause(&[
            solver.var(2)?.not(),
            solver.var(3)?.not(),
            solver.var(4)?.into(),
        ]);

        // ~1 ~2 3
        solver.add_clause(&[
            solver.var(1)?.not(),
            solver.var(2)?.not(),
            solver.var(3)?.into(),
        ]);

        // 4 ~1 2
        solver.add_clause(&[
            solver.var(4)?.into(),
            solver.var(1)?.not(),
            solver.var(2)?.into(),
        ]);

        // 3 4 1
        solver.add_clause(&[
            solver.var(3)?.into(),
            solver.var(4)?.into(),
            solver.var(1)?.into(),
        ]);

        // 2 3 ~4
        solver.add_clause(&[
            solver.var(2)?.into(),
            solver.var(3)?.into(),
            solver.var(4)?.not(),
        ]);

        // 1 2 ~3
        solver.add_clause(&[
            solver.var(1)?.into(),
            solver.var(2)?.into(),
            solver.var(3)?.not(),
        ]);

        assert!(!solver.solve());

        Ok(())
    }
}
