use std::slice::Iter;

use crate::{utils::BuddyMemory, Lit};

struct BimpMemory {
    memory: BuddyMemory<Lit>,
    blocks: Vec<u32>,
}

impl BimpMemory {
    pub fn new(num_vars: u32) -> Self {
        let mut memory = BuddyMemory::new(10);
        let mut blocks = Vec::with_capacity(2 * num_vars as usize);

        for _ in 0..2 * num_vars {
            let block = memory.reserve(2);
            blocks.push(block.address());
        }

        Self { memory, blocks }
    }
}

struct LookaheadSolver {
    /// n in Algorithm L
    num_vars: usize,

    /// F in Algorithm L (could be removed if we had an array of storing all fixed vars)
    num_fixed_vars: usize,

    /// VAR in Algorithm L (permutation of all variables, where the first `num_free_vars` are free vars)
    vars: Vec<usize>,

    /// N in Algorithm X (could be removed and derived from num_fixed_vars?)
    num_free_vars: usize,
}
enum AlgorithmXResult {
    Satisfiable,
}

impl LookaheadSolver {
    #[allow(dead_code)]
    fn algorithm_x(&mut self) -> AlgorithmXResult {
        enum State {
            X1,
            X2,
            X3,
            X4,
            X5,
            X6,
            X7,
            X8,
            X9,
            X10,
            X11,
            X12,
            X13,
        }

        let mut curr = State::X1;

        let mut h: Vec<f64> = vec![];

        loop {
            curr = match curr {
                State::X1 => {
                    // [Satisfied?]
                    if self.num_fixed_vars() == self.num_vars() {
                        return AlgorithmXResult::Satisfiable;
                    }
                    State::X2
                }
                State::X2 => {
                    // [Compile rough heuristics.]
                    self.num_free_vars = self.num_vars() - self.num_fixed_vars();
                    h = self.rough_heuristics();
                    State::X3
                }
                State::X3 => {
                    // [Preselect candidates.]
                    todo!();
                }
                _ => unreachable!(),
            }
        }
    }

    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn num_fixed_vars(&self) -> usize {
        self.num_fixed_vars
    }

    fn num_free_vars(&self) -> usize {
        self.num_free_vars
    }

    fn free_vars(&self) -> impl Iterator<Item = usize> + '_ {
        self.vars.iter().take(self.num_free_vars).cloned()
    }

    fn free_lits(&self) -> impl Iterator<Item = usize> + '_ {
        self.free_vars().flat_map(|var| [2 * var, 2 * var + 1])
    }

    fn bimp_lits(&self, lit: usize) -> impl Iterator<Item = usize> + '_ {
        todo!();
        std::iter::once(0)
    }

    fn timp_lits(&self, lit: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        todo!();
        std::iter::once((0, 0))
    }

    fn is_free_lit(&self, lit: usize) -> bool {
        todo!();
    }

    /// One step to refine h(l) variables (see Eq. 65)
    fn refine(&self, h: Vec<f64>, alpha: f64) -> Vec<f64> {
        let h_ave = 1.0_f64 / (2.0_f64 * self.num_free_vars() as f64);

        self.free_lits()
            .map(|lit| {
                let bimp_term = self
                    .bimp_lits(lit)
                    .filter_map(|u| {
                        if self.is_free_lit(u) {
                            Some(h[u] / h_ave)
                        } else {
                            None
                        }
                    })
                    .sum::<f64>();

                let timp_term = self
                    .timp_lits(lit)
                    .map(|(u, v)| (h[u] / h_ave) * (h[v] / h_ave))
                    .sum::<f64>();

                0.1 * alpha * bimp_term * timp_term
            })
            .collect()
    }

    fn rough_heuristics(&self) -> Vec<f64> {
        let num_iterations = 5;
        let alpha = 3.5;

        let mut h: Vec<_> = std::iter::repeat(1.0_f64)
            .take(2 * self.num_free_vars())
            .collect();

        for _ in 0..num_iterations {
            h = self.refine(h, alpha);
        }

        h
    }
}
