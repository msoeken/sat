use std::fmt::Debug;

use rand::{prelude::StdRng, Rng, SeedableRng};

#[derive(Default)]
pub struct Heap {
    num_vars: usize,
    length: usize,
    heap: Vec<u32>,
    hloc: Vec<i32>,
    act: Vec<f64>,
    scaling_factor: f64,
}

impl Heap {
    pub fn new(num_vars: usize) -> Self {
        let (heap, hloc) = Self::init(num_vars);

        Self {
            num_vars,
            length: num_vars,
            heap,
            hloc,
            act: vec![0.0; num_vars + 1],
            scaling_factor: 1.0,
        }
    }

    /// Initializes the heap as a random permutation over ${1, ..., n}$ based on
    /// a variant of Algorithm 3.4.2P.
    ///
    /// This is described in Exercise 7.2.2.2-260.
    fn init(num_vars: usize) -> (Vec<u32>, Vec<i32>) {
        let mut heap = vec![0; num_vars];
        let mut hloc = vec![0; num_vars + 1];

        let mut rng = StdRng::seed_from_u64(655341);
        for k in 1..=num_vars {
            let j = rng.gen_range(0..k);

            heap[k - 1] = heap[j];
            heap[j] = k as u32;
        }

        for j in 0..num_vars {
            hloc[heap[j] as usize] = j as i32;
        }

        (heap, hloc)
    }

    pub fn pop(&mut self) -> u32 {
        // [Make a decision.]
        let k = self.heap[0];

        // delete k from heap (Exercise 262 and 266.)
        self.length -= 1;
        self.hloc[k as usize] = -1;

        if self.length == 0 {
            return k;
        }

        let i = self.heap[self.length] as usize;
        let alpha = self.act[i];
        let mut j = 0;
        let mut jj = 1usize;

        while jj < self.length {
            let mut alpha2 = self.act[self.heap[jj] as usize];
            if jj + 1 < self.length && self.act[self.heap[jj + 1] as usize] > alpha2 {
                jj += 1;
                alpha2 = self.act[self.heap[jj] as usize];
            }
            if alpha > alpha2 {
                jj = self.length;
            } else {
                self.heap[j] = self.heap[jj];
                self.hloc[self.heap[jj] as usize] = j as i32;
                j = jj;
                jj = 2 * j + 1;
            }
        }

        self.heap[j] = i as u32;
        self.hloc[i] = j as i32;

        k
    }

    pub fn push(&mut self, k: u32) {
        if self.hloc[k as usize] >= 0 {
            return;
        }

        let alpha = self.act[k as usize];
        let j = self.length;
        self.length += 1;
        if j == 0 {
            self.heap[0] = k;
            self.hloc[k as usize] = 0;
        } else {
            self.siftup(k, j as i32, alpha);
        }
    }

    pub fn bump_activity(&mut self, k: u32) {
        let alpha = self.act[k as usize];
        self.act[k as usize] += self.scaling_factor;
        let j = self.hloc[k as usize];
        self.siftup(k, j, alpha);
    }

    pub fn update_scaling_factor(&mut self, rho: f64) {
        self.scaling_factor /= rho;
    }

    /// Performs siftup operation described in Exercise 262.
    fn siftup(&mut self, k: u32, mut j: i32, alpha: f64) {
        if j > 0 {
            // siftup
            loop {
                let jj = (j - 1) >> 1;
                let i = self.heap[jj as usize];
                if self.act[i as usize] >= alpha {
                    break;
                } else {
                    self.heap[j as usize] = i;
                    self.hloc[i as usize] = j;
                    j = jj;
                    if j == 0 {
                        break;
                    }
                }
            }
            self.heap[j as usize] = k;
            self.hloc[k as usize] = j;
        }
    }

    pub fn sanity_check(&self) {
        for k in 1..self.num_vars {
            if self.hloc[k] != -1 {
                assert_eq!(self.heap[self.hloc[k] as usize], k as u32);
            }
        }
    }
}

impl Debug for Heap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "heap = {:?}, h = {}",
            &self.heap[0..self.length],
            self.length,
        )
    }
}
