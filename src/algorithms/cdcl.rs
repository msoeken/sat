use itertools::Itertools;
use rand::{thread_rng, Rng};

#[derive(Default)]
pub struct CDCLSolver {
    /// Number of variables $n$
    num_vars: usize,

    /// Memory array to store clauses
    mem: Vec<u32>,

    /// Low pointer to learned clauses
    minl: usize,

    /// High pointer to learned clauses
    maxl: usize,

    /// Array of variables indexed from 1..n
    vars: Vec<Variable>,

    /// Heap for free variables, indexed from 0..n
    heap: Vec<u32>,

    /// Watch list, indexed from 2..=2n + 1
    watch: Vec<u32>,

    /// Length of the trail $F$
    len_trail: usize,
}

#[derive(Default, Clone)]
struct Variable {
    stamp: u32,
    val: i32,
    tloc: u32,
    hloc: u32,
    act: u32,
}

impl CDCLSolver {
    pub fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            vars: vec![Default::default(); num_vars + 1],
            heap: vec![0; num_vars],
            watch: vec![0; (2 + 1) * num_vars],
            ..Default::default()
        }
    }

    pub fn solve(&mut self, problem: impl Iterator<Item = impl Iterator<Item = u32>>) {
        self.initialize_heap();
        self.initialize_mem(problem);
    }

    pub fn show_mem(&self) {
        let chunk_size = 20;
        for (row, chunk) in self.mem.chunks(chunk_size).enumerate() {
            print!("    i  =");
            for i in row * chunk_size..(row * chunk_size + chunk.len()) {
                print!(" {:<5}", i);
            }
            println!();
            print!("MEM[i] =");
            for val in chunk {
                print!(" {:<5}", val);
            }
            println!();
        }
    }

    pub fn show_watched_lists(&self) {
        for l in 2..=2 * self.num_vars + 1 {
            print!("W[{}] =", l);

            let mut c = self.watch[l];

            while c != 0 {
                print!(" {} (", c);
                for cl in 0..self.mem[c as usize - 1] {
                    print!(" {}", self.mem[(c + cl) as usize]);
                }
                c = if self.mem[c as usize] == l as u32 {
                    self.mem[(c - 2) as usize]
                } else if self.mem[(c + 1) as usize] == l as u32 {
                    self.mem[(c - 3) as usize]
                } else {
                    0
                };
                print!(" ) ->");
            }
            println!(" 0;");
        }
    }

    /// Initializes the heap as a random permutation over ${1, ..., n}$ based on
    /// a variant of Algorithm 3.4.2P.
    ///
    /// This is described in Exercise 7.2.2.2-260.
    fn initialize_heap(&mut self) {
        let mut rng = thread_rng();
        for k in 1..=self.num_vars {
            let j = rng.gen_range(0..k);

            self.heap[k - 1] = self.heap[j];
            self.heap[j] = k as u32;
        }

        for j in 0..self.num_vars {
            self.vars[self.heap[j] as usize].hloc = j as u32;
        }
    }

    /// Initialize MEM
    fn initialize_mem(&mut self, problem: impl Iterator<Item = impl Iterator<Item = u32>>) -> bool {
        self.len_trail = 0;

        self.watch[2..=(2 * self.num_vars + 1)].fill(0);

        let mut c = 3;

        for clause_iter in problem {
            let clause = clause_iter.collect_vec();
            let k = clause.len();

            if k == 0 {
                return false;
            } else if k == 1 {
                let var = (clause[0] >> 1) as usize;
                let val = self.vars[var].val;

                if val >= 0 && (val as u32) != (clause[0] & 1) {
                    return false;
                }

                if val < 0 {
                    self.vars[var].val = (clause[0] & 1) as i32;
                    self.vars[var].tloc = self.len_trail as u32;
                    self.len_trail += 1;
                }
            } else {
                // Position c - 3 and c - 2
                self.mem.push(self.watch[clause[1] as usize]);
                self.mem.push(self.watch[clause[0] as usize]);
                self.watch[clause[0] as usize] = c as u32;
                self.watch[clause[1] as usize] = c as u32;

                // Position c - 1
                self.mem.push(k as u32);

                // Append clause
                self.mem.extend_from_slice(&clause);

                c += k + 3;

                // self.mem[c..(c + k)].clone_from_slice(&clause);

                // self.mem[c - 1] = k as u32;
                // self.mem[c - 2] = self.watch[clause[0] as usize];
                // self.watch[clause[0] as usize] = c as u32;
                // self.mem[c - 3] = self.watch[clause[1] as usize];
                // self.watch[clause[1] as usize] = c as u32;
                // c += k + 3;
            }
        }

        // Allocate two cells for extra data in the preamble of the first
        // learned clause.
        self.mem.push(0);
        self.mem.push(0);

        assert_eq!(self.mem.len(), c - 1);

        self.minl = c + 2;
        self.maxl = c + 2;

        true
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use crate::{waerden, CDCLSolver};

    #[test]
    fn test_waerden339() {
        let waerden = waerden(3, 3, 9);
        let problem = waerden.iter().map(|clause| {
            clause
                .iter()
                .map(|&l| (l.abs() * 2 + if l < 0 { 1 } else { 0 }) as u32)
        });

        let mut solver = CDCLSolver::new(9);
        solver.solve(problem);

        solver.show_mem();
        solver.show_watched_lists();
    }

    #[test]
    fn generate_random_heap() {
        let n = 8;
        let mut rng = rand::thread_rng();

        let mut heap = vec![0; n];
        for k in 1..=n {
            let j = rng.gen_range(0..k);

            heap[k - 1] = heap[j];
            heap[j] = k;
        }

        println!("{:?}", heap);
    }
}
