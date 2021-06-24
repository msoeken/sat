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
            watch: vec![0; 2 * num_vars as usize],
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

        // B2. [Rejoice or choose.]
        if d > self.num_vars {
            return true;
        }

        m[d as usize] = if self.watch[2 * d as usize] == 0 || self.watch[2 * d as usize + 1] != 0 {
            1
        } else {
            0
        };
        let mut l = Lit {
            index: 2 * d + m[d as usize],
        };

        // B3. [Remove !l if possible.]
        todo!();

        todo!()
    }
}
