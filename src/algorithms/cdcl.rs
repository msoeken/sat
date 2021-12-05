use std::fmt::Debug;

use itertools::Itertools;
use log::info;
use rand::{prelude::StdRng, Rng, SeedableRng};

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

    /// Literal trail $L$
    trail: Vec<u32>,

    /// Length of the trail $F$, indexed from 0..=n (one additional item for possible final conflict)
    len_trail: usize,

    /// Length of forced literals $G$
    len_forced: usize,

    /// List of decision time points $i_d$ together with stamps
    decisions: Vec<Decision>,

    /// Decision level $d$
    decision_level: u32,

    /// Reasons for literal in trail $R_l$, indexed from 2..=2n + 1
    reasons: Vec<u32>,

    /// Unique stamp number $s$
    stamp: u32,

    /// Number of learned clauses $M$
    num_learned: u32,

    /// Heap size $h$
    len_heap: u32,

    /// Activity scaling factor DEL
    scaling_factor: f64,
}

#[derive(Clone)]
struct Variable {
    stamp: u32,
    val: i32,
    /// control the polarity of a new decision
    oval: i32,
    tloc: i32,
    hloc: i32,
    act: f64,
}

#[derive(Default, Clone)]
struct Decision {
    time: u32,
    stamp: u32,
}

enum State {
    C2,
    C3,
    C5,
    C6,
}

impl Default for Variable {
    fn default() -> Self {
        Self {
            stamp: 0,
            val: -1,
            oval: -1,
            tloc: -1,
            hloc: Default::default(),
            act: 0.0,
        }
    }
}

impl CDCLSolver {
    pub fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            vars: vec![Default::default(); num_vars + 1],
            heap: vec![0; num_vars],
            watch: vec![0; (2 + 1) * num_vars],
            trail: vec![0; num_vars + 1],
            decisions: vec![Default::default(); num_vars + 1],
            reasons: vec![0; (2 + 1) * num_vars],
            ..Default::default()
        }
    }

    pub fn solve(&mut self, problem: impl Iterator<Item = impl Iterator<Item = u32>>) -> bool {
        if !self.initialize(problem) {
            return false;
        }

        self.sanity_check();

        // global? variables
        let mut l;

        let mut current = State::C2;

        loop {
            current = match current {
                State::C2 => {
                    // [Level complete?]
                    if self.len_forced == self.len_trail {
                        State::C5
                    } else {
                        State::C3
                    }
                }

                State::C3 => {
                    // [Advance G.]
                    l = self.trail[self.len_forced];
                    self.len_forced += 1;

                    if let Some(conflict_clause) = self.propagate(l) {
                        // [C7. Resolve conflict.]
                        if self.decision_level == 0 {
                            return false;
                        }

                        let (ll, learned_rest, dd) = self.resolve_conflict_clause(conflict_clause);

                        // [C8. Backjump.]
                        let bound = self.decisions[dd as usize + 1].time as usize;

                        while self.len_trail > bound {
                            self.len_trail -= 1;
                            let l = self.trail[self.len_trail];
                            let k = l >> 1;
                            self.vars[k as usize].oval = self.vars[k as usize].val;
                            self.vars[k as usize].val = -1;
                            self.reasons[l as usize] = 0;
                            if self.vars[k as usize].hloc < 0 {
                                // insert k into heap
                                let alpha = self.vars[k as usize].act;
                                let j = self.len_heap;
                                self.len_heap += 1;
                                if j == 0 {
                                    self.heap[0] = k;
                                    self.vars[k as usize].hloc = 0;
                                } else {
                                    self.siftup(k, j as i32, alpha);
                                }
                            }
                        }

                        self.len_forced = self.len_trail;
                        self.decision_level = dd;

                        // [C9. Learn.]
                        if self.decision_level > 0 {
                            let c = self.maxl;
                            // MEM may grow a bit larger, but we keep MAXL correct to be able to ignore this
                            self.mem.resize(self.maxl + learned_rest.len() + 3, 0);
                            // insert learned clause into MEM
                            self.mem[c] = ll ^ 1;
                            let mut k = 0;
                            let mut jj = 1;
                            for j in 1..=learned_rest.len() {
                                let bj = learned_rest[j - 1];

                                // here we compare the stamp again, making use of checking redundancies before
                                if self.vars[bj as usize >> 1].stamp != self.stamp {
                                    continue;
                                }

                                k += 1;
                                if jj == 0 || (self.vars[bj as usize >> 1].val as u32 >> 1) < dd {
                                    self.mem[c + k + jj] = bj ^ 1;
                                } else {
                                    self.mem[c + 1] = bj ^ 1;
                                    jj = 0;
                                    self.mem[c - 2] = self.watch[ll as usize ^ 1];
                                    self.watch[ll as usize ^ 1] = c as u32;
                                    self.mem[c - 3] = self.watch[bj as usize ^ 1];
                                    self.watch[bj as usize ^ 1] = c as u32;
                                }
                            }
                            self.mem[c - 1] = k as u32 + 1;
                            self.maxl = c + k + 6;

                            self.reasons[ll as usize] = c as u32;
                        } else {
                            // new decision (invert literal at level 0)
                            self.reasons[ll as usize] = 0;
                        }

                        self.num_learned += 1;
                        self.trail[self.len_trail] = ll ^ 1;
                        self.vars[ll as usize >> 1].val =
                            ((2 * self.decision_level) + ((ll ^ 1) & 1)) as i32;
                        self.vars[ll as usize >> 1].tloc = self.len_trail as i32;
                        // is this right? why not complemented?
                        self.len_trail += 1;
                        // TODO make this a parameter
                        self.scaling_factor /= 0.95;

                        State::C3
                    } else {
                        State::C2
                    }
                }

                State::C5 => {
                    // [New level?]
                    if self.len_trail == self.num_vars {
                        return true;
                    }

                    // TODO purge excess clauses
                    // TODO flush literals
                    self.decision_level += 1;
                    self.decisions[self.decision_level as usize].time = self.len_trail as u32;
                    State::C6
                }

                State::C6 => {
                    let k = self.decide();
                    info!(
                        "decision at level {}, F = {}, k = {}",
                        self.decision_level, self.len_trail, k
                    );

                    if self.vars[k as usize].val >= 0 {
                        State::C6
                    } else {
                        let l = (2 * k + (self.vars[k as usize].oval as u32 & 1)) as u32;
                        self.vars[k as usize].val = (2 * self.decision_level
                            + (self.vars[k as usize].oval as u32 & 1))
                            as i32;
                        // TODO set Lf
                        self.trail[self.len_trail] = l;
                        self.vars[k as usize].tloc = self.len_trail as i32;
                        self.reasons[l as usize] = 0;
                        self.len_trail += 1;
                        assert_eq!(self.len_trail, self.len_forced + 1);

                        State::C3
                    }
                }
            }
        }
    }

    #[inline]
    fn clause_lit(&self, c: u32, j: u32) -> u32 {
        self.mem[(c + j) as usize]
    }

    #[inline]
    fn clause_len(&self, c: u32) -> u32 {
        self.mem[c as usize - 1]
    }

    #[allow(dead_code)]
    #[inline]
    fn clause_watch0(&self, c: u32) -> u32 {
        self.mem[c as usize - 2]
    }

    #[inline]
    fn clause_watch1(&self, c: u32) -> u32 {
        self.mem[c as usize - 3]
    }

    #[inline]
    fn is_lit_true(&self, l: u32) -> bool {
        let val = self.vars[l as usize >> 1].val;
        val >= 0 && (val as u32 + l) % 2 == 0
    }

    #[inline]
    fn is_lit_false(&self, l: u32) -> bool {
        let val = self.vars[l as usize >> 1].val;
        val >= 0 && (val as u32 + l) % 2 == 1
    }

    #[inline]
    fn clause(&self, c: u32) -> Clause {
        Clause::new(self, c)
    }

    #[inline]
    fn lit_var_mut(&mut self, lit: u32) -> &mut Variable {
        &mut self.vars[lit as usize >> 1]
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

    fn lit_to_str(lit: u32) -> String {
        format!("{}{}", if lit & 1 == 1 { "!" } else { "" }, lit >> 1)
    }

    #[allow(dead_code)]
    fn show_trail(&self) {
        println!(" t   TLOC   L_t   level   reason");
        for t in 0..self.len_trail {
            let lit = self.trail[t];
            let reason = self.reasons[lit as usize];
            println!(
                "{:>2}   {:>4}   {:>3}   {:>5}   {}",
                t,
                self.vars[(lit >> 1) as usize].tloc,
                Self::lit_to_str(lit),
                self.vars[(lit >> 1) as usize].val >> 1,
                if reason == 0 {
                    "Λ".into()
                } else {
                    format!("{:?}", self.clause(self.reasons[lit as usize]))
                }
            );
        }
    }

    pub fn show_watched_lists(&self) {
        for l in 2..=2 * self.num_vars + 1 {
            print!("W[{:>4}] =", Self::lit_to_str(l as u32));

            let mut c = self.watch[l];

            while c != 0 {
                print!(" {} (", c);
                for cl in 0..self.mem[c as usize - 1] {
                    print!(" {}", Self::lit_to_str(self.mem[(c + cl) as usize]));
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

    fn show_heap(&self) {
        println!(
            "heap = {:?}, h = {}",
            &self.heap[0..self.len_heap as usize],
            self.len_heap,
        );
    }

    fn sanity_check(&self) {
        for k in 1..self.num_vars {
            if self.vars[k].hloc != -1 {
                assert_eq!(self.heap[self.vars[k].hloc as usize], k as u32);
            }
        }
    }

    fn initialize(&mut self, problem: impl Iterator<Item = impl Iterator<Item = u32>>) -> bool {
        self.initialize_heap();
        if !self.initialize_mem(problem) {
            return false;
        }

        self.decisions[0].time = 0;
        self.decision_level = 0;
        self.stamp = 0;
        self.num_learned = 0;
        self.len_forced = 0;
        self.len_heap = self.num_vars as u32;
        self.scaling_factor = 1.0;

        true
    }

    fn decide(&mut self) -> u32 {
        // [Make a decision.]
        let k = self.heap[0];

        // delete k from heap (Exercise 262 and 266.)
        self.len_heap -= 1;
        self.vars[k as usize].hloc = -1;

        if self.len_heap == 0 {
            return k;
        }

        let i = self.heap[self.len_heap as usize] as usize;
        let alpha = self.vars[i].act;
        let mut j = 0;
        let mut jj = 1usize;

        while jj < self.len_heap as usize {
            let mut alpha2 = self.vars[self.heap[jj] as usize].act;
            if jj + 1 < self.len_heap as usize && self.vars[self.heap[jj + 1] as usize].act > alpha2
            {
                jj += 1;
                alpha2 = self.vars[self.heap[jj] as usize].act;
            }
            if alpha > alpha2 {
                jj = self.len_heap as usize;
            } else {
                self.heap[j] = self.heap[jj];
                self.vars[self.heap[jj] as usize].hloc = j as i32;
                j = jj;
                jj = 2 * j + 1;
            }
        }

        // NOTE: should this be part of the loop above?
        self.heap[j] = i as u32;
        self.vars[i].hloc = j as i32;

        k
    }

    /// Propagates the most recent decision `l` and forces units, returns false
    /// if a conflict is detected
    fn propagate(&mut self, l: u32) -> Option<u32> {
        // do step C4 for all c in the watch list of \bar l

        // iterate through all clauses watched by l ^ 1; q points to last c in
        // loop to update watch lists
        let mut q = 0;
        let mut c = self.watch[l as usize ^ 1];

        while c != 0 {
            if self.clause_lit(c, 0) == (l ^ 1) {
                // reorder clause (l0 with l1, and watch0 with watch1)
                self.mem.swap(c as usize, c as usize + 1);
                self.mem.swap(c as usize - 3, c as usize - 2);
            }

            let cc = self.clause_watch1(c);

            // Now l_0 is the "other" watched literal, check whether a decision has been made for l_0
            let l0 = self.clause_lit(c, 0);
            if self.is_lit_true(l0) {
                // l_0 is already true, and therefore the clause is satisfied
                // (*)
                if q != 0 {
                    self.mem[q as usize - 3] = c;
                } else {
                    self.watch[l as usize ^ 1] = c;
                    q = c;
                }
            } else {
                // l_0 is not true, so let's check for an undecided literal lj
                if let Some(j) =
                    (2..self.clause_len(c)).find(|&j| !self.is_lit_false(self.clause_lit(c, j)))
                {
                    // We have found some undecided literal lj
                    // (where j >= 2).  Move current clause c into
                    // the watch list of that literal and re-order
                    // clause accordingly.

                    // we found some undecided lj, so watch clause on lj
                    // swap lj with l1
                    self.mem.swap((c + 1) as usize, (c + j) as usize);

                    let l1 = self.clause_lit(c, 1) as usize;
                    self.mem[c as usize - 3] = self.watch[l1];
                    self.watch[l1] = c;
                } else {
                    // (*)
                    if q != 0 {
                        self.mem[q as usize - 3] = c;
                    } else {
                        self.watch[l as usize ^ 1] = c;
                        q = c;
                    }

                    // if l0 has a value (i.e., it is false we have found
                    // conflict with l0 as conflict literal)
                    if self.vars[l0 as usize >> 1].val >= 0 {
                        return Some(c);
                    } else {
                        // if l0 has no value we force it
                        info!(
                            "force unit {} at level {}, F = {}",
                            Self::lit_to_str(l0),
                            self.decision_level,
                            self.len_trail
                        );

                        self.trail[self.len_trail] = l0;
                        let var = &mut self.vars[l0 as usize >> 1];
                        var.tloc = self.len_trail as i32;
                        var.val = (2 * self.decision_level + (l0 & 1)) as i32;
                        self.reasons[l0 as usize] = c;
                        self.len_trail += 1;
                    }
                }
            }

            c = cc;
        }

        // (*)
        if q != 0 {
            self.mem[q as usize - 3] = c;
        } else {
            self.watch[l as usize ^ 1] = c;
        }

        None
    }

    /// Resolves a conflict clause from an initial clause `c` as described in
    /// Exercise 263.
    ///
    /// Returns l' and b array, and max level d'
    fn resolve_conflict_clause(&mut self, c: u32) -> (u32, Vec<u32>, u32) {
        let mut dd = 0;
        let mut q = 0;
        let mut new_clause = vec![];

        self.stamp += 3;
        self.lit_var_mut(self.clause_lit(c, 0)).stamp = self.stamp;
        self.bump(self.clause_lit(c, 0));

        let mut t = self.vars[self.clause_lit(c, 0) as usize >> 1].tloc;
        for j in 1..self.clause_len(c) {
            let lj = self.clause_lit(c, j);
            self.blit(lj, &mut q, &mut new_clause, &mut dd);
            t = std::cmp::max(t, self.vars[lj as usize >> 1].tloc);
        }

        while q > 0 {
            let l = self.trail[t as usize];
            t -= 1;
            if self.vars[l as usize >> 1].stamp == self.stamp {
                q -= 1;
                // TODO: move out of if?
            }
            let rc = self.reasons[l as usize];
            if rc != 0 {
                for j in 1..self.clause_len(rc) {
                    let lj = self.clause_lit(rc, j);
                    self.blit(lj, &mut q, &mut &mut new_clause, &mut dd);
                }
            }
        }

        let mut ll = self.trail[t as usize];
        while self.vars[ll as usize >> 1].stamp != self.stamp {
            t -= 1;
            ll = self.trail[t as usize];
        }

        info!(
            "computed conflict clause from {:?}: b = {:?}, ll = {}, t = {}, d' = {}",
            self.clause(c),
            new_clause
                .iter()
                .map(|&l| Self::lit_to_str(l))
                .collect_vec(),
            Self::lit_to_str(ll),
            t,
            dd
        );

        // TODO check for redundancies (Exercise 257)

        (ll, new_clause, dd)
    }

    /// Bump operation as described in Exercise 263 and 262.
    fn bump(&mut self, l: u32) {
        let k = l >> 1;
        let del = self.scaling_factor;

        let var = self.lit_var_mut(l);
        let alpha = var.act;
        var.act = alpha + del;
        let j = self.vars[k as usize].hloc;
        self.siftup(k, j, alpha);
    }

    /// Performs siftup operation described in Exercise 262.
    fn siftup(&mut self, k: u32, mut j: i32, alpha: f64) {
        if j > 0 {
            // siftup
            loop {
                let jj = (j - 1) >> 1;
                let i = self.heap[jj as usize];
                if self.vars[i as usize].act >= alpha {
                    break;
                } else {
                    self.heap[j as usize] = i;
                    self.vars[i as usize].hloc = j;
                    j = jj;
                    if j == 0 {
                        break;
                    }
                }
            }
            self.heap[j as usize] = k;
            self.vars[k as usize].hloc = j;
        }
    }

    /// Blit operation as described in Exercise 263.
    fn blit(&mut self, l: u32, q: &mut u32, new_clause: &mut Vec<u32>, dd: &mut u32) {
        let s = self.stamp;
        let var = self.lit_var_mut(l);

        if var.stamp == s {
            return;
        }

        var.stamp = s;
        assert!(var.val >= 0);
        let p = (var.val >> 1) as u32;
        if p > 0 {
            self.bump(l);
        }
        if p == self.decision_level {
            *q += 1;
        } else {
            new_clause.push(l ^ 1);
            if p > *dd {
                *dd = p;
            }
            if self.decisions[p as usize].stamp <= s {
                self.decisions[p as usize].stamp = s + if self.decisions[p as usize].stamp == s {
                    1
                } else {
                    0
                };
            }
        }
    }

    /// Initializes the heap as a random permutation over ${1, ..., n}$ based on
    /// a variant of Algorithm 3.4.2P.
    ///
    /// This is described in Exercise 7.2.2.2-260.
    fn initialize_heap(&mut self) {
        //let mut rng = thread_rng();
        let mut rng = StdRng::seed_from_u64(655341);
        for k in 1..=self.num_vars {
            let j = rng.gen_range(0..k);

            self.heap[k - 1] = self.heap[j];
            self.heap[j] = k as u32;
        }

        for j in 0..self.num_vars {
            self.vars[self.heap[j] as usize].hloc = j as i32;
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
                    self.vars[var].tloc = self.len_trail as i32;
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

struct Clause<'a> {
    solver: &'a CDCLSolver,
    clause: usize,
    len: usize,
}

impl<'a> Clause<'a> {
    pub fn new(solver: &'a CDCLSolver, clause: u32) -> Self {
        Self {
            solver,
            clause: clause as usize,
            len: solver.mem[clause as usize - 1] as usize,
        }
    }
}

impl Debug for Clause<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        for j in 0..self.len {
            write!(
                f,
                " {}",
                CDCLSolver::lit_to_str(self.solver.mem[self.clause + j])
            )?;
        }
        write!(f, " )")
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use crate::{waerden, CDCLSolver};

    #[test]
    fn test_waerden339() {
        test_logger::ensure_env_logger_initialized();

        let waerden = waerden(3, 3, 9);
        let problem = waerden.iter().map(|clause| {
            clause
                .iter()
                .map(|&l| (l.abs() * 2 + if l < 0 { 1 } else { 0 }) as u32)
        });

        let mut solver = CDCLSolver::new(9);
        assert!(!solver.solve(problem));
    }

    #[test]
    fn test_waerden33() {
        test_logger::ensure_env_logger_initialized();

        for n in 3..=9 {
            let waerden = waerden(3, 3, n);
            let problem = waerden.iter().map(|clause| {
                clause
                    .iter()
                    .map(|&l| (l.abs() * 2 + if l < 0 { 1 } else { 0 }) as u32)
            });

            let mut solver = CDCLSolver::new(n);

            assert_eq!(solver.solve(problem), n < 9, "invalid result for n = {}", n);
        }
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
