use std::ops::Not;

#[derive(Clone, Copy)]
pub struct Var {
    index: u32,
}

impl Var {
    pub fn new(index: u32) -> Self {
        Self { index }
    }
}

impl Into<Lit> for Var {
    fn into(self) -> Lit {
        Lit::pos(self)
    }
}

impl Not for Var {
    type Output = Lit;

    fn not(self) -> Self::Output {
        Lit::neg(self)
    }
}

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit {
    pub index: u32,
}

impl Lit {
    pub fn pos(var: Var) -> Self {
        Self {
            index: var.index << 1,
        }
    }

    pub fn neg(var: Var) -> Self {
        Self {
            index: (var.index << 1) + 1,
        }
    }
}

impl Not for Lit {
    type Output = Lit;

    fn not(self) -> Self::Output {
        Self {
            index: self.index ^ 1,
        }
    }
}

#[derive(Debug)]
pub enum Error {
    InvalidVariableIndex,
}

pub type Result<T> = std::result::Result<T, Error>;

pub trait Solver {
    fn new(num_vars: u32, num_clauses: u32) -> Self;

    fn var(&self, index: u32) -> Result<Var> {
        if index < 1 || index > self.num_vars() {
            Err(Error::InvalidVariableIndex)
        } else {
            Ok(Var::new(index))
        }
    }

    fn num_vars(&self) -> u32;

    fn num_clauses(&self) -> u32;

    fn add_clause(&mut self, clause: &[Lit]);

    fn solve(&mut self) -> bool;
}
