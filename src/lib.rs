mod solver;
pub use solver::{Error, Lit, Result, Solver, Var};

mod algorithms {
    mod backtrack;
    pub use backtrack::BacktrackingSolver;
}

pub use algorithms::BacktrackingSolver;
