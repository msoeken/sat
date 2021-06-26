mod solver;
pub use solver::{Error, Lit, Result, Solver, Var};

mod algorithms {
    mod backtrack;
    pub use backtrack::BacktrackingSolver;

    mod watching;
}

mod problems {
    mod waerden;

    pub use waerden::waerden;
}

pub use algorithms::BacktrackingSolver;
