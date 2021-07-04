mod solver;
pub use solver::{Error, Lit, Result, Solver, Var};

mod algorithms {
    mod backtrack;
    pub use backtrack::BacktrackingSolver;

    mod watching;
    pub use watching::WatchingSolver;

    mod dpll;
    pub use dpll::DPLLSolver;
}

mod problems {
    mod waerden;

    pub use waerden::waerden;
}

pub mod utils {
    mod buddy_memory;

    pub use buddy_memory::BuddyMemory;
}

pub use algorithms::{BacktrackingSolver, DPLLSolver, WatchingSolver};
pub use problems::waerden;
