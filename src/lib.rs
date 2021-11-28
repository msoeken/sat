mod solver;
pub use solver::{Error, Lit, Result, Solver, Var};

mod algorithms {
    mod backtrack;
    pub use backtrack::BacktrackingSolver;

    mod watching;
    pub use watching::WatchingSolver;

    mod cdcl;
    pub use cdcl::CDCLSolver;

    mod dpll;
    pub use dpll::DPLLSolver;

    mod lookahead;
}

mod problems {
    mod waerden;

    pub use waerden::waerden;
}

pub mod utils {
    mod buddy_memory;

    pub use buddy_memory::{AllocatedBlock, BuddyMemory};
}

pub use algorithms::{BacktrackingSolver, CDCLSolver, DPLLSolver, WatchingSolver};
pub use problems::waerden;
