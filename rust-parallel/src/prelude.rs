//! The filament prelude: import everything needed to use parallel
//! iterators.
//!
//! ```
//! use filament::prelude::*;
//! ```

pub use crate::iter::FromParallelIterator;
pub use crate::iter::IndexedParallelIterator;
pub use crate::iter::IntoParallelIterator;
pub use crate::iter::IntoParallelRefIterator;
pub use crate::iter::IntoParallelRefMutIterator;
pub use crate::iter::ParallelExtend;
pub use crate::iter::ParallelIterator;
pub use crate::slice::ParallelSlice;
pub use crate::slice::ParallelSliceMut;
