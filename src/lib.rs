// Copyright 2019 Intel Corporation. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Collection of modules that provides helpers and utilities used by multiple
//! [rust-vmm](https://github.com/rust-vmm/community) components.

#![deny(missing_docs)]
extern crate libc;
#[cfg(feature = "with-serde")]
extern crate serde;
#[cfg(feature = "with-serde")]
extern crate serde_derive;

#[cfg(unix)]
mod unix;
#[cfg(unix)]
pub use unix::*;

pub mod errno;
pub mod fam;
pub mod rand;
pub mod struct_util;
pub mod tempfile;
