// Copyright 2019 Intel Corporation. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Collection of modules that provides helpers and utilities used by multiple
//! [rust-vmm](https://github.com/rust-vmm/community) components.

#![deny(missing_docs)]
extern crate libc;

#[macro_use]
pub mod ioctl;

pub mod aio;
pub mod errno;
pub mod eventfd;
pub mod fallocate;
pub mod fam;
pub mod file_traits;
pub mod poll;
pub mod rand;
pub mod seek_hole;
pub mod signal;
pub mod sock_ctrl_msg;
pub mod tempdir;
pub mod tempfile;
pub mod terminal;
pub mod timerfd;
pub mod write_zeroes;
