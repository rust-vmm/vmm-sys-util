// Copyright 2019 Intel Corporation. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
extern crate libc;

// Export the syslog module first so that the macros are available to the other modules.
#[macro_use]
pub mod syslog;

#[macro_use]
pub mod ioctl;
/// Structures, helpers, and type definitions for working with
/// [`errno`](http://man7.org/linux/man-pages/man3/errno.3.html).
pub mod errno;
pub mod eventfd;
pub mod fallocate;
pub mod file_traits;
pub mod poll;
pub mod rand;
pub mod seek_hole;
pub mod signal;
pub mod tempdir;
pub mod terminal;
pub mod timerfd;
pub mod write_zeroes;
