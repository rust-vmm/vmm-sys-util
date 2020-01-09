// Copyright 2019 Intel Corporation. All Rights Reserved.
//
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
//
// SPDX-License-Identifier: (Apache-2.0 AND BSD-3-Clause)

//! Structures, helpers, and type definitions for working with
//! [`errno`](http://man7.org/linux/man-pages/man3/errno.3.html).

use std::fmt::{Display, Formatter};
use std::io;
use std::result;

use libc::__errno_location;

/// Wrapper over [`errno`](http://man7.org/linux/man-pages/man3/errno.3.html).
///
/// The error number is an integer number set by system calls and some libc
/// functions in case of error.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Error(i32);

/// A specialized [Result](https://doc.rust-lang.org/std/result/enum.Result.html) type
/// for operations that can return `errno`.
///
/// This typedef is generally used to avoid writing out `errno::Error` directly and is
/// otherwise a direct mapping to `Result`.
pub type Result<T> = result::Result<T, Error>;

impl Error {
    /// Creates a new error from the given error number.
    ///
    /// # Arguments
    ///
    /// * `errno`: error number used for creating the `Error`.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate libc;
    /// extern crate vmm_sys_util;
    /// #
    /// # use libc;
    /// use vmm_sys_util::errno::Error;
    ///
    /// let err = Error::new(libc::EBADFD);
    /// ```
    pub fn new(errno: i32) -> Error {
        Error(errno)
    }

    /// Returns the last occurred `errno` wrapped in an `Error`.
    ///
    /// Calling `Error::last()` is the equivalent of using
    /// [`errno`](http://man7.org/linux/man-pages/man3/errno.3.html) in C/C++.
    /// The result of this function only has meaning after a libc call or syscall
    /// where `errno` was set.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate libc;
    /// extern crate vmm_sys_util;
    /// #
    /// # use libc;
    /// # use std::fs::File;
    /// # use std::io::{self, Write};
    /// # use std::os::unix::io::FromRawFd;
    /// use vmm_sys_util::errno::Error;
    /// #
    /// // Writing to an invalid file returns the error number EBADF.
    /// let mut file = unsafe { File::from_raw_fd(-1) };
    /// let _ = file.write(b"test");
    ///
    /// // Retrieve the error number of the previous operation using `Error::last()`:
    /// let write_err = Error::last();
    /// assert_eq!(write_err, Error::new(libc::EBADF));
    /// ```
    pub fn last() -> Error {
        Error(unsafe { *__errno_location() })
    }

    /// Returns the raw integer value (`errno`) corresponding to this Error.
    ///
    /// # Examples
    /// ```
    /// extern crate vmm_sys_util;
    /// use vmm_sys_util::errno::Error;
    ///
    /// let err = Error::new(13);
    /// assert_eq!(err.errno(), 13);
    /// ```
    pub fn errno(self) -> i32 {
        self.0
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        io::Error::from_raw_os_error(self.0).fmt(f)
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Error::new(e.raw_os_error().unwrap_or_default())
    }
}

/// Returns the last `errno` as a [`Result`] that is always an error.
///
/// [`Result`]: type.Result.html
pub fn errno_result<T>() -> Result<T> {
    Err(Error::last())
}

#[cfg(test)]
mod tests {
    use super::*;
    use libc;
    use std::error::Error as _;
    use std::fs::File;
    use std::io::{self, Write};
    use std::os::unix::io::FromRawFd;

    #[test]
    pub fn test_invalid_fd() {
        let mut file = unsafe { File::from_raw_fd(-1) };
        assert!(file.write(b"test").is_err());

        // Test that errno_result returns Err and the error is the expected one.
        let last_err = errno_result::<i32>().unwrap_err();
        assert_eq!(last_err, Error::new(libc::EBADF));

        // Test that the inner value of `Error` corresponds to libc::EBADF.
        assert_eq!(last_err.errno(), libc::EBADF);
        assert!(last_err.source().is_none());

        // Test creating an `Error` from a `std::io::Error`.
        assert_eq!(last_err, Error::from(io::Error::last_os_error()));

        // Test that calling `last()` returns the same error as `errno_result()`.
        assert_eq!(last_err, Error::last());

        // Test the display implementation.
        assert_eq!(
            format!("{}", Error::new(libc::EBADF)),
            "Bad file descriptor (os error 9)"
        );
    }
}
