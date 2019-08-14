// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: BSD-3-Clause

//! Struct for handling temporary files as well as any cleanup required.
//!
//! The temporary files will be created with a name available as well as having
//! an exposed `fs::File` for reading/writing.
//!
//! The file will be removed when the object goes out of scope.
//!
//! # Examples
//!
//! ```
//! use std::io::Write;
//! use std::path::{Path, PathBuf};
//! use vmm_sys_util::tempfile::TempFile;
//! let t = TempFile::new("/tmp/testfile").unwrap();
//! let mut f = t.as_file();
//! f.write_all(b"hello world").unwrap();
//! f.sync_all().unwrap();

use std::ffi::{CString, OsStr};
use std::fs;
use std::fs::File;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::io::FromRawFd;
use std::path::{Path, PathBuf};

use libc;

use crate::errno::{errno_result, Error, Result};

/// Wrapper for working with temporary files.
///
/// The file will be maintained for the lifetime of the `TempFile` object.
pub struct TempFile {
    path: PathBuf,
    file: File,
}

impl TempFile {
    /// Creates the TempFile
    ///
    /// # Arguments
    ///
    /// `prefix`: The path and filename where to creat the temporary file. Six
    /// random alphanumeric characters will be added to the end of this to form
    /// the filename.
    pub fn new<P: AsRef<OsStr>>(prefix: P) -> Result<TempFile> {
        let mut os_fname = prefix.as_ref().to_os_string();
        os_fname.push("XXXXXX");

        let raw_fname = CString::new(os_fname.into_vec()).unwrap().into_raw();

        // Safe because I'm sure `raw_fname` is a valid CString.
        let fd = unsafe { libc::mkstemp(raw_fname) };

        // The `raw_fname` is the same as `os_fname` (which is `prefix` with X's
        // appended). The X's are documented as "six characters" which seem to
        // always be alphanumerics so appears safe.
        let c_tempname = unsafe { CString::from_raw(raw_fname) };
        let os_tempname = OsStr::from_bytes(c_tempname.as_bytes());

        if fd == -1 {
            return errno_result();
        }

        // Safe because we checked `fd != -1` above and we uniquely own the file
        // descriptor. This `fd` will be freed etc when `File` and thus
        // `TempFile` goes out of scope.
        let file = unsafe { File::from_raw_fd(fd) };

        Ok(TempFile {
            path: PathBuf::from(os_tempname),
            file,
        })
    }

    /// Removes the temporary file.
    ///
    /// Calling this is optional as dropping a `TempFile` object will also
    /// remove the file.  Calling remove explicitly allows for better error
    /// handling.
    pub fn remove(&mut self) -> Result<()> {
        fs::remove_file(&self.path).map_err(Error::from)
    }

    /// Returns the path to the tempfile if it is currently valid
    pub fn as_path(&self) -> &Path {
        &self.path
    }

    /// Returns a reference to the File
    pub fn as_file(&self) -> &File {
        &self.file
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = self.remove();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn test_create_file() {
        fn between(lower: u8, upper: u8, to_check: u8) -> bool {
            (to_check >= lower) && (to_check <= upper)
        }

        let tempname = "/tmp/asdf";
        let t = TempFile::new(tempname).unwrap();
        assert_eq!(tempname, "/tmp/asdf");
        let path = t.as_path().to_owned();

        // Check filename exists
        assert!(path.is_file());

        // Check filename is in the correct location
        assert!(path.starts_with("/tmp"));

        // Check filename has random added
        assert_eq!(path.as_os_str().len(), 15);

        // Check filename has only ascii letters / numbers
        for n in &path.to_string_lossy().as_bytes()[5..] {
            assert!(between(48, 57, *n) || between(65, 90, *n) || between(97, 122, *n));
        }

        // Check we can write to the file
        let mut f = t.as_file();
        f.write_all(b"hello world").unwrap();
        f.sync_all().unwrap();
        assert_eq!(f.metadata().unwrap().len(), 11);
    }

    #[test]
    fn test_remove_file() {
        let mut t = TempFile::new("/tmp/asdf").unwrap();
        let path = t.as_path().to_owned();
        assert!(path.starts_with("/tmp"));

        // Check removal
        assert!(t.remove().is_ok());
        assert!(!path.exists());

        // Check removal doesn't error a second time
        assert!(t.remove().is_err());
    }

    #[test]
    fn test_drop_file() {
        let t = TempFile::new("/tmp/asdf").unwrap();
        let path = t.as_path().to_owned();
        assert!(path.starts_with("/tmp"));
        drop(t);
        assert!(!path.exists());
    }
}
