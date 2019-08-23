// Copyright 2019 Intel Corporation. All Rights Reserved.
//
// Copyright 2017 The Chromium OS Authors. All rights reserved.
//
// SPDX-License-Identifier: (Apache-2.0 AND BSD-3-Clause)

use libc;
use std::ffi::{CString, OsStr, OsString};
use std::fs;
use std::os::unix::ffi::OsStringExt;
use std::path::{Path, PathBuf};

use crate::errno::{errno_result, Error, Result};

/// Create and remove a temporary directory.  The directory will be maintained for the lifetime of
/// the `TempDir` object.
pub struct TempDir {
    path: PathBuf,
}

impl TempDir {
    /// Creates a new tempory directory.
    /// The directory will be removed when the object goes out of scope.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::path::Path;
    /// # use std::path::PathBuf;
    /// # use vmm_sys_util::tempdir::TempDir;
    /// # fn test_create_temp_dir() -> Result<(), ()> {
    ///       let t = TempDir::new("/tmp/testdir").map_err(|_| ())?;
    ///       assert!(t.as_path().unwrap().exists());
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new<P: AsRef<OsStr>>(prefix: P) -> Result<TempDir> {
        let mut dir_string = prefix.as_ref().to_os_string();
        dir_string.push("XXXXXX");
        // unwrap this result as the internal bytes can't have a null with a valid path.
        let dir_name = CString::new(dir_string.into_vec()).unwrap();
        let mut dir_bytes = dir_name.into_bytes_with_nul();
        let ret = unsafe {
            // Creating the directory isn't unsafe.  The fact that it modifies the guts of the path
            // is also OK because it only overwrites the last 6 Xs added above.
            libc::mkdtemp(dir_bytes.as_mut_ptr() as *mut libc::c_char)
        };
        if ret.is_null() {
            return errno_result();
        }
        dir_bytes.pop(); // Remove the null becasue from_vec can't handle it.
        Ok(TempDir {
            path: PathBuf::from(OsString::from_vec(dir_bytes)),
        })
    }

    /// Removes the temporary directory.  Calling this is optional as dropping a `TempDir` object
    /// will also remove the directory.  Calling remove explicitly allows for better error handling.
    pub fn remove(&self) -> Result<()> {
        fs::remove_dir_all(&self.path).map_err(Error::from)
    }

    /// Returns the path to the tempdir if it is currently valid
    pub fn as_path(&self) -> &Path {
        self.path.as_ref()
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = self.remove();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_dir() {
        let t = TempDir::new("/tmp/asdf").unwrap();
        let path = t.as_path();
        assert!(path.exists());
        assert!(path.is_dir());
        assert!(path.starts_with("/tmp/"));
    }

    #[test]
    fn test_remove_dir() {
        let t = TempDir::new("/tmp/asdf").unwrap();
        let path = t.as_path().to_owned();
        assert!(t.remove().is_ok());
        // Calling remove twice returns error.
        assert!(t.remove().is_err());
        assert!(!path.exists());
    }

    #[test]
    fn test_drop() {
        use std::mem::drop;
        let t = TempDir::new("/tmp/asdf").unwrap();
        let path = t.as_path().to_owned();
        // Force tempdir object to go out of scope.
        drop(t);

        assert!(!(path.exists()));
    }

}
