// Copyright 2019 Intel Corporation. All Rights Reserved.
//
// Copyright 2018 The Chromium OS Authors. All rights reserved.
//
// SPDX-License-Identifier: (Apache-2.0 AND BSD-3-Clause)

//! Traits for replacing a range with a hole and writing zeroes in a file.

use std::cmp::min;
use std::io::{Result, Seek, Write};

/// A trait for writing zeroes to a stream.
pub trait WriteZeroes {
    /// Write zeroes to a stream.
    ///
    /// Write `length` bytes of zeroes to the stream, returning how many
    /// bytes were written.
    fn write_zeroes(&mut self, length: usize) -> Result<usize>;
}

impl<T: Seek + Write> WriteZeroes for T {
    fn write_zeroes(&mut self, length: usize) -> Result<usize> {
        // write a buffer of zeroes until we have written up to length.
        let buf_size = min(length, 0x10000);
        let buf = vec![0u8; buf_size];
        let mut nwritten: usize = 0;
        while nwritten < length {
            let remaining = length - nwritten;
            let write_size = min(remaining, buf_size);
            nwritten += self.write(&buf[0..write_size])?;
        }
        Ok(length)
    }
}

#[cfg(test)]
#[allow(clippy::unused_io_amount)]
mod tests {
    use super::*;
    use std::fs::OpenOptions;
    use std::io::{Read, Seek, SeekFrom};
    use std::path::PathBuf;

    use crate::tempdir::TempDir;

    #[test]
    fn simple_test() {
        let tempdir = TempDir::new_with_prefix("/tmp/write_zeroes_test").unwrap();
        let mut path = PathBuf::from(tempdir.as_path());
        path.push("file");
        let mut f = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(&path)
            .unwrap();
        f.set_len(16384).unwrap();

        // Write buffer of non-zero bytes to offset 1234
        let orig_data = [0x55u8; 5678];
        f.seek(SeekFrom::Start(1234)).unwrap();
        f.write(&orig_data).unwrap();

        // Read back the data plus some overlap on each side
        let mut readback = [0u8; 16384];
        f.seek(SeekFrom::Start(0)).unwrap();
        f.read(&mut readback).unwrap();
        // Bytes before the write should still be 0
        for read in readback[0..1234].iter() {
            assert_eq!(*read, 0);
        }
        // Bytes that were just written should be 0x55
        for read in readback[1234..(1234 + 5678)].iter() {
            assert_eq!(*read, 0x55);
        }
        // Bytes after the written area should still be 0
        for read in readback[(1234 + 5678)..].iter() {
            assert_eq!(*read, 0);
        }

        // Overwrite some of the data with zeroes
        f.seek(SeekFrom::Start(2345)).unwrap();
        f.write_zeroes(4321).expect("write_zeroes failed");
        // Verify seek position after write_zeroes()
        assert_eq!(f.seek(SeekFrom::Current(0)).unwrap(), 2345 + 4321);

        // Read back the data and verify that it is now zero
        f.seek(SeekFrom::Start(0)).unwrap();
        f.read(&mut readback).unwrap();
        // Bytes before the write should still be 0
        for read in readback[0..1234].iter() {
            assert_eq!(*read, 0);
        }
        // Original data should still exist before the write_zeroes region
        for read in readback[1234..2345].iter() {
            assert_eq!(*read, 0x55);
        }
        // The write_zeroes region should now be zero
        for read in readback[2345..(2345 + 4321)].iter() {
            assert_eq!(*read, 0);
        }
        // Original data should still exist after the write_zeroes region
        for read in readback[(2345 + 4321)..(1234 + 5678)].iter() {
            assert_eq!(*read, 0x55);
        }
        // The rest of the file should still be 0
        for read in readback[(1234 + 5678)..].iter() {
            assert_eq!(*read, 0);
        }
    }

    #[test]
    fn large_write_zeroes() {
        let tempdir = TempDir::new_with_prefix("/tmp/write_zeroes_test").unwrap();
        let mut path = PathBuf::from(tempdir.as_path());
        path.push("file");
        let mut f = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(&path)
            .unwrap();
        f.set_len(16384).unwrap();

        // Write buffer of non-zero bytes
        let orig_data = [0x55u8; 0x20000];
        f.seek(SeekFrom::Start(0)).unwrap();
        f.write(&orig_data).unwrap();

        // Overwrite some of the data with zeroes
        f.seek(SeekFrom::Start(0)).unwrap();
        f.write_zeroes(0x10001).expect("write_zeroes failed");
        // Verify seek position after write_zeroes()
        assert_eq!(f.seek(SeekFrom::Current(0)).unwrap(), 0x10001);

        // Read back the data and verify that it is now zero
        let mut readback = [0u8; 0x20000];
        f.seek(SeekFrom::Start(0)).unwrap();
        f.read(&mut readback).unwrap();
        // The write_zeroes region should now be zero
        for read in readback[0..0x10001].iter() {
            assert_eq!(*read, 0);
        }
        // Original data should still exist after the write_zeroes region
        for read in readback[0x10001..0x20000].iter() {
            assert_eq!(*read, 0x55);
        }
    }
}
