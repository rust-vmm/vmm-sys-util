// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: BSD-3-Clause

//! Miscellaneous functions related to getting (pseudo) random numbers and
//! strings.
//!
//! NOTE! This should not be used when you do need __real__ random numbers such
//! as for encryption but will probably be suitable when you want locally
//! unique ID's that will not be shared over the network.

use std::ffi::OsString;
use std::str;

/// Gets an ever increasing u64 (at least for this process).
///
/// The number retrieved will be based upon the time of the last reboot (x86_64)
/// and something undefined for other architectures.
pub fn timestamp_cycles() -> u64 {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: Safe because there's nothing that can go wrong with this call.
    unsafe {
        std::arch::x86_64::_rdtsc()
    }

    #[cfg(not(target_arch = "x86_64"))]
    {
        const MONOTONIC_CLOCK_MULTPIPLIER: u64 = 1_000_000_000;

        let mut ts = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        // SAFETY: We initialized the parameters correctly and we trust the function.
        unsafe {
            libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut ts);
        }
        (ts.tv_sec as u64) * MONOTONIC_CLOCK_MULTPIPLIER + (ts.tv_nsec as u64)
    }
}

/// Generate pseudo random u32 numbers based on the current timestamp.
pub fn xor_pseudo_rng_u32() -> u32 {
    let mut t: u32 = timestamp_cycles() as u32;
    // Taken from https://en.wikipedia.org/wiki/Xorshift
    t ^= t << 13;
    t ^= t >> 17;
    t ^ (t << 5)
}

// This will get an array of numbers that can safely be converted to strings
// because they will be in the range [a-zA-Z0-9]. The return vector could be any
// size between 0 and 4.
fn xor_pseudo_rng_u8_alphanumerics(rand_fn: &dyn Fn() -> u32) -> Vec<u8> {
    rand_fn()
        .to_ne_bytes()
        .to_vec()
        .drain(..)
        .filter(|val| {
            (48..=57).contains(val) || (65..=90).contains(val) || (97..=122).contains(val)
        })
        .collect()
}

fn xor_pseudo_rng_u8_bytes(rand_fn: &dyn Fn() -> u32) -> Vec<u8> {
    rand_fn().to_ne_bytes().to_vec()
}

fn rand_alphanumerics_impl(rand_fn: &dyn Fn() -> u32, len: usize) -> OsString {
    let mut buf = OsString::new();
    let mut done = 0;
    loop {
        for n in xor_pseudo_rng_u8_alphanumerics(rand_fn) {
            done += 1;
            buf.push(str::from_utf8(&[n]).unwrap_or("_"));
            if done >= len {
                return buf;
            }
        }
    }
}

fn rand_bytes_impl(rand_fn: &dyn Fn() -> u32, len: usize) -> Vec<u8> {
    let mut buf: Vec<Vec<u8>> = Vec::new();
    let mut num = if len % 4 == 0 { len / 4 } else { len / 4 + 1 };
    while num > 0 {
        buf.push(xor_pseudo_rng_u8_bytes(rand_fn));
        num -= 1;
    }
    buf.into_iter().flatten().take(len).collect()
}

/// Gets a pseudo random OsString of length `len` with characters in the
/// range [a-zA-Z0-9].
pub fn rand_alphanumerics(len: usize) -> OsString {
    rand_alphanumerics_impl(&xor_pseudo_rng_u32, len)
}

/// Get a pseudo random vector of `len` bytes.
pub fn rand_bytes(len: usize) -> Vec<u8> {
    rand_bytes_impl(&xor_pseudo_rng_u32, len)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_timestamp_cycles() {
        for _ in 0..1000 {
            assert!(timestamp_cycles() < timestamp_cycles());
        }
    }

    #[test]
    fn test_xor_pseudo_rng_u32() {
        for _ in 0..1000 {
            assert_ne!(xor_pseudo_rng_u32(), xor_pseudo_rng_u32());
        }
    }

    #[test]
    fn test_xor_pseudo_rng_u8_alphas() {
        let i = 3612982; // 55 (shifted 16 places), 33 (shifted 8 places), 54...
                         // The 33 will be discarded as it is not a valid letter
                         // (upper or lower) or number.
        let s = xor_pseudo_rng_u8_alphanumerics(&|| i);
        if cfg!(target_endian = "big") {
            assert_eq!(vec![55, 54], s);
        } else {
            assert_eq!(vec![54, 55], s);
        }
    }

    #[test]
    fn test_rand_alphanumerics_impl() {
        let s = rand_alphanumerics_impl(&|| 14134, 5);
        if cfg!(target_endian = "big") {
            assert_eq!("76767", s);
        } else {
            assert_eq!("67676", s);
        }
    }

    #[test]
    fn test_rand_alphanumerics() {
        let s = rand_alphanumerics(5);
        assert_eq!(5, s.len());
    }

    #[test]
    fn test_xor_pseudo_rng_u8_bytes() {
        let i = 3612982; // 55 (shifted 16 places), 33 (shifted 8 places), 54...
                         // The 33 will be discarded as it is not a valid letter
                         // (upper or lower) or number.
        let s = xor_pseudo_rng_u8_bytes(&|| i);
        if cfg!(target_endian = "big") {
            assert_eq!(vec![0, 55, 33, 54], s);
        } else {
            assert_eq!(vec![54, 33, 55, 0], s);
        }
    }

    #[test]
    fn test_rand_bytes_impl() {
        let s = rand_bytes_impl(&|| 1234567, 4);
        if cfg!(target_endian = "big") {
            assert_eq!(vec![0, 18, 214, 135], s);
        } else {
            assert_eq!(vec![135, 214, 18, 0], s);
        }
    }

    #[test]
    fn test_rand_bytes() {
        for i in 0..8 {
            assert_eq!(i, rand_bytes(i).len());
        }
    }
}
