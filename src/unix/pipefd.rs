// SPDX-License-Identifier: BSD-3-Clause
//! Structure and wrapper functions for working with
//! [`pipe`](https://man7.org/linux/man-pages/man2/pipe.2.html).

use std::{
    fs::File,
    io::{self, Read, Write},
    os::fd::{AsRawFd, FromRawFd, RawFd},
    result,
};

pub use libc::{O_CLOEXEC, O_NONBLOCK};

/// A safe wrapper around Unix
/// [`pipe`](https://man7.org/linux/man-pages/man2/pipe.2.html).
#[derive(Debug)]
pub struct PipeFd {
    rfd: File,
    wfd: File,
}

impl PipeFd {
    /// Create a new PipeFd with an initial value.
    ///
    /// # Arguments
    ///
    /// * `flag`: The initial value used for creating the `PipeFd`.
    ///   Refer to Linux [`pipe`](https://man7.org/linux/man-pages/man2/pipe.2.html).
    /// # Examples
    ///
    /// ```
    /// use vmm_sys_util::pipefd::{PipeFd, O_NONBLOCK};
    ///
    /// PipeFd::new(O_NONBLOCK).unwrap();
    /// ```
    pub fn new(flag: i32) -> result::Result<PipeFd, io::Error> {
        let mut fds: [RawFd; 2] = [-1, -1];
        // SAFETY: This is safe because pipe merely allocated two pipefds for
        // our process and we handle the error case.
        let ret = unsafe { libc::pipe(fds.as_mut_ptr()) };
        if ret < 0 {
            Err(io::Error::last_os_error())
        } else {
            let set_fd_flags = |fd: RawFd| -> io::Result<()> {
                // SAFETY: This is safe because fcntl merely queries the file descriptor's
                // status flags an fd for our process and we handle the error case.
                let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
                if flags < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: This is safe because fcntl merely sets the file descriptor's
                // status flags an fd for our process and we handle the error case.
                if unsafe { libc::fcntl(fd, libc::F_SETFL, flags | flag) } < 0 {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            };

            set_fd_flags(fds[0])?;
            set_fd_flags(fds[1])?;

            Ok(PipeFd {
                // SAFETY: This is safe because we checked ret for success and know
                // the kernel gave us an fd that we own.
                rfd: unsafe { File::from_raw_fd(fds[0]) },
                // SAFETY: This is safe because we checked ret for success and know
                // the kernel gave us an fd that we own.
                wfd: unsafe { File::from_raw_fd(fds[1]) },
            })
        }
    }

    /// Return a read fd in pipefd.
    pub fn get_rfd(&self) -> RawFd {
        self.rfd.as_raw_fd()
    }

    /// Return a write fd in pipefd.
    pub fn get_wfd(&self) -> RawFd {
        self.wfd.as_raw_fd()
    }

    /// Add a value to the pipfd's buffer.
    ///
    ///
    /// # Arguments
    ///
    /// * `v`: the value to be added to the pipefd's buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use vmm_sys_util::pipefd::{PipeFd, O_NONBLOCK};
    ///
    /// let mut evt = PipeFd::new(O_NONBLOCK).unwrap();
    /// evt.write(55).unwrap();
    /// ```
    pub fn write(&mut self, v: u64) -> result::Result<(), io::Error> {
        self.wfd.write_all(&v.to_ne_bytes())
    }

    /// Read a value from the pipefd.
    ///
    /// # Examples
    ///
    /// ```
    /// use vmm_sys_util::pipefd::{PipeFd, O_NONBLOCK};
    ///
    /// let mut evt = PipeFd::new(O_NONBLOCK).unwrap();
    /// evt.write(55).unwrap();
    /// assert_eq!(evt.read().unwrap(), 55);
    /// ```
    pub fn read(&mut self) -> result::Result<u64, io::Error> {
        let mut buf = [0u8; std::mem::size_of::<u64>()];
        self.rfd
            .read_exact(buf.as_mut_slice())
            .map(|_| u64::from_ne_bytes(buf))
    }

    /// Clone this PipeFd.
    ///
    /// This internally creates a new file descriptor and it will share the same
    /// underlying count within the kernel.
    ///
    /// # Examples
    ///
    /// ```
    /// use vmm_sys_util::pipefd::{PipeFd, O_NONBLOCK};
    ///
    /// let mut evt = PipeFd::new(O_NONBLOCK).unwrap();
    /// let mut evt_clone = evt.try_clone().unwrap();
    /// evt.write(923).unwrap();
    /// assert_eq!(evt_clone.read().unwrap(), 923);
    /// ```
    pub fn try_clone(&self) -> result::Result<PipeFd, io::Error> {
        Ok(PipeFd {
            rfd: self.rfd.try_clone()?,
            wfd: self.wfd.try_clone()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        PipeFd::new(O_NONBLOCK).unwrap();
        PipeFd::new(0).unwrap();
    }

    #[test]
    fn test_read_write() {
        let mut evt = PipeFd::new(O_NONBLOCK).unwrap();
        evt.write(55).unwrap();
        assert_eq!(evt.read().unwrap(), 55);
    }

    #[test]
    fn test_read_nothing() {
        let mut evt = PipeFd::new(O_NONBLOCK).unwrap();
        let r = evt.read();
        match r {
            Err(ref inner) if inner.kind() == io::ErrorKind::WouldBlock => (),
            _ => panic!("Unexpected"),
        }
    }
    #[test]
    fn test_clone() {
        let mut evt = PipeFd::new(O_NONBLOCK).unwrap();
        let mut evt_clone = evt.try_clone().unwrap();
        evt.write(923).unwrap();
        assert_eq!(evt_clone.read().unwrap(), 923);
    }
}
