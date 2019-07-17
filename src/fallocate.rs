use std::os::unix::io::AsRawFd;

use crate::errno::{errno_result, Error, Result};

pub enum FallocateMode {
    PunchHole,
    ZeroRange,
}

/// Safe wrapper for `fallocate()`.
pub fn fallocate(
    file: &dyn AsRawFd,
    mode: FallocateMode,
    keep_size: bool,
    offset: u64,
    len: u64,
) -> Result<()> {
    let offset = if offset > libc::off64_t::max_value() as u64 {
        return Err(Error::new(libc::EINVAL));
    } else {
        offset as libc::off64_t
    };

    let len = if len > libc::off64_t::max_value() as u64 {
        return Err(Error::new(libc::EINVAL));
    } else {
        len as libc::off64_t
    };

    let mut mode = match mode {
        FallocateMode::PunchHole => libc::FALLOC_FL_PUNCH_HOLE,
        FallocateMode::ZeroRange => libc::FALLOC_FL_ZERO_RANGE,
    };

    if keep_size {
        mode |= libc::FALLOC_FL_KEEP_SIZE;
    }

    // Safe since we pass in a valid fd and fallocate mode, validate offset and len,
    // and check the return value.
    let ret = unsafe { libc::fallocate64(file.as_raw_fd(), mode, offset, len) };
    if ret < 0 {
        errno_result()
    } else {
        Ok(())
    }
}
