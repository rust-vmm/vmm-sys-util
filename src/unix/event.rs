// SPDX-License-Identifier: BSD-3-Clause
//! This is an abstract EventNotifer and EventConsumer for eventfd and pipefd

use std::io::{Read, Write};
use std::{
    fs::File,
    io,
    os::fd::{AsRawFd, FromRawFd, IntoRawFd},
    result,
};

#[cfg(any(target_os = "linux", target_os = "android"))]
pub use libc::{EFD_CLOEXEC, EFD_NONBLOCK};
#[cfg(not(any(target_os = "linux", target_os = "android")))]
pub use libc::{O_CLOEXEC, O_NONBLOCK};

/// EventFlag
/// This enum is used to define flags for the event notifier and consumer.
#[derive(Debug)]
pub enum EventFlag {
    /// No flags set
    NoFlag,
    /// Non-blocking flag
    NonBlock,
    /// Close-on-exec flag
    CloseOnExec,
}

#[cfg(any(target_os = "linux", target_os = "android"))]
impl From<EventFlag> for i32 {
    fn from(flag: EventFlag) -> Self {
        match flag {
            EventFlag::NoFlag => 0,
            EventFlag::NonBlock => libc::EFD_NONBLOCK,
            EventFlag::CloseOnExec => libc::EFD_CLOEXEC,
        }
    }
}

#[cfg(not(any(target_os = "linux", target_os = "android")))]
impl From<EventFlag> for i32 {
    fn from(flag: EventFlag) -> Self {
        match flag {
            EventFlag::NoFlag => 0,
            EventFlag::NonBlock => libc::O_NONBLOCK,
            EventFlag::CloseOnExec => libc::O_CLOEXEC,
        }
    }
}

/// EventNotifier
/// This is a generic event notifier that can be used with eventfd or pipefd.
/// It allows writing a value to the file descriptor to notify an event.
///
/// # Examples
///
/// ```
/// use std::os::fd::FromRawFd;
/// use std::os::unix::io::IntoRawFd;
/// use vmm_sys_util::event::EventNotifier;
/// let (_, writer) = std::io::pipe().expect("Failed to create pipe");
/// let notifier = unsafe { EventNotifier::from_raw_fd(writer.into_raw_fd()) };
/// ```
#[derive(Debug)]
pub struct EventNotifier {
    fd: File,
}

impl EventNotifier {
    /// Write a value to the EventNotifier's fd
    /// Writing 1 to fd is for compatibility with Eventfd
    pub fn notify(&self) -> result::Result<(), io::Error> {
        let v = 1u64;
        (&self.fd).write_all(&v.to_ne_bytes())
    }

    /// Clone this EventNotifier.
    pub fn try_clone(&self) -> result::Result<EventNotifier, io::Error> {
        Ok(EventNotifier {
            fd: self.fd.try_clone()?,
        })
    }
}

impl AsRawFd for EventNotifier {
    fn as_raw_fd(&self) -> std::os::unix::prelude::RawFd {
        self.fd.as_raw_fd()
    }
}

/// Convert a raw file descriptor into an EventNotifier.
impl FromRawFd for EventNotifier {
    unsafe fn from_raw_fd(fd: std::os::unix::prelude::RawFd) -> Self {
        EventNotifier {
            fd: File::from_raw_fd(fd),
        }
    }
}

/// EventReceiver
/// This is a generic event consumer that can be used with eventfd or pipefd.
/// It allows reading a value from the file descriptor to consume an event.
///
/// # Examples
///
/// ```
/// use std::os::fd::FromRawFd;
/// use std::os::unix::io::IntoRawFd;
/// use vmm_sys_util::event::EventConsumer;
/// let (reader, _) = std::io::pipe().expect("Failed to create pipe");
/// let consumer = unsafe { EventConsumer::from_raw_fd(reader.into_raw_fd()) };
/// ```
#[derive(Debug)]
pub struct EventConsumer {
    fd: File,
}

impl EventConsumer {
    /// Read a value from the EventConsumer.
    pub fn consume(&self) -> result::Result<(), io::Error> {
        let mut buf = [0u8; size_of::<u64>()];
        (&self.fd).read_exact(buf.as_mut_slice()).map(|_| Ok(()))?
    }

    /// Clone this EventConsumer.
    pub fn try_clone(&self) -> result::Result<EventConsumer, io::Error> {
        Ok(EventConsumer {
            fd: self.fd.try_clone()?,
        })
    }
}

impl AsRawFd for EventConsumer {
    fn as_raw_fd(&self) -> std::os::unix::prelude::RawFd {
        self.fd.as_raw_fd()
    }
}

/// Convert a raw file descriptor into an EventConsumer.
impl FromRawFd for EventConsumer {
    unsafe fn from_raw_fd(fd: std::os::unix::prelude::RawFd) -> Self {
        EventConsumer {
            fd: File::from_raw_fd(fd),
        }
    }
}

/// Create a new EventNotifier and EventConsumer using a pipe.
///
/// # Arguments
///
/// * `flag` - Flags to set on the file descriptor, such as `O_NONBLOCK` or `O_CLOEXEC`.
///
/// # Examples
///
/// ```
/// use vmm_sys_util::event::{new_event_notifier_and_consumer, EventFlag};
/// let (notifier, consumer) = new_event_notifier_and_consumer(EventFlag::NonBlock)
///     .expect("Failed to create notifier and consumer");
/// notifier.notify().unwrap();
/// assert!(consumer.consume().is_ok());
/// ```
#[cfg(not(any(target_os = "linux", target_os = "android")))]
pub fn new_event_notifier_and_consumer(
    flag: EventFlag,
) -> std::result::Result<(EventNotifier, EventConsumer), io::Error> {
    // Use a pipe for non-Linux platforms.
    let (reader, writer) = std::io::pipe()?;
    // SAFETY: Safe because we check the fd is valid and check the return value.
    let flags = unsafe { libc::fcntl(reader.as_raw_fd(), libc::F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    let flag: i32 = flag.into();
    // SAFETY: Safe because we check the fd is valid and check the return value.
    let ret = unsafe { libc::fcntl(reader.as_raw_fd(), libc::F_SETFL, flags | flag) };
    if ret < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: Safe because we check the fd is valid. And the kernel gave us an fd that we own.
    let notifier = unsafe { EventNotifier::from_raw_fd(writer.into_raw_fd()) };
    // SAFETY: Safe because we check the fd is valid. And the kernel gave us an fd that we own.
    let consumer = unsafe { EventConsumer::from_raw_fd(reader.into_raw_fd()) };
    Ok((notifier, consumer))
}

/// Create a new EventNotifier and EventConsumer using eventfd.
///
/// # Arguments
///
/// * `flag` - Flags to set on the eventfd, such as `EFD_NONBLOCK`, `EFD_CLOEXEC` or `EFD_SEMAPHORE`.
///
/// # Examples
///
/// ```
/// use vmm_sys_util::event::{new_event_notifier_and_consumer, EventFlag};
/// let (notifier, consumer) = new_event_notifier_and_consumer(EventFlag::NonBlock)
///     .expect("Failed to create notifier and consumer");
/// notifier.notify().unwrap();
/// assert!(consumer.consume().is_ok());
/// ```
#[cfg(any(target_os = "linux", target_os = "android"))]
pub fn new_event_notifier_and_consumer(
    flag: EventFlag,
) -> std::result::Result<(EventNotifier, EventConsumer), io::Error> {
    let eventfd = crate::linux::eventfd::EventFd::new(flag.into())?;
    let eventfd_clone = eventfd.try_clone()?;
    // SAFETY: Safe because we check the fd is valid. And the kernel gave us an fd that we own.
    let notifier = unsafe { EventNotifier::from_raw_fd(eventfd.into_raw_fd()) };
    // SAFETY: Safe because we check the fd is valid. And the kernel gave us an fd that we own.
    let consumer = unsafe { EventConsumer::from_raw_fd(eventfd_clone.into_raw_fd()) };
    Ok((notifier, consumer))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{io::pipe, os::fd::IntoRawFd};

    #[test]
    fn test_notify_and_consume() {
        let (reader, writer) = pipe().expect("Failed to create pipe");
        // SAFETY: Safe because we check the fd is valid. And the kernel gave us an fd that we own.
        let notifier = unsafe { EventNotifier::from_raw_fd(writer.into_raw_fd()) };
        // SAFETY: Safe because we check the fd is valid. And the kernel gave us an fd that we own.
        let consumer = unsafe { EventConsumer::from_raw_fd(reader.into_raw_fd()) };

        notifier.notify().unwrap();
        assert!(consumer.consume().is_ok());
    }

    #[test]
    fn test_clone() {
        let (reader, writer) = pipe().expect("Failed to create pipe");
        // SAFETY: Safe because we check the fd is valid. And the kernel gave us an fd that we own.
        let notifier = unsafe { EventNotifier::from_raw_fd(writer.into_raw_fd()) };
        // SAFETY: Safe because we check the fd is valid. And the kernel gave us an fd that we own.
        let consumer = unsafe { EventConsumer::from_raw_fd(reader.into_raw_fd()) };

        let cloned_notifier = notifier.try_clone().expect("Failed to clone notifier");
        let cloned_consumer = consumer.try_clone().expect("Failed to clone consumer");

        cloned_notifier.notify().unwrap();
        assert!(cloned_consumer.consume().is_ok());
    }

    #[test]
    fn test_new_event_notifier_and_consumer() {
        let (notifier, consumer) = new_event_notifier_and_consumer(EventFlag::NoFlag)
            .expect("Failed to create notifier and consumer");
        notifier.notify().unwrap();
        assert!(consumer.consume().is_ok());
    }
}
