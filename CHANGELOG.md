# v0.1.0

This is the first vmm-sys-util crate release.

It is a collection of modules implementing helpers and utilities used by
multiple rust-vmm components and rust-vmm based VMMs.
Most of the code in this first release is based on either the crosvm or the
Firecracker projects, or both.

The first release comes with the following Rust modules:

* errno: Structures, helpers, and type definitions for working with
  [`errno`](http://man7.org/linux/man-pages/man3/errno.3.html).

* eventfd: Structure and wrapper functions for working with
  [`eventfd`](http://man7.org/linux/man-pages/man2/eventfd.2.html).

* fallocate: Enum and function for dealing with an allocated disk space
  by [`fallocate`](http://man7.org/linux/man-pages/man2/fallocate.2.html).

* fam: Trait and wrapper for working with C defined FAM structures.

* file_traits: Traits for handling file synchronization and length.

* ioctls: Macros and functions for working with
  [`ioctl`](http://man7.org/linux/man-pages/man2/ioctl.2.html).

* poll: Traits and structures for working with
  [`epoll`](http://man7.org/linux/man-pages/man7/epoll.7.html)

* rand: Miscellaneous functions related to getting (pseudo) random
  numbers and strings.

* seek_hole: Traits and implementations over
  [`lseek64`](https://linux.die.net/man/3/lseek64).

* signal: Enums, traits and functions for working with
  [`signal`](http://man7.org/linux/man-pages/man7/signal.7.html).

* tempdir: Structure for handling temporary directories.

* tempfile: Struct for handling temporary files as well as any cleanup
  required.

* terminal: Trait for working with
  [`termios`](http://man7.org/linux/man-pages/man3/termios.3.html).

* timerfd: Structure and functions for working with
  [`timerfd`](http://man7.org/linux/man-pages/man2/timerfd_create.2.html).

* write_zeroes: Traits for replacing a range with a hole and writing
  zeroes in a file.
