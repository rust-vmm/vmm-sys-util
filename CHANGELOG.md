# v0.7.0

* Switched to Rust edition 2018.
* Added the `metric` module that provides a `Metric` interface as well as a
  default implementation for `AtomicU64`.

# v0.6.1

* Implemented `From<io::Error>` for `errno::Error`.

# v0.6.0

* Derived Copy for EpollEvent.
* Implemented Debug for EpollEvent.
* Changed `Epoll::ctl` signature such that `EpollEvent` is passed by
  value and not by reference.
* Enabled this crate to be used on other Unixes (besides Linux) by using
  target_os = linux where appropriate.

# v0.5.0

* Added conditionally compiled `serde` compatibility to `FamStructWrapper`,
  gated by the `with-serde` feature.
* Implemented `Into<std::io::Error` for `errno::Error`.
* Added a wrapper over `libc::epoll` used for basic epoll operations.

# v0.4.0

* Added Windows support for TempFile and errno::Error.
* Added `into_file` for TempFile which enables the TempFile to be used as a
  regular file.
* Implemented std::error::Error for errno::Error.
* Fixed the implementation of `register_signal_handler` by allowing only
  valid signal numbers.

# v0.3.1

* Advertise functionality for obtaining POSIX real time signal base which is
  needed to provide absolute signals in the API changed in v0.3.0.

# v0.3.0

* Removed `for_vcpu` argument from `signal::register_signal_handler` and
  `signal::validate_signal_num`. Users can now pass absolute values for all
  valid  signal numbers.
* Removed `flag` argument of `signal::register_signal_handler` public methods,
  which now defaults to `libc::SA_SIGINFO`.
* Changed `TempFile::new` and `TempDir::new` to create new temporary files/
  directories inside `$TMPDIR` if set, otherwise inside `/tmp`.
* Added methods which create temporary files/directories with prefix.

# v0.2.1

* Fixed the FamStructWrapper Clone implementation to avoid UB.

# v0.2.0

* fam: updated the macro that generates implementions of FamStruct to
  also take a parameter that specifies the name of the flexible array
  member.

# v0.1.1

* Fixed the Cargo.toml license.
* Fixed some clippy warnings.

# v0.1.0

This is the first vmm-sys-util crate release.

It is a collection of modules implementing helpers and utilities used by
multiple rust-vmm components and rust-vmm based VMMs.
Most of the code in this first release is based on either the crosvm or the
Firecracker projects, or both.

The first release comes with the following Rust modules:

* aio: Safe wrapper over
  [`Linux AIO`](http://man7.org/linux/man-pages/man7/aio.7.html).

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

* sockctrl_msg: Wrapper for sending and receiving messages with file
  descriptors on sockets that accept control messages (e.g. Unix domain
  sockets).

* tempdir: Structure for handling temporary directories.

* tempfile: Struct for handling temporary files as well as any cleanup
  required.

* terminal: Trait for working with
  [`termios`](http://man7.org/linux/man-pages/man3/termios.3.html).

* timerfd: Structure and functions for working with
  [`timerfd`](http://man7.org/linux/man-pages/man2/timerfd_create.2.html).

* write_zeroes: Traits for replacing a range with a hole and writing
  zeroes in a file.
