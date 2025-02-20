<!--
SPDX-FileCopyrightText: 2023 Shun Sakai

SPDX-License-Identifier: Apache-2.0 OR MIT
-->

# nt-time

[![CI][ci-badge]][ci-url]
[![Version][version-badge]][version-url]
![MSRV][msrv-badge]
[![Docs][docs-badge]][docs-url]
![License][license-badge]

**nt-time** is a [Windows file time] library for [Rust].

A Windows file time is a 64-bit unsigned integer value that represents the
number of 100-nanosecond intervals that have elapsed since "1601-01-01 00:00:00
UTC", and is used as timestamps such as [NTFS] and [7z]. Windows uses a file
time to record when an application creates, accesses, or writes to a file.

Note that many environments, such as the [Win32 API], may limit the largest
value of the file time to "+30828-09-14 02:48:05.477580700 UTC", which is equal
to the largest value of a 64-bit signed integer type when represented as an
underlying integer value. This is the largest file time accepted by the
[`FileTimeToSystemTime`] function of the Win32 API.

## Usage

Run the following command in your project directory:

```sh
cargo add nt-time
```

### Crate features

#### `chrono`

Enables the [`chrono`] crate.

#### `large-dates`

Enables the `large-dates` feature of the [`time`] crate.

#### `rand`

Enables the [`rand`] crate.

#### `serde`

Enables the [`serde`] crate.

#### `serde-human-readable`

Allows Serde representations to use a human-readable format. This implicitly
enables the `serde` feature.

#### `std`

Enables features that depend on the standard library. This is enabled by
default.

### `no_std` support

This supports `no_std` mode. Disables the `default` feature to enable this.

### Documentation

See the [documentation][docs-url] for more details.

## Minimum supported Rust version

The minimum supported Rust version (MSRV) of this library is v1.67.1.

## Source code

The upstream repository is available at
<https://github.com/sorairolake/nt-time.git>.

The source code is also available at:

- <https://gitlab.com/sorairolake/nt-time.git>
- <https://codeberg.org/sorairolake/nt-time.git>

## Changelog

Please see [CHANGELOG.adoc].

## Contributing

Please see [CONTRIBUTING.adoc].

## License

Copyright (C) 2023 Shun Sakai (see [AUTHORS.adoc])

This library is distributed under the terms of either the _Apache License 2.0_
or the _MIT License_.

This project is compliant with version 3.2 of the [_REUSE Specification_]. See
copyright notices of individual files for more details on copyright and
licensing information.

[ci-badge]: https://img.shields.io/github/actions/workflow/status/sorairolake/nt-time/CI.yaml?branch=develop&style=for-the-badge&logo=github&label=CI
[ci-url]: https://github.com/sorairolake/nt-time/actions?query=branch%3Adevelop+workflow%3ACI++
[version-badge]: https://img.shields.io/crates/v/nt-time?style=for-the-badge&logo=rust
[version-url]: https://crates.io/crates/nt-time
[msrv-badge]: https://img.shields.io/crates/msrv/nt-time?style=for-the-badge&logo=rust
[docs-badge]: https://img.shields.io/docsrs/nt-time?style=for-the-badge&logo=docsdotrs&label=Docs.rs
[docs-url]: https://docs.rs/nt-time
[license-badge]: https://img.shields.io/crates/l/nt-time?style=for-the-badge
[Windows file time]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times
[Rust]: https://www.rust-lang.org/
[NTFS]: https://en.wikipedia.org/wiki/NTFS
[7z]: https://www.7-zip.org/7z.html
[Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
[`FileTimeToSystemTime`]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-filetimetosystemtime
[`time`]: https://crates.io/crates/time
[`chrono`]: https://crates.io/crates/chrono
[`rand`]: https://crates.io/crates/rand
[`serde`]: https://serde.rs/
[CHANGELOG.adoc]: CHANGELOG.adoc
[CONTRIBUTING.adoc]: CONTRIBUTING.adoc
[AUTHORS.adoc]: AUTHORS.adoc
[_REUSE Specification_]: https://reuse.software/spec/
