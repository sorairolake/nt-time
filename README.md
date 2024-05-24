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

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
nt-time = "0.6.13"
```

### Example

```rust
use core::time::Duration;

use nt_time::{
    time::{macros::datetime, OffsetDateTime},
    FileTime,
};

let ft = FileTime::NT_TIME_EPOCH;
assert_eq!(
    OffsetDateTime::try_from(ft).unwrap(),
    datetime!(1601-01-01 00:00 UTC)
);

let ft = ft + Duration::from_secs(11_644_473_600);
assert_eq!(
    OffsetDateTime::try_from(ft).unwrap(),
    OffsetDateTime::UNIX_EPOCH
);
assert_eq!(ft.to_raw(), 116_444_736_000_000_000);

assert_eq!(FileTime::new(u64::MAX), FileTime::MAX);
```

### Crate features

#### `std`

Enables features that depend on the standard library. This is enabled by
default.

#### `large-dates`

Enables the `large-dates` feature of the [`time`] crate.

#### `chrono`

Enables the [`chrono`] crate.

#### `serde`

Enables the [`serde`] crate.

#### `serde-human-readable`

Allows Serde representations to use a human-readable format. This implicitly
enables the `serde` feature.

#### `zip`

Enables the [`zip`] crate. This implicitly enables the `std` feature.

### `no_std` support

This supports `no_std` mode. Disables the `default` feature to enable this.

### Documentation

See the [documentation][docs-url] for more details.

## Minimum supported Rust version

The minimum supported Rust version (MSRV) of this library is v1.65.0.

## Changelog

Please see [CHANGELOG.adoc].

## Contributing

Please see [CONTRIBUTING.adoc].

## License

Copyright &copy; 2023&ndash;2024 Shun Sakai (see [AUTHORS.adoc])

This library is distributed under the terms of either the _Apache License 2.0_
or the _MIT License_.

This project is compliant with version 3.0 of the [_REUSE Specification_]. See
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
[`time`]: https://crates.io/crates/time
[`chrono`]: https://crates.io/crates/chrono
[`serde`]: https://serde.rs/
[`zip`]: https://crates.io/crates/zip
[CHANGELOG.adoc]: CHANGELOG.adoc
[CONTRIBUTING.adoc]: CONTRIBUTING.adoc
[AUTHORS.adoc]: AUTHORS.adoc
[_REUSE Specification_]: https://reuse.software/spec/
