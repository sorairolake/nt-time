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
nt-time = "0.10.4"
```

### Crate features

#### `std`

Enables features that depend on the standard library. This is enabled by
default.

#### `large-dates`

Enables the `large-dates` feature of the [`time`] crate.

#### `chrono`

Enables the [`chrono`] crate.

#### `rand`

Enables the [`rand`] crate.

#### `serde`

Enables the [`serde`] crate.

#### `serde-human-readable`

Allows Serde representations to use a human-readable format. This implicitly
enables the `serde` feature.

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
[`time`]: https://crates.io/crates/time
[`chrono`]: https://crates.io/crates/chrono
[`rand`]: https://crates.io/crates/rand
[`serde`]: https://serde.rs/
[CHANGELOG.adoc]: CHANGELOG.adoc
[CONTRIBUTING.adoc]: CONTRIBUTING.adoc
[AUTHORS.adoc]: AUTHORS.adoc
[_REUSE Specification_]: https://reuse.software/spec/
