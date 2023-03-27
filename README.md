# nt-time

[![CI][ci-badge]][ci-url]
[![Version][version-badge]][version-url]
[![Docs][docs-badge]][docs-url]
![License][license-badge]

**nt-time** is a [Windows NT system time][file-time-docs-url] library for
[Rust][rust-official-url].

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
nt-time = "0.1.0"
```

### Crate features

#### `std`

Enables features that depend on the standard library.
This is enabled by default.

#### `large-dates`

Enables the `large-dates` feature of the [`time`][time-crate-url] crate.

### `no_std` support

This supports `no_std` mode.
Disables the `default` feature to enable this.

### Documentation

See the [documentation][docs-url] for more details.

## Minimum supported Rust version

The minimum supported Rust version (MSRV) of this library is v1.63.0.

## Changelog

Please see [CHANGELOG.adoc](CHANGELOG.adoc).

## Contributing

Please see [CONTRIBUTING.adoc](CONTRIBUTING.adoc).

## License

Copyright &copy; 2023 Shun Sakai (see [AUTHORS.adoc](AUTHORS.adoc))

This library is distributed under the terms of either the _Apache License 2.0_
or the _MIT License_.

See [COPYRIGHT](COPYRIGHT), [LICENSE-APACHE](LICENSE-APACHE) and
[LICENSE-MIT](LICENSE-MIT) for more details.

[ci-badge]: https://github.com/sorairolake/nt-time/workflows/CI/badge.svg
[ci-url]: https://github.com/sorairolake/nt-time/actions?query=workflow%3ACI
[version-badge]: https://img.shields.io/crates/v/nt-time
[version-url]: https://crates.io/crates/nt-time
[docs-badge]: https://img.shields.io/docsrs/nt-time
[docs-url]: https://docs.rs/nt-time
[license-badge]: https://img.shields.io/crates/l/nt-time
[file-time-docs-url]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times
[rust-official-url]: https://www.rust-lang.org/
[time-crate-url]: https://crates.io/crates/time
