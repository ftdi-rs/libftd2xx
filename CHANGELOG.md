# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Fixed
- Fixed compilation errors for `aarch64-unknown-linux` targets.

## [0.24.0] - 2020-12-28
### Changed
- **BREAKING CHANGE** `read` and `write` methods now return
  `Result<usize, FtStatus>` where `usize` is the the number of bytes read or
  written.
  Previous `read` and `write` functionality that returned
  `Result<(), TimeoutError>` is replaced by `read_all` and `write_all`.

## [0.23.0] - 2020-10-23
### Changed
- `synchronize_mpsse` will now timeout if no read data is received and a read
  timeout has been set.

## [0.22.0] - 2020-10-15
### Added
- Added `list_devices_fs` to work around vendor driver bug.
- Added `DeviceType::with_pid`.

### Changed
- `Speed`, `DeviceType`, and `DeviceInfo` derive `Ord` and `PartialOrd`.
- The return vector from `list_devices` is now sorted.

## [0.21.1] - 2020-10-08
### Fixed
- Expose `ClockBits`, `ClockBitsIn`, `ClockBitsOut` enums.

## [0.21.0] - 2020-10-07
### Added
- Added methods to `MpsseCmdBuilder` for clocking data bits in and out.

### Fixed
- Modified `clock_data_in` in `MpsseCmdBuilder` to accept `usize` instead of
  `u16` to allow for the maximum command size (65536) to be used.

## [0.20.0] - 2020-10-05
### Changed
- Changed logging in `set_bit_mode` to hex.

### Fixed
- Remove unnecessary mutable reference in `MpsseCmdBuilder`.

## [0.19.0] - 2020-09-30
### Changed
- Changed the arguments of the `clock_data_in` method in `MpsseCmdBuilder` to
  allow take a data length instead of a `u8` buffer.

## [0.18.0] - 2020-09-26
### Added
- Added `MpsseCmdBuilder` to enable writing commands in batches.

## [0.17.0] - 2020-09-13
### Added
- Added a changelog.

### Changed
- Added a `clock_frequency` field to `MpsseSettings`.

## Prior releases
A changelog was not kept for prior releases.

[Unreleased]: https://github.com/newAM/libftd2xx-rs/compare/0.24.0...HEAD
[0.24.0]: https://github.com/newAM/libftd2xx-rs/compare/0.23.0...0.24.0
[0.23.0]: https://github.com/newAM/libftd2xx-rs/compare/0.22.0...0.23.0
[0.22.0]: https://github.com/newAM/libftd2xx-rs/compare/0.21.1...0.22.0
[0.21.1]: https://github.com/newAM/libftd2xx-rs/compare/0.21.0...0.21.1
[0.21.0]: https://github.com/newAM/libftd2xx-rs/compare/0.20.0...0.21.0
[0.20.0]: https://github.com/newAM/libftd2xx-rs/compare/0.19.0...0.20.0
[0.19.0]: https://github.com/newAM/libftd2xx-rs/compare/0.18.0...0.19.0
[0.18.0]: https://github.com/newAM/libftd2xx-rs/compare/0.17.0...0.18.0
[0.17.0]: https://github.com/newAM/libftd2xx-rs/releases/tag/0.17.0
