# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
### Changed
### Fixed
### Removed

## [0.19.0]
### Changed
- Changed the argumenets of the `clock_data_in` method in `MpsseCmdBuilder` to
  allow take a data length instead of a `u8` buffer.

## [0.18.0]
### Added
- Added `MpsseCmdBuilder` to enable writing commands in batches.

## [0.17.0]
### Added
- Added a changelog.
### Changed
- Added a `clock_frequency` field to `MpsseSettings`.

## Prior releases
A changelog was not kept for prior releases.

[Unreleased]: https://github.com/newAM/libftd2xx-rs/compare/0.19.0...HEAD
[0.19.0]: https://github.com/newAM/libftd2xx-rs/releases/tag/0.19.0
[0.18.0]: https://github.com/newAM/libftd2xx-rs/releases/tag/0.18.0
[0.17.0]: https://github.com/newAM/libftd2xx-rs/releases/tag/0.17.0
