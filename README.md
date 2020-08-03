![Maintenance](https://img.shields.io/badge/maintenance-as--is-yellow.svg)
[![crates.io](https://img.shields.io/crates/v/libftd2xx.svg)](https://crates.io/crates/libftd2xx)
[![docs.rs](https://docs.rs/libftd2xx/badge.svg)](https://docs.rs/libftd2xx/)
[![Build Status](https://travis-ci.com/newAM/libftd2xx-rs.svg?branch=master)](https://travis-ci.com/newAM/libftd2xx-rs)

# libftd2xx

Rust safe wrapper for the [FTDI D2XX drivers].

This takes the [libftd2xx-ffi] C bindings crate and extends it with rust
safe wrappers.

## Usage
Simply add this crate as a dependency in your `Cargo.toml`.
The static library is distributed in the [libftd2xx-ffi] crate with
permission from FTDI.

```toml
[dependencies]
libftd2xx = "~0.8.2"
```

This is a basic example to get your started.
Check the source code or documentation for more examples.
```rust
use libftd2xx::{Ftdi, FtdiCommon};

let mut ft = Ftdi::new()?;
let info = ft.device_info()?;
println!("Device information: {:?}", info);
```

## References

* [D2XX Programmers Guide V1.4]
* [D2XX Drivers Download Page]

## Troubleshooting
### Unknown Device on Linux
Remove the VCP FTDI driver.
```bash
sudo rmmod ftdi_sio
sudo rmmod usbserial
```
See [FTDI Drivers Installation Guide for Linux] for more details.

## Maintainers Notes
### README Generation
The README file is generated with [cargo-readme].

```bash
cargo install cargo-readme
cargo readme > README.md
```

[cargo-readme]: https://github.com/livioribeiro/cargo-readme
[D2XX Drivers Download Page]: https://www.ftdichip.com/Drivers/D2XX.htm
[D2xx Programmers Guide V1.4]: https://www.ftdichip.com/Support/Documents/ProgramGuides/D2XX_Programmer's_Guide(FT_000071).pdf
[FTDI D2XX drivers]: https://www.ftdichip.com/Drivers/D2XX.htm
[FTDI Drivers Installation Guide for Linux]: http://www.ftdichip.cn/Support/Documents/AppNotes/AN_220_FTDI_Drivers_Installation_Guide_for_Linux.pdf
[libftd2xx-ffi]: https://github.com/newAM/libftd2xx-ffi-rs
