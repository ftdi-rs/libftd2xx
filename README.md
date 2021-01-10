![Maintenance](https://img.shields.io/badge/maintenance-experimental-blue.svg)
[![crates.io](https://img.shields.io/crates/v/libftd2xx.svg)](https://crates.io/crates/libftd2xx)
[![docs.rs](https://docs.rs/libftd2xx/badge.svg)](https://docs.rs/libftd2xx/)
[![CI](https://github.com/newAM/libftd2xx-rs/workflows/CI/badge.svg)](https://github.com/newAM/libftd2xx-rs/actions)

# libftd2xx

Rust safe wrapper for the [FTDI D2XX drivers].

This takes the [libftd2xx-ffi] C bindings crate and extends it with rust
safe wrappers.

## Usage
Simply add this crate as a dependency in your `Cargo.toml`.
On Linux the static library is distributed in the [libftd2xx-ffi] crate with
permission from FTDI.

```toml
[dependencies]
libftd2xx = "~0.24.0"
```

This is a basic example to get your started.
Check the source code or documentation for more examples.
```rust
use libftd2xx::{Ftdi, FtdiCommon};

let mut ft = Ftdi::new()?;
let info = ft.device_info()?;
println!("Device information: {:?}", info);
```

### One-time Linux Setup
To access the FTDI USB device as a regular user you need to update the
[udev] rules.

Create a file called `/etc/udev/rules.d/99-ftdi.rules` with:
```
SUBSYSTEM=="usb", ATTRS{idVendor}=="0403", ATTRS{idProduct}=="6001", MODE="0666"
SUBSYSTEM=="usb", ATTRS{idVendor}=="0403", ATTRS{idProduct}=="6010", MODE="0666"
SUBSYSTEM=="usb", ATTRS{idVendor}=="0403", ATTRS{idProduct}=="6011", MODE="0666"
SUBSYSTEM=="usb", ATTRS{idVendor}=="0403", ATTRS{idProduct}=="6014", MODE="0666"
SUBSYSTEM=="usb", ATTRS{idVendor}=="0403", ATTRS{idProduct}=="6015", MODE="0666"
```

Then, reload the rules:
```bash
sudo udevadm control --reload-rules
sudo udevadm trigger
```

### One-time Windows Setup
Unlike Linux the Windows vendor driver is dynamically linked.
The FTD2XX DLL must exist on your system PATH.
The easiest way to install this is with the vendor provided [setup executable].

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

[D2XX Drivers Download Page]: https://www.ftdichip.com/Drivers/D2XX.htm
[D2xx Programmers Guide V1.4]: https://www.ftdichip.com/Support/Documents/ProgramGuides/D2XX_Programmer's_Guide(FT_000071).pdf
[FTDI D2XX drivers]: https://www.ftdichip.com/Drivers/D2XX.htm
[FTDI Drivers Installation Guide for Linux]: http://www.ftdichip.cn/Support/Documents/AppNotes/AN_220_FTDI_Drivers_Installation_Guide_for_Linux.pdf
[libftd2xx-ffi]: https://github.com/newAM/libftd2xx-ffi-rs
[setup executable]: https://www.ftdichip.com/Drivers/CDM/CDM21228_Setup.zip
[udev]: https://en.wikipedia.org/wiki/Udev
