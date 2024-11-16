[![crates.io](https://img.shields.io/crates/v/libftd2xx.svg)](https://crates.io/crates/libftd2xx)
[![docs.rs](https://docs.rs/libftd2xx/badge.svg)](https://docs.rs/libftd2xx/)
[![CI](https://github.com/ftdi-rs/libftd2xx/workflows/CI/badge.svg)](https://github.com/ftdi-rs/libftd2xx/actions)

# libftd2xx

Rust safe wrapper for the [FTDI D2XX drivers].

This takes the [libftd2xx-ffi] C bindings crate and extends it with rust
safe wrappers.

## Usage
Simply add this crate as a dependency in your `Cargo.toml`.

```toml
[dependencies.libftd2xx]
version = "0.33.1"
# statically link the vendor library, defaults to dynamic if not set
# this will make things "just work" on Linux and Windows
features = ["static"]
```

This is a basic example to get your started.
Check the source code or documentation for more examples.
```rust
use libftd2xx::{Ftdi, FtdiCommon};

let mut ft = Ftdi::new()?;
let info = ft.device_info()?;
println!("Device information: {:?}", info);
```

This crate is just a wrapper around the FTD2XX driver; I2C, SPI, and GPIO
examples using the [`embedded-hal`] traits can be found in
[`ftdi-embedded-hal`].

### udev rules
To access the FTDI USB device as a regular user on Linux you need to update
the [udev] rules.

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

### Linking

By default this crate with use dynamic linking for the vendor library.
Use the `static` feature flag to enable static linking.

#### Dynamic Linking on Linux

The shared object `libftd2xx.so` must exist on your system.
See [FTDI Drivers Installation Guide for Linux] for instructions.

#### Dynamic Linking on Windows

The FTD2XX DLL must exist on your system PATH.
The easiest way to install this is with the vendor provided [setup executable].

#### Static Linking on Linux or Windows

No special considerations are needed, the static library is distributed with
permission from FTDI in the [libftd2xx-ffi] crate.

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
[D2xx Programmers Guide V1.4]: https://ftdichip.com/document/programming-guides/
[FTDI D2XX drivers]: https://www.ftdichip.com/Drivers/D2XX.htm
[FTDI Drivers Installation Guide for Linux]: http://www.ftdichip.cn/Support/Documents/AppNotes/AN_220_FTDI_Drivers_Installation_Guide_for_Linux.pdf
[libftd2xx-ffi]: https://github.com/ftdi-rs/libftd2xx-ffi
[setup executable]: https://www.ftdichip.com/Drivers/CDM/CDM21228_Setup.zip
[udev]: https://en.wikipedia.org/wiki/Udev
[`ftdi-embedded-hal`]: https://github.com/ftdi-rs/ftdi-embedded-hal
[`embedded-hal`]: https://crates.io/crates/embedded-hal
