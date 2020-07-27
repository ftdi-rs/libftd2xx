use libftd2xx::{DeviceTypeError, Ft4232h, Ftdi, FtdiEeprom};
use std::convert::TryFrom;

fn main() -> Result<(), DeviceTypeError> {
    let mut ftdi = Ftdi::new()?;
    let mut ft = Ft4232h::try_from(&mut ftdi)?;
    let eeprom = ft.eeprom_read()?;
    println!("FT4232H EEPROM contents: {:?}", eeprom);

    Ok(())
}
