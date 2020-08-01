use libftd2xx::{DeviceTypeError, Ft4232h, FtdiEeprom};

fn main() -> Result<(), DeviceTypeError> {
    let mut ft = Ft4232h::with_serial_number("FT4PWSEOA")?;
    let eeprom = ft.eeprom_read()?;
    println!("FT4232H EEPROM contents: {:?}", eeprom);

    Ok(())
}
