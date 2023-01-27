use libftd2xx::{DeviceTypeError, Ft232h, FtdiEeprom};

fn main() -> Result<(), DeviceTypeError> {
    let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    let (eeprom, eeprom_strings) = ft.eeprom_read()?;
    println!("FT232H EEPROM contents: {eeprom:?}");
    println!("FT232H EEPROM strings: {eeprom_strings:?}");
    Ok(())
}
