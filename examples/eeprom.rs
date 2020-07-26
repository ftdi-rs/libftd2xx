#![deny(unsafe_code, warnings)]
use libftd2xx::Ftdi;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let mut ft = Ftdi::new()?;
    let eeprom = ft.eeprom_read().unwrap();

    println!("{:?}", eeprom);

    Ok(())
}
