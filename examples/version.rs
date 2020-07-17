#![deny(unsafe_code, warnings)]
use libftd2xx::{library_version, Ftd2xxError, Ftdi};

fn main() -> Result<(), Ftd2xxError> {
    println!("Library Version: {}", library_version()?);

    let mut ft = Ftdi::new()?;
    let version = ft.driver_version()?;
    println!("Driver Version: {}", version);

    Ok(())
}
