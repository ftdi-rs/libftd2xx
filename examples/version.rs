#[deny(unsafe_code, warnings)]
use libftd2xx::{library_version, Ftdi};
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    println!("Library Version: {}", library_version()?);

    let mut ft = Ftdi::new()?;
    let version = ft.driver_version()?;
    println!("Driver Version: {}", version);

    Ok(())
}
