#![deny(unsafe_code, warnings)]
use libftd2xx::{num_devices, Ftd2xxError};

fn main() -> Result<(), Ftd2xxError> {
    let num_devices = num_devices()?;
    println!("Number of devices: {}", num_devices);

    Ok(())
}
