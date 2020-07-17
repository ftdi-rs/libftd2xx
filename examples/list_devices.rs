#![deny(unsafe_code, warnings)]
use libftd2xx::{list_devices, Ftd2xxError};

fn main() -> Result<(), Ftd2xxError> {
    let mut devices = list_devices()?;

    while let Some(device) = devices.pop() {
        println!("device: {:?}", device);
    }

    Ok(())
}
