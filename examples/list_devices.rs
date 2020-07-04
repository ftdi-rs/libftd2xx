#[deny(unsafe_code, warnings)]
use libftd2xx::list_devices;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let mut devices = list_devices()?;

    while let Some(device) = devices.pop() {
        println!("device: {}", device);
    }

    Ok(())
}
