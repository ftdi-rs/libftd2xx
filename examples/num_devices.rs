use libftd2xx::num_devices;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let num_devices = num_devices()?;
    println!("Number of devices: {}", num_devices);

    Ok(())
}
