#![deny(unsafe_code, warnings)]
use libftd2xx::{num_devices, FtStatus};

fn main() -> Result<(), FtStatus> {
    let num_devices = num_devices()?;
    println!("Number of devices: {}", num_devices);

    Ok(())
}
