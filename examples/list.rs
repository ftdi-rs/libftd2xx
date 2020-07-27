#![deny(unsafe_code, warnings)]
use libftd2xx::{list_devices, FtStatus};

fn main() -> Result<(), FtStatus> {
    let mut devices = list_devices()?;

    while let Some(device) = devices.pop() {
        println!("device: {:?}", device);
    }

    Ok(())
}
