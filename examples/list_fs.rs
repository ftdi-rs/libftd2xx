#![deny(unsafe_code, warnings)]
use libftd2xx::list_devices_fs;

fn main() -> std::io::Result<()> {
    let mut devices = list_devices_fs()?;

    while let Some(device) = devices.pop() {
        println!("device: {:?}", device);
    }

    Ok(())
}
