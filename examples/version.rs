#![deny(unsafe_code, warnings)]
use libftd2xx::{library_version, FtStatus, Ftdi, FtdiCommon};

fn main() -> Result<(), FtStatus> {
    println!("Library Version: {}", library_version()?);

    let mut ft = Ftdi::new()?;
    let version = ft.driver_version()?;
    println!("Driver Version: {version}");

    Ok(())
}
