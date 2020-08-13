use libftd2xx::{BitMode, Ftdi, FtdiCommon, TimeoutError};

fn main() -> Result<(), TimeoutError> {
    let mut ft = Ftdi::new()?;
    let mask: u8 = 0x00;
    ft.set_bit_mode(mask, BitMode::AsyncBitbang)?;
    let mode = ft.bit_mode()?;
    for pin_index in 0..8 {
        if mode & (1 << pin_index) == 0 {
            println!("Pin {}: Off", pin_index);
        } else {
            println!("Pin {}: On", pin_index);
        }
    }
    ft.close()?;

    Ok(())
}
