#![deny(unsafe_code, warnings)]
use libftd2xx::{FtStatus, Ftdi, FtdiCommon};
use std::convert::TryFrom;

fn main() -> Result<(), FtStatus> {
    let mut ft = Ftdi::new()?;
    const MAX_ADDR: u32 = 256;
    const BYTES_PER_ROW: u32 = 16;
    const WORDS_PER_ROW: u32 = BYTES_PER_ROW / 2;
    const NUM_ROWS: u32 = MAX_ADDR / BYTES_PER_ROW;

    let mut ascii: [u8; BYTES_PER_ROW as usize] = [0; BYTES_PER_ROW as usize];

    for r in 0..NUM_ROWS {
        print!("{:04x}  ", r * BYTES_PER_ROW);
        for x in 0..WORDS_PER_ROW {
            let word: u16 = ft.eeprom_word_read(x + r * WORDS_PER_ROW)?;
            let low = u8::try_from(word & 0xFF).unwrap();
            let high = u8::try_from(word >> 8).unwrap();
            print!("{high:02x} {low:02x} ");
            ascii[(x as usize) * 2] = high;
            ascii[(x as usize) * 2 + 1] = low;
            if x == WORDS_PER_ROW / 2 - 1 {
                print!(" ");
            }
        }

        print!(" ");

        for byte in ascii.iter() {
            let ch = if 0x20 <= *byte && *byte < 0x7f {
                *byte as char
            } else {
                '.'
            };
            print!("{ch}");
        }

        println!();
    }

    Ok(())
}
