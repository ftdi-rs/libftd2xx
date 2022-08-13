//! This example is adapted from the [MPSSE Basics] application note from FTDI.
//!
//! Get out your logic analyzer or oscilloscope!
//!
//! On the FT232H this will toggle ADBUS0 from high to low.
//!
//! [MPSSE Basics]: https://www.ftdichip.com/Support/Documents/AppNotes/AN_135_MPSSE_Basics.pdf
#![deny(unsafe_code, warnings)]
use libftd2xx::{BitMode, Ft232h, Ftdi, FtdiCommon, FtdiMpsse};
use std::error::Error;
use std::time::Duration;

fn main() -> Result<(), Box<dyn Error>> {
    let mut ft: Ft232h = Ftdi::new()?.try_into()?;

    ft.reset()?;
    ft.purge_all()?;
    debug_assert_eq!(ft.queue_status()?, 0);
    ft.set_usb_parameters(65536)?;
    ft.set_chars(0, false, 0, false)?;
    ft.set_timeouts(Duration::from_millis(1000), Duration::from_millis(1000))?;
    ft.set_latency_timer(Duration::from_millis(2))?;
    ft.set_flow_control_rts_cts()?;
    ft.set_bit_mode(0x0, BitMode::Reset)?;
    ft.set_bit_mode(0x0, BitMode::Mpsse)?;

    // From the application note "Wait for all the USB stuff to complete and work"
    // This does not seem to be necessary though
    // thread::sleep(Duration::from_millis(100));

    ft.enable_loopback()?;
    ft.synchronize_mpsse()?;
    ft.disable_loopback()?;

    // Toggle AD0
    for _ in 0..8 {
        print!(".");
        ft.set_gpio_lower(0xFF, 0xFF)?;
        ft.set_gpio_lower(0xFE, 0xFF)?;
    }

    println!();

    ft.close()?;

    Ok(())
}
