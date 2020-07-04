//! This example is adapted from the [MPSSE Basics] application note from FTDI.
//!
//! Get out your logic analyzer or oscilloscope!
//!
//! On the FT232H this will toggle ADBUS0 from high to low.
//!
//! [MPSSE Basics]: https://www.ftdichip.com/Support/Documents/AppNotes/AN_135_MPSSE_Basics.pdf
#[deny(unsafe_code, warnings)]
use libftd2xx::{BitMode, Ftdi};
use std::error::Error;
use std::process;
use std::thread;
use std::time::Duration;

fn main() -> Result<(), Box<dyn Error>> {
    let mut ft = Ftdi::open_by_index(0)?;
    ft.reset()?;
    let mut buf: [u8; 4096] = [0; 4096];
    let rx_bytes = ft.queue_status()? as usize;

    if rx_bytes > 0 {
        ft.read(&mut buf[0..rx_bytes])?;
    }

    ft.set_usb_parameters(65536)?;
    ft.set_chars(0, false, 0, false)?;
    ft.set_timeouts(Duration::from_millis(0), Duration::from_millis(1000))?;
    ft.set_latency_timer(Duration::from_millis(2))?;
    ft.set_flow_control_rts_cts()?;
    ft.set_bit_mode(0x0, BitMode::Reset)?;
    ft.set_bit_mode(0x0, BitMode::Mpsse)?;

    // From the application note "Wait for all the USB stuff to complete and work"
    thread::sleep(Duration::from_millis(100));

    // enable internal loop-back
    {
        let num_written = ft.write(&[0x84])?;
        assert_eq!(num_written, 1);
        let rx_bytes = ft.queue_status()?;
        println!("rx_bytes={}", rx_bytes);
        if rx_bytes != 0 {
            ft.purge_all()?;
        }
    }

    // synchronize MPSSE
    {
        let num_written = ft.write(&[0xAB])?;
        assert_eq!(num_written, 1);
        let mut num_bytes;
        loop {
            num_bytes = ft.queue_status()?;
            if num_bytes > 0 {
                break;
            }
        }

        let mut buf: [u8; 65536] = [0; 65536];
        let num_read = ft.read(&mut buf[0..(num_bytes as usize)])?;

        let mut command_echoed = false;
        for count in 0..(num_read as usize) {
            if buf[count] == 0xFA && buf[count + 1] == 0xAB {
                command_echoed = true;
                break;
            }
        }

        if command_echoed == false {
            println!("Error in synchronizing the MPSSE");
            process::exit(1);
        } else {
            println!("Successfully synchronized the MPSSE")
        }
    }

    // disable loopback
    {
        let num_written = ft.write(&[0x85])?;
        assert_eq!(num_written, 1);
        let rx_bytes = ft.queue_status()?;
        assert_eq!(rx_bytes, 0);
    }

    // Set ADBUS0 low.
    {
        let num_written = ft.write(&[0x81])?;
        assert_eq!(num_written, 1);

        // wait for data to be transmitted and returned by the device driver
        // see latency timer above
        thread::sleep(Duration::from_millis(10));

        let rx_bytes = ft.queue_status()?;
        assert_eq!(rx_bytes, 1);

        let mut buf: [u8; 1] = [0; 1];
        let num_read = ft.read(&mut buf)?;
        assert_eq!(num_read, 1);

        println!("GPIO low-byte 0x{:X}", buf[0]);

        let num_written = ft.write(&[0x80, buf[0] & 0xFE, 0xFB])?;
        assert_eq!(num_written, 3);

        thread::sleep(Duration::from_millis(10));
    }

    ft.close()?;

    Ok(())
}
