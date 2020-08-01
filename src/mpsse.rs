use super::{DeviceType, FtdiCommon, TimeoutError};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
#[allow(dead_code)]
enum MpsseCmd {
    DataLsbFirst = 0x08,
    DataOutBytesPosEdge = 0x10,
    DataOutBytesNegEdge = 0x11,
    DataOutBitsPosEdge = 0x12,
    DataOutBitsNegEdge = 0x13,
    DataInBytesPosEdge = 0x20,
    DataInBitsPosEdge = 0x22,
    DataInBytesNegEdge = 0x24,
    DataInBitsNegEdge = 0x26,
    DataBytesInPosOutNegEdge = 0x31,
    DataBitsInPosOutNegEdge = 0x33,
    DataBytesInNegOutPosEdge = 0x34,
    DataBitsInNegOutPosEdge = 0x36,
    SetDataBitsLowbyte = 0x80,
    GetDataBitsLowbyte = 0x81,
    SetDataBitsHighbyte = 0x82,
    GetDataBitsHighbyte = 0x83,
    EnableLoopback = 0x84,
    DisableLoopback = 0x85,
    SetClockFrequency = 0x86,
    SendImmediate = 0x87,
    EnableClockDivide = 0x8A,
    DisableClockDivide = 0x8B,
    Enable3PhaseClocking = 0x8C,
    Disable3PhaseClocking = 0x8D,
    EnableDriveOnlyZero = 0x9E,
}

fn check_limits(device: DeviceType, frequency: u32, max: u32) {
    const MIN: u32 = 92;
    assert!(
        frequency >= MIN,
        "frequency of {} exceeds minimum of {} for {:?}",
        frequency,
        MIN,
        device
    );
    assert!(
        frequency <= max,
        "frequency of {} exceeds maximum of {} for {:?}",
        frequency,
        max,
        device
    );
}

// calculate the clock divisor from a frequency
fn clock_divisor(device: DeviceType, frequency: u32) -> (u32, Option<MpsseCmd>) {
    match device {
        // FT2232D appears as FT2232C in FTD2XX
        DeviceType::FT2232C => {
            check_limits(device, frequency, 6_000_000);
            (6_000_000 / frequency - 1, None)
        }
        DeviceType::FT2232H | DeviceType::FT4232H | DeviceType::FT232H => {
            check_limits(device, frequency, 30_000_000);
            if frequency <= 6_000_000 {
                (6_000_000 / frequency - 1, Some(MpsseCmd::EnableClockDivide))
            } else {
                (
                    30_000_000 / frequency - 1,
                    Some(MpsseCmd::DisableClockDivide),
                )
            }
        }
        _ => panic!("Unknown device type: {:?}", device),
    }
}

#[cfg(test)]
mod clock_divisor {
    use super::*;

    macro_rules! pos {
        ($NAME:ident, $DEVICE:expr, $FREQ:expr, $OUT:expr) => {
            #[test]
            fn $NAME() {
                assert_eq!(clock_divisor($DEVICE, $FREQ), $OUT);
            }
        };
    }

    macro_rules! neg {
        ($NAME:ident, $DEVICE:expr, $FREQ:expr) => {
            #[test]
            #[should_panic]
            fn $NAME() {
                clock_divisor($DEVICE, $FREQ);
            }
        };
    }

    pos!(ft232c_min, DeviceType::FT2232C, 92, (65216, None));
    pos!(ft232c_max, DeviceType::FT2232C, 6_000_000, (0, None));
    pos!(
        min,
        DeviceType::FT2232H,
        92,
        (65216, Some(MpsseCmd::EnableClockDivide))
    );
    pos!(
        max_with_div,
        DeviceType::FT2232H,
        6_000_000,
        (0, Some(MpsseCmd::EnableClockDivide))
    );
    pos!(
        min_without_div,
        DeviceType::FT2232H,
        6_000_001,
        (3, Some(MpsseCmd::DisableClockDivide))
    );
    pos!(
        max,
        DeviceType::FT4232H,
        30_000_000,
        (0, Some(MpsseCmd::DisableClockDivide))
    );

    neg!(panic_unknown, DeviceType::Unknown, 1_000);
    neg!(panic_ft232c_min, DeviceType::FT2232C, 91);
    neg!(panic_ft232c_max, DeviceType::FT2232C, 6_000_001);
    neg!(panic_min, DeviceType::FT232H, 91);
    neg!(panic_max, DeviceType::FT232H, 30_000_001);
}

/// FTDI Multi-Protocol Synchronous Serial Engine (MPSSE).
///
/// For details about the MPSSE read the [FTDI MPSSE Basics].
///
/// [FTDI MPSSE Basics]: https://www.ftdichip.com/Support/Documents/AppNotes/AN_135_MPSSE_Basics.pdf
pub trait FtdiMpsse: FtdiCommon {
    /// Set the clock frequency.
    ///
    /// # Frequency Limits
    ///
    /// | Device Type              | Minimum | Maximum |
    /// |--------------------------|---------|---------|
    /// | FT2232D                  | 92 Hz   | 6 MHz   |
    /// | FT4232H, FT2232H, FT232H | 460 Hz  | 30 MHz  |
    ///
    /// Values outside of these limits will result in panic.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft4232h, FtdiMpsse};
    ///
    /// let mut ft = Ft4232h::with_serial_number("FT4PWSEOA").unwrap();
    /// ft.set_clock(100_000)?;
    /// # Ok::<(), libftd2xx::TimeoutError>(())
    /// ```
    fn set_clock(&mut self, frequency: u32) -> Result<(), TimeoutError> {
        let (value, divisor) = clock_divisor(Self::DEVICE_TYPE, frequency);
        debug_assert!(value <= 0xFFFF);

        if let Some(div) = divisor {
            let buf: [u8; 1] = [div as u8; 1];
            self.write(&buf)?;
        };

        let buf: [u8; 3] = [
            MpsseCmd::SetClockFrequency as u8,
            (value & 0xFF) as u8,
            ((value >> 8) & 0xFF) as u8,
        ];

        self.write(&buf)
    }

    /// Enable the MPSSE loopback state.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft4232h, FtdiMpsse};
    ///
    /// let mut ft = Ft4232h::with_serial_number("FT4PWSEOA").unwrap();
    /// ft.enable_loopback()?;
    /// # Ok::<(), libftd2xx::TimeoutError>(())
    /// ```
    fn enable_loopback(&mut self) -> Result<(), TimeoutError> {
        self.write(&[MpsseCmd::EnableLoopback as u8])
    }

    /// Disable the MPSSE loopback state.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft4232h, FtdiMpsse};
    ///
    /// let mut ft = Ft4232h::with_serial_number("FT4PWSEOA").unwrap();
    /// ft.disable_loopback()?;
    /// # Ok::<(), libftd2xx::TimeoutError>(())
    /// ```
    fn disable_loopback(&mut self) -> Result<(), TimeoutError> {
        self.write(&[MpsseCmd::DisableLoopback as u8])
    }
}
