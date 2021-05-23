#![deny(missing_docs, unsafe_code)]

use super::{BitMode, DeviceType, FtStatus, FtdiCommon, TimeoutError};
use std::convert::From;
use std::time::Duration;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
enum MpsseCmd {
    SetDataBitsLowbyte = 0x80,
    GetDataBitsLowbyte = 0x81,
    SetDataBitsHighbyte = 0x82,
    GetDataBitsHighbyte = 0x83,
    EnableLoopback = 0x84,
    DisableLoopback = 0x85,
    SetClockFrequency = 0x86,
    SendImmediate = 0x87,
    WaitOnIOHigh = 0x88,
    WaitOnIOLow = 0x89,
    DisableClockDivide = 0x8A,
    EnableClockDivide = 0x8B,
    Enable3PhaseClocking = 0x8C,
    Disable3PhaseClocking = 0x8D,
    // EnableDriveOnlyZero = 0x9E,
}

/// Modes for clocking data out of the FTDI device.
///
/// This is an argument to the [`clock_data_out`] method.
///
/// [`clock_data_out`]: ./struct.MpsseCmdBuilder.html#method.clock_data_out
#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ClockDataOut {
    /// Positive clock edge MSB first.
    ///
    /// The data is sent MSB first.
    ///
    /// The data will change to the next bit on the rising edge of the CLK pin.
    MsbPos = 0x10,
    /// Negative clock edge MSB first.
    ///
    /// The data is sent MSB first.
    ///
    /// The data will change to the next bit on the falling edge of the CLK pin.
    MsbNeg = 0x11,
    /// Positive clock edge LSB first.
    ///
    /// The first bit in will be the LSB of the first byte and so on.
    ///
    /// The data will change to the next bit on the rising edge of the CLK pin.
    LsbPos = 0x18,
    /// Negative clock edge LSB first.
    ///
    /// The first bit in will be the LSB of the first byte and so on.
    ///
    /// The data will change to the next bit on the falling edge of the CLK pin.
    LsbNeg = 0x19,
}

impl From<ClockDataOut> for u8 {
    fn from(value: ClockDataOut) -> u8 {
        value as u8
    }
}

/// Modes for clocking bits out of the FTDI device.
///
/// This is an argument to the [`clock_bits_out`] method.
///
/// [`clock_bits_out`]: ./struct.MpsseCmdBuilder.html#method.clock_bits_out
#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ClockBitsOut {
    /// Positive clock edge MSB first.
    ///
    /// The data is sent MSB first (bit 7 first).
    ///
    /// The data will change to the next bit on the rising edge of the CLK pin.
    MsbPos = 0x12,
    /// Negative clock edge MSB first.
    ///
    /// The data is sent MSB first (bit 7 first).
    ///
    /// The data will change to the next bit on the falling edge of the CLK pin.
    MsbNeg = 0x13,
    /// Positive clock edge LSB first (bit 0 first).
    ///
    /// The first bit in will be the LSB of the first byte and so on.
    ///
    /// The data will change to the next bit on the rising edge of the CLK pin.
    LsbPos = 0x1A,
    /// Negative clock edge LSB first (bit 0 first).
    ///
    /// The first bit in will be the LSB of the first byte and so on.
    ///
    /// The data will change to the next bit on the falling edge of the CLK pin.
    LsbNeg = 0x1B,
}

impl From<ClockBitsOut> for u8 {
    fn from(value: ClockBitsOut) -> u8 {
        value as u8
    }
}

/// Modes for clocking data into the FTDI device.
///
/// This is an argument to the [`clock_data_in`] method.
///
/// [`clock_data_in`]: ./struct.MpsseCmdBuilder.html#method.clock_data_in
#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ClockDataIn {
    /// Positive clock edge MSB first.
    ///
    /// The first bit in will be the MSB of the first byte and so on.
    ///
    /// The data will be sampled on the rising edge of the CLK pin.
    MsbPos = 0x20,
    /// Negative clock edge MSB first.
    ///
    /// The first bit in will be the MSB of the first byte and so on.
    ///
    /// The data will be sampled on the falling edge of the CLK pin.
    MsbNeg = 0x24,
    /// Positive clock edge LSB first.
    ///
    /// The first bit in will be the LSB of the first byte and so on.
    ///
    /// The data will be sampled on the rising edge of the CLK pin.
    LsbPos = 0x28,
    /// Negative clock edge LSB first.
    ///
    /// The first bit in will be the LSB of the first byte and so on.
    ///
    /// The data will be sampled on the falling edge of the CLK pin.
    LsbNeg = 0x2C,
}

impl From<ClockDataIn> for u8 {
    fn from(value: ClockDataIn) -> u8 {
        value as u8
    }
}

/// Modes for clocking data bits into the FTDI device.
///
/// This is an argument to the [`clock_bits_in`] method.
///
/// [`clock_bits_in`]: ./struct.MpsseCmdBuilder.html#method.clock_bits_in
#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ClockBitsIn {
    /// Positive clock edge MSB first.
    ///
    /// The data will be shifted up so that the first bit in may not be in bit 7
    /// but from 6 downwards depending on the number of bits to shift
    /// (i.e. a length of 1 bit will have the data bit sampled in bit 0 of the
    /// byte sent back to the PC).
    ///
    /// The data will be sampled on the rising edge of the CLK pin.
    MsbPos = 0x22,
    /// Negative clock edge MSB first.
    ///
    /// The data will be shifted up so that the first bit in may not be in bit 7
    /// but from 6 downwards depending on the number of bits to shift
    /// (i.e. a length of 1 bit will have the data bit sampled in bit 0 of the
    /// byte sent back to the PC).
    ///
    /// The data will be sampled on the falling edge of the CLK pin.
    MsbNeg = 0x26,
    /// Positive clock edge LSB first.
    ///
    /// The data will be shifted down so that the first bit in may not be in bit
    /// 0 but from 1 upwards depending on the number of bits to shift
    /// (i.e. a length of 1 bit will have the data bit sampled in bit 7 of the
    /// byte sent back to the PC).
    ///
    /// The data will be sampled on the rising edge of the CLK pin.
    LsbPos = 0x2A,
    /// Negative clock edge LSB first.
    ///
    /// The data will be shifted down so that thefirst bit in may not be in bit
    /// 0 but from 1 upwards depending on the number of bits to shift
    /// (i.e. a length of 1 bit will have the data bit sampled in bit 7 of the
    /// byte sent back to the PC).
    ///
    /// The data will be sampled on the falling edge of the CLK pin.
    LsbNeg = 0x2E,
}

impl From<ClockBitsIn> for u8 {
    fn from(value: ClockBitsIn) -> u8 {
        value as u8
    }
}

/// Modes for clocking data in and out of the FTDI device.
///
/// This is an argument to the [`clock_data`] method.
///
/// [`clock_data`]: ./struct.MpsseCmdBuilder.html#method.clock_data
#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ClockData {
    /// MSB first, data in on positive edge, data out on negative edge.
    MsbPosIn = 0x31,
    /// MSB first, data in on negative edge, data out on positive edge.
    MsbNegIn = 0x34,
    /// LSB first, data in on positive edge, data out on negative edge.
    LsbPosIn = 0x39,
    /// LSB first, data in on negative edge, data out on positive edge.
    LsbNegIn = 0x3C,
}

impl From<ClockData> for u8 {
    fn from(value: ClockData) -> u8 {
        value as u8
    }
}

/// Modes for clocking data bits in and out of the FTDI device.
///
/// This is an argument to the [`clock_bits`] method.
///
/// [`clock_bits`]: ./struct.MpsseCmdBuilder.html#method.clock_bits
#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ClockBits {
    /// MSB first, data in on positive edge, data out on negative edge.
    MsbPosIn = 0x33,
    /// MSB first, data in on negative edge, data out on positive edge.
    MsbNegIn = 0x36,
    /// LSB first, data in on positive edge, data out on negative edge.
    LsbPosIn = 0x3B,
    /// LSB first, data in on negative edge, data out on positive edge.
    LsbNegIn = 0x3E,
}

impl From<ClockBits> for u8 {
    fn from(value: ClockBits) -> u8 {
        value as u8
    }
}

// seemingly arbitrary values from libmpsse
// const ECHO_CMD_1: u8 = 0xAA;
const ECHO_CMD_2: u8 = 0xAB;

impl From<MpsseCmd> for u8 {
    fn from(value: MpsseCmd) -> Self {
        value as u8
    }
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

/// Initialization settings for the MPSSE.
///
/// Used by [`initialize_mpsse`].
///
/// [`initialize_mpsse`]: ./trait.FtdiMpsse.html#method.initialize_mpsse
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct MpsseSettings {
    /// Reset the MPSSE on initialization.
    ///
    /// This calls [`reset`] if `true`.
    ///
    /// [`reset`]: ./trait.FtdiCommon.html#method.reset
    pub reset: bool,
    /// USB in transfer size in bytes.
    ///
    /// This gets passed to [`set_usb_parameters`].
    ///
    /// [`set_usb_parameters`]: ./trait.FtdiCommon.html#method.set_usb_parameters
    pub in_transfer_size: u32,
    /// Read timeout.
    ///
    /// This gets passed along with [`write_timeout`] to [`set_timeouts`].
    ///
    /// [`set_timeouts`]: ./trait.FtdiCommon.html#method.set_timeouts
    /// [`write_timeout`]: #structfield.write_timeout
    pub read_timeout: Duration,
    /// Write timeout.
    ///
    /// This gets passed along with [`read_timeout`] to [`set_timeouts`].
    ///
    /// [`set_timeouts`]: ./trait.FtdiCommon.html#method.set_timeouts
    /// [`read_timeout`]: #structfield.read_timeout
    pub write_timeout: Duration,
    /// Latency timer.
    ///
    /// This gets passed to [`set_latency_timer`].
    ///
    /// [`set_latency_timer`]: ./trait.FtdiCommon.html#method.set_latency_timer
    pub latency_timer: Duration,
    /// Bitmode mask.
    ///
    /// * A bit value of `0` sets the corresponding pin to an input.
    /// * A bit value of `1` sets the corresponding pin to an output.
    ///
    /// This gets passed to [`set_bit_mode`].
    ///
    /// [`set_bit_mode`]: ./trait.FtdiCommon.html#method.set_bit_mode
    pub mask: u8,
    /// Clock frequency.
    ///
    /// If not `None` this will call [`set_clock`] to set the clock frequency.
    ///
    /// [`set_clock`]: crate::FtdiMpsse::set_clock
    pub clock_frequency: Option<u32>,
}

impl std::default::Default for MpsseSettings {
    fn default() -> Self {
        MpsseSettings {
            reset: true,
            in_transfer_size: 4096,
            read_timeout: Duration::from_secs(1),
            write_timeout: Duration::from_secs(1),
            latency_timer: Duration::from_millis(16),
            mask: 0x00,
            clock_frequency: None,
        }
    }
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
    /// | FT4232H, FT2232H, FT232H | 92 Hz   | 30 MHz  |
    ///
    /// Values outside of these limits will result in panic.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft4232h, FtdiMpsse};
    ///
    /// let mut ft = Ft4232h::with_serial_number("FT4PWSEOA")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.set_clock(100_000)?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    fn set_clock(&mut self, frequency: u32) -> Result<(), TimeoutError> {
        let (value, divisor) = clock_divisor(Self::DEVICE_TYPE, frequency);
        debug_assert!(value <= 0xFFFF);

        let mut buf: Vec<u8> = Vec::new();

        if let Some(div) = divisor {
            buf.push(div.into());
        };

        buf.push(MpsseCmd::SetClockFrequency.into());
        buf.push((value & 0xFF) as u8);
        buf.push(((value >> 8) & 0xFF) as u8);

        self.write_all(&buf.as_slice())
    }

    /// Initialize the MPSSE.
    ///
    /// This method does the following:
    ///
    /// 1. Optionally [`reset`]s the device.
    /// 2. Sets USB transfer sizes using values provided.
    /// 3. Disables special characters.
    /// 4. Sets the transfer timeouts using values provided.
    /// 5. Sets latency timers using values provided.
    /// 6. Sets the flow control to RTS CTS.
    /// 7. Resets the bitmode, then sets it to MPSSE.
    /// 8. Enables loopback.
    /// 9. Synchronizes the MPSSE.
    /// 10. Disables loopback.
    /// 11. Optionally sets the clock frequency.
    ///
    /// Upon failure cleanup is not guaranteed.
    ///
    /// # Example
    ///
    /// Initialize the MPSSE with a 5 second read timeout.
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiMpsse, MpsseSettings};
    /// use std::time::Duration;
    ///
    /// let mut settings = MpsseSettings::default();
    /// settings.read_timeout = Duration::from_secs(5);
    /// let mut ft = Ft232h::with_serial_number("FT59UO4C")?;
    /// ft.initialize_mpsse(&settings)?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// [`reset`]: ./trait.FtdiCommon.html#method.reset
    fn initialize_mpsse(&mut self, settings: &MpsseSettings) -> Result<(), TimeoutError> {
        if settings.reset {
            self.reset()?;
        }
        self.purge_rx()?;
        debug_assert_eq!(self.queue_status()?, 0);
        self.set_usb_parameters(settings.in_transfer_size)?;
        self.set_chars(0, false, 0, false)?;
        self.set_timeouts(settings.read_timeout, settings.write_timeout)?;
        self.set_latency_timer(settings.latency_timer)?;
        self.set_flow_control_rts_cts()?;
        self.set_bit_mode(0x0, BitMode::Reset)?;
        self.set_bit_mode(settings.mask, BitMode::Mpsse)?;
        self.enable_loopback()?;
        self.synchronize_mpsse()?;

        // bundle the disable loopback and clock divisor writes together
        // to save some time
        let mut mpsse_cmd = MpsseCmdBuilder::new().disable_loopback();
        if let Some(frequency) = settings.clock_frequency {
            mpsse_cmd = mpsse_cmd.set_clock(frequency, Self::DEVICE_TYPE);
        }
        self.write_all(mpsse_cmd.as_slice())?;

        Ok(())
    }

    /// Initializes the MPSSE to default settings.
    ///
    /// This simply calles [`initialize_mpsse`] with the default
    /// [`MpsseSettings`].
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiMpsse};
    ///
    /// let mut ft = Ft232h::with_serial_number("FT59UO4C")?;
    /// ft.initialize_mpsse_default()?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// [`initialize_mpsse`]: #method.initialize_mpsse
    /// [`MpsseSettings`]: ./struct.MpsseSettings.html
    fn initialize_mpsse_default(&mut self) -> Result<(), TimeoutError> {
        self.initialize_mpsse(&MpsseSettings::default())
    }

    /// Synchronize the MPSSE port with the application.
    ///
    /// There are various implementations of the synchronization flow, this
    /// uses the flow from [FTDI MPSSE Basics].
    ///
    /// [FTDI MPSSE Basics]: https://www.ftdichip.com/Support/Documents/AppNotes/AN_135_MPSSE_Basics.pdf
    fn synchronize_mpsse(&mut self) -> Result<(), TimeoutError> {
        self.purge_rx()?;
        debug_assert_eq!(self.queue_status()?, 0);
        self.write_all(&[ECHO_CMD_2])?;

        // the FTDI MPSSE basics polls the queue status here
        // we purged the RX buffer so the response should always be 2 bytes
        // this allows us to leverage the timeout built into read
        let mut buf: [u8; 2] = [0; 2];
        self.read_all(&mut buf)?;

        if buf[0] == 0xFA && buf[1] == ECHO_CMD_2 {
            Ok(())
        } else {
            Err(TimeoutError::from(FtStatus::OTHER_ERROR))
        }
    }

    /// Enable the MPSSE loopback state.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft4232h, FtdiMpsse};
    ///
    /// let mut ft = Ft4232h::with_serial_number("FT4PWSEOA")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.enable_loopback()?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    fn enable_loopback(&mut self) -> Result<(), TimeoutError> {
        self.write_all(&[MpsseCmd::EnableLoopback.into()])
    }

    /// Disable the MPSSE loopback state.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft4232h, FtdiMpsse};
    ///
    /// let mut ft = Ft4232h::with_serial_number("FT4PWSEOA")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.disable_loopback()?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    fn disable_loopback(&mut self) -> Result<(), TimeoutError> {
        self.write_all(&[MpsseCmd::DisableLoopback.into()])
    }

    /// Set the pin direction and state of the lower byte (0-7) GPIO pins on the
    /// MPSSE interface.
    ///
    /// The pins that this controls depends on the device.
    ///
    /// * On the FT232H this will control the AD0-AD7 pins.
    ///
    /// # Arguments
    ///
    /// * `state` - GPIO state mask, `0` is low (or input pin), `1` is high.
    /// * `direction` - GPIO direction mask, `0` is input, `1` is output.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiMpsse};
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.set_gpio_lower(0xFF, 0xFF)?;
    /// ft.set_gpio_lower(0x00, 0xFF)?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    fn set_gpio_lower(&mut self, state: u8, direction: u8) -> Result<(), TimeoutError> {
        self.write_all(&[MpsseCmd::SetDataBitsLowbyte.into(), state, direction])
    }

    /// Get the pin state state of the lower byte (0-7) GPIO pins on the MPSSE
    /// interface.
    ///
    /// # Example
    ///
    /// Set the first GPIO, without modify the state of the other GPIOs.
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiMpsse};
    ///
    /// let mut ft = Ft232h::with_serial_number("FT59UO4C")?;
    /// ft.initialize_mpsse_default()?;
    /// let mut gpio_state: u8 = ft.gpio_lower()?;
    /// gpio_state |= 0x01;
    /// ft.set_gpio_lower(gpio_state, 0xFF)?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    fn gpio_lower(&mut self) -> Result<u8, TimeoutError> {
        self.write_all(&[
            MpsseCmd::GetDataBitsLowbyte.into(),
            MpsseCmd::SendImmediate.into(),
        ])?;
        let mut buf: [u8; 1] = [0];
        self.read_all(&mut buf)?;
        Ok(buf[0])
    }

    /// Set the pin direction and state of the upper byte (8-15) GPIO pins on
    /// the MPSSE interface.
    ///
    /// The pins that this controls depends on the device.
    /// This method may do nothing for some devices, such as the FT4232H that
    /// only have 8 pins per port.
    ///
    /// See [`set_gpio_lower`] for an example.
    ///
    /// # Arguments
    ///
    /// * `state` - GPIO state mask, `0` is low (or input pin), `1` is high.
    /// * `direction` - GPIO direction mask, `0` is input, `1` is output.
    ///
    /// # FT232H Corner Case
    ///
    /// On the FT232H only CBUS5, CBUS6, CBUS8, and CBUS9 can be controlled.
    /// These pins confusingly map to the first four bits in the direction and
    /// state masks.
    ///
    /// [`set_gpio_lower`]: #method.set_gpio_lower
    fn set_gpio_upper(&mut self, state: u8, direction: u8) -> Result<(), TimeoutError> {
        self.write_all(&[MpsseCmd::SetDataBitsHighbyte.into(), state, direction])
    }

    /// Get the pin state state of the upper byte (8-15) GPIO pins on the MPSSE
    /// interface.
    ///
    /// See [`gpio_lower`] for an example.
    ///
    /// See [`set_gpio_upper`] for additional information about physical pin
    /// mappings.
    ///
    /// [`gpio_lower`]: #method.gpio_lower
    /// [`set_gpio_upper`]: #method.set_gpio_upper
    fn gpio_upper(&mut self) -> Result<u8, TimeoutError> {
        self.write_all(&[
            MpsseCmd::GetDataBitsHighbyte.into(),
            MpsseCmd::SendImmediate.into(),
        ])?;
        let mut buf: [u8; 1] = [0];
        self.read_all(&mut buf)?;
        Ok(buf[0])
    }

    /// Clock data out.
    ///
    /// This will clock out bytes on TDI/DO.
    /// No data is clocked into the device on TDO/DI.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{ClockDataOut, Ft232h, FtdiMpsse};
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.set_clock(100_000)?;
    /// ft.set_gpio_lower(0xFA, 0xFB)?;
    /// ft.set_gpio_lower(0xF2, 0xFB)?;
    /// ft.clock_data_out(ClockDataOut::MsbNeg, &[0x12, 0x34, 0x56])?;
    /// ft.set_gpio_lower(0xFA, 0xFB)?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    fn clock_data_out(&mut self, mode: ClockDataOut, data: &[u8]) -> Result<(), TimeoutError> {
        let mut len = data.len();
        if len == 0 {
            return Ok(());
        }
        len -= 1;
        assert!(len <= 65536);
        let mut payload = vec![mode.into(), (len & 0xFF) as u8, ((len >> 8) & 0xFF) as u8];
        payload.extend_from_slice(&data);
        self.write_all(&payload.as_slice())
    }

    /// Clock data in.
    ///
    /// This will clock in bytes on TDO/DI.
    /// No data is clocked out of the device on TDI/DO.
    fn clock_data_in(&mut self, mode: ClockDataIn, data: &mut [u8]) -> Result<(), TimeoutError> {
        let mut len = data.len();
        if len == 0 {
            return Ok(());
        }
        len -= 1;
        assert!(len <= 65536);
        self.write_all(&[mode.into(), (len & 0xFF) as u8, ((len >> 8) & 0xFF) as u8])?;
        self.read_all(data)
    }

    /// Clock data in and out at the same time.
    fn clock_data(&mut self, mode: ClockData, data: &mut [u8]) -> Result<(), TimeoutError> {
        let mut len = data.len();
        if len == 0 {
            return Ok(());
        }
        len -= 1;
        assert!(len <= 65536);
        let mut payload = vec![mode.into(), (len & 0xFF) as u8, ((len >> 8) & 0xFF) as u8];
        payload.extend_from_slice(&data);
        self.write_all(&payload.as_slice())?;
        self.read_all(data)
    }
}

/// This contains MPSSE commands that are only available on the the FT232H,
/// FT2232H, and FT4232H devices.
///
/// For details about the MPSSE read the [FTDI MPSSE Basics].
///
/// [FTDI MPSSE Basics]: https://www.ftdichip.com/Support/Documents/AppNotes/AN_135_MPSSE_Basics.pdf
pub trait Ftx232hMpsse: FtdiMpsse {
    /// Enable 3 phase data clocking.
    ///
    /// This will give a 3 stage data shift for the purposes of supporting
    /// interfaces such as I2C which need the data to be valid on both edges of
    /// the clock.
    ///
    /// It will appears as:
    ///
    /// 1. Data setup for 1/2 clock period
    /// 2. Pulse clock for 1/2 clock period
    /// 3. Data hold for 1/2 clock period
    ///
    /// # Example
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiMpsse, Ftx232hMpsse};
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.enable_3phase_data_clocking()?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    fn enable_3phase_data_clocking(&mut self) -> Result<(), TimeoutError> {
        self.write_all(&[MpsseCmd::Enable3PhaseClocking.into()])
    }

    /// Disable 3 phase data clocking.
    ///
    /// This will give a 2 stage data shift which is the default state.
    ///
    /// It will appears as:
    ///
    /// 1. Data setup for 1/2 clock period
    /// 2. Pulse clock for 1/2 clock period
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiMpsse, Ftx232hMpsse};
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.disable_3phase_data_clocking()?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    fn disable_3phase_data_clocking(&mut self) -> Result<(), TimeoutError> {
        self.write_all(&[MpsseCmd::Disable3PhaseClocking.into()])
    }
}

/// FTDI Multi-Protocol Synchronous Serial Engine (MPSSE) command builder.
///
/// For details about the MPSSE read the [FTDI MPSSE Basics].
///
/// This structure is a `Vec<u8>` that the methods push bytewise commands onto.
/// These commands can then be written to the device with the [`write_all`]
/// method.
///
/// This is useful for creating commands that need to do multiple operations
/// quickly, since individual [`write_all`] calls can be expensive.
/// For example, this can be used to set a GPIO low and clock data out for
/// SPI operations.
///
/// [FTDI MPSSE Basics]: https://www.ftdichip.com/Support/Documents/AppNotes/AN_135_MPSSE_Basics.pdf
/// [`write_all`]: ./trait.FtdiCommon.html#method.write_all
pub struct MpsseCmdBuilder(pub Vec<u8>);

impl MpsseCmdBuilder {
    /// Create a new command builder.
    ///
    /// # Example
    ///
    /// ```
    /// use libftd2xx::MpsseCmdBuilder;
    ///
    /// MpsseCmdBuilder::new();
    /// ```
    pub const fn new() -> MpsseCmdBuilder {
        MpsseCmdBuilder(Vec::new())
    }

    /// Create a new command builder from a vector.
    ///
    /// # Example
    ///
    /// ```
    /// use libftd2xx::MpsseCmdBuilder;
    ///
    /// MpsseCmdBuilder::with_vec(Vec::new());
    /// ```
    pub const fn with_vec(vec: Vec<u8>) -> MpsseCmdBuilder {
        MpsseCmdBuilder(vec)
    }

    /// Get the MPSSE command as a slice.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{DeviceType, Ft232h, FtdiCommon, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new().set_clock(100_000, DeviceType::FT232H);
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.write_all(cmd.as_slice())?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_slice()
    }

    /// Set the clock frequency.
    ///
    /// # Frequency Limits
    ///
    /// | Device Type              | Minimum | Maximum |
    /// |--------------------------|---------|---------|
    /// | FT2232D                  | 92 Hz   | 6 MHz   |
    /// | FT4232H, FT2232H, FT232H | 92 Hz   | 30 MHz  |
    ///
    /// Values outside of these limits will result in panic.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{DeviceType, Ft232h, FtdiCommon, FtdiMpsse, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new()
    ///     .set_clock(100_000, DeviceType::FT232H)
    ///     .set_gpio_lower(0xFF, 0xFF);
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.write_all(cmd.as_slice())?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    pub fn set_clock(mut self, frequency: u32, device_type: DeviceType) -> Self {
        let (value, divisor) = clock_divisor(device_type, frequency);
        debug_assert!(value <= 0xFFFF);

        if let Some(div) = divisor {
            self.0.push(div.into());
        };

        self.0.push(MpsseCmd::SetClockFrequency.into());
        self.0.push((value & 0xFF) as u8);
        self.0.push(((value >> 8) & 0xFF) as u8);

        self
    }

    /// Enable the MPSSE loopback state.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiCommon, FtdiMpsse, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new().enable_loopback();
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.write_all(cmd.as_slice())?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    pub fn enable_loopback(mut self) -> Self {
        self.0.push(MpsseCmd::EnableLoopback.into());
        self
    }

    /// Disable the MPSSE loopback state.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiCommon, FtdiMpsse, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new().disable_loopback();
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.write_all(cmd.as_slice())?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    pub fn disable_loopback(mut self) -> Self {
        self.0.push(MpsseCmd::DisableLoopback.into());
        self
    }

    /// Disable 3 phase data clocking.
    ///
    /// This is only avaliable on FTx232H devices.
    ///
    /// This will give a 2 stage data shift which is the default state.
    ///
    /// It will appears as:
    ///
    /// 1. Data setup for 1/2 clock period
    /// 2. Pulse clock for 1/2 clock period
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiCommon, FtdiMpsse, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new().disable_3phase_data_clocking();
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.write_all(cmd.as_slice())?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    pub fn disable_3phase_data_clocking(mut self) -> Self {
        self.0.push(MpsseCmd::Disable3PhaseClocking.into());
        self
    }

    /// Enable 3 phase data clocking.
    ///
    /// This is only avaliable on FTx232H devices.
    ///
    /// This will give a 3 stage data shift for the purposes of supporting
    /// interfaces such as I2C which need the data to be valid on both edges of
    /// the clock.
    ///
    /// It will appears as:
    ///
    /// 1. Data setup for 1/2 clock period
    /// 2. Pulse clock for 1/2 clock period
    /// 3. Data hold for 1/2 clock period
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiCommon, FtdiMpsse, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new().enable_3phase_data_clocking();
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.write_all(cmd.as_slice())?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    pub fn enable_3phase_data_clocking(mut self) -> Self {
        self.0.push(MpsseCmd::Enable3PhaseClocking.into());
        self
    }

    /// Set the pin direction and state of the lower byte (0-7) GPIO pins on the
    /// MPSSE interface.
    ///
    /// The pins that this controls depends on the device.
    ///
    /// * On the FT232H this will control the AD0-AD7 pins.
    ///
    /// # Arguments
    ///
    /// * `state` - GPIO state mask, `0` is low (or input pin), `1` is high.
    /// * `direction` - GPIO direction mask, `0` is input, `1` is output.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiCommon, FtdiMpsse, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new()
    ///     .set_gpio_lower(0xFF, 0xFF)
    ///     .set_gpio_lower(0x00, 0xFF);
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.write_all(cmd.as_slice())?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    pub fn set_gpio_lower(mut self, state: u8, direction: u8) -> Self {
        self.0
            .extend_from_slice(&[MpsseCmd::SetDataBitsLowbyte.into(), state, direction]);
        self
    }

    /// Set the pin direction and state of the upper byte (8-15) GPIO pins on
    /// the MPSSE interface.
    ///
    /// The pins that this controls depends on the device.
    /// This method may do nothing for some devices, such as the FT4232H that
    /// only have 8 pins per port.
    ///
    /// # Arguments
    ///
    /// * `state` - GPIO state mask, `0` is low (or input pin), `1` is high.
    /// * `direction` - GPIO direction mask, `0` is input, `1` is output.
    ///
    /// # FT232H Corner Case
    ///
    /// On the FT232H only CBUS5, CBUS6, CBUS8, and CBUS9 can be controlled.
    /// These pins confusingly map to the first four bits in the direction and
    /// state masks.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiCommon, FtdiMpsse, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new()
    ///     .set_gpio_upper(0xFF, 0xFF)
    ///     .set_gpio_upper(0x00, 0xFF);
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.write_all(cmd.as_slice())?;
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    pub fn set_gpio_upper(mut self, state: u8, direction: u8) -> Self {
        self.0
            .extend_from_slice(&[MpsseCmd::SetDataBitsHighbyte.into(), state, direction]);
        self
    }

    /// Get the pin state state of the lower byte (0-7) GPIO pins on the MPSSE
    /// interface.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiCommon, FtdiMpsse, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new().gpio_lower().send_immediate();
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.write_all(cmd.as_slice())?;
    /// let mut buf: [u8; 1] = [0; 1];
    /// ft.read_all(&mut buf)?;
    /// println!("GPIO lower state: 0x{:02X}", buf[0]);
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    pub fn gpio_lower(mut self) -> Self {
        self.0.push(MpsseCmd::GetDataBitsLowbyte.into());
        self
    }

    /// Get the pin state state of the upper byte (8-15) GPIO pins on the MPSSE
    /// interface.
    ///
    /// See [`set_gpio_upper`] for additional information about physical pin
    /// mappings.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ft232h, FtdiCommon, FtdiMpsse, MpsseCmdBuilder};
    ///
    /// let cmd = MpsseCmdBuilder::new().gpio_upper().send_immediate();
    ///
    /// let mut ft = Ft232h::with_serial_number("FT5AVX6B")?;
    /// ft.initialize_mpsse_default()?;
    /// ft.write_all(cmd.as_slice())?;
    /// let mut buf: [u8; 1] = [0; 1];
    /// ft.read_all(&mut buf)?;
    /// println!("GPIO upper state: 0x{:02X}", buf[0]);
    /// # Ok::<(), std::boxed::Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// [`set_gpio_upper`]: #method.set_gpio_upper
    pub fn gpio_upper(mut self) -> Self {
        self.0.push(MpsseCmd::GetDataBitsHighbyte.into());
        self
    }

    /// Send the preceding commands immediately.
    ///
    /// # Example
    ///
    /// ```
    /// use libftd2xx::MpsseCmdBuilder;
    ///
    /// let cmd = MpsseCmdBuilder::new()
    ///     .set_gpio_upper(0xFF, 0xFF)
    ///     .set_gpio_upper(0x00, 0xFF)
    ///     .send_immediate();
    /// ```
    pub fn send_immediate(mut self) -> Self {
        self.0.push(MpsseCmd::SendImmediate.into());
        self
    }

    /// Make controller wait until GPIOL1 or I/O1 is high before running further commands.
    ///
    /// # Example
    ///
    /// ```
    /// use libftd2xx::{ClockData, MpsseCmdBuilder};
    ///
    /// // Assume a "chip ready" signal is connected to GPIOL1. This signal is pulled high
    /// // shortly after AD3 (chip select) is pulled low. Data will not be clocked out until
    /// // the chip is ready.
    /// let cmd = MpsseCmdBuilder::new()
    ///     .set_gpio_lower(0x0, 0xb)
    ///     .wait_on_io_high()
    ///     .clock_data(ClockData::MsbPosIn, &[0x12, 0x34, 0x56])
    ///     .set_gpio_lower(0x8, 0xb)
    ///     .send_immediate();
    /// ```
    pub fn wait_on_io_high(mut self) -> Self {
        self.0.push(MpsseCmd::WaitOnIOHigh.into());
        self
    }

    /// Make controller wait until GPIOL1 or I/O1 is low before running further commands.
    ///
    /// # Example
    ///
    /// ```
    /// use libftd2xx::{ClockData, MpsseCmdBuilder};
    ///
    /// // Assume a "chip ready" signal is connected to GPIOL1. This signal is pulled low
    /// // shortly after AD3 (chip select) is pulled low. Data will not be clocked out until
    /// // the chip is ready.
    /// let cmd = MpsseCmdBuilder::new()
    ///     .set_gpio_lower(0x0, 0xb)
    ///     .wait_on_io_low()
    ///     .clock_data(ClockData::MsbPosIn, &[0x12, 0x34, 0x56])
    ///     .set_gpio_lower(0x8, 0xb)
    ///     .send_immediate();
    /// ```
    pub fn wait_on_io_low(mut self) -> Self {
        self.0.push(MpsseCmd::WaitOnIOLow.into());
        self
    }

    /// Clock data out.
    ///
    /// This will clock out bytes on TDI/DO.
    /// No data is clocked into the device on TDO/DI.
    ///
    /// This will panic for data lengths greater than `u16::MAX + 1`.
    pub fn clock_data_out(mut self, mode: ClockDataOut, data: &[u8]) -> Self {
        let mut len = data.len();
        assert!(len <= 65536, "data length cannot exceed u16::MAX + 1");
        if len == 0 {
            return self;
        }
        len -= 1;
        self.0
            .extend_from_slice(&[mode.into(), (len & 0xFF) as u8, ((len >> 8) & 0xFF) as u8]);
        self.0.extend_from_slice(&data);
        self
    }

    /// Clock data in.
    ///
    /// This will clock in bytes on TDO/DI.
    /// No data is clocked out of the device on TDI/DO.
    ///
    /// # Arguments
    ///
    /// * `mode` - Data clocking mode.
    /// * `len` - Number of bytes to clock in.
    ///           This will panic for values greater than `u16::MAX + 1`.
    pub fn clock_data_in(mut self, mode: ClockDataIn, mut len: usize) -> Self {
        assert!(len <= 65536, "data length cannot exceed u16::MAX + 1");
        if len == 0 {
            return self;
        }
        len -= 1;
        self.0
            .extend_from_slice(&[mode.into(), (len & 0xFF) as u8, ((len >> 8) & 0xFF) as u8]);
        self
    }

    /// Clock data in and out simultaneously.
    ///
    /// This will panic for data lengths greater than `u16::MAX + 1`.
    pub fn clock_data(mut self, mode: ClockData, data: &[u8]) -> Self {
        let mut len = data.len();
        assert!(len <= 65536, "data length cannot exceed u16::MAX + 1");
        if len == 0 {
            return self;
        }
        len -= 1;
        self.0
            .extend_from_slice(&[mode.into(), (len & 0xFF) as u8, ((len >> 8) & 0xFF) as u8]);
        self.0.extend_from_slice(&data);
        self
    }

    /// Clock data bits out.
    ///
    /// # Arguments
    ///
    /// * `mode` - Bit clocking mode.
    /// * `data` - Data bits.
    /// * `len` - Number of bits to clock out.
    ///           This will panic for values greater than 8.
    pub fn clock_bits_out(mut self, mode: ClockBitsOut, data: u8, mut len: u8) -> Self {
        assert!(len <= 8, "data length cannot exceed 8");
        if len == 0 {
            return self;
        }
        len -= 1;
        self.0.extend_from_slice(&[mode.into(), len, data]);
        self
    }

    /// Clock data bits in.
    ///
    /// # Arguments
    ///
    /// * `mode` - Bit clocking mode.
    /// * `len` - Number of bits to clock in.
    ///           This will panic for values greater than 8.
    pub fn clock_bits_in(mut self, mode: ClockBitsIn, mut len: u8) -> Self {
        assert!(len <= 8, "data length cannot exceed 8");
        if len == 0 {
            return self;
        }
        len -= 1;
        self.0.extend_from_slice(&[mode.into(), len]);
        self
    }

    /// Clock data bits in and out simultaneously.
    ///
    /// # Arguments
    ///
    /// * `mode` - Bit clocking mode.
    /// * `len` - Number of bits to clock in.
    ///           This will panic for values greater than 8.
    pub fn clock_bits(mut self, mode: ClockBits, data: u8, mut len: u8) -> Self {
        assert!(len <= 8, "data length cannot exceed 8");
        if len == 0 {
            return self;
        }
        len -= 1;
        self.0.extend_from_slice(&[mode.into(), len, data]);
        self
    }
}
