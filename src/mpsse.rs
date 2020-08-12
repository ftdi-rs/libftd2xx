#![deny(missing_docs, warnings, unsafe_code)]

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
/// [`clock_data_out`]: ./trait.FtdiMpsse.html#method.clock_data_out
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

/// Modes for clocking data into the FTDI device.
///
/// This is an argument to the [`clock_data_in`] method.
///
/// [`clock_data_in`]: ./trait.FtdiMpsse.html#method.clock_data_in
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

/// Modes for clocking data in and out of the FTDI device.
///
/// This is an argument to the [`clock_data`] method.
///
/// [`clock_data`]: ./trait.FtdiMpsse.html#method.clock_data
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
    /// | FT4232H, FT2232H, FT232H | 460 Hz  | 30 MHz  |
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

        self.write(&buf.as_slice())
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
        self.disable_loopback()?;

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
        self.write(&[ECHO_CMD_2])?;

        let mut num_bytes: usize = 0;
        while num_bytes == 0 {
            num_bytes = self.queue_status()?;
        }

        let mut buf = vec![0; num_bytes].into_boxed_slice();
        self.read(&mut buf)?;

        let mut command_echoed = false;
        for count in 0..(num_bytes - 1) {
            if buf[count] == 0xFA && buf[count + 1] == ECHO_CMD_2 {
                command_echoed = true;
                break;
            }
        }

        if !command_echoed {
            Err(TimeoutError::from(FtStatus::OTHER_ERROR))
        } else {
            Ok(())
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
        self.write(&[MpsseCmd::EnableLoopback.into()])
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
        self.write(&[MpsseCmd::DisableLoopback.into()])
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
        self.write(&[MpsseCmd::SetDataBitsLowbyte.into(), state, direction])
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
        self.write(&[
            MpsseCmd::GetDataBitsLowbyte.into(),
            MpsseCmd::SendImmediate.into(),
        ])?;
        let mut buf: [u8; 1] = [0];
        self.read(&mut buf)?;
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
        self.write(&[MpsseCmd::SetDataBitsHighbyte.into(), state, direction])
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
        self.write(&[
            MpsseCmd::GetDataBitsHighbyte.into(),
            MpsseCmd::SendImmediate.into(),
        ])?;
        let mut buf: [u8; 1] = [0];
        self.read(&mut buf)?;
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
    /// use libftd2xx::{Ft232h, FtdiMpsse, ClockDataOut};
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
        self.write(&payload.as_slice())
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
        self.write(&[mode.into(), (len & 0xFF) as u8, ((len >> 8) & 0xFF) as u8])?;
        self.read(data)
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
        self.write(&payload.as_slice())?;
        self.read(data)
    }
}

/// This contains MPSSE commands that are only avaliable on the the FT232H,
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
        self.write(&[MpsseCmd::Enable3PhaseClocking.into()])
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
        self.write(&[MpsseCmd::Disable3PhaseClocking.into()])
    }
}
