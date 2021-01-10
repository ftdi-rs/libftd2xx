#![deny(missing_docs, unsafe_code)]

// FT_X_SERIES_CBUS_
use libftd2xx_ffi::{
    FT_X_SERIES_CBUS_BCD_CHARGER, FT_X_SERIES_CBUS_BCD_CHARGER_N, FT_X_SERIES_CBUS_BITBANG_RD,
    FT_X_SERIES_CBUS_BITBANG_WR, FT_X_SERIES_CBUS_CLK12, FT_X_SERIES_CBUS_CLK24,
    FT_X_SERIES_CBUS_CLK6, FT_X_SERIES_CBUS_DRIVE_0, FT_X_SERIES_CBUS_DRIVE_1,
    FT_X_SERIES_CBUS_I2C_RXF, FT_X_SERIES_CBUS_I2C_TXE, FT_X_SERIES_CBUS_IOMODE,
    FT_X_SERIES_CBUS_KEEP_AWAKE, FT_X_SERIES_CBUS_PWREN, FT_X_SERIES_CBUS_RXLED,
    FT_X_SERIES_CBUS_SLEEP, FT_X_SERIES_CBUS_TIMESTAMP, FT_X_SERIES_CBUS_TRISTATE,
    FT_X_SERIES_CBUS_TXDEN, FT_X_SERIES_CBUS_TXLED, FT_X_SERIES_CBUS_TXRXLED,
    FT_X_SERIES_CBUS_VBUS_SENSE,
};

// FT_232H_CBUS_
use libftd2xx_ffi::{
    FT_232H_CBUS_CLK15, FT_232H_CBUS_CLK30, FT_232H_CBUS_CLK7_5, FT_232H_CBUS_DRIVE_0,
    FT_232H_CBUS_DRIVE_1, FT_232H_CBUS_IOMODE, FT_232H_CBUS_PWREN, FT_232H_CBUS_RXLED,
    FT_232H_CBUS_SLEEP, FT_232H_CBUS_TRISTATE, FT_232H_CBUS_TXDEN, FT_232H_CBUS_TXLED,
    FT_232H_CBUS_TXRXLED,
};

// FT_232R_CBUS_
use libftd2xx_ffi::{
    FT_232R_CBUS_BITBANG_RD, FT_232R_CBUS_BITBANG_WR, FT_232R_CBUS_CLK12, FT_232R_CBUS_CLK24,
    FT_232R_CBUS_CLK48, FT_232R_CBUS_CLK6, FT_232R_CBUS_IOMODE, FT_232R_CBUS_PWRON,
    FT_232R_CBUS_RXLED, FT_232R_CBUS_SLEEP, FT_232R_CBUS_TXDEN, FT_232R_CBUS_TXLED,
    FT_232R_CBUS_TXRXLED,
};

// FT_BITMODE_
use libftd2xx_ffi::{
    FT_BITMODE_ASYNC_BITBANG, FT_BITMODE_CBUS_BITBANG, FT_BITMODE_FAST_SERIAL, FT_BITMODE_MCU_HOST,
    FT_BITMODE_MPSSE, FT_BITMODE_RESET, FT_BITMODE_SYNC_BITBANG, FT_BITMODE_SYNC_FIFO,
};

// FT_DEVICE_
use libftd2xx_ffi::{
    FT_DEVICE_100AX, FT_DEVICE_2232C, FT_DEVICE_2232H, FT_DEVICE_232H, FT_DEVICE_232R,
    FT_DEVICE_4222H_0, FT_DEVICE_4222H_1_2, FT_DEVICE_4222H_3, FT_DEVICE_4222_PROG,
    FT_DEVICE_4232H, FT_DEVICE_AM, FT_DEVICE_BM, FT_DEVICE_UNKNOWN, FT_DEVICE_X_SERIES,
};

// FT_DRIVER_TYPE_
use libftd2xx_ffi::{FT_DRIVER_TYPE_D2XX, FT_DRIVER_TYPE_VCP};

// FT_EEPROM_
use libftd2xx_ffi::{FT_EEPROM_232H, FT_EEPROM_4232H, FT_EEPROM_HEADER};

use super::{EepromStringsError, EepromValueError};
use crate::util::slice_into_string;
use std::{convert::TryFrom, fmt};

/// Maximum length of common FTDI strings.
pub const STRING_LEN: usize = 64;

/// Bits per word.
///
/// This is used by the [`set_data_characteristics`] method.
///
/// [`set_data_characteristics`]: ./trait.FtdiCommon.html#method.set_data_characteristics
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
pub enum BitsPerWord {
    /// 7 bits per word.
    Bits7 = 7,
    /// 8 bits per word.
    Bits8 = 8,
}

impl From<BitsPerWord> for u8 {
    fn from(val: BitsPerWord) -> u8 {
        val as u8
    }
}

impl Default for BitsPerWord {
    fn default() -> Self {
        BitsPerWord::Bits8
    }
}

/// Stop bits.
///
/// This is used by the [`set_data_characteristics`] method.
///
/// [`set_data_characteristics`]: ./trait.FtdiCommon.html#method.set_data_characteristics
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
pub enum StopBits {
    /// 1 stop bit.
    Bits1 = 0,
    /// 2 stop bits.
    Bits2 = 2,
}

impl From<StopBits> for u8 {
    fn from(val: StopBits) -> u8 {
        val as u8
    }
}

impl Default for StopBits {
    fn default() -> Self {
        StopBits::Bits1
    }
}

/// Serial parity bits.
///
/// This is used by the [`set_data_characteristics`] method.
///
/// [`set_data_characteristics`]: ./trait.FtdiCommon.html#method.set_data_characteristics
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
pub enum Parity {
    /// No pairty.
    No = 0,
    /// Odd parity.
    Odd = 1,
    /// Even parity.
    Even = 2,
    /// Mark parity.
    Mark = 3,
    /// Space parity.
    Space = 4,
}

impl From<Parity> for u8 {
    fn from(val: Parity) -> u8 {
        val as u8
    }
}

impl Default for Parity {
    fn default() -> Self {
        Parity::No
    }
}

// These get around an annoyance with bindgen generating different types for
// enums on Linux vs Windows.
const DEVICE_BM: u32 = FT_DEVICE_BM as u32;
const DEVICE_AM: u32 = FT_DEVICE_AM as u32;
const DEVICE_100AX: u32 = FT_DEVICE_100AX as u32;
const DEVICE_UNKNOWN: u32 = FT_DEVICE_UNKNOWN as u32;
const DEVICE_2232C: u32 = FT_DEVICE_2232C as u32;
const DEVICE_232R: u32 = FT_DEVICE_232R as u32;
const DEVICE_2232H: u32 = FT_DEVICE_2232H as u32;
const DEVICE_4232H: u32 = FT_DEVICE_4232H as u32;
const DEVICE_232H: u32 = FT_DEVICE_232H as u32;
const DEVICE_X_SERIES: u32 = FT_DEVICE_X_SERIES as u32;
const DEVICE_4222H_0: u32 = FT_DEVICE_4222H_0 as u32;
const DEVICE_4222H_1_2: u32 = FT_DEVICE_4222H_1_2 as u32;
const DEVICE_4222H_3: u32 = FT_DEVICE_4222H_3 as u32;
const DEVICE_4222_PROG: u32 = FT_DEVICE_4222_PROG as u32;

/// FTDI device types.
///
/// There is an unfortunate lack of documentation for which chip shows up as
/// which device with the FTD2XX driver.
///
/// This is used in the [`DeviceInfo`] struct.
///
/// [`DeviceInfo`]: ./struct.DeviceInfo.html
#[allow(non_camel_case_types)]
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u32)]
pub enum DeviceType {
    /// FTDI BM device.
    FTBM = DEVICE_BM,
    /// FTDI AM device.
    FTAM = DEVICE_AM,
    /// FTDI 100AX device.
    FT100AX = DEVICE_100AX,
    /// Unknown FTDI device.
    ///
    /// This frequently occurs on Linux when the VCP FTDI driver is in use.
    ///
    /// The driver can be removed with these commands.
    /// ```bash
    /// sudo rmmod ftdi_sio
    /// sudo rmmod usbserial
    /// ```
    /// See [FTDI Drivers Installation Guide for Linux] for more details.
    ///
    /// [FTDI Drivers Installation Guide for Linux]: http://www.ftdichip.cn/Support/Documents/AppNotes/AN_220_FTDI_Drivers_Installation_Guide_for_Linux.pdf
    Unknown = DEVICE_UNKNOWN,
    /// FTDI 2232C device.
    ///
    /// The FTDI 2232D also appears as a FTDI 2232C.
    FT2232C = DEVICE_2232C,
    /// FTDI 232R device.
    FT232R = DEVICE_232R,
    /// FT2232H device.
    FT2232H = DEVICE_2232H,
    /// FT4232H device.
    FT4232H = DEVICE_4232H,
    /// FT232H device.
    FT232H = DEVICE_232H,
    /// FTDI x series device.
    FT_X_SERIES = DEVICE_X_SERIES,
    /// FT4222H device.
    FT4222H_0 = DEVICE_4222H_0,
    /// FT4222H device.
    FT4222H_1_2 = DEVICE_4222H_1_2,
    /// FT4222H device.
    FT4222H_3 = DEVICE_4222H_3,
    /// FT4222 device.
    FT4222_PROG = DEVICE_4222_PROG,
}

impl DeviceType {
    /// Get a device type with a USB product ID.
    ///
    /// This is not entirely accurate since soem devices share the same PID.
    ///
    /// # Example
    ///
    /// ```
    /// use libftd2xx::DeviceType;
    ///
    /// let my_device: Option<DeviceType> = DeviceType::with_pid(0x6014);
    /// assert_eq!(my_device, Some(DeviceType::FT232H));
    /// ```
    pub const fn with_pid(pid: u16) -> Option<DeviceType> {
        if pid == 0x6001 {
            Some(DeviceType::FTAM)
        } else if pid == 0x6010 {
            Some(DeviceType::FT2232H)
        } else if pid == 0x6011 {
            Some(DeviceType::FT4232H)
        } else if pid == 0x6014 {
            Some(DeviceType::FT232H)
        } else if pid == 0x6015 {
            Some(DeviceType::FT_X_SERIES)
        } else {
            None
        }
    }
}

impl Default for DeviceType {
    fn default() -> Self {
        DeviceType::Unknown
    }
}

#[test]
fn device_type_default() {
    let default: DeviceType = Default::default();
    assert_eq!(DeviceType::Unknown, default);
}

impl From<u32> for DeviceType {
    fn from(value: u32) -> DeviceType {
        match value {
            DEVICE_AM => DeviceType::FTBM,
            DEVICE_BM => DeviceType::FTAM,
            DEVICE_100AX => DeviceType::FT100AX,
            DEVICE_UNKNOWN => DeviceType::Unknown,
            DEVICE_2232C => DeviceType::FT2232C,
            DEVICE_232R => DeviceType::FT232R,
            DEVICE_2232H => DeviceType::FT2232H,
            DEVICE_4232H => DeviceType::FT4232H,
            DEVICE_232H => DeviceType::FT232H,
            DEVICE_X_SERIES => DeviceType::FT_X_SERIES,
            DEVICE_4222H_0 => DeviceType::FT4222H_0,
            DEVICE_4222H_1_2 => DeviceType::FT4222H_1_2,
            DEVICE_4222H_3 => DeviceType::FT4222H_3,
            DEVICE_4222_PROG => DeviceType::FT4222_PROG,
            _ => panic!("unknown device: {}", value),
        }
    }
}

/// D2XX version structure.
///
/// **Note** this is not a [SemVer].  [SemVer] defines the last number as the
/// patch number, whereas FTDI uses it as a build number.
///
/// This is returned by [`library_version`] and [`driver_version`].
///
/// [`library_version`]: ./fn.library_version.html
/// [`driver_version`]: ./struct.Ftdi.html#method.driver_version
/// [SemVer]: https://semver.org/
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Version {
    /// Major version.
    pub major: u8,
    /// Minor version.
    pub minor: u8,
    /// Build number.
    pub build: u8,
}

#[cfg(test)]
mod version {
    use super::*;

    macro_rules! case {
        ($name:ident, ($a:expr, $b:expr, $c:expr), ($d:expr, $e:expr, $f:expr)) => {
            #[test]
            fn $name() {
                let big = Version::new($a, $b, $c);
                let little = Version::new($d, $e, $f);
                assert!(big > little);
                assert!(little < big);
            }
        };
    }

    case!(case_1, (0, 0, 1), (0, 0, 0));
    case!(case_2, (0, 1, 0), (0, 0, 0));
    case!(case_3, (1, 0, 0), (0, 0, 0));
    case!(case_4, (2, 2, 2), (1, 1, 1));
    case!(case_5, (255, 255, 255), (254, 255, 255));
    case!(case_6, (1, 0, 0), (0, 255, 255));
    case!(case_7, (13, 255, 0), (13, 254, 255));

    #[test]
    fn display() {
        assert_eq!(
            format!("{}", Version::with_raw(0x00030115)),
            String::from("3.1.15")
        )
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.build)
    }
}

fn bcd_decode(value: u8) -> u8 {
    let nibble_lo: u8 = value & 0xF;
    let nibble_hi: u8 = (value >> 4) & 0xF;
    assert!(nibble_lo < 0xA);
    assert!(nibble_hi < 0xA);

    nibble_hi * 10 + nibble_lo
}

impl Version {
    /// Create a new version structure from decimal values.
    ///
    /// # Example
    ///
    /// ```
    /// use libftd2xx::Version;
    ///
    /// let version = Version::new(3, 1, 15);
    /// assert_eq!(
    ///     version,
    ///     Version {
    ///         major: 3,
    ///         minor: 1,
    ///         build: 15
    ///     }
    /// );
    /// ```
    pub const fn new(major: u8, minor: u8, build: u8) -> Version {
        Version {
            major,
            minor,
            build,
        }
    }

    /// Create a new version structure from [binary-coded decimal] (BCD) values.
    ///
    /// # Example
    ///
    /// ```
    /// use libftd2xx::Version;
    ///
    /// let version = Version::with_bcd(0x03, 0x01, 0x15);
    /// assert_eq!(version, Version::new(3, 1, 15));
    /// ```
    ///
    /// [binary-coded decimal]: https://en.wikipedia.org/wiki/Binary-coded_decimal
    pub fn with_bcd(major: u8, minor: u8, build: u8) -> Version {
        Version::new(bcd_decode(major), bcd_decode(minor), bcd_decode(build))
    }

    /// Create a new version structure from the raw C-API value.
    ///
    /// # Example
    ///
    /// ```
    /// use libftd2xx::Version;
    ///
    /// let version = Version::with_raw(0x00030115);
    /// assert_eq!(version, Version::new(3, 1, 15));
    /// ```
    pub fn with_raw(value: u32) -> Version {
        Version::with_bcd(
            ((value >> 16) & 0xFF) as u8,
            ((value >> 8) & 0xFF) as u8,
            (value & 0xFF) as u8,
        )
    }
}

/// BitModes for the FTDI ports.
///
/// This structure is passed to [`set_bit_mode`] to set the bit mode.
///
/// [`set_bit_mode`]: ./struct.Ftdi.html#method.set_bit_mode
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum BitMode {
    /// Reset.
    Reset = FT_BITMODE_RESET as u8,
    /// Asynchronous bit bang.
    AsyncBitbang = FT_BITMODE_ASYNC_BITBANG as u8,
    /// MPSSE (FT2232, FT2232H, FT4232H and FT232H devices only)
    Mpsse = FT_BITMODE_MPSSE as u8,
    /// Synchronous Bit Bang
    /// (FT232R, FT245R,FT2232, FT2232H, FT4232H and FT232H devices only)
    SyncBitbang = FT_BITMODE_SYNC_BITBANG as u8,
    /// MCU Host Bus Emulation Mode
    /// (FT2232, FT2232H, FT4232Hand FT232H devices only)
    McuHost = FT_BITMODE_MCU_HOST as u8,
    /// FastOpto-Isolated Serial Mode
    /// (FT2232, FT2232H, FT4232H and FT232H devices only)
    FastSerial = FT_BITMODE_FAST_SERIAL as u8,
    /// CBUS Bit Bang Mode (FT232R and FT232H devices only)
    CbusBitbang = FT_BITMODE_CBUS_BITBANG as u8,
    /// Single Channel Synchronous 245 FIFO Mode
    /// (FT2232H and FT232H devices only)
    SyncFifo = FT_BITMODE_SYNC_FIFO as u8,
}

impl From<u8> for BitMode {
    fn from(x: u8) -> BitMode {
        match x {
            x if x == BitMode::Reset as u8 => BitMode::Reset,
            x if x == BitMode::AsyncBitbang as u8 => BitMode::AsyncBitbang,
            x if x == BitMode::Mpsse as u8 => BitMode::Mpsse,
            x if x == BitMode::SyncBitbang as u8 => BitMode::SyncBitbang,
            x if x == BitMode::McuHost as u8 => BitMode::McuHost,
            x if x == BitMode::FastSerial as u8 => BitMode::FastSerial,
            x if x == BitMode::CbusBitbang as u8 => BitMode::CbusBitbang,
            x if x == BitMode::SyncFifo as u8 => BitMode::SyncFifo,
            _ => panic!("invalid BitMode value: {}", x),
        }
    }
}

#[test]
fn bit_mode_sanity() {
    assert_eq!(BitMode::Reset as u8, 0x00);
    assert_eq!(BitMode::AsyncBitbang as u8, 0x01);
    assert_eq!(BitMode::Mpsse as u8, 0x02);
    assert_eq!(BitMode::SyncBitbang as u8, 0x04);
    assert_eq!(BitMode::McuHost as u8, 0x08);
    assert_eq!(BitMode::FastSerial as u8, 0x10);
    assert_eq!(BitMode::CbusBitbang as u8, 0x20);
    assert_eq!(BitMode::SyncFifo as u8, 0x40);
}

/// USB device speed.
///
/// This is used in the [`DeviceInfo`] struct.
///
/// [`DeviceInfo`]: ./struct.DeviceInfo.html
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
pub enum Speed {
    /// High speed USB.
    HighSpeed,
    /// Full speed USB.
    FullSpeed,
}

impl From<u32> for Speed {
    fn from(value: u32) -> Speed {
        if value == 0 {
            Speed::FullSpeed
        } else {
            Speed::HighSpeed
        }
    }
}

/// FTDI device status.
///
/// This is returned by [`status`](crate::FtdiCommon::status).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct DeviceStatus {
    /// Number of characters in the receive queue.
    pub ammount_in_rx_queue: u32,
    /// Number of characters in the transmit queue.
    pub ammount_in_tx_queue: u32,
    /// Current state of the event status.
    pub event_status: u32,
}

/// FTDI modem status.
///
/// This is returned by [`modem_status`](crate::FtdiCommon::modem_status).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct ModemStatus(u32);

impl ModemStatus {
    /// Construct a new `ModemStatus` from a raw value.
    pub const fn new(status: u32) -> ModemStatus {
        ModemStatus(status)
    }

    /// Get the line status byte.
    pub fn line_status(&self) -> u8 {
        u8::try_from(((self.0) >> 8) & 0xFF).unwrap()
    }

    /// Get the modem status byte.
    pub fn modem_status(&self) -> u8 {
        u8::try_from((self.0) & 0xFF).unwrap()
    }

    /// Clear to send (CTS) status.
    pub fn clear_to_send(&self) -> bool {
        self.modem_status() & 0x10 != 0
    }

    /// Data set ready (DSR) status.
    pub fn data_set_ready(&self) -> bool {
        self.modem_status() & 0x20 != 0
    }

    /// Ring indicator (RI) status.
    pub fn ring_indicator(&self) -> bool {
        self.modem_status() & 0x40 != 0
    }

    /// Data carrier detect (DCD) status.
    pub fn data_carrier_detect(&self) -> bool {
        self.modem_status() & 0x80 != 0
    }

    /// Overrun error (OE) status.
    pub fn overrun_error(&self) -> bool {
        self.line_status() & 0x02 != 0
    }

    /// Parity error (PE) status.
    pub fn parity_error(&self) -> bool {
        self.line_status() & 0x04 != 0
    }

    /// Framing error (FE) status.
    pub fn framing_error(&self) -> bool {
        self.line_status() & 0x08 != 0
    }

    /// Break interrupt (BI) status.
    pub fn break_interrupt(&self) -> bool {
        self.line_status() & 0x10 != 0
    }
}

/// FTDI device information.
///
/// This is returned by [`list_devices`] and [`device_info`].
///
/// [`list_devices`]: ./fn.list_devices.html
/// [`device_info`]: ./struct.Ftdi.html#method.device_info
#[derive(Clone, Eq, PartialEq, Default, Ord, PartialOrd)]
pub struct DeviceInfo {
    /// `true` if the port is open.
    pub port_open: bool,
    /// USB link speed.
    ///
    /// This will be `None` when getting the information of an open device with
    /// the [`device_info`] function.
    ///
    /// [`device_info`]: ./struct.Ftdi.html#method.device_info
    pub speed: Option<Speed>,
    /// FTDI device type.
    pub device_type: DeviceType,
    /// FTDI USB device vendor ID.
    ///
    /// This is typically `0x0403`.
    pub vendor_id: u16,
    /// FTDI USB product ID.
    ///
    /// Typical FTDI product IDs:
    /// * `0x6001` FT232AM/FT232BM/FT232R
    /// * `0x6010` FT2232C/FT2232D/FT2232H
    /// * `0x6011` FT4232/FT4232H
    /// * `0x6014` FT232H
    /// * `0x6015` FT230X/FT231X/FT234X
    pub product_id: u16,
    /// Device serial number.
    ///
    /// This is assumed to be UTF-8.
    /// Data that is not UTF-8 will appear as the replacement character �.
    pub serial_number: String,
    /// Device description.
    ///
    /// This is assumed to be UTF-8.
    /// Data that is not UTF-8 will appear as the replacement character �.
    pub description: String,
}

pub fn vid_pid_from_id(id: u32) -> (u16, u16) {
    (((id >> 16) & 0xFFFF) as u16, (id & 0xFFFF) as u16)
}

#[test]
fn test_vid_pid_from_id() {
    assert_eq!((0x0403, 0x6014), vid_pid_from_id(0x04036014))
}

impl fmt::Debug for DeviceInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "DeviceInfo {{ \
                port_open: {}, \
                speed: {:?}, \
                device_type: {:?}, \
                vendor_id: 0x{:04X}, \
                product_id: 0x{:04X}, \
                serial_number: {}, \
                description: {} \
            }}",
            self.port_open,
            self.speed,
            self.device_type,
            self.vendor_id,
            self.product_id,
            self.serial_number,
            self.description,
        )
    }
}

// These get around an annoyance with bindgen generating different types for
// preprocessor macros on Linux vs Windows.
const DRIVER_TYPE_D2XX: u8 = FT_DRIVER_TYPE_D2XX as u8;
const DRIVER_TYPE_VCP: u8 = FT_DRIVER_TYPE_VCP as u8;

/// FTDI driver type.
///
/// This is used in EEPROM structures.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum DriverType {
    /// FTDI D2XX driver.
    D2XX = DRIVER_TYPE_D2XX,
    /// FTDI VCP driver.
    Vcp = DRIVER_TYPE_VCP,
}

impl TryFrom<u8> for DriverType {
    type Error = EepromValueError;

    fn try_from(value: u8) -> Result<DriverType, EepromValueError> {
        match value {
            DRIVER_TYPE_D2XX => Ok(DriverType::D2XX),
            DRIVER_TYPE_VCP => Ok(DriverType::Vcp),
            _ => Err(EepromValueError::new(value)),
        }
    }
}

/// FTDI pin drive currents.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
pub enum DriveCurrent {
    /// 4mA drive current.
    Milliamps4 = 4,
    /// 8mA drive current.
    Milliamps8 = 8,
    /// 12mA drive current.
    Milliamps12 = 12,
    /// 16mA drive current.
    Milliamps16 = 16,
}

impl TryFrom<u8> for DriveCurrent {
    type Error = EepromValueError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            4 => Ok(DriveCurrent::Milliamps4),
            8 => Ok(DriveCurrent::Milliamps8),
            12 => Ok(DriveCurrent::Milliamps12),
            16 => Ok(DriveCurrent::Milliamps16),
            _ => Err(EepromValueError::new(value)),
        }
    }
}

/// FT1248 clock polarity
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum ClockPolarity {
    /// Clock idle low.
    IdleLow = 0,
    /// Clock idle high.
    IdleHigh = 1,
}

impl From<u8> for ClockPolarity {
    fn from(value: u8) -> ClockPolarity {
        if value == 0 {
            ClockPolarity::IdleLow
        } else {
            ClockPolarity::IdleHigh
        }
    }
}

/// FT1248 byte order.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum ByteOrder {
    /// LSB first.
    LSB,
    /// MSB first.
    MSB,
}

impl From<u8> for ByteOrder {
    fn from(value: u8) -> ByteOrder {
        if value == 0 {
            ByteOrder::MSB
        } else {
            ByteOrder::LSB
        }
    }
}

// Implements From<u8> for cbus enums
macro_rules! cbus_enum {
    (
        $(#[$OUTER:meta])*
        pub enum $NAME:ident {
            $(
                $(#[$INNER:ident $($ARGS:tt)*])*
                $FIELD:ident = $VALUE:ident,
            )+
        }
    ) => {
        $(#[$OUTER])*
        pub enum $NAME {
            $(
                $(#[$INNER $($ARGS)*])*
                $FIELD = $VALUE,
            )*
        }

        impl TryFrom<u8> for $NAME {
            type Error = EepromValueError;

            fn try_from(value: u8) -> Result<$NAME, Self::Error> {
                match value {
                    $(
                        $VALUE => Ok($NAME::$FIELD),
                    )*
                    _ => Err(
                        Self::Error::new(value)
                    ),
                }
            }
        }
    };
}

// These get around an annoyance with bindgen generating different types for
// preprocessor macros on Linux vs Windows.
const NORM_232H_CBUS_TRISTATE: u8 = FT_232H_CBUS_TRISTATE as u8;
const NORM_232H_CBUS_TXLED: u8 = FT_232H_CBUS_TXLED as u8;
const NORM_232H_CBUS_RXLED: u8 = FT_232H_CBUS_RXLED as u8;
const NORM_232H_CBUS_TXRXLED: u8 = FT_232H_CBUS_TXRXLED as u8;
const NORM_232H_CBUS_PWREN: u8 = FT_232H_CBUS_PWREN as u8;
const NORM_232H_CBUS_SLEEP: u8 = FT_232H_CBUS_SLEEP as u8;
const NORM_232H_CBUS_DRIVE_0: u8 = FT_232H_CBUS_DRIVE_0 as u8;
const NORM_232H_CBUS_DRIVE_1: u8 = FT_232H_CBUS_DRIVE_1 as u8;
const NORM_232H_CBUS_IOMODE: u8 = FT_232H_CBUS_IOMODE as u8;
const NORM_232H_CBUS_TXDEN: u8 = FT_232H_CBUS_TXDEN as u8;
const NORM_232H_CBUS_CLK30: u8 = FT_232H_CBUS_CLK30 as u8;
const NORM_232H_CBUS_CLK15: u8 = FT_232H_CBUS_CLK15 as u8;
const NORM_232H_CBUS_CLK7_5: u8 = FT_232H_CBUS_CLK7_5 as u8;

cbus_enum!(
    /// FT232H CBUS options.
    #[derive(Debug, Copy, Clone, Eq, PartialEq)]
    #[repr(u8)]
    pub enum Cbus232h {
        /// Tristate.
        Tristate = NORM_232H_CBUS_TRISTATE,
        /// TX LED.
        TxLed = NORM_232H_CBUS_TXLED,
        /// RX LED.
        RxLed = NORM_232H_CBUS_RXLED,
        /// TX and RX LED.
        TxRxLed = NORM_232H_CBUS_TXRXLED,
        /// Power enable.
        PowerEnable = NORM_232H_CBUS_PWREN,
        /// Sleep.
        Sleep = NORM_232H_CBUS_SLEEP,
        /// Drive pin to logic 0.
        Drive0 = NORM_232H_CBUS_DRIVE_0,
        /// Drive pin to logic 1.
        Drive1 = NORM_232H_CBUS_DRIVE_1,
        /// IO Mode doe CBUS bit-bang.
        IoMode = NORM_232H_CBUS_IOMODE,
        /// TX data enable.
        TxDen = NORM_232H_CBUS_TXDEN,
        /// 30MHz clock.
        Clk30 = NORM_232H_CBUS_CLK30,
        /// 15MHz clock.
        Clk15 = NORM_232H_CBUS_CLK15,
        /// 7.5MHz clock.
        Clk7_5 = NORM_232H_CBUS_CLK7_5,
    }
);

/// EEPROM strings structure.
///
/// This structure contains the strings programmed into EEPROM that are common
/// across all FTDI devices.
///
/// This is used by the [`eeprom_read`] and [`eeprom_program`] methods.
///
/// [`eeprom_read`]: crate::FtdiEeprom::eeprom_read
/// [`eeprom_program`]: crate::FtdiEeprom::eeprom_program
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct EepromStrings {
    manufacturer: String,
    manufacturer_id: String,
    description: String,
    serial_number: String,
}

impl EepromStrings {
    /// Create a new EEPROM strings structure.
    pub fn with_strs(
        manufacturer: &str,
        manufacturer_id: &str,
        description: &str,
        serial_number: &str,
    ) -> Result<Self, EepromStringsError> {
        let mut ret = Self::default();
        ret.set_manufacturer(manufacturer.to_string())?;
        ret.set_manufacturer_id(manufacturer_id.to_string())?;
        ret.set_description(description.to_string())?;
        ret.set_serial_number(serial_number.to_string())?;
        Ok(ret)
    }

    /// Create a new EEPROM strings structure from raw slices.
    pub fn with_slices(
        manufacturer: &[i8],
        manufacturer_id: &[i8],
        description: &[i8],
        serial_number: &[i8],
    ) -> Result<Self, EepromStringsError> {
        let mut ret = Self::default();
        ret.set_manufacturer(slice_into_string(manufacturer.as_ref()))?;
        ret.set_manufacturer_id(slice_into_string(manufacturer_id.as_ref()))?;
        ret.set_description(slice_into_string(description.as_ref()))?;
        ret.set_serial_number(slice_into_string(serial_number.as_ref()))?;
        Ok(ret)
    }
    /// Total length of the `manufacturer`, `manufacturer_id`,
    /// `description`, and `serial_number` strings.
    ///
    /// Together these strings cannot exceed 96 characters.
    pub fn string_len(&self) -> usize {
        self.manufacturer.len()
            + self.manufacturer_id.len()
            + self.description.len()
            + self.serial_number.len()
    }

    /// Manufacturer string.
    pub fn manufacturer(&self) -> String {
        self.manufacturer.clone()
    }

    /// Set the manufacturer string.
    ///
    /// # Requirements
    ///
    /// * Less than or equal to 64 characters.
    /// * The total length of the `manufacturer`, `manufacturer_id`,
    ///   `description`, and `serial_number` strings can not exceed
    ///   96 characters.
    pub fn set_manufacturer(&mut self, value: String) -> Result<(), EepromStringsError> {
        if value.len() > EepromStringsError::MAX_LEN
            || self.manufacturer_id.len() + self.description.len() + self.serial_number.len()
                > EepromStringsError::MAX_TOTAL_LEN
        {
            Err(EepromStringsError {
                manufacturer: value.len(),
                manufacturer_id: self.manufacturer_id.len(),
                description: self.description.len(),
                serial_number: self.serial_number.len(),
            })
        } else {
            self.manufacturer = value;
            Ok(())
        }
    }

    /// Manufacturer ID string.
    pub fn manufacturer_id(&self) -> String {
        self.manufacturer_id.clone()
    }

    /// Set the manufacturer ID string.
    ///
    /// The first two characters of this string should be the same as
    /// the first two characters of the device serial number.
    /// For example, if your manufacturer ID is "FTDI" your serial
    /// number should start with "FT".
    ///
    /// # Requirements
    ///
    /// * Less than or equal to 64 characters.
    /// * The total length of the `manufacturer`, `manufacturer_id`,
    ///   `description`, and `serial_number` strings can not exceed
    ///   96 characters.
    pub fn set_manufacturer_id(&mut self, value: String) -> Result<(), EepromStringsError> {
        if value.len() > EepromStringsError::MAX_LEN
            || self.manufacturer.len() + self.description.len() + self.serial_number.len()
                > EepromStringsError::MAX_TOTAL_LEN
        {
            Err(EepromStringsError {
                manufacturer: self.manufacturer.len(),
                manufacturer_id: value.len(),
                description: self.description.len(),
                serial_number: self.serial_number.len(),
            })
        } else {
            self.manufacturer_id = value;
            Ok(())
        }
    }

    /// Description string.
    pub fn description(&self) -> String {
        self.description.clone()
    }

    /// Set the description string.
    ///
    /// # Requirements
    ///
    /// * Less than or equal to 64 characters.
    /// * The total length of the `manufacturer`, `manufacturer_id`,
    ///   `description`, and `serial_number` strings can not exceed
    ///   96 characters.
    pub fn set_description(&mut self, value: String) -> Result<(), EepromStringsError> {
        if value.len() > EepromStringsError::MAX_LEN
            || self.manufacturer.len() + self.manufacturer_id.len() + self.serial_number.len()
                > EepromStringsError::MAX_TOTAL_LEN
        {
            Err(EepromStringsError {
                manufacturer: self.manufacturer.len(),
                manufacturer_id: self.manufacturer_id.len(),
                description: value.len(),
                serial_number: self.serial_number.len(),
            })
        } else {
            self.description = value;
            Ok(())
        }
    }

    /// Serial number string.
    pub fn serial_number(&self) -> String {
        self.serial_number.clone()
    }

    /// Set the manufacturer ID string.
    ///
    /// The first two characters of this string should be the same as
    /// the first two characters of the device serial number.
    /// For example, if your manufacturer ID is "FTDI" your serial
    /// number should start with "FT".
    ///
    /// # Requirements
    ///
    /// * Less than or equal to 64 characters.
    /// * The total length of the `manufacturer`, `manufacturer_id`,
    ///   `description`, and `serial_number` strings can not exceed
    ///   96 characters.
    pub fn set_serial_number(&mut self, value: String) -> Result<(), EepromStringsError> {
        if value.len() > EepromStringsError::MAX_LEN
            || self.manufacturer.len() + self.manufacturer_id.len() + self.description.len()
                > EepromStringsError::MAX_TOTAL_LEN
        {
            Err(EepromStringsError {
                manufacturer: self.manufacturer.len(),
                manufacturer_id: self.manufacturer_id.len(),
                description: self.description.len(),
                serial_number: value.len(),
            })
        } else {
            self.serial_number = value;
            Ok(())
        }
    }
}

/// EEPROM structure for the FT232H.
///
/// This is used by the [`eeprom_read`] and [`eeprom_program`] methods.
///
/// [`eeprom_read`]: crate::FtdiEeprom::eeprom_read
/// [`eeprom_program`]: crate::FtdiEeprom::eeprom_program
#[derive(Debug, Copy, Clone)]
pub struct Eeprom232h(FT_EEPROM_232H);

impl From<Eeprom232h> for FT_EEPROM_232H {
    fn from(val: Eeprom232h) -> FT_EEPROM_232H {
        val.0
    }
}

impl From<FT_EEPROM_232H> for Eeprom232h {
    fn from(val: FT_EEPROM_232H) -> Eeprom232h {
        Eeprom232h(val)
    }
}

impl Default for Eeprom232h {
    fn default() -> Self {
        let mut header = EepromHeader::default();
        header.set_device_type(DeviceType::FT232H);
        header.set_product_id(0x6014);
        Self(FT_EEPROM_232H {
            common: header.0,
            ACDriveCurrent: 4,
            ADDriveCurrent: 4,
            ..FT_EEPROM_232H::default()
        })
    }
}

/// EEPROM structure for the FT4232H.
///
/// This is used by the [`eeprom_read`] and [`eeprom_program`] methods.
///
/// [`eeprom_read`]: crate::FtdiEeprom::eeprom_read
/// [`eeprom_program`]: crate::FtdiEeprom::eeprom_program
#[derive(Debug, Copy, Clone)]
pub struct Eeprom4232h(FT_EEPROM_4232H);

impl From<Eeprom4232h> for FT_EEPROM_4232H {
    fn from(val: Eeprom4232h) -> FT_EEPROM_4232H {
        val.0
    }
}

impl From<FT_EEPROM_4232H> for Eeprom4232h {
    fn from(val: FT_EEPROM_4232H) -> Eeprom4232h {
        Eeprom4232h(val)
    }
}

impl Default for Eeprom4232h {
    fn default() -> Self {
        let mut header = EepromHeader::default();
        header.set_device_type(DeviceType::FT4232H);
        header.set_product_id(0x6011);
        Self(FT_EEPROM_4232H {
            common: header.0,
            ADriveCurrent: 4,
            BDriveCurrent: 4,
            CDriveCurrent: 4,
            DDriveCurrent: 4,
            ..FT_EEPROM_4232H::default()
        })
    }
}

impl Eeprom4232h {
    /// Get the EEPROM header.
    pub fn header(&self) -> EepromHeader {
        EepromHeader((self.0).common)
    }

    /// Set the EEPROM header.
    pub fn set_header(&mut self, header: EepromHeader) {
        (self.0).common = header.into()
    }
}

/// FTDI EEPROM header common to all FTDI devices.
#[derive(Debug, Copy, Clone)]
pub struct EepromHeader(FT_EEPROM_HEADER);

impl EepromHeader {
    /// Set the FTDI device type.
    pub fn set_device_type(&mut self, device_type: DeviceType) {
        (self.0).deviceType = device_type as u32;
    }

    /// FTDI USB device vendor ID.
    ///
    /// This is typically `0x0403`.
    pub fn vendor_id(&self) -> u16 {
        (self.0).VendorId
    }

    /// Set the FTDI USB device vendor ID.
    pub fn set_vendor_id(&mut self, value: u16) {
        (self.0).VendorId = value
    }

    /// FTDI USB product ID.
    ///
    /// Typical FTDI product IDs:
    /// * `0x6001` FT232AM/FT232BM/FT232R
    /// * `0x6010` FT2232C/FT2232D/FT2232H
    /// * `0x6011` FT4232/FT4232H
    /// * `0x6014` FT232H
    /// * `0x6015` FT230X/FT231X/FT234X
    pub fn product_id(&self) -> u16 {
        (self.0).ProductId
    }

    /// Set the FTDI USB product ID.
    pub fn set_product_id(&mut self, value: u16) {
        (self.0).ProductId = value
    }

    /// Serial Number Enable.
    ///
    /// `true` if the serial number is to be used.
    ///
    /// The documentation is unclear what *exactly* this means.
    pub fn serial_number_enable(&self) -> bool {
        (self.0).SerNumEnable != 0
    }

    /// Set Serial Number Enable.
    pub fn set_serial_number_enable(&mut self, value: bool) {
        (self.0).SerNumEnable = if value { 1 } else { 0 }
    }

    /// Maximum bus current.
    ///
    /// The unit for this value is milliamps, and the value range is
    /// 0-500 mA.
    pub fn max_current(&self) -> u16 {
        (self.0).MaxPower
    }

    /// Set maximum bus current in milliamps.
    ///
    /// Values greater than 500 mA (`500u16`) will result in panic.
    pub fn set_max_current(&mut self, value: u16) {
        assert!(value <= 500, "{} exceeds 500 mA limit", value);
        (self.0).MaxPower = value
    }

    /// Device power source.
    ///
    /// * `true` if the device is self-powered (not powered by USB bus).
    /// * `false` if the device is powered by the USB bus.
    pub fn self_powered(&self) -> bool {
        (self.0).SelfPowered != 0
    }

    /// Set device power source.
    ///
    /// * `true` if the device is self-powered (not powered by USB bus).
    /// * `false` if the device is powered by the USB bus.
    pub fn set_self_powered(&mut self, value: bool) {
        (self.0).SelfPowered = if value { 1 } else { 0 }
    }

    /// Remote wakeup capabilities.
    ///
    /// USB remote wakeup is the ability for the device to resume the PC from
    /// USB suspend (sleep) state.
    ///
    /// * `true` if the device is capable of remote wakeup.
    /// * `false` if the device is not capable of remote wakeup.
    pub fn remote_wakeup(&self) -> bool {
        (self.0).RemoteWakeup != 0
    }

    /// Set remote wakeup capabilities.
    ///
    /// USB remote wakeup is the ability for the device to resume the PC from
    /// USB suspend (sleep) state.
    ///
    /// * `true` if the device is capable of remote wakeup.
    /// * `false` if the device is not capable of remote wakeup.
    pub fn set_remote_wakeup(&mut self, value: bool) {
        (self.0).RemoteWakeup = if value { 1 } else { 0 }
    }

    /// Pull down in suspend mode.
    ///
    /// * `true` if pull-down in suspend is enabled.
    /// * `false` if pull-down in suspend is disabled.
    pub fn pull_down_enable(&self) -> bool {
        (self.0).PullDownEnable != 0
    }

    /// Set pull down in suspend mode.
    ///
    /// * `true` if pull-down in suspend is enabled.
    /// * `false` if pull-down in suspend is disabled.
    pub fn set_pull_down_enable(&mut self, value: bool) {
        (self.0).PullDownEnable = if value { 1 } else { 0 }
    }
}

impl Default for EepromHeader {
    fn default() -> Self {
        Self(FT_EEPROM_HEADER {
            deviceType: DeviceType::Unknown as u32,
            VendorId: 0x0403,
            ProductId: 0x6000,
            SerNumEnable: 1,
            MaxPower: 150,
            SelfPowered: 0,
            RemoteWakeup: 0,
            PullDownEnable: 0,
        })
    }
}

impl From<FT_EEPROM_HEADER> for EepromHeader {
    fn from(val: FT_EEPROM_HEADER) -> EepromHeader {
        EepromHeader(val)
    }
}

impl From<EepromHeader> for FT_EEPROM_HEADER {
    fn from(val: EepromHeader) -> FT_EEPROM_HEADER {
        val.0
    }
}

impl Eeprom232h {
    /// Get the EEPROM header.
    pub fn header(&self) -> EepromHeader {
        EepromHeader((self.0).common)
    }

    /// Set the EEPROM header.
    pub fn set_header(&mut self, header: EepromHeader) {
        (self.0).common = header.into()
    }

    /// FT1248 clock polarity.
    pub fn ft1248_cpol(&self) -> ClockPolarity {
        (self.0).FT1248Cpol.into()
    }

    /// Set FT1248 clock polarity.
    pub fn set_ft1248_cpol(&mut self, value: ClockPolarity) {
        (self.0).FT1248Cpol = value as u8
    }

    /// FT1248 byte order.
    pub fn ft1248_byteorder(&self) -> ByteOrder {
        (self.0).FT1248Lsb.into()
    }

    /// Set FT1248 byte order.
    pub fn set_ft1248_byteorder(&mut self, value: ByteOrder) {
        (self.0).FT1248Lsb = value as u8
    }

    /// FT1248 flow control enable.
    pub fn ft1248_flow_control(&self) -> bool {
        (self.0).FT1248FlowControl != 0
    }

    /// Set FT1248 flow control enable.
    pub fn set_ft1248_flow_control(&mut self, value: bool) {
        (self.0).FT1248FlowControl = if value { 1 } else { 0 }
    }

    /// FT245 FIFO interface mode.
    pub fn is_fifo(&self) -> bool {
        (self.0).IsFifo != 0
    }

    /// Set FT245 FIFO interface mode.
    pub fn set_is_fifo(&mut self, value: bool) {
        (self.0).IsFifo = if value { 1 } else { 0 }
    }

    /// FT245 FIFO CPU target mode.
    pub fn is_fifo_target(&self) -> bool {
        (self.0).IsFifoTar != 0
    }

    /// Set FT245 FIFO CPU target mode.
    pub fn set_is_fifo_target(&mut self, value: bool) {
        (self.0).IsFifoTar = if value { 1 } else { 0 }
    }

    /// Fast serial interface mode.
    pub fn is_fast_serial(&self) -> bool {
        (self.0).IsFastSer != 0
    }

    /// Set Fast serial interface mode.
    pub fn set_is_fast_serial(&mut self, value: bool) {
        (self.0).IsFastSer = if value { 1 } else { 0 }
    }

    /// FT1248 interface mode.
    pub fn is_ft1248(&self) -> bool {
        (self.0).IsFT1248 != 0
    }

    /// Set FT1248 interface mode.
    pub fn set_is_ft1248(&mut self, value: bool) {
        (self.0).IsFT1248 = if value { 1 } else { 0 }
    }

    /// Power save enable.
    ///
    /// Use a pin to save power for self-powered designs.
    pub fn power_save_enable(&self) -> bool {
        (self.0).PowerSaveEnable != 0
    }

    /// Set power save enable.
    pub fn set_power_save_enable(&mut self, value: bool) {
        (self.0).PowerSaveEnable = if value { 1 } else { 0 }
    }
}

macro_rules! impl_bus_pins {
    ($NAME:ident, $($FIELD:ident),+) => {
        impl $NAME {
            $(
                paste::item! {
                    #[doc = "Slow slew for bus " $FIELD "."]
                    ///
                    /// `true` if the pins on this bus have slow slew.
                    pub fn [<$FIELD:lower _slow_slew>](&self) -> bool {
                        (self.0).[<$FIELD:upper SlowSlew>] != 0
                    }

                    #[doc = "Set slow slew for bus " $FIELD "."]
                    pub fn [<set_ $FIELD:lower _slow_slew>](&mut self, value: bool) {
                        (self.0).[<$FIELD:upper SlowSlew>] = if value { 1 } else { 0 }
                    }

                    #[doc = "Schmitt input for bus " $FIELD "."]
                    ///
                    /// `true` if the pins on this bus are Schmitt input.
                    pub fn [<$FIELD:lower _schmitt_input>](&self) -> bool {
                        (self.0).[<$FIELD:upper SchmittInput>] != 0
                    }

                    #[doc = "Set Schmitt input for bus " $FIELD "."]
                    pub fn [<set_ $FIELD:lower _schmitt_input>](&mut self, value: bool) {
                        (self.0).[<$FIELD:upper SchmittInput>] = if value { 1 } else { 0 }
                    }

                    #[doc = "Drive current for bus " $FIELD "."]
                    ///
                    /// This is the drive current for the pins on this bus.
                    pub fn [<$FIELD:lower _drive_current>](&self) -> Result<DriveCurrent, EepromValueError> {
                        DriveCurrent::try_from((self.0).[<$FIELD:upper DriveCurrent>])
                    }

                    #[doc = "Drive current unchecked for bus " $FIELD "."]
                    ///
                    /// Valid values are 4mA, 8mA, 12mA, or 16mA,
                    /// represented by 4u8, 8u8, 12u8, or 16u8 respectively.
                    ///
                    /// This is the **unchecked** raw value retrived from the EEPROM and it may
                    /// not be a valid value.
                    pub fn [<$FIELD:lower _drive_current_unchecked>](&self) -> u8 {
                        (self.0).[<$FIELD:upper SchmittInput>]
                    }

                    #[doc = "Set drive current for bus " $FIELD "."]
                    pub fn [<set_ $FIELD:lower _drive_current>](&mut self, value: DriveCurrent) {
                        (self.0).[<$FIELD:upper SchmittInput>] = value as u8
                    }
                }
            )*
        }
    };
}

macro_rules! impl_driver_type {
    ($NAME:ident) => {
        impl $NAME {
            /// Get the device driver type.
            pub fn driver_type(&self) -> Result<DriverType, EepromValueError> {
                DriverType::try_from((self.0).DriverType)
            }

            /// Get the unchecked device driver type.
            ///
            /// This is the **unchecked** raw value retrieved from the
            /// EEPROM and it may not be a valid value.
            pub fn driver_type_unchecked(&self) -> u8 {
                (self.0).DriverType
            }

            /// Set the device driver type.
            pub fn set_driver_type(&mut self, value: DriverType) {
                (self.0).DriverType = value as u8
            }
        }
    };

    ($NAME:ident, $($FIELD:ident),+) => {
        impl $NAME {
            paste::item! {
                $(
                    #[doc = "Get the driver type for port " $FIELD "."]
                    pub fn [<$FIELD:lower _driver_type>](&self) -> Result<DriverType, EepromValueError> {
                        DriverType::try_from((self.0).[<$FIELD:upper DriverType>])
                    }

                    #[doc = "Get the unchecked driver type for port " $FIELD "."]
                    ///
                    /// This is the **unchecked** raw value retrieved from the
                    /// EEPROM and it may not be a valid value.
                    pub fn [<$FIELD:lower _driver_type_unchecked>](&self) -> u8 {
                        (self.0).[<$FIELD:upper DriverType>]
                    }

                    #[doc = "Set the driver type for port " $FIELD "."]
                    pub fn [<set_ $FIELD:lower _driver_type>](&mut self, value: DriverType) {
                        (self.0).[<$FIELD:upper DriverType>] = value as u8
                    }
                )*
            }
        }
    };
}

macro_rules! impl_tx_data_enable {
    ($NAME:ident, $($FIELD:ident),+) => {
        impl $NAME {
            $(
                paste::item! {
                    #[doc = "Use port " $FIELD " as RS485 TX data enable."]
                    pub fn [<$FIELD:lower _ri_is_tx_data_enable>](&self) -> bool {
                        (self.0).[<$FIELD:upper RIIsTXDEN>] != 0
                    }

                    #[doc = "Use port " $FIELD " as RS485 TX data enable."]
                    pub fn [<set_ $FIELD:lower _ri_is_tx_data_enable>](&mut self, value: bool) {
                        (self.0).[<$FIELD:upper RIIsTXDEN>] = if value { 1 } else { 0 }
                    }
                }
            )*
        }
    };
}

macro_rules! impl_cbus {
    (
        $NAME:ident,
        $ENUM:ident,
        $($FIELD:ident,)+
    ) => {
        impl $NAME {
            $(
                paste::item! {
                    #[doc = "Get the unchecked value of the " $FIELD " pin."]
                    ///
                    /// This is the **unchecked** raw value retrieved from the
                    /// EEPROM and it may not be a valid value.
                    pub fn [<$FIELD:lower _unchecked>](&self) -> u8 {
                        (self.0).$FIELD
                    }

                    #[doc = "Get the value of the " $FIELD " pin."]
                    pub fn [<$FIELD:lower>](&self) -> Result<$ENUM, EepromValueError> {
                        $ENUM::try_from((self.0).$FIELD)
                    }

                    #[doc = "Get the value of the " $FIELD " pin."]
                    pub fn [<set_ $FIELD:lower>](&mut self, value: $ENUM) {
                        (self.0).$FIELD = value as u8;
                    }
                }
            )*
        }
    };
}

// this is where most of the boilerplate is implemented
impl_bus_pins!(Eeprom232h, AD, AC);
impl_cbus!(
    Eeprom232h, Cbus232h, Cbus0, Cbus1, Cbus2, Cbus3, Cbus4, Cbus5, Cbus6, Cbus7, Cbus8, Cbus9,
);
impl_driver_type!(Eeprom232h);

impl_bus_pins!(Eeprom4232h, A, B, C, D);
impl_tx_data_enable!(Eeprom4232h, A, B, C, D);
impl_driver_type!(Eeprom4232h, A, B, C, D);

// These get around an annoyance with bindgen generating different types for
// preprocessor macros on Linux vs Windows.
const NORM_232R_CBUS_TXDEN: u8 = FT_232R_CBUS_TXDEN as u8;
const NORM_232R_CBUS_PWRON: u8 = FT_232R_CBUS_PWRON as u8;
const NORM_232R_CBUS_RXLED: u8 = FT_232R_CBUS_RXLED as u8;
const NORM_232R_CBUS_TXLED: u8 = FT_232R_CBUS_TXLED as u8;
const NORM_232R_CBUS_TXRXLED: u8 = FT_232R_CBUS_TXRXLED as u8;
const NORM_232R_CBUS_SLEEP: u8 = FT_232R_CBUS_SLEEP as u8;
const NORM_232R_CBUS_CLK48: u8 = FT_232R_CBUS_CLK48 as u8;
const NORM_232R_CBUS_CLK24: u8 = FT_232R_CBUS_CLK24 as u8;
const NORM_232R_CBUS_CLK12: u8 = FT_232R_CBUS_CLK12 as u8;
const NORM_232R_CBUS_CLK6: u8 = FT_232R_CBUS_CLK6 as u8;
const NORM_232R_CBUS_IOMODE: u8 = FT_232R_CBUS_IOMODE as u8;
const NORM_232R_CBUS_BITBANG_WR: u8 = FT_232R_CBUS_BITBANG_WR as u8;
const NORM_232R_CBUS_BITBANG_RD: u8 = FT_232R_CBUS_BITBANG_RD as u8;

cbus_enum!(
    /// FT232R CBUS options.
    #[derive(Debug, Copy, Clone, Eq, PartialEq)]
    #[repr(u8)]
    pub enum Cbus232r {
        /// TX data enable.
        TxDataEnable = NORM_232R_CBUS_TXDEN,
        /// Power on.
        PowerOn = NORM_232R_CBUS_PWRON,
        /// RX LED.
        RxLed = NORM_232R_CBUS_RXLED,
        /// TX LED.
        TxLed = NORM_232R_CBUS_TXLED,
        /// TX and RX LED.
        TxRxLed = NORM_232R_CBUS_TXRXLED,
        /// Sleep.
        Sleep = NORM_232R_CBUS_SLEEP,
        /// 48MHz clock.
        Clk48 = NORM_232R_CBUS_CLK48,
        /// 24MHz clock.
        Clk24 = NORM_232R_CBUS_CLK24,
        /// 12MHz clock.
        Clk12 = NORM_232R_CBUS_CLK12,
        /// 6MHz clock.
        Clk6 = NORM_232R_CBUS_CLK6,
        /// IO mode for CBUS bit-bang.
        IoMode = NORM_232R_CBUS_IOMODE,
        /// Bit-bang write stobe.
        BitbangWrite = NORM_232R_CBUS_BITBANG_WR,
        /// Bit-bang read stobe.
        BitbangRead = NORM_232R_CBUS_BITBANG_RD,
    }
);

// These get around an annoyance with bindgen generating different types for
// preprocessor macros on Linux vs Windows.
const NORM_X_SERIES_CBUS_TRISTATE: u8 = FT_X_SERIES_CBUS_TRISTATE as u8;
const NORM_X_SERIES_CBUS_TXLED: u8 = FT_X_SERIES_CBUS_TXLED as u8;
const NORM_X_SERIES_CBUS_RXLED: u8 = FT_X_SERIES_CBUS_RXLED as u8;
const NORM_X_SERIES_CBUS_TXRXLED: u8 = FT_X_SERIES_CBUS_TXRXLED as u8;
const NORM_X_SERIES_CBUS_PWREN: u8 = FT_X_SERIES_CBUS_PWREN as u8;
const NORM_X_SERIES_CBUS_SLEEP: u8 = FT_X_SERIES_CBUS_SLEEP as u8;
const NORM_X_SERIES_CBUS_DRIVE_0: u8 = FT_X_SERIES_CBUS_DRIVE_0 as u8;
const NORM_X_SERIES_CBUS_DRIVE_1: u8 = FT_X_SERIES_CBUS_DRIVE_1 as u8;
const NORM_X_SERIES_CBUS_IOMODE: u8 = FT_X_SERIES_CBUS_IOMODE as u8;
const NORM_X_SERIES_CBUS_TXDEN: u8 = FT_X_SERIES_CBUS_TXDEN as u8;
const NORM_X_SERIES_CBUS_CLK24: u8 = FT_X_SERIES_CBUS_CLK24 as u8;
const NORM_X_SERIES_CBUS_CLK12: u8 = FT_X_SERIES_CBUS_CLK12 as u8;
const NORM_X_SERIES_CBUS_CLK6: u8 = FT_X_SERIES_CBUS_CLK6 as u8;
const NORM_X_SERIES_CBUS_BCD_CHARGER: u8 = FT_X_SERIES_CBUS_BCD_CHARGER as u8;
const NORM_X_SERIES_CBUS_BCD_CHARGER_N: u8 = FT_X_SERIES_CBUS_BCD_CHARGER_N as u8;
const NORM_X_SERIES_CBUS_I2C_TXE: u8 = FT_X_SERIES_CBUS_I2C_TXE as u8;
const NORM_X_SERIES_CBUS_I2C_RXF: u8 = FT_X_SERIES_CBUS_I2C_RXF as u8;
const NORM_X_SERIES_CBUS_VBUS_SENSE: u8 = FT_X_SERIES_CBUS_VBUS_SENSE as u8;
const NORM_X_SERIES_CBUS_BITBANG_WR: u8 = FT_X_SERIES_CBUS_BITBANG_WR as u8;
const NORM_X_SERIES_CBUS_BITBANG_RD: u8 = FT_X_SERIES_CBUS_BITBANG_RD as u8;
const NORM_X_SERIES_CBUS_TIMESTAMP: u8 = FT_X_SERIES_CBUS_TIMESTAMP as u8;
const NORM_X_SERIES_CBUS_KEEP_AWAKE: u8 = FT_X_SERIES_CBUS_KEEP_AWAKE as u8;

cbus_enum!(
    /// FT X Series CBUS options.
    #[derive(Debug, Copy, Clone, Eq, PartialEq)]
    #[repr(u8)]
    pub enum CbusX {
        /// Tristate.
        Tristate = NORM_X_SERIES_CBUS_TRISTATE,
        /// TX LED.
        TxLed = NORM_X_SERIES_CBUS_TXLED,
        /// RX LED.
        RxLed = NORM_X_SERIES_CBUS_RXLED,
        /// TX and RX LED.
        TxRxLed = NORM_X_SERIES_CBUS_TXRXLED,
        /// Power enable.
        PowerEnable = NORM_X_SERIES_CBUS_PWREN,
        /// Sleep.
        Sleep = NORM_X_SERIES_CBUS_SLEEP,
        /// Drive pin to logic 0.
        Drive0 = NORM_X_SERIES_CBUS_DRIVE_0,
        /// Drive pin to logic 1.
        Drive1 = NORM_X_SERIES_CBUS_DRIVE_1,
        /// IO Mode doe CBUS bit-bang.
        IoMode = NORM_X_SERIES_CBUS_IOMODE,
        /// TX data enable.
        TxDen = NORM_X_SERIES_CBUS_TXDEN,
        /// 24MHz clock.
        Clk24 = NORM_X_SERIES_CBUS_CLK24,
        /// 12MHz clock.
        Clk12 = NORM_X_SERIES_CBUS_CLK12,
        /// 6MHz clock.
        Clk6 = NORM_X_SERIES_CBUS_CLK6,
        /// Battery charger detected.
        BatteryCharger = NORM_X_SERIES_CBUS_BCD_CHARGER,
        /// Battery charger detected inverted.
        BatteryChargerN = NORM_X_SERIES_CBUS_BCD_CHARGER_N,
        /// I2C Tx empty.
        I2cTxEmpty = NORM_X_SERIES_CBUS_I2C_TXE,
        /// I2C Rx full.
        I2cRxFull = NORM_X_SERIES_CBUS_I2C_RXF,
        /// Detect VBUS.
        VbusSense = NORM_X_SERIES_CBUS_VBUS_SENSE,
        /// Bit-bang write strobe.
        BitbangWrite = NORM_X_SERIES_CBUS_BITBANG_WR,
        /// Bit-bang read strobe.
        BitbangRead = NORM_X_SERIES_CBUS_BITBANG_RD,
        /// Toggle output when a USB SOF token is received.
        Timestamp = NORM_X_SERIES_CBUS_TIMESTAMP,
        /// No documentation is provided by the source.
        KeepAwake = NORM_X_SERIES_CBUS_KEEP_AWAKE,
    }
);
