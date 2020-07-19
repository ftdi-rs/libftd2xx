#![deny(missing_docs, warnings)]
use libftd2xx_ffi::{
    FT_BITMODE_ASYNC_BITBANG, FT_BITMODE_CBUS_BITBANG, FT_BITMODE_FAST_SERIAL, FT_BITMODE_MCU_HOST,
    FT_BITMODE_MPSSE, FT_BITMODE_RESET, FT_BITMODE_SYNC_BITBANG, FT_BITMODE_SYNC_FIFO,
    FT_DEVICE_100AX, FT_DEVICE_2232C, FT_DEVICE_2232H, FT_DEVICE_232H, FT_DEVICE_232R,
    FT_DEVICE_4222H_0, FT_DEVICE_4222H_1_2, FT_DEVICE_4222H_3, FT_DEVICE_4222_PROG,
    FT_DEVICE_4232H, FT_DEVICE_AM, FT_DEVICE_BM, FT_DEVICE_LIST_NOT_READY, FT_DEVICE_NOT_FOUND,
    FT_DEVICE_NOT_OPENED, FT_DEVICE_NOT_OPENED_FOR_ERASE, FT_DEVICE_NOT_OPENED_FOR_WRITE,
    FT_DEVICE_UNKNOWN, FT_DEVICE_X_SERIES, FT_EEPROM_ERASE_FAILED, FT_EEPROM_NOT_PRESENT,
    FT_EEPROM_NOT_PROGRAMMED, FT_EEPROM_READ_FAILED, FT_EEPROM_WRITE_FAILED,
    FT_FAILED_TO_WRITE_DEVICE, FT_INSUFFICIENT_RESOURCES, FT_INVALID_ARGS, FT_INVALID_BAUD_RATE,
    FT_INVALID_HANDLE, FT_INVALID_PARAMETER, FT_IO_ERROR, FT_NOT_SUPPORTED, FT_OK, FT_OTHER_ERROR,
    FT_STATUS,
};
use std::error::Error;
use std::fmt;

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
/// This is used in the [`DeviceInfo`] struct.
///
/// There is an unfortunate lack of documentation for which chip shows up as
/// which device with the FTD2XX driver.
///
/// [`DeviceInfo`]: ./struct.DeviceInfo.html
#[allow(non_camel_case_types)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
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
/// This is returned by [`library_version`] and [`driver_version`].
///
/// [`library_version`]: ./fn.library_version.html
/// [`driver_version`]: ./struct.Ftdi.html#method.driver_version
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
    /// assert_eq!(version, Version{major: 3, minor: 1, build: 15});
    /// ```
    pub fn new(major: u8, minor: u8, build: u8) -> Version {
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

// These get around an annoyance with bindgen generating different types for
// preprocessor macros on Linux vs Windows.
const OK: FT_STATUS = FT_OK as FT_STATUS;
const INVALID_HANDLE: FT_STATUS = FT_INVALID_HANDLE as FT_STATUS;
const DEVICE_NOT_FOUND: FT_STATUS = FT_DEVICE_NOT_FOUND as FT_STATUS;
const DEVICE_NOT_OPENED: FT_STATUS = FT_DEVICE_NOT_OPENED as FT_STATUS;
const IO_ERROR: FT_STATUS = FT_IO_ERROR as FT_STATUS;
const INSUFFICIENT_RESOURCES: FT_STATUS = FT_INSUFFICIENT_RESOURCES as FT_STATUS;
const INVALID_PARAMETER: FT_STATUS = FT_INVALID_PARAMETER as FT_STATUS;
const INVALID_BAUD_RATE: FT_STATUS = FT_INVALID_BAUD_RATE as FT_STATUS;
const DEVICE_NOT_OPENED_FOR_ERASE: FT_STATUS = FT_DEVICE_NOT_OPENED_FOR_ERASE as FT_STATUS;
const DEVICE_NOT_OPENED_FOR_WRITE: FT_STATUS = FT_DEVICE_NOT_OPENED_FOR_WRITE as FT_STATUS;
const FAILED_TO_WRITE_DEVICE: FT_STATUS = FT_FAILED_TO_WRITE_DEVICE as FT_STATUS;
const EEPROM_READ_FAILED: FT_STATUS = FT_EEPROM_READ_FAILED as FT_STATUS;
const EEPROM_WRITE_FAILED: FT_STATUS = FT_EEPROM_WRITE_FAILED as FT_STATUS;
const EEPROM_ERASE_FAILED: FT_STATUS = FT_EEPROM_ERASE_FAILED as FT_STATUS;
const EEPROM_NOT_PRESENT: FT_STATUS = FT_EEPROM_NOT_PRESENT as FT_STATUS;
const EEPROM_NOT_PROGRAMMED: FT_STATUS = FT_EEPROM_NOT_PROGRAMMED as FT_STATUS;
const INVALID_ARGS: FT_STATUS = FT_INVALID_ARGS as FT_STATUS;
const NOT_SUPPORTED: FT_STATUS = FT_NOT_SUPPORTED as FT_STATUS;
const OTHER_ERROR: FT_STATUS = FT_OTHER_ERROR as FT_STATUS;
const DEVICE_LIST_NOT_READY: FT_STATUS = FT_DEVICE_LIST_NOT_READY as FT_STATUS;

/// These are the C API error codes.
///
/// Unfortunately there are provided in the C API as self documenting,
/// which they are for the most part.
///
/// This is used in the [`Ftd2xxError`] error structure.
///
/// [`Ftd2xxError`]: ./struct.Ftd2xxError.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[allow(non_camel_case_types, missing_docs)]
#[repr(u32)]
pub enum ErrorCode {
    INVALID_HANDLE = INVALID_HANDLE,
    DEVICE_NOT_FOUND = DEVICE_NOT_FOUND,
    DEVICE_NOT_OPENED = DEVICE_NOT_OPENED,
    IO_ERROR = IO_ERROR,
    INSUFFICIENT_RESOURCES = INSUFFICIENT_RESOURCES,
    INVALID_PARAMETER = INVALID_PARAMETER,
    INVALID_BAUD_RATE = INVALID_BAUD_RATE,
    DEVICE_NOT_OPENED_FOR_ERASE = DEVICE_NOT_OPENED_FOR_ERASE,
    DEVICE_NOT_OPENED_FOR_WRITE = DEVICE_NOT_OPENED_FOR_WRITE,
    FAILED_TO_WRITE_DEVICE = FAILED_TO_WRITE_DEVICE,
    EEPROM_READ_FAILED = EEPROM_READ_FAILED,
    EEPROM_WRITE_FAILED = EEPROM_WRITE_FAILED,
    EEPROM_ERASE_FAILED = EEPROM_ERASE_FAILED,
    EEPROM_NOT_PRESENT = EEPROM_NOT_PRESENT,
    EEPROM_NOT_PROGRAMMED = EEPROM_NOT_PROGRAMMED,
    INVALID_ARGS = INVALID_ARGS,
    NOT_SUPPORTED = NOT_SUPPORTED,
    /// This seems to be used only in higher level FTDI provided C libraries
    /// such as libmpsse.
    OTHER_ERROR = OTHER_ERROR,
    DEVICE_LIST_NOT_READY = DEVICE_LIST_NOT_READY,
}

impl From<FT_STATUS> for ErrorCode {
    fn from(x: FT_STATUS) -> ErrorCode {
        match x {
            OK => panic!("OK is not an error status"),
            INVALID_HANDLE => ErrorCode::INVALID_HANDLE,
            DEVICE_NOT_FOUND => ErrorCode::DEVICE_NOT_FOUND,
            DEVICE_NOT_OPENED => ErrorCode::DEVICE_NOT_OPENED,
            IO_ERROR => ErrorCode::IO_ERROR,
            INSUFFICIENT_RESOURCES => ErrorCode::INSUFFICIENT_RESOURCES,
            INVALID_PARAMETER => ErrorCode::INVALID_PARAMETER,
            INVALID_BAUD_RATE => ErrorCode::INVALID_BAUD_RATE,
            DEVICE_NOT_OPENED_FOR_ERASE => ErrorCode::DEVICE_NOT_OPENED_FOR_ERASE,
            DEVICE_NOT_OPENED_FOR_WRITE => ErrorCode::DEVICE_NOT_OPENED_FOR_WRITE,
            FAILED_TO_WRITE_DEVICE => ErrorCode::FAILED_TO_WRITE_DEVICE,
            EEPROM_READ_FAILED => ErrorCode::EEPROM_READ_FAILED,
            EEPROM_WRITE_FAILED => ErrorCode::EEPROM_WRITE_FAILED,
            EEPROM_ERASE_FAILED => ErrorCode::EEPROM_ERASE_FAILED,
            EEPROM_NOT_PRESENT => ErrorCode::EEPROM_NOT_PRESENT,
            EEPROM_NOT_PROGRAMMED => ErrorCode::EEPROM_NOT_PROGRAMMED,
            INVALID_ARGS => ErrorCode::INVALID_ARGS,
            NOT_SUPPORTED => ErrorCode::NOT_SUPPORTED,
            OTHER_ERROR => ErrorCode::OTHER_ERROR,
            DEVICE_LIST_NOT_READY => ErrorCode::DEVICE_LIST_NOT_READY,
            _ => panic!("invalid FT_STATUS value: {}", x),
        }
    }
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// FTD2XX API errors.
///
/// The FTDI C API returns integer values from each function to mark the status.
///
/// This error will be returned in the [`Result`] whenever the underlying FTD2XX
/// C API returns with a non-OK status.
///
/// [`Result`]: https://doc.rust-lang.org/std/result/
#[derive(Debug)]
pub struct Ftd2xxError {
    /// Error value.
    pub value: ErrorCode,
}

impl Ftd2xxError {
    /// Create a new FTD2XX error from a C API integer status.
    pub fn new(status: FT_STATUS) -> Ftd2xxError {
        Ftd2xxError {
            value: status.into(),
        }
    }
}

impl fmt::Display for Ftd2xxError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "FTD2XX C API error: {} ({})",
            self.value, self.value as FT_STATUS
        )
    }
}

#[test]
fn ftd2xx_error_display() {
    assert_eq!(
        format!("{}", Ftd2xxError::new(1)),
        "FTD2XX C API error: INVALID_HANDLE (1)"
    )
}

impl Error for Ftd2xxError {}

/// USB device speed.
///
/// This is used in the [`DeviceInfo`] struct.
///
/// [`DeviceInfo`]: ./struct.DeviceInfo.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum Speed {
    /// High speed USB
    HighSpeed,
    /// Full speed USB
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

/// FTDI device information.
///
/// This is returned by [`list_devices`] and [`device_info`].
///
/// [`list_devices`]: ./fn.list_devices.html
/// [`device_info`]: ./struct.Ftdi.html#method.device_info
#[derive(Clone, Eq, PartialEq)]
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
    /// FTDI device vendor ID.
    ///
    /// This is typically `0x0403`.
    pub vendor_id: u16,
    /// FTDI product ID.
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
