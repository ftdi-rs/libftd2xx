#![deny(missing_docs, unsafe_code)]

use std::convert::From;
use std::error::Error;
use std::fmt;

use super::DeviceType;

// Error codes
use libftd2xx_ffi::FT_STATUS;
use libftd2xx_ffi::{
    FT_DEVICE_LIST_NOT_READY, FT_DEVICE_NOT_FOUND, FT_DEVICE_NOT_OPENED,
    FT_DEVICE_NOT_OPENED_FOR_ERASE, FT_DEVICE_NOT_OPENED_FOR_WRITE, FT_EEPROM_ERASE_FAILED,
    FT_EEPROM_NOT_PRESENT, FT_EEPROM_NOT_PROGRAMMED, FT_EEPROM_READ_FAILED, FT_EEPROM_WRITE_FAILED,
    FT_FAILED_TO_WRITE_DEVICE, FT_INSUFFICIENT_RESOURCES, FT_INVALID_ARGS, FT_INVALID_BAUD_RATE,
    FT_INVALID_HANDLE, FT_INVALID_PARAMETER, FT_IO_ERROR, FT_NOT_SUPPORTED, FT_OK, FT_OTHER_ERROR,
};

/// FTDI timeout errors.
///
/// This is used by the [`read`] and [`write`] functions.
///
/// [`read`]: trait.FtdiCommon.html#method.read
/// [`write`]: trait.FtdiCommon.html#method.read
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TimeoutError {
    /// FTDI status errors.
    FtStatus(FtStatus),
    /// Timeout errors.
    Timeout {
        /// Number of bytes read or written.
        actual: usize,
        /// Number of bytes that attempted to read or write.
        expected: usize,
    },
}
impl Error for TimeoutError {}

impl fmt::Display for TimeoutError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TimeoutError::FtStatus(status) => write!(f, "{}", status),
            TimeoutError::Timeout { actual, expected } => {
                write!(f, "IO Timeout {}/{} Bytes", actual, expected)
            }
        }
    }
}

impl From<FtStatus> for TimeoutError {
    fn from(value: FtStatus) -> TimeoutError {
        TimeoutError::FtStatus(value)
    }
}

#[test]
fn timeout_error_display() {
    assert_eq!(
        format!("{}", TimeoutError::FtStatus(FtStatus::IO_ERROR)),
        "FtStatus::IO_ERROR"
    );
    assert_eq!(
        format!("{:?}", TimeoutError::FtStatus(FtStatus::IO_ERROR)),
        "FtStatus(IO_ERROR)"
    );
    let to = TimeoutError::Timeout {
        expected: 1,
        actual: 0,
    };
    assert_eq!(format!("{}", to), "IO Timeout 0/1 Bytes");
    assert_eq!(format!("{:?}", to), "Timeout { actual: 0, expected: 1 }");
}

/// Device type errors.
///
/// This is the error used by `TryFrom` trait for FTDI devices.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum DeviceTypeError {
    /// FTDI status errors.
    FtStatus(FtStatus),
    /// Device type errors.
    DeviceType {
        /// Expected device type.
        expected: DeviceType,
        /// Detected device type.
        detected: DeviceType,
    },
}
impl Error for DeviceTypeError {}

impl fmt::Display for DeviceTypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DeviceTypeError::FtStatus(status) => write!(f, "{}", status),
            DeviceTypeError::DeviceType { expected, detected } => write!(
                f,
                "Device mismatch, expected {:?}, detected {:?}",
                expected, detected
            ),
        }
    }
}

impl From<FtStatus> for DeviceTypeError {
    fn from(value: FtStatus) -> DeviceTypeError {
        DeviceTypeError::FtStatus(value)
    }
}

#[test]
fn device_type_error_display() {
    assert_eq!(
        format!("{}", DeviceTypeError::FtStatus(FtStatus::IO_ERROR)),
        "FtStatus::IO_ERROR"
    );
    assert_eq!(
        format!("{:?}", DeviceTypeError::FtStatus(FtStatus::IO_ERROR)),
        "FtStatus(IO_ERROR)"
    );
    let dt = DeviceTypeError::DeviceType {
        expected: DeviceType::FT232H,
        detected: DeviceType::FT4232H,
    };
    assert_eq!(
        format!("{}", dt),
        "Device mismatch, expected FT232H, detected FT4232H"
    );
    assert_eq!(
        format!("{:?}", dt),
        "DeviceType { expected: FT232H, detected: FT4232H }"
    );
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
/// This is the most common error in this crate, majority of functions and
/// methods will return this in the `Result`.
///
/// This is also used in the [`TimeoutError`], and [`DeviceTypeError`]
/// enumerations.
///
/// [`DeviceTypeError`]: ./enum.DeviceTypeError.html
/// [`TimeoutError`]: ./enum.TimeoutError.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[allow(non_camel_case_types, missing_docs)]
#[repr(u32)]
pub enum FtStatus {
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
    OTHER_ERROR = OTHER_ERROR,
    DEVICE_LIST_NOT_READY = DEVICE_LIST_NOT_READY,
}

impl From<FT_STATUS> for FtStatus {
    fn from(x: FT_STATUS) -> FtStatus {
        match x {
            OK => panic!("OK is not an error status"),
            INVALID_HANDLE => FtStatus::INVALID_HANDLE,
            DEVICE_NOT_FOUND => FtStatus::DEVICE_NOT_FOUND,
            DEVICE_NOT_OPENED => FtStatus::DEVICE_NOT_OPENED,
            IO_ERROR => FtStatus::IO_ERROR,
            INSUFFICIENT_RESOURCES => FtStatus::INSUFFICIENT_RESOURCES,
            INVALID_PARAMETER => FtStatus::INVALID_PARAMETER,
            INVALID_BAUD_RATE => FtStatus::INVALID_BAUD_RATE,
            DEVICE_NOT_OPENED_FOR_ERASE => FtStatus::DEVICE_NOT_OPENED_FOR_ERASE,
            DEVICE_NOT_OPENED_FOR_WRITE => FtStatus::DEVICE_NOT_OPENED_FOR_WRITE,
            FAILED_TO_WRITE_DEVICE => FtStatus::FAILED_TO_WRITE_DEVICE,
            EEPROM_READ_FAILED => FtStatus::EEPROM_READ_FAILED,
            EEPROM_WRITE_FAILED => FtStatus::EEPROM_WRITE_FAILED,
            EEPROM_ERASE_FAILED => FtStatus::EEPROM_ERASE_FAILED,
            EEPROM_NOT_PRESENT => FtStatus::EEPROM_NOT_PRESENT,
            EEPROM_NOT_PROGRAMMED => FtStatus::EEPROM_NOT_PROGRAMMED,
            INVALID_ARGS => FtStatus::INVALID_ARGS,
            NOT_SUPPORTED => FtStatus::NOT_SUPPORTED,
            OTHER_ERROR => FtStatus::OTHER_ERROR,
            DEVICE_LIST_NOT_READY => FtStatus::DEVICE_LIST_NOT_READY,
            _ => panic!("invalid FT_STATUS value: {}", x),
        }
    }
}

impl fmt::Display for FtStatus {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "FtStatus::{:?}", self)
    }
}

impl Error for FtStatus {}

#[test]
fn ft_status_display() {
    assert_eq!(format!("{}", FtStatus::IO_ERROR), "FtStatus::IO_ERROR");
    assert_eq!(format!("{:?}", FtStatus::IO_ERROR), "IO_ERROR");
}

/// EEPROM value error.
///
/// This is used in the `TryFrom` trait implementation for these EEPROM enums:
///
/// * [`Cbus232h`]
/// * [`Cbus232r`]
/// * [`CbusX`]
/// * [`DriveCurrent`]
/// * [`DriverType`]
///
/// Some EEPROM values, such as the [`DriveCurrent`] have a fixed range of valid
/// values.  However, the EEPROM may not be programmed with valid values.
///
/// [`Cbus232h`]: ./enum.Cbus232h.html
/// [`Cbus232r`]: ./enum.Cbus232r.html
/// [`CbusX`]: ./enum.CbusX.html
/// [`DriveCurrent`]: ./enum.DriveCurrent.html
/// [`DriverType`]: ./enum.DriverType.html
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct EepromValueError {
    /// Invalid value.
    pub value: u8,
}

impl EepromValueError {
    /// Create a new `EepromValueError`.
    pub fn new(value: u8) -> EepromValueError {
        EepromValueError { value }
    }
}

impl fmt::Display for EepromValueError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Invalid value for this EEPROM field: {}", self.value)
    }
}

impl Error for EepromValueError {}

#[test]
fn drive_current_error_display() {
    assert_eq!(
        format!("{}", EepromValueError::new(1)),
        "Invalid value for this EEPROM field: 1"
    );
    assert_eq!(
        format!("{:?}", EepromValueError::new(1)),
        "EepromValueError { value: 1 }"
    );
}

/// EEPROM strings error.
///
/// This error is used by `set_manufacturer`, `set_manufacturer_id`,
/// `set_description`, and `set_serial_number` methods on EEPROM structures when
/// the length of these strings exceeds the maximums.
///
/// There are two limits to these strings:
///
/// * Less than or equal to 64 characters for each individual string.
/// * The total length of the `manufacturer`, `manufacturer_id`,
///   `description`, and `serial_number` strings can not exceed
///   96 characters.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Default)]
pub struct EepromStringsError {
    /// Manufacturer string length.
    pub manufacturer: usize,
    /// Manufacturer ID string length.
    pub manufacturer_id: usize,
    /// Description string length.
    pub description: usize,
    /// Serial number string length.
    pub serial_number: usize,
}

impl EepromStringsError {
    /// Maximum length per string.
    pub const MAX_LEN: usize = 64;
    /// Maximum total string length.
    pub const MAX_TOTAL_LEN: usize = 96;
    /// Total length of all the strings.
    pub fn total_len(self) -> usize {
        self.manufacturer + self.manufacturer_id + self.description + self.serial_number
    }
}

impl fmt::Display for EepromStringsError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "EEPROM strings exceed limits \
        manufacturer {}/{} \
        manufacturer_id {}/{} \
        description {}/{} \
        serial_number {}/{} \
        total {}/{}",
            self.manufacturer,
            EepromStringsError::MAX_LEN,
            self.manufacturer_id,
            EepromStringsError::MAX_LEN,
            self.description,
            EepromStringsError::MAX_LEN,
            self.serial_number,
            EepromStringsError::MAX_LEN,
            self.total_len(),
            EepromStringsError::MAX_TOTAL_LEN,
        )
    }
}
