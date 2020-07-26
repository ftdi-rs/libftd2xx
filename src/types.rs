#![deny(missing_docs, warnings)]
use libftd2xx_ffi::{
    FT_BITMODE_ASYNC_BITBANG, FT_BITMODE_CBUS_BITBANG, FT_BITMODE_FAST_SERIAL, FT_BITMODE_MCU_HOST,
    FT_BITMODE_MPSSE, FT_BITMODE_RESET, FT_BITMODE_SYNC_BITBANG, FT_BITMODE_SYNC_FIFO,
    FT_DEVICE_LIST_NOT_READY, FT_DEVICE_NOT_FOUND, FT_DEVICE_NOT_OPENED,
    FT_DEVICE_NOT_OPENED_FOR_ERASE, FT_DEVICE_NOT_OPENED_FOR_WRITE, FT_EEPROM_232H,
    FT_EEPROM_ERASE_FAILED, FT_EEPROM_HEADER, FT_EEPROM_NOT_PRESENT, FT_EEPROM_NOT_PROGRAMMED,
    FT_EEPROM_READ_FAILED, FT_EEPROM_WRITE_FAILED, FT_FAILED_TO_WRITE_DEVICE,
    FT_INSUFFICIENT_RESOURCES, FT_INVALID_ARGS, FT_INVALID_BAUD_RATE, FT_INVALID_HANDLE,
    FT_INVALID_PARAMETER, FT_IO_ERROR, FT_NOT_SUPPORTED, FT_OK, FT_OTHER_ERROR, FT_STATUS,
};
use std::error::Error;
use std::fmt;
use std::mem::transmute;

/// FTDI device types.
///
/// This is used in the [`DeviceInfo`] struct.
///
/// [`DeviceInfo`]: ./struct.DeviceInfo.html
#[allow(non_camel_case_types)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u32)]
pub enum DeviceType {
    /// FTDI BM device.
    FTBM = 0,
    /// FTDI AM device.
    FTAM = 1,
    /// FTDI 100AX device.
    FT100AX = 2,
    /// FTDI 2232C device.
    FT2232C = 4,
    /// FTDI 232R device.
    FT232R = 5,
    /// FT2232H device.
    FT2232H = 6,
    /// FT4232H device.
    FT4232H = 7,
    /// FT232H device.
    FT232H = 8,
    /// FTDI x series device.
    FT_X_SERIES = 9,
    /// FT4222H device.
    FT4222H_0 = 10,
    /// FT4222H device.
    FT4222H_1_2 = 11,
    /// FT4222H device.
    FT4222H_3 = 12,
    /// FT4222H device.
    FT4222_PROG = 13,
}

impl From<u32> for DeviceType {
    fn from(value: u32) -> DeviceType {
        match value {
            0 => DeviceType::FTBM,
            1 => DeviceType::FTAM,
            2 => DeviceType::FT100AX,
            4 => DeviceType::FT2232C,
            5 => DeviceType::FT232R,
            6 => DeviceType::FT2232H,
            7 => DeviceType::FT4232H,
            8 => DeviceType::FT232H,
            9 => DeviceType::FT_X_SERIES,
            10 => DeviceType::FT4222H_0,
            11 => DeviceType::FT4222H_1_2,
            12 => DeviceType::FT4222H_3,
            13 => DeviceType::FT4222_PROG,
            _ => panic!("unknown device: {}", value),
        }
    }
}

// Maximum lengths for EEPROM strings
pub const EEPROM_STRING_LEN: usize = 64;

/// EEPROM header structurecommon to all FTDI devices.
///
/// Used in the [`eeprom_read`] and [`eeprom_program`] functions.
///
/// [`eeprom_read`]: ./struct.Ftdi.html#method.eeprom_read
/// [`eeprom_program`]: ./struct.Ftdi.html#method.eeprom_program
#[derive(Copy, Clone)]
pub struct EepromHeader {
    /// Manufacturer.
    pub manufacturer: [u8; EEPROM_STRING_LEN],
    /// Manufacturer ID, typically the first two characters of the serial
    /// number.
    pub manufacturer_id: [u8; EEPROM_STRING_LEN],
    /// Device description.
    pub description: [u8; EEPROM_STRING_LEN],
    /// Serial number.
    pub serial_number: [u8; EEPROM_STRING_LEN],
    /// Device type.
    pub device_type: DeviceType,
    /// USB vendor ID, typically 0x0403.
    pub vendor_id: u16,
    /// USB product ID.
    pub product_id: u16,
    /// non-zero if serial number to be used (TODO)
    pub serial_number_enable: bool,
    /// Maximum power.
    ///
    /// The source documentation is a little lacking here.
    /// My best assumption is that this a maximum device power in milliamps.
    ///
    /// This field cannot be programmed to a value greater than 500.
    pub max_power: u16,
    /// 0 = bus powered, 1 = self powered
    pub self_powered: bool,
    /// 0 = not capable, 1 = capable
    pub remote_wakeup: bool,
    /// non-zero if pull down in suspend enabled
    pub pull_down_enable: bool,
}

impl EepromHeader {
    fn new(
        data: FT_EEPROM_HEADER,
        manufacturer: [i8; EEPROM_STRING_LEN],
        manufacturer_id: [i8; EEPROM_STRING_LEN],
        description: [i8; EEPROM_STRING_LEN],
        serial_number: [i8; EEPROM_STRING_LEN],
    ) -> EepromHeader {
        EepromHeader {
            device_type: data.deviceType.into(),
            manufacturer: unsafe {
                transmute::<[i8; EEPROM_STRING_LEN], [u8; EEPROM_STRING_LEN]>(manufacturer)
            },
            manufacturer_id: unsafe {
                transmute::<[i8; EEPROM_STRING_LEN], [u8; EEPROM_STRING_LEN]>(manufacturer_id)
            },
            description: unsafe {
                transmute::<[i8; EEPROM_STRING_LEN], [u8; EEPROM_STRING_LEN]>(description)
            },
            serial_number: unsafe {
                transmute::<[i8; EEPROM_STRING_LEN], [u8; EEPROM_STRING_LEN]>(serial_number)
            },
            vendor_id: data.VendorId,
            product_id: data.ProductId,
            serial_number_enable: data.SerNumEnable != 0,
            max_power: data.MaxPower,
            self_powered: data.SelfPowered != 0,
            remote_wakeup: data.RemoteWakeup != 0,
            pull_down_enable: data.PullDownEnable != 0,
        }
    }
}

// if there is a better way to deal with C-strings that contain interior nul
// bytes let me know
fn u8_into_string(array: &[u8]) -> String {
    debug_assert!(!array.is_empty());
    let mut idx: usize = array.len();
    for i in 1..array.len() {
        if array[i] == 0 {
            idx = i;
            break;
        }
    }
    String::from_utf8_lossy(&array[0..idx]).to_string()
}

impl fmt::Debug for EepromHeader {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "DeviceInfo {{ \
                manufacturer: {}, \
                manufacturer_id: {}, \
                description: {}, \
                serial_number: {}, \
                device_type: {:?}, \
                vendor_id: 0x{:04X}, \
                product_id: 0x{:04X}, \
                serial_number_enable: {}, \
                max_power: {}, \
                self_powered: {}, \
                remote_wakeup: {}, \
                pull_down_enable: {} \
            }}",
            u8_into_string(&self.manufacturer),
            u8_into_string(&self.manufacturer_id),
            u8_into_string(&self.description),
            u8_into_string(&self.serial_number),
            self.device_type,
            self.vendor_id,
            self.product_id,
            self.serial_number_enable,
            self.max_power,
            self.self_powered,
            self.remote_wakeup,
            self.pull_down_enable,
        )
    }
}

/// FT232H EEPROM structure.
///
/// Used in the [`eeprom_read`] and [`eeprom_program`] functions.
///
/// [`eeprom_read`]: ./struct.Ftdi.html#method.eeprom_read
/// [`eeprom_program`]: ./struct.Ftdi.html#method.eeprom_program
#[derive(Debug, Copy, Clone)]
pub struct Eeprom232h {
    /// Common EEPROM header
    pub header: EepromHeader,
    /// non-zero if AC bus pins have slow slew
    pub ac_slow_slew: u8,
    /// non-zero if AC bus pins are Schmitt input
    pub ac_schmitt_input: u8,
    /// valid values are 4mA, 8mA, 12mA, 16mA
    pub ac_drive_current: u8,
    /// non-zero if AD bus pins have slow slew
    pub ad_slow_slew: u8,
    /// non-zero if AD bus pins are Schmitt input
    pub ad_schmitt_input: u8,
    /// valid values are 4mA, 8mA, 12mA, 16mA
    pub ad_drive_current: u8,
    /// CBUS mux control
    pub cbus0: u8,
    /// CBUS mux control
    pub cbus1: u8,
    /// CBUS mux control
    pub cbus2: u8,
    /// CBUS mux control
    pub cbus3: u8,
    /// CBUS mux control
    pub cbus4: u8,
    /// CBUS mux control
    pub cbus5: u8,
    /// CBUS mux control
    pub cbus6: u8,
    /// CBUS mux control
    pub cbus7: u8,
    /// CBUS mux control
    pub cbus8: u8,
    /// CBUS mux control
    pub cbus9: u8,
    /// FT1248 clock polarity - clock idle high (1) or clock idle low (0)
    pub ft1248_cpol: u8,
    /// FT1248 data is LSB (1) or MSB (0)
    pub ft1248_lsb: u8,
    /// FT1248 flow control enable
    pub ft1248_flow_control: u8,
    /// non-zero if interface is 245 FIFO
    pub is_fifo: u8,
    /// non-zero if interface is 245 FIFO CPU target
    pub is_fifo_target: u8,
    /// non-zero if interface is Fast serial
    pub is_fast_serial: u8,
    /// non-zero if interface is FT1248
    pub is_ft1248: u8,
    /// TODO
    pub power_save_enable: u8,
    /// Driver option
    pub driver_type: u8,
}

impl Eeprom232h {
    /// Create a new FT232H EEPROM structure.
    pub fn new(
        data: FT_EEPROM_232H,
        manufacturer: [i8; EEPROM_STRING_LEN],
        manufacturer_id: [i8; EEPROM_STRING_LEN],
        description: [i8; EEPROM_STRING_LEN],
        serial_number: [i8; EEPROM_STRING_LEN],
    ) -> Eeprom232h {
        Eeprom232h {
            header: EepromHeader::new(
                data.common,
                manufacturer,
                manufacturer_id,
                description,
                serial_number,
            ),
            ac_slow_slew: data.ACSlowSlew,
            ac_schmitt_input: data.ACSchmittInput,
            ac_drive_current: data.ACDriveCurrent,
            ad_slow_slew: data.ADSlowSlew,
            ad_schmitt_input: data.ADSchmittInput,
            ad_drive_current: data.ADDriveCurrent,
            cbus0: data.Cbus0,
            cbus1: data.Cbus1,
            cbus2: data.Cbus2,
            cbus3: data.Cbus3,
            cbus4: data.Cbus4,
            cbus5: data.Cbus5,
            cbus6: data.Cbus6,
            cbus7: data.Cbus7,
            cbus8: data.Cbus8,
            cbus9: data.Cbus9,
            ft1248_cpol: data.FT1248Cpol,
            ft1248_lsb: data.FT1248Lsb,
            ft1248_flow_control: data.FT1248FlowControl,
            is_fifo: data.IsFifo,
            is_fifo_target: data.IsFifoTar,
            is_fast_serial: data.IsFastSer,
            is_ft1248: data.IsFT1248,
            power_save_enable: data.PowerSaveEnable,
            driver_type: data.DriverType,
        }
    }
}

/// D2XX version structure.
///
/// This is returned by [`library_version`] and [`driver_version`].
///
/// [`library_version`]: ./fn.library_version.html
/// [`driver_version`]: ./struct.Ftdi.html#method.driver_version
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Version {
    /// Major version.
    pub major: u8,
    /// Minor version.
    pub minor: u8,
    /// Build number.
    pub build: u8,
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
fn test_bit_mode_sanity() {
    assert_eq!(BitMode::Reset as u8, 0x00);
    assert_eq!(BitMode::AsyncBitbang as u8, 0x01);
    assert_eq!(BitMode::Mpsse as u8, 0x02);
    assert_eq!(BitMode::SyncBitbang as u8, 0x04);
    assert_eq!(BitMode::McuHost as u8, 0x08);
    assert_eq!(BitMode::FastSerial as u8, 0x10);
    assert_eq!(BitMode::CbusBitbang as u8, 0x20);
    assert_eq!(BitMode::SyncFifo as u8, 0x40);
}

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
pub enum ErrorCode {
    INVALID_HANDLE = FT_INVALID_HANDLE as isize,
    DEVICE_NOT_FOUND = FT_DEVICE_NOT_FOUND as isize,
    DEVICE_NOT_OPENED = FT_DEVICE_NOT_OPENED as isize,
    IO_ERROR = FT_IO_ERROR as isize,
    INSUFFICIENT_RESOURCES = FT_INSUFFICIENT_RESOURCES as isize,
    INVALID_PARAMETER = FT_INVALID_PARAMETER as isize,
    INVALID_BAUD_RATE = FT_INVALID_BAUD_RATE as isize,
    DEVICE_NOT_OPENED_FOR_ERASE = FT_DEVICE_NOT_OPENED_FOR_ERASE as isize,
    DEVICE_NOT_OPENED_FOR_WRITE = FT_DEVICE_NOT_OPENED_FOR_WRITE as isize,
    FAILED_TO_WRITE_DEVICE = FT_FAILED_TO_WRITE_DEVICE as isize,
    EEPROM_READ_FAILED = FT_EEPROM_READ_FAILED as isize,
    EEPROM_WRITE_FAILED = FT_EEPROM_WRITE_FAILED as isize,
    EEPROM_ERASE_FAILED = FT_EEPROM_ERASE_FAILED as isize,
    EEPROM_NOT_PRESENT = FT_EEPROM_NOT_PRESENT as isize,
    EEPROM_NOT_PROGRAMMED = FT_EEPROM_NOT_PROGRAMMED as isize,
    INVALID_ARGS = FT_INVALID_ARGS as isize,
    NOT_SUPPORTED = FT_NOT_SUPPORTED as isize,
    /// This seems to be used only in higher level FTDI provided C libraries
    /// such as libmpsse.
    OTHER_ERROR = FT_OTHER_ERROR as isize,
    DEVICE_LIST_NOT_READY = FT_DEVICE_LIST_NOT_READY as isize,
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
fn test_ftd2xx_error_diplay() {
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

// Maximum lengths for returned string values.
pub const SERIAL_NUMBER_LEN: usize = 16;
pub const DESCRIPTION_LEN: usize = 64;

/// FTDI device information.
///
/// This is returned by [`list_devices`] and [`device_info`].
///
/// [`list_devices`]: ./fn.list_devices.html
/// [`device_info`]: ./struct.Ftdi.html#method.device_info
#[derive(Clone)]
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
    /// FTDI vendor ID.
    pub vendor_id: u16,
    /// FTDI product ID.
    pub product_id: u16,
    /// Device serial number.
    pub serial_number: [u8; SERIAL_NUMBER_LEN],
    /// Device description.
    pub description: [u8; DESCRIPTION_LEN],
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
            u8_into_string(&self.serial_number),
            u8_into_string(&self.description),
        )
    }
}

/// Enumeration of all EEPROM structures.
#[derive(Debug, Copy, Clone)]
pub enum Eeprom {
    /// FT232H EEPROM.
    Eeprom232h(Eeprom232h),
}
