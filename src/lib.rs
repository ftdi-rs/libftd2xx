//! Rust safe wrapper for the [FTDI D2XX drivers].
//!
//! This takes the [libftd2xx-ffi] C bindings crate and extends it with rust
//! safe wrappers.
//!
//! # Usage
//! Simply add this crate as a dependency in your `Cargo.toml`.
//! The static library is distributed in the [libftd2xx-ffi] crate with
//! permission from FTDI.
//!
//! ```toml
//! [dependencies]
//! libftd2xx = "0.3"
//! ```
//!
//! This is a basic example to get your started.
//! Check the source code or documentation for more examples.
//! ```no_run
//! use libftd2xx::Ftdi;
//!
//! let mut ft = Ftdi::new()?;
//! let info = ft.device_info()?;
//! println!("Device information: {}", info);
//! # Ok::<(), libftd2xx::Ftd2xxError>(())
//! ```
//!
//! # References
//!
//! * [D2XX Programmers Guide V1.4]
//! * [D2XX Drivers Download Page]
//!
//! # Troubleshooting
//! ## Unknown Device on Linux
//! Remove the VCP FTDI driver.
//! ```bash
//! sudo rmmod ftdi_sio
//! sudo rmmod usbserial
//! ```
//! See [FTDI Drivers Installation Guide for Linux] for more details.
//!
//! # Maintainers Notes
//! ## README Generation
//! The README file is generated with [cargo-readme].
//!
//! ```bash
//! cargo install cargo-readme
//! cargo readme > README.md
//! ```
//!
//! [cargo-readme]: https://github.com/livioribeiro/cargo-readme
//! [D2XX Drivers Download Page]: https://www.ftdichip.com/Drivers/D2XX.htm
//! [D2xx Programmers Guide V1.4]: https://www.ftdichip.com/Support/Documents/ProgramGuides/D2XX_Programmer's_Guide(FT_000071).pdf
//! [FTDI D2XX drivers]: https://www.ftdichip.com/Drivers/D2XX.htm
//! [FTDI Drivers Installation Guide for Linux]: http://www.ftdichip.cn/Support/Documents/AppNotes/AN_220_FTDI_Drivers_Installation_Guide_for_Linux.pdf
//! [libftd2xx-ffi]: https://github.com/newAM/libftd2xx-ffi-rs
#![doc(html_root_url = "https://docs.rs/libftd2xx/0.3.0")]
#![deny(missing_docs, warnings)]

use libftd2xx_ffi::{
    FT_Close, FT_CreateDeviceInfoList, FT_GetDeviceInfo, FT_GetDeviceInfoList,
    FT_GetLibraryVersion, FT_GetQueueStatus, FT_ListDevices, FT_Open, FT_OpenEx, FT_Purge, FT_Read,
    FT_ResetDevice, FT_SetBitMode, FT_SetChars, FT_SetFlowControl, FT_SetLatencyTimer,
    FT_SetTimeouts, FT_SetUSBParameters, FT_Write, FT_BITMODE_ASYNC_BITBANG,
    FT_BITMODE_CBUS_BITBANG, FT_BITMODE_FAST_SERIAL, FT_BITMODE_MCU_HOST, FT_BITMODE_MPSSE,
    FT_BITMODE_RESET, FT_BITMODE_SYNC_BITBANG, FT_BITMODE_SYNC_FIFO, FT_DEVICE_LIST_INFO_NODE,
    FT_DEVICE_LIST_NOT_READY, FT_DEVICE_NOT_FOUND, FT_DEVICE_NOT_OPENED,
    FT_DEVICE_NOT_OPENED_FOR_ERASE, FT_DEVICE_NOT_OPENED_FOR_WRITE, FT_EEPROM_ERASE_FAILED,
    FT_EEPROM_NOT_PRESENT, FT_EEPROM_NOT_PROGRAMMED, FT_EEPROM_READ_FAILED, FT_EEPROM_WRITE_FAILED,
    FT_FAILED_TO_WRITE_DEVICE, FT_FLOW_DTR_DSR, FT_FLOW_NONE, FT_FLOW_RTS_CTS, FT_FLOW_XON_XOFF,
    FT_HANDLE, FT_INSUFFICIENT_RESOURCES, FT_INVALID_ARGS, FT_INVALID_BAUD_RATE, FT_INVALID_HANDLE,
    FT_INVALID_PARAMETER, FT_IO_ERROR, FT_LIST_NUMBER_ONLY, FT_NOT_SUPPORTED, FT_OK,
    FT_OPEN_BY_SERIAL_NUMBER, FT_OTHER_ERROR, FT_PURGE_RX, FT_PURGE_TX, FT_STATUS, PVOID, UCHAR,
    ULONG, USHORT,
};

use std::error::Error;
use std::ffi::c_void;
use std::fmt;
use std::mem;
use std::mem::transmute;
use std::ptr;
use std::time::Duration;
use std::vec::Vec;

/// BitModes for the FTDI ports.
///
/// This structure is passed to [`set_bit_mode`] to set the bit mode.
///
/// [`set_bit_mode`]: ./struct.Ftdi.html#method.set_bit_mode
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BitMode {
    /// Reset.
    Reset = FT_BITMODE_RESET as isize,
    /// Asynchronous bit bang.
    AsyncBitbang = FT_BITMODE_ASYNC_BITBANG as isize,
    /// MPSSE (FT2232, FT2232H, FT4232H and FT232H devices only)
    Mpsse = FT_BITMODE_MPSSE as isize,
    /// Synchronous Bit Bang
    /// (FT232R, FT245R,FT2232, FT2232H, FT4232H and FT232H devices only)
    SyncBitbang = FT_BITMODE_SYNC_BITBANG as isize,
    /// MCU Host Bus Emulation Mode
    /// (FT2232, FT2232H, FT4232Hand FT232H devices only)
    McuHost = FT_BITMODE_MCU_HOST as isize,
    /// FastOpto-Isolated Serial Mode
    /// (FT2232, FT2232H, FT4232H and FT232H devices only)
    FastSerial = FT_BITMODE_FAST_SERIAL as isize,
    /// CBUS Bit Bang Mode (FT232R and FT232H devices only)
    CbusBitbang = FT_BITMODE_CBUS_BITBANG as isize,
    /// Single Channel Synchronous 245 FIFO Mode
    /// (FT2232H and FT232H devices only)
    SyncFifo = FT_BITMODE_SYNC_FIFO as isize,
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
/// Unfortunately there are provided in the C API as self documenting, which they
/// are for the most part.
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
    /// Error name.
    pub name: &'static str,
    /// Error value.
    pub value: ErrorCode,
}

impl Ftd2xxError {
    fn new(status: FT_STATUS) -> Ftd2xxError {
        let name = match status {
            OK => panic!("OK is not an error"),
            INVALID_HANDLE => "INVALID_HANDLE",
            DEVICE_NOT_FOUND => "DEVICE_NOT_FOUND",
            DEVICE_NOT_OPENED => "DEVICE_NOT_OPENED",
            IO_ERROR => "IO_ERROR",
            INSUFFICIENT_RESOURCES => "INSUFFICIENT_RESOURCES",
            INVALID_PARAMETER => "INVALID_PARAMETER",
            INVALID_BAUD_RATE => "INVALID_BAUD_RATE",
            DEVICE_NOT_OPENED_FOR_ERASE => "DEVICE_NOT_OPENED_FOR_ERASE",
            DEVICE_NOT_OPENED_FOR_WRITE => "DEVICE_NOT_OPENED_FOR_WRITE",
            FAILED_TO_WRITE_DEVICE => "FAILED_TO_WRITE_DEVICE",
            EEPROM_READ_FAILED => "EEPROM_READ_FAILED",
            EEPROM_WRITE_FAILED => "EEPROM_WRITE_FAILED",
            EEPROM_ERASE_FAILED => "EEPROM_ERASE_FAILED",
            EEPROM_NOT_PRESENT => "EEPROM_NOT_PRESENT",
            EEPROM_NOT_PROGRAMMED => "EEPROM_NOT_PROGRAMMED",
            INVALID_ARGS => "INVALID_ARGS",
            NOT_SUPPORTED => "NOT_SUPPORTED",
            OTHER_ERROR => "OTHER_ERROR",
            DEVICE_LIST_NOT_READY => "DEVICE_LIST_NOT_READY",
            _ => panic!("unknown status: {}", status),
        };
        Ftd2xxError {
            name: name,
            value: status.into(),
        }
    }
}

impl fmt::Display for Ftd2xxError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "FTD2xx C API error {} ({})", self.name, self.value)
    }
}

impl Error for Ftd2xxError {
    fn description(&self) -> &str {
        &self.name
    }
}

macro_rules! ft_result {
    ($value:expr, $status:expr) => {
        if $status != 0 {
            Err(Ftd2xxError::new($status))
        } else {
            Ok($value)
        }
    };
}

/// Returns the number of FTDI devices connected to the system.
///
/// # Example
///
/// ```no_run
/// use libftd2xx::num_devices;
///
/// let num_devices = num_devices()?;
/// println!("Number of devices: {}", num_devices);
/// # Ok::<(), libftd2xx::Ftd2xxError>(())
/// ```
pub fn num_devices() -> Result<u32, Ftd2xxError> {
    let mut num_devs: u32 = 0;
    let num_devs_ptr: *mut u32 = &mut num_devs;
    let dummy: PVOID = std::ptr::null_mut();
    let status: FT_STATUS =
        unsafe { FT_ListDevices(num_devs_ptr as *mut c_void, dummy, FT_LIST_NUMBER_ONLY) };

    ft_result!(num_devs, status)
}

/// D2xx library version.
///
/// This is returned by [`library_version`].
///
/// [`library_version`]: ./fn.library_version.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Version {
    /// Major version.
    pub major: u8,
    /// Minor version.
    pub minor: u8,
    /// Build number.
    pub build: u8,
}

/// Returns the version of the underlying C library.
///
/// **Note**: The documentation says this function is only supported on Windows
/// but it seems to correctly work on Linux.
///
/// # Example
///
/// ```no_run
/// use libftd2xx::library_version;
///
/// let version = library_version()?;
/// println!("libftd2xx C library version: {:?}", version);
/// # Ok::<(), libftd2xx::Ftd2xxError>(())
/// ```
pub fn library_version() -> Result<Version, Ftd2xxError> {
    let mut version: u32 = 0;
    let status: FT_STATUS = unsafe { FT_GetLibraryVersion(&mut version) };
    ft_result!(
        Version {
            major: ((version >> 16) & 0xFF) as u8,
            minor: ((version >> 8) & 0xFF) as u8,
            build: (version & 0xFF) as u8
        },
        status
    )
}

/// USB device speed.
///
/// This is used in the [`DeviceInfo`] struct.
///
/// [`DeviceInfo`]: ./struct.DeviceInfo.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Speed {
    /// High speed USB
    HighSpeed,
    /// Full speed USB
    FullSpeed,
}

impl From<ULONG> for Speed {
    fn from(value: ULONG) -> Speed {
        if value == 0 {
            Speed::FullSpeed
        } else {
            Speed::HighSpeed
        }
    }
}

/// FTDI device types.
///
/// This is used in the [`DeviceInfo`] struct.
///
/// [`DeviceInfo`]: ./struct.DeviceInfo.html
#[allow(non_camel_case_types)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
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

impl From<ULONG> for DeviceType {
    fn from(value: ULONG) -> DeviceType {
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

// Maximum lengths for returned string values.
const SERIAL_NUMBER_LEN: usize = 16;
const DESCRIPTION_LEN: usize = 64;

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

// if there is a better way to deal with C-strings that contain interior nul
// bytes let me know
fn get_first_zero_char(array: &[u8]) -> Option<usize> {
    debug_assert!(array.len() >= 1);
    for i in 1..array.len() {
        if array[i] == 0 {
            return Some(i);
        }
    }
    None
}

impl fmt::Display for DeviceInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sn_nul_idx = get_first_zero_char(&self.serial_number).unwrap_or(SERIAL_NUMBER_LEN);
        let description_nul_idx = get_first_zero_char(&self.description).unwrap_or(DESCRIPTION_LEN);
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
            String::from_utf8_lossy(&self.serial_number[0..sn_nul_idx]),
            String::from_utf8_lossy(&self.description[0..description_nul_idx]),
        )
    }
}

fn create_device_info_list() -> Result<u32, Ftd2xxError> {
    let mut num_devices: u32 = 0;
    let status: FT_STATUS = unsafe { FT_CreateDeviceInfoList(&mut num_devices) };
    ft_result!(num_devices, status)
}

/// This function returns a device information vector with information about
/// the D2xx devices connected to the system.
///
/// # Example
///
/// ```no_run
/// use libftd2xx::list_devices;
///
/// let mut devices = list_devices()?;
///
/// while let Some(device) = devices.pop() {
///     println!("device: {}", device);
/// }
/// # Ok::<(), libftd2xx::Ftd2xxError>(())
/// ```
pub fn list_devices() -> Result<Vec<DeviceInfo>, Ftd2xxError> {
    let mut devices = Vec::new();
    let mut num_devices: u32 = create_device_info_list()?;
    let num_devices_usize: usize = num_devices as usize;
    if num_devices == 0 {
        return Ok(devices);
    }

    let status: FT_STATUS = unsafe {
        let list_info_memory_size = mem::size_of::<FT_DEVICE_LIST_INFO_NODE>() * num_devices_usize;
        let list_info_memory = libc::malloc(list_info_memory_size);
        if list_info_memory.is_null() {
            panic!("failed to allocate memory");
        }

        libc::memset(list_info_memory, 0, list_info_memory_size);

        let status = FT_GetDeviceInfoList(
            list_info_memory as *mut FT_DEVICE_LIST_INFO_NODE,
            &mut num_devices,
        );

        let slice: *const [FT_DEVICE_LIST_INFO_NODE] = ptr::slice_from_raw_parts(
            list_info_memory as *mut FT_DEVICE_LIST_INFO_NODE,
            num_devices_usize,
        );

        for n in 0..num_devices_usize {
            let info_node: FT_DEVICE_LIST_INFO_NODE = { &*slice }[n];

            devices.push(DeviceInfo {
                port_open: info_node.Flags & 0x1 == 0x1,
                speed: Some((info_node.Flags & 0x2).into()),
                device_type: info_node.Type.into(),
                product_id: (info_node.ID & 0xFFFF) as u16,
                vendor_id: ((info_node.ID >> 16) & 0xFFFF) as u16,
                serial_number: transmute::<[i8; SERIAL_NUMBER_LEN], [u8; SERIAL_NUMBER_LEN]>(
                    info_node.SerialNumber,
                ),
                description: transmute::<[i8; DESCRIPTION_LEN], [u8; DESCRIPTION_LEN]>(
                    info_node.Description,
                ),
            });
        }

        libc::free(list_info_memory as *mut libc::c_void);

        status
    };

    ft_result!(devices, status)
}

/// FTDI device. **Start here!**
pub struct Ftdi {
    handle: FT_HANDLE,
}

impl Ftdi {
    /// Open the first device on the system.
    ///
    /// This is equivalent to calling [`with_index`] with an index of `0`.
    ///
    /// This function cannot be used to open a specific device.
    /// Ordering of devices on a system is not guaranteed to remain constant.
    /// Calling this function multiple times may result in a different device
    /// each time when there is more than one device connected to the system.
    /// Use [`with_serial_number`] to open a specific device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// Ftdi::new()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    ///
    /// [`with_index`]: #method.with_index
    /// [`with_serial_number`]: #method.with_serial_number
    pub fn new() -> Result<Ftdi, Ftd2xxError> {
        Ftdi::with_index(0)
    }

    /// Open the device by an arbitrary index and initialize the handle.
    ///
    /// This function can open multiple devices, but it cannot be used to open
    /// a specific device.
    /// Ordering of devices on a system is not guaranteed to remain constant.
    /// Calling this function multiple times with the same index may result in a
    /// different device each time when there is more than one device connected
    /// to the system.
    /// Use [`with_serial_number`] to open a specific device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// Ftdi::with_index(0)?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    ///
    /// [`with_serial_number`]: #method.with_serial_number
    pub fn with_index(index: i32) -> Result<Ftdi, Ftd2xxError> {
        let mut handle: FT_HANDLE = std::ptr::null_mut();
        let status: FT_STATUS = unsafe { FT_Open(index, &mut handle) };
        ft_result!(Ftdi { handle: handle }, status)
    }

    /// Open the device by its serial number and initialize the handle.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// Ftdi::with_serial_number("FT59UO4C")?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn with_serial_number(serial_number: &str) -> Result<Ftdi, Ftd2xxError> {
        let mut handle: FT_HANDLE = std::ptr::null_mut();
        let status: FT_STATUS = unsafe {
            FT_OpenEx(
                serial_number.as_ptr() as *mut c_void,
                FT_OPEN_BY_SERIAL_NUMBER,
                &mut handle,
            )
        };

        ft_result!(Ftdi { handle: handle }, status)
    }

    /// Get device information for an open device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// let info = ft.device_info()?;
    /// println!("Device information: {}", info);
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn device_info(&mut self) -> Result<DeviceInfo, Ftd2xxError> {
        let mut dev_type: ULONG = 0;
        let mut dev_id: ULONG = 0;
        let mut sn: [u8; SERIAL_NUMBER_LEN] = [0; SERIAL_NUMBER_LEN];
        let mut description: [u8; DESCRIPTION_LEN] = [0; DESCRIPTION_LEN];
        let status: FT_STATUS = unsafe {
            FT_GetDeviceInfo(
                self.handle,
                &mut dev_type,
                &mut dev_id,
                sn.as_mut_ptr() as *mut i8,
                description.as_mut_ptr() as *mut i8,
                std::ptr::null_mut(),
            )
        };

        ft_result!(
            DeviceInfo {
                port_open: true,
                speed: None,
                device_type: dev_type.into(),
                vendor_id: ((dev_id >> 16) & 0xFFFF) as u16,
                product_id: (dev_id & 0xFFFF) as u16,
                serial_number: sn,
                description: description,
            },
            status
        )
    }

    /// This function sends a reset command to the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.reset()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn reset(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS = unsafe { FT_ResetDevice(self.handle) };
        ft_result!((), status)
    }

    /// Set the USB request transfer size.
    ///
    /// This function can be used to change the transfer sizes from the default
    /// transfer size of 4096 bytes to better suit the application requirements.
    /// Transfer sizes must be set to a multiple of 64 bytes between 64 bytes
    /// and 64k bytes.
    /// When [`set_usb_parameters`] is called, the change comes into effect
    /// immediately and any data that was held in the driver at the time of the
    /// change is lost.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_usb_parameters(16384)?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    ///
    /// [`set_usb_parameters`]: : #method.set_usb_parameters
    pub fn set_usb_parameters(&mut self, in_transfer_size: u32) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS =
            unsafe { FT_SetUSBParameters(self.handle, in_transfer_size, in_transfer_size) };
        ft_result!((), status)
    }

    /// This function sets the special characters for the device.
    ///
    /// This function allows for inserting specified characters in the data
    /// stream to represent events firing or errors occurring.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    ///
    /// // disable all special characters
    /// ft.set_chars(0, false, 0, false)?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_chars(
        &mut self,
        event_char: u8,
        event_enable: bool,
        error_char: u8,
        error_enable: bool,
    ) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS = unsafe {
            FT_SetChars(
                self.handle,
                event_char,
                event_enable as u8,
                error_char,
                error_enable as u8,
            )
        };
        ft_result!((), status)
    }

    /// This function sets the read and write timeouts for the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    /// use std::time::Duration;
    ///
    /// let mut ft = Ftdi::new()?;
    ///
    /// // Set read timeout of 5sec, write timeout of 1sec
    /// ft.set_timeouts(Duration::from_millis(5000), Duration::from_millis(1000))?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_timeouts(
        &mut self,
        read_timeout: Duration,
        write_timeout: Duration,
    ) -> Result<(), Ftd2xxError> {
        debug_assert!(
            read_timeout.as_millis() <= u32::max_value() as u128,
            "read_timeout integer overflow"
        );
        debug_assert!(
            write_timeout.as_millis() <= u32::max_value() as u128,
            "write_timeout integer overflow"
        );
        let status: FT_STATUS = unsafe {
            FT_SetTimeouts(
                self.handle,
                read_timeout.as_millis() as u32,
                write_timeout.as_millis() as u32,
            )
        };
        ft_result!((), status)
    }

    /// Set the latency timer value.
    ///
    /// In the FT8U232AM and FT8U245AM devices, the receive buffer timeout that
    /// is used to flush remaining data from the receive buffer was fixed at
    /// 16 ms.
    /// In all other FTDI devices, this timeout is programmable and can be set
    /// at 1 ms intervals between 2ms and 255 ms.  This allows the device to be
    /// better optimized for protocols requiring faster response times from
    /// short data packets.
    ///
    /// The valid range for the latency timer is 2 to 255 milliseconds.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    /// use std::time::Duration;
    ///
    /// let mut ft = Ftdi::new()?;
    ///
    /// // Set latency timer to 10 milliseconds
    /// ft.set_latency_timer(Duration::from_millis(10))?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_latency_timer(&mut self, timer: Duration) -> Result<(), Ftd2xxError> {
        debug_assert!(timer.as_millis() >= 2, "duration must be >= 2ms");
        debug_assert!(timer.as_millis() <= 255, "duration must be <= 255ms");
        let status: FT_STATUS =
            unsafe { FT_SetLatencyTimer(self.handle, timer.as_millis() as UCHAR) };
        ft_result!((), status)
    }

    /// This function disables flow control for the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_flow_control_none()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_flow_control_none(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_NONE as USHORT, 0, 0) };

        ft_result!((), status)
    }

    /// This function sets RTS/CTS flow control for the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_flow_control_rts_cts()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_flow_control_rts_cts(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_RTS_CTS as USHORT, 0, 0) };

        ft_result!((), status)
    }

    /// This function sets DTS/DSR flow control for the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_flow_control_dtr_dsr()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_flow_control_dtr_dsr(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_DTR_DSR as USHORT, 0, 0) };

        ft_result!((), status)
    }

    /// This function sets XON/XOFF flow control for the device.
    ///
    /// # Arguments
    ///
    /// * `xon` - Character used to signal Xon.
    /// * `xoff` - Character used to signal Xoff.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_flow_control_xon_xoff(0x11, 0x13)?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_flow_control_xon_xoff(&mut self, xon: u8, xoff: u8) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_XON_XOFF as USHORT, xon, xoff) };

        ft_result!((), status)
    }

    /// Enables different chip modes.
    ///
    /// # Arguments
    ///
    /// * `mask` - This bit mask sets up which bits are inputs and outputs.
    ///   A bit value of 0 sets the corresponding pin to an input,
    ///   a bit value of 1 sets the corresponding pin to an output.
    ///   In the case of CBUS Bit Bang, the upper nibble of this value controls
    ///   which pins are inputs and outputs, while the lower nibble controls
    ///   which of the outputs are high and low.
    /// * `mode` - Bitmode, see the `BitMode` struct for more details.
    ///
    /// For a description of available bit modes for the FT232R,
    /// see the application note [Bit Bang Modes for the FT232R and FT245R].
    ///
    /// For a description of available bit modes for the FT2232,
    /// see the application note [Bit Mode Functions for the FT2232].
    ///
    /// For a description of Bit Bang Mode for the FT232B and FT245B,
    /// see the application note [FT232B/FT245B Bit Bang Mode].
    ///
    /// Application notes are available for download from the [FTDI website].
    ///
    /// Note that to use CBUS Bit Bang for the FT232R,
    /// the CBUS must be configured for CBUS Bit Bang in the EEPROM.
    ///
    /// Note that to use Single Channel Synchronous 245 FIFO mode for the
    /// FT2232H, channel A must be configured for FT245 FIFO mode in the EEPROM.
    ///
    /// [Bit Bang Modes for the FT232R and FT245R]: https://www.ftdichip.com/Support/Documents/AppNotes/AN_232R-01_Bit_Bang_Mode_Available_For_FT232R_and_Ft245R.pdf
    /// [Bit Mode Functions for the FT2232]: https://www.ftdichip.com/Support/Documents/AppNotes/AN2232C-02_FT2232CBitMode.pdf
    /// [FT232B/FT245B Bit Bang Mode]: https://www.ftdichip.com/Support/Documents/AppNotes/AN232B-01_BitBang.pdf
    /// [FTDI website]: https://www.ftdichip.com/Support/Documents/AppNotes.htm
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, BitMode};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_bit_mode(0xFF, BitMode::AsyncBitbang)?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_bit_mode(&mut self, mask: u8, mode: BitMode) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS = unsafe { FT_SetBitMode(self.handle, mask, mode as u8) };

        ft_result!((), status)
    }

    /// Gets the number of bytes in the receive queue.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut buf: [u8; 4096] = [0; 4096];
    /// let mut ft = Ftdi::new()?;
    /// let rx_bytes = ft.queue_status()? as usize;
    ///
    /// if (rx_bytes > 0) {
    ///     ft.read(&mut buf[0..rx_bytes])?;
    /// }
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn queue_status(&mut self) -> Result<u32, Ftd2xxError> {
        let mut queue_status: u32 = 0;
        let status: FT_STATUS = unsafe { FT_GetQueueStatus(self.handle, &mut queue_status) };

        ft_result!(queue_status, status)
    }

    /// Read data from the device.
    ///
    /// This function does not return until the the buffer has been filled.
    /// The number of bytes in the receive queue can be determined by calling
    /// [`queue_status`], and then an buffer equal to the length of that
    /// value can be passed to [`read`] so that the function reads the device
    /// and returns immediately.
    ///
    /// When a read timeout value has been specified in a previous call to
    /// [`set_timeouts`], [`read`] returns when the timer expires or when the
    /// buffer has been filled, whichever occurs first.
    /// If the timeout occurred, [`read`] reads available data into the buffer
    /// and returns the number of bytes read.
    ///
    /// If the return value of [`read`] is equal to the length of the buffer
    /// then [`read`] has completed normally.
    ///
    /// If the return value of [`read`] is less than the length of the buffer
    /// then a timeout has occurred and the read has been partially completed.
    ///
    /// # Examples
    ///
    /// ## Read all available data
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut buf: [u8; 4096] = [0; 4096];
    /// let mut ft = Ftdi::new()?;
    /// let rx_bytes = ft.queue_status()? as usize;
    ///
    /// if rx_bytes > 0 {
    ///     ft.read(&mut buf[0..rx_bytes])?;
    /// }
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    ///
    /// ## Read with a timeout of 5 seconds
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    /// use std::time::Duration;
    ///
    /// const BUF_LEN: usize = 4096;
    /// let mut buf: [u8; BUF_LEN] = [0; BUF_LEN];
    /// let mut ft = Ftdi::new()?;
    ///
    /// ft.set_timeouts(Duration::from_millis(5000), Duration::from_millis(0))?;
    ///
    /// let bytes_read = ft.read(&mut buf)? as usize;
    /// if bytes_read == BUF_LEN {
    ///     println!("no read timeout")
    /// } else {
    ///     println!("read timeout")
    /// }
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    ///
    /// [`read`]: #method.read
    /// [`queue_status`]: #method.queue_status
    /// [`set_timeouts`]: #method.set_timeouts
    pub fn read(&mut self, buf: &mut [u8]) -> Result<u32, Ftd2xxError> {
        let mut bytes_returned: u32 = 0;
        let len = buf.len();
        debug_assert!(len < u32::max_value() as usize, "buffer is too large");
        let status: FT_STATUS = unsafe {
            FT_Read(
                self.handle,
                buf.as_mut_ptr() as *mut c_void,
                len as u32,
                &mut bytes_returned,
            )
        };

        ft_result!(bytes_returned, status)
    }

    /// Write data to the device.
    ///
    /// Returns the number of bytes written.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// const BUF_SIZE: usize = 256;
    /// let buf: [u8; BUF_SIZE] = [0; BUF_SIZE];
    /// let mut ft = Ftdi::new()?;
    /// let num_bytes_written = ft.write(&buf)? as usize;
    /// if num_bytes_written == BUF_SIZE {
    ///     println!("no write timeout")
    /// } else {
    ///     println!("write timeout")
    /// }
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn write(&mut self, buf: &[u8]) -> Result<u32, Ftd2xxError> {
        let mut bytes_written: u32 = 0;
        let len = buf.len();
        debug_assert!(len < u32::max_value() as usize, "buffer is too large");
        let status: FT_STATUS = unsafe {
            FT_Write(
                self.handle,
                buf.as_ptr() as *mut c_void,
                len as u32,
                &mut bytes_written,
            )
        };
        ft_result!(bytes_written, status)
    }

    /// This function purges the transmit buffers in the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.purge_tx()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn purge_tx(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS = unsafe { FT_Purge(self.handle, FT_PURGE_TX) };
        ft_result!((), status)
    }

    /// This function purges the receive buffers in the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.purge_rx()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn purge_rx(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS = unsafe { FT_Purge(self.handle, FT_PURGE_RX) };
        ft_result!((), status)
    }

    /// This function purges the transmit and receive buffers in the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.purge_all()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn purge_all(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS = unsafe { FT_Purge(self.handle, FT_PURGE_TX | FT_PURGE_RX) };
        ft_result!((), status)
    }

    /// Close an open device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.close()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn close(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS = unsafe { FT_Close(self.handle) };
        ft_result!((), status)
    }
}

impl Drop for Ftdi {
    fn drop(&mut self) {
        // TODO: This can return an error, but all the sample code in the
        // programmers guide ignores it.
        unsafe { FT_Close(self.handle) };
    }
}
