//! libftd2xx rust library.
//!
//! This takes the [libftd2xx-ffi-rs] C bindings library and extends it with
//! rust safe wrappers.
//!
//! Documentation for the underlying C API can be found here:
//! [D2xx Programmers Guide V1.4].
//!
//! Downloads for the ftd2xx compiled releases (FTDI does not release source)
//! can be found here: [D2XX Drivers].
//!
//! Licensing for the underlying driver can be found here:
//! [Driver License Terms].
//!
//! [libftd2xx-ffi-rs]: https://github.com/newAM/libftd2xx-ffi-rs
//! [D2xx Programmers Guide V1.4]: https://www.ftdichip.com/Support/Documents/ProgramGuides/D2XX_Programmer's_Guide(FT_000071).pdf
//! [D2XX Drivers]: https://www.ftdichip.com/Drivers/D2XX.htm
//! [Driver License Terms]: https://www.ftdichip.com/Drivers/FTDriverLicenceTermsSummary.htm
#![doc(html_root_url = "https://docs.rs/libftd2xx/0.1.0")]
#![deny(missing_docs, warnings)]

pub use libftd2xx_ffi::DWORD;
use libftd2xx_ffi::{
    FT_Close, FT_CreateDeviceInfoList, FT_GetDeviceInfoList, FT_GetLibraryVersion,
    FT_GetQueueStatus, FT_ListDevices, FT_OpenEx, FT_Read, FT_ResetDevice, FT_SetBitMode,
    FT_SetChars, FT_SetFlowControl, FT_SetLatencyTimer, FT_SetTimeouts, FT_SetUSBParameters,
    FT_Write, FT_BITMODE_ASYNC_BITBANG, FT_BITMODE_CBUS_BITBANG, FT_BITMODE_FAST_SERIAL,
    FT_BITMODE_MCU_HOST, FT_BITMODE_MPSSE, FT_BITMODE_RESET, FT_BITMODE_SYNC_BITBANG,
    FT_BITMODE_SYNC_FIFO, FT_DEVICE_LIST_INFO_NODE, FT_FLOW_DTR_DSR, FT_FLOW_NONE, FT_FLOW_RTS_CTS,
    FT_FLOW_XON_XOFF, FT_HANDLE, FT_LIST_NUMBER_ONLY, FT_OPEN_BY_SERIAL_NUMBER, FT_STATUS, PVOID,
    UCHAR, ULONG, USHORT,
};
use std::error::Error;
use std::ffi::{c_void, CStr, CString};
use std::fmt;
use std::mem;
use std::ptr;
use std::time::Duration;
use std::vec::Vec;

/// BitModes for the FTDI ports.
pub enum BitMode {
    /// Reset.
    Reset = FT_BITMODE_RESET as isize,
    /// Asynchronous bit bang.
    AsyncBitbang = FT_BITMODE_ASYNC_BITBANG as isize,
    /// MPSSE (FT2232, FT2232H, FT4232H and FT232Hdevices only)
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

/// FTD2XX API errors.
///
/// This is the equivalent of `FT_STATUS` in the C API.
#[derive(Debug)]
pub struct Ftd2xxError {
    /// Error name.
    pub name: String,
    /// Error value.
    pub value: usize,
}

impl Ftd2xxError {
    fn new(status: FT_STATUS) -> Ftd2xxError {
        let name = match status {
            0 => panic!("OK is not an error"),
            1 => "INVALID_HANDLE",
            2 => "DEVICE_NOT_FOUND",
            3 => "DEVICE_NOT_OPENED",
            4 => "IO_ERROR",
            5 => "INSUFFICIENT_RESOURCES",
            6 => "INVALID_PARAMETER",
            7 => "INVALID_BAUD_RATE",
            8 => "DEVICE_NOT_OPENED_FOR_ERASE",
            9 => "DEVICE_NOT_OPENED_FOR_WRITE",
            10 => "FAILED_TO_WRITE_DEVICE",
            11 => "EEPROM_READ_FAILED",
            12 => "EEPROM_WRITE_FAILED",
            13 => "EEPROM_ERASE_FAILED",
            14 => "EEPROM_NOT_PRESENT",
            15 => "EEPROM_NOT_PROGRAMMED",
            16 => "INVALID_ARGS",
            17 => "NOT_SUPPORTED",
            18 => "OTHER_ERROR",
            19 => "DEVICE_LIST_NOT_READY",
            _ => panic!("unknown status"),
        };
        Ftd2xxError {
            name: name.to_string(),
            value: status as usize,
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
pub fn num_devices() -> Result<DWORD, Ftd2xxError> {
    let mut num_devs: DWORD = 0;
    let num_devs_ptr: *mut DWORD = &mut num_devs;
    let dummy: PVOID = std::ptr::null_mut();
    let status: FT_STATUS =
        unsafe { FT_ListDevices(num_devs_ptr as *mut c_void, dummy, FT_LIST_NUMBER_ONLY) };

    ft_result!(num_devs, status)
}

/// D2xx library version.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Version {
    /// Major version.
    pub major: u8,
    /// Minor version.
    pub minor: u8,
    /// Build number.
    pub build: u8,
}

/// Returns the version of the underlying library.
///
/// **Note**: The documentation says this function is only supported on Windows
/// but it seems to correctly work on Linux.
///
/// # Example
///
/// ```
/// use libftd2xx::library_version;
///
/// let version = library_version()?;
/// println!("libftd2xx C library version: {:?}", version);
/// # Ok::<(), libftd2xx::Ftd2xxError>(())
/// ```
pub fn library_version() -> Result<Version, Ftd2xxError> {
    let mut version: DWORD = 0;
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
#[allow(non_camel_case_types)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum DeviceType {
    /// FTDI BM device.
    FT_BM,
    /// FTDI AM device.
    FT_AM,
    /// FTDI 100AX device.
    FT_100AX,
    /// FTDI 2232C device.
    FT_2232C,
    /// FTDI 232R device.
    FT_232R,
    /// FT2232H device.
    FT_2232H,
    /// FT4232H device.
    FT_4232H,
    /// FT232H device.
    FT_232H,
    /// FTDI x series device.
    FT_X_SERIES,
    /// FT4222H device.
    FT_4222H_0,
    /// FT4222H device.
    FT_4222H_1_2,
    /// FT4222H device.
    FT_4222H_3,
    /// FT4222H device.
    FT_4222_PROG,
}

impl From<ULONG> for DeviceType {
    fn from(value: ULONG) -> DeviceType {
        match value {
            0 => DeviceType::FT_BM,
            1 => DeviceType::FT_AM,
            2 => DeviceType::FT_100AX,
            3 => DeviceType::FT_2232C,
            4 => DeviceType::FT_232R,
            5 => DeviceType::FT_2232H,
            6 => DeviceType::FT_4232H,
            7 => DeviceType::FT_232H,
            8 => DeviceType::FT_X_SERIES,
            9 => DeviceType::FT_4222H_0,
            10 => DeviceType::FT_4222H_1_2,
            11 => DeviceType::FT_4222H_3,
            12 => DeviceType::FT_4222_PROG,
            _ => panic!("unknown device"),
        }
    }
}

/// FTDI device information.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct DeviceInfo {
    /// `true` if the port is open.
    pub port_open: bool,
    /// USB link speed.
    pub speed: Speed,
    /// FTDI device type.
    pub device_type: DeviceType,
    /// FTDI vendor ID.
    pub vendor_id: u16,
    /// FTDI product ID.
    pub product_id: u16,
    /// Device serial number.
    pub serial_number: String,
    /// Device description.
    pub description: String,
}

impl fmt::Display for DeviceInfo {
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
            self.description
        )
    }
}

fn create_device_info_list() -> Result<DWORD, Ftd2xxError> {
    let mut num_devices: DWORD = 0;
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
    let mut num_devices: DWORD = create_device_info_list()?;
    let num_devices_usize: usize = num_devices as usize;
    if num_devices == 0 {
        return Ok(devices);
    }

    let status: FT_STATUS = unsafe {
        let list_info_memory =
            libc::malloc(mem::size_of::<FT_DEVICE_LIST_INFO_NODE>() * num_devices_usize)
                as *mut FT_DEVICE_LIST_INFO_NODE;

        if list_info_memory.is_null() {
            panic!("failed to allocate memory");
        }

        let status = FT_GetDeviceInfoList(list_info_memory, &mut num_devices);

        let slice: *const [FT_DEVICE_LIST_INFO_NODE] =
            ptr::slice_from_raw_parts(list_info_memory, num_devices_usize);

        for n in 0..num_devices_usize {
            let info_node: FT_DEVICE_LIST_INFO_NODE = { &*slice }[n];

            devices.push(DeviceInfo {
                port_open: info_node.Flags & 0x1 == 0x1,
                speed: (info_node.Flags & 0x2).into(),
                device_type: info_node.Type.into(),
                product_id: (info_node.ID & 0xFFFF) as u16,
                vendor_id: ((info_node.ID >> 16) & 0xFFFF) as u16,
                serial_number: CStr::from_ptr(info_node.SerialNumber.as_ptr())
                    .to_string_lossy()
                    .into_owned(),
                description: CStr::from_ptr(info_node.Description.as_ptr())
                    .to_string_lossy()
                    .into_owned(),
            });
        }

        libc::free(list_info_memory as *mut libc::c_void);

        status
    };

    ft_result!(devices, status)
}

/// FTDI device.
pub struct FTDI {
    handle: FT_HANDLE,
}

impl FTDI {
    /// Open the device by its serial number and initialize the handle.
    pub fn open_by_serial_number(serial_number: &str) -> Result<FTDI, Ftd2xxError> {
        let sn = CString::new(serial_number).unwrap();
        let mut handle: FT_HANDLE = std::ptr::null_mut();
        let status: FT_STATUS = unsafe {
            FT_OpenEx(
                sn.as_ptr() as *mut c_void,
                FT_OPEN_BY_SERIAL_NUMBER,
                &mut handle,
            )
        };

        ft_result!(FTDI { handle: handle }, status)
    }

    /// This function sends a reset command to the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::FTDI;
    ///
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
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
    /// When FT_SetUSBParameters is called, the change comes into effect
    /// immediately and any data that was held in the driver at the time of the
    /// change is lost.
    ///
    /// Note that, at present, only `in_transfer_size` is supported.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::FTDI;
    ///
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
    /// ft.set_usb_parameters(16384, 0)?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_usb_parameters(
        &mut self,
        in_transfer_size: DWORD,
        out_transfer_size: DWORD,
    ) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS =
            unsafe { FT_SetUSBParameters(self.handle, in_transfer_size, out_transfer_size) };
        ft_result!((), status)
    }

    /// This function sets the special characters for the device.
    ///
    /// This function allows for inserting specified characters in the data
    /// stream to represent events firing or errors occurring.
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
    /// use libftd2xx::FTDI;
    /// use std::time::Duration;
    ///
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
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
            read_timeout.as_millis() <= DWORD::max_value() as u128,
            "read_timeout integer overflow"
        );
        debug_assert!(
            write_timeout.as_millis() <= DWORD::max_value() as u128,
            "write_timeout integer overflow"
        );
        let status: FT_STATUS = unsafe {
            FT_SetTimeouts(
                self.handle,
                read_timeout.as_millis() as DWORD,
                write_timeout.as_millis() as DWORD,
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
    /// use libftd2xx::FTDI;
    /// use std::time::Duration;
    ///
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
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
    /// use libftd2xx::FTDI;
    ///
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
    /// ft.set_flow_control_none()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn set_flow_control_none(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_NONE as USHORT, 0, 0) };

        ft_result!((), status)
    }

    /// This function sets RTS/CTS flow control for the device.
    pub fn set_flow_control_rts_cts(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_RTS_CTS as USHORT, 0, 0) };

        ft_result!((), status)
    }

    /// This function sets DTS/DSR flow control for the device.
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
    /// see the applicationnote [Bit Mode Functions for the FT2232].
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
    /// use libftd2xx::{FTDI, BitMode};
    ///
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
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
    /// use libftd2xx::FTDI;
    ///
    /// let mut buf: [u8; 4096] = [0; 4096];
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
    /// let rx_bytes = ft.queue_status()? as usize;
    ///
    /// if (rx_bytes > 0) {
    ///     ft.read(&mut buf[0..rx_bytes])?;
    /// }
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn queue_status(&mut self) -> Result<DWORD, Ftd2xxError> {
        let mut queue_status: DWORD = 0;
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
    /// ## Read all avliable data
    ///
    /// ```no_run
    /// use libftd2xx::FTDI;
    ///
    /// let mut buf: [u8; 4096] = [0; 4096];
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
    /// let rx_bytes = ft.queue_status()? as usize;
    ///
    /// if (rx_bytes > 0) {
    ///     ft.read(&mut buf[0..rx_bytes])?;
    /// }
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    ///
    /// ## Read with a timeout of 5 seconds
    ///
    /// ```no_run
    /// use libftd2xx::FTDI;
    /// use std::time::Duration;
    ///
    /// const BUF_LEN: usize = 4096;
    /// let mut buf: [u8; BUF_LEN] = [0; BUF_LEN];
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
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
    pub fn read(&mut self, buf: &mut [u8]) -> Result<DWORD, Ftd2xxError> {
        let mut bytes_returned: DWORD = 0;
        let len = buf.len();
        debug_assert!(len < DWORD::max_value() as usize, "buffer is too large");
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
    /// ```no_run
    /// use libftd2xx::FTDI;
    ///
    /// let buf: [u8; 256] = [0; 256];
    /// let mut ft = FTDI::open_by_serial_number("FT59UO4C")?;
    /// ft.write(&buf)?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn write(&mut self, buf: &[u8]) -> Result<DWORD, Ftd2xxError> {
        let mut bytes_written: DWORD = 0;
        let len = buf.len();
        debug_assert!(len < DWORD::max_value() as usize, "buffer is too large");
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
}

impl Drop for FTDI {
    fn drop(&mut self) {
        // TODO: This can return an error, but all the sample code in the
        // programmers guide ignores it.
        unsafe { FT_Close(self.handle) };
    }
}
