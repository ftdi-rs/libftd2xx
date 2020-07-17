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
//! libftd2xx = "~0.5.0"
//! ```
//!
//! This is a basic example to get your started.
//! Check the source code or documentation for more examples.
//! ```no_run
//! use libftd2xx::Ftdi;
//!
//! let mut ft = Ftdi::new()?;
//! let info = ft.device_info()?;
//! println!("Device information: {:?}", info);
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
#![doc(html_root_url = "https://docs.rs/libftd2xx/0.5.0")]
#![deny(missing_docs, warnings)]
#![allow(clippy::redundant_field_names)]

mod types;
pub use types::{
    BitMode, Description, DeviceInfo, DeviceType, Ftd2xxError, SerialNumber, Speed, Version,
};
use types::{DESCRIPTION_LEN, SERIAL_NUMBER_LEN};

use libftd2xx_ffi::{
    FT_Close, FT_CreateDeviceInfoList, FT_EE_UARead, FT_EE_UASize, FT_EE_UAWrite, FT_EraseEE,
    FT_GetDeviceInfo, FT_GetDeviceInfoList, FT_GetDriverVersion, FT_GetLibraryVersion,
    FT_GetQueueStatus, FT_ListDevices, FT_Open, FT_OpenEx, FT_Purge, FT_Read, FT_ReadEE,
    FT_ResetDevice, FT_SetBitMode, FT_SetChars, FT_SetFlowControl, FT_SetLatencyTimer,
    FT_SetTimeouts, FT_SetUSBParameters, FT_Write, FT_WriteEE, FT_DEVICE_LIST_INFO_NODE,
    FT_FLOW_DTR_DSR, FT_FLOW_NONE, FT_FLOW_RTS_CTS, FT_FLOW_XON_XOFF, FT_HANDLE,
    FT_LIST_NUMBER_ONLY, FT_OPEN_BY_SERIAL_NUMBER, FT_PURGE_RX, FT_PURGE_TX, FT_STATUS,
};

use std::convert::TryFrom;
use std::ffi::c_void;
use std::mem;
use std::ptr;
use std::time::Duration;
use std::vec::Vec;

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
    let dummy = std::ptr::null_mut();
    let status: FT_STATUS = unsafe {
        FT_ListDevices(
            &mut num_devs as *mut u32 as *mut c_void,
            dummy,
            FT_LIST_NUMBER_ONLY,
        )
    };

    ft_result!(num_devs, status)
}

/// Returns the version of the underlying C library.
///
/// **Note**: The documentation says this function is only supported on Windows
/// but it seems work correctly on Linux.
///
/// # Example
///
/// ```no_run
/// use libftd2xx::library_version;
///
/// let version = library_version()?;
/// println!("libftd2xx C library version: {}", version);
/// # Ok::<(), libftd2xx::Ftd2xxError>(())
/// ```
pub fn library_version() -> Result<Version, Ftd2xxError> {
    let mut version: u32 = 0;
    let status: FT_STATUS = unsafe { FT_GetLibraryVersion(&mut version) };

    ft_result!(Version::with_raw(version), status)
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
///     println!("device: {:?}", device);
/// }
/// # Ok::<(), libftd2xx::Ftd2xxError>(())
/// ```
pub fn list_devices() -> Result<Vec<DeviceInfo>, Ftd2xxError> {
    let mut devices = Vec::new();
    let mut num_devices: u32 = create_device_info_list()?;
    let num_devices_usize: usize = usize::try_from(num_devices).unwrap();
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
            devices.push(DeviceInfo::with_info_node(info_node));
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
        ft_result!(Ftdi { handle }, status)
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
        let cstr_serial_number = std::ffi::CString::new(serial_number).unwrap();
        let status: FT_STATUS = unsafe {
            FT_OpenEx(
                cstr_serial_number.as_ptr() as *mut c_void,
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
    /// println!("Device information: {:?}", info);
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn device_info(&mut self) -> Result<DeviceInfo, Ftd2xxError> {
        let mut dev_type: u32 = 0;
        let mut dev_id: u32 = 0;
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
            DeviceInfo::with_open_device_info(dev_type, dev_id, sn, description),
            status
        )
    }

    /// Returns the D2XX driver version number.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// let version = ft.driver_version()?;
    /// println!("Driver Version: {}", version);
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn driver_version(&mut self) -> Result<Version, Ftd2xxError> {
        let mut version: u32 = 0;
        let status: FT_STATUS = unsafe { FT_GetDriverVersion(self.handle, &mut version) };

        ft_result!(Version::with_raw(version), status)
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
                u8::try_from(event_enable).unwrap(),
                error_char,
                u8::try_from(error_enable).unwrap(),
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
        let status: FT_STATUS = unsafe {
            FT_SetTimeouts(
                self.handle,
                u32::try_from(read_timeout.as_millis()).expect("read_timeout integer overflow"),
                u32::try_from(write_timeout.as_millis()).expect("write_timeout integer overflow"),
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
        let status: FT_STATUS = unsafe { FT_SetLatencyTimer(self.handle, timer.as_millis() as u8) };
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
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_NONE as u16, 0, 0) };

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
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_RTS_CTS as u16, 0, 0) };

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
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_DTR_DSR as u16, 0, 0) };

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
            unsafe { FT_SetFlowControl(self.handle, FT_FLOW_XON_XOFF as u16, xon, xoff) };

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
    /// let rx_bytes = ft.queue_status()?;
    ///
    /// if (rx_bytes > 0) {
    ///     ft.read(&mut buf[0..rx_bytes])?;
    /// }
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn queue_status(&mut self) -> Result<usize, Ftd2xxError> {
        let mut queue_status: u32 = 0;
        let status: FT_STATUS = unsafe { FT_GetQueueStatus(self.handle, &mut queue_status) };

        ft_result!(usize::try_from(queue_status).unwrap(), status)
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
    /// let rx_bytes = ft.queue_status()?;
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
    /// let bytes_read = ft.read(&mut buf)?;
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
    pub fn read(&mut self, buf: &mut [u8]) -> Result<usize, Ftd2xxError> {
        let mut bytes_returned: u32 = 0;
        let len: u32 = u32::try_from(buf.len()).unwrap();
        let status: FT_STATUS = unsafe {
            FT_Read(
                self.handle,
                buf.as_mut_ptr() as *mut c_void,
                len,
                &mut bytes_returned,
            )
        };

        ft_result!(usize::try_from(bytes_returned).unwrap(), status)
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
    /// let num_bytes_written = ft.write(&buf)?;
    /// if num_bytes_written == BUF_SIZE {
    ///     println!("no write timeout")
    /// } else {
    ///     println!("write timeout")
    /// }
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn write(&mut self, buf: &[u8]) -> Result<usize, Ftd2xxError> {
        let mut bytes_written: u32 = 0;
        let len: u32 = u32::try_from(buf.len()).unwrap();
        let status: FT_STATUS = unsafe {
            FT_Write(
                self.handle,
                buf.as_ptr() as *mut c_void,
                len,
                &mut bytes_written,
            )
        };
        ft_result!(usize::try_from(bytes_written).unwrap(), status)
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

    /// Read a value from an EEPROM location.
    ///
    /// # Arguments
    ///
    /// * `offset` - EEPROM location to read from.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// const LOCATION: u32 = 0x0;
    /// let mut ft = Ftdi::new()?;
    /// let value = ft.eeprom_word_read(LOCATION)?;
    /// println!("The value at EEPROM address 0x{:X} is 0x{:04X}", LOCATION, value);
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn eeprom_word_read(&mut self, offset: u32) -> Result<u16, Ftd2xxError> {
        let mut value: u16 = 0;
        let status: FT_STATUS = unsafe { FT_ReadEE(self.handle, offset, &mut value) };
        ft_result!(value, status)
    }

    /// Writes a value to an EEPROM location.
    ///
    /// # Arguments
    ///
    /// * `offset` - EEPROM location to write to.
    /// * `value` - Value to write.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.eeprom_word_write(0x0, 0x1234)?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn eeprom_word_write(&mut self, offset: u32, value: u16) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS = unsafe { FT_WriteEE(self.handle, offset, value) };
        ft_result!((), status)
    }

    /// Erases the entire contents of the EEPROM, including the user area.
    ///
    /// **Note:** The FT232R and FT245R have an internal EEPROM that cannot be
    /// erased.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.eeprom_erase()?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn eeprom_erase(&mut self) -> Result<(), Ftd2xxError> {
        let status: FT_STATUS = unsafe { FT_EraseEE(self.handle) };
        ft_result!((), status)
    }

    /// Get the available size of the EEPROM user area in bytes.
    ///
    /// The user area of an FTDI device EEPROM is the total area of the EEPROM
    /// that is unused by device configuration information and descriptors.
    /// This area is available to the user to store information specific to
    /// their application.
    /// The size of the user area depends on the length of the Manufacturer,
    /// ManufacturerId, Description and SerialNumber strings programmed into the
    /// EEPROM.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// let ua_size = ft.eeprom_user_size()?;
    /// println!("EEPROM user area size: {} Bytes", ua_size);
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    pub fn eeprom_user_size(&mut self) -> Result<usize, Ftd2xxError> {
        let mut value: u32 = 0;
        let status: FT_STATUS = unsafe { FT_EE_UASize(self.handle, &mut value) };
        ft_result!(usize::try_from(value).unwrap(), status)
    }

    /// Read the contents of the EEPROM user area.
    ///
    /// The size of the user area can be determined with [`eeprom_user_size`].
    ///
    /// The function returns the actual number of bytes read into the buffer.
    /// If the buffer is larger than the user size the return value will be less
    /// than the length of the buffer.
    /// The return value should be checked to ensure the expected number of
    /// bytes was read.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// let mut buf: [u8; 9] = [0; 9];
    /// let num_read = ft.eeprom_user_read(&mut buf)?;
    /// assert_eq!(buf.len(), num_read);
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    ///
    /// [`eeprom_user_size`]: #method.eeprom_user_size
    pub fn eeprom_user_read(&mut self, buf: &mut [u8]) -> Result<usize, Ftd2xxError> {
        let mut num_read: u32 = 0;
        let len: u32 = u32::try_from(buf.len()).unwrap();
        let status: FT_STATUS =
            unsafe { FT_EE_UARead(self.handle, buf.as_mut_ptr(), len, &mut num_read) };
        ft_result!(usize::try_from(num_read).unwrap(), status)
    }

    /// Write to the EEPROM user area.
    ///
    /// An error will be returned when the buffer size is larger than the user
    /// area size.
    /// The size of the user area can be determined with [`eeprom_user_size`].
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// let mut ft = Ftdi::new()?;
    /// let data = "Hello, World";
    /// ft.eeprom_user_write(&data.as_bytes())?;
    /// # Ok::<(), libftd2xx::Ftd2xxError>(())
    /// ```
    ///
    /// [`eeprom_user_size`]: #method.eeprom_user_size
    pub fn eeprom_user_write(&mut self, buf: &[u8]) -> Result<(), Ftd2xxError> {
        let len: u32 = u32::try_from(buf.len()).unwrap();
        let status: FT_STATUS = unsafe { FT_EE_UAWrite(self.handle, buf.as_ptr() as *mut u8, len) };
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
