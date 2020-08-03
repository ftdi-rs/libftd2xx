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
//! libftd2xx = "~0.8.2"
//! ```
//!
//! This is a basic example to get your started.
//! Check the source code or documentation for more examples.
//! ```no_run
//! use libftd2xx::{Ftdi, FtdiCommon};
//!
//! let mut ft = Ftdi::new()?;
//! let info = ft.device_info()?;
//! println!("Device information: {:?}", info);
//! # Ok::<(), libftd2xx::FtStatus>(())
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
#![doc(html_root_url = "https://docs.rs/libftd2xx/0.8.2")]
#![deny(missing_docs, warnings)]
#![allow(clippy::redundant_field_names)]

mod errors;
pub use errors::{DeviceTypeError, EepromStringsError, EepromValueError, FtStatus, TimeoutError};

mod mpsse;
pub use mpsse::{FtdiMpsse, MpsseSettings};

mod types;
use types::{vid_pid_from_id, STRING_LEN};
pub use types::{
    BitMode, ByteOrder, Cbus232h, Cbus232r, CbusX, ClockPolarity, DeviceInfo, DeviceType,
    DriveCurrent, DriverType, Eeprom232h, Eeprom4232h, Speed, Version,
};

mod util;
use util::slice_into_string;

use libftd2xx_ffi::{
    FT_Close, FT_CreateDeviceInfoList, FT_EEPROM_Program, FT_EEPROM_Read, FT_EE_UARead,
    FT_EE_UASize, FT_EE_UAWrite, FT_EraseEE, FT_GetDeviceInfo, FT_GetDeviceInfoList,
    FT_GetDriverVersion, FT_GetLatencyTimer, FT_GetLibraryVersion, FT_GetQueueStatus,
    FT_ListDevices, FT_Open, FT_OpenEx, FT_Purge, FT_Read, FT_ReadEE, FT_ResetDevice,
    FT_SetBitMode, FT_SetChars, FT_SetDeadmanTimeout, FT_SetFlowControl, FT_SetLatencyTimer,
    FT_SetTimeouts, FT_SetUSBParameters, FT_Write, FT_WriteEE, FT_DEVICE_LIST_INFO_NODE,
    FT_EEPROM_232H, FT_EEPROM_4232H, FT_FLOW_DTR_DSR, FT_FLOW_NONE, FT_FLOW_RTS_CTS,
    FT_FLOW_XON_XOFF, FT_HANDLE, FT_LIST_NUMBER_ONLY, FT_OPEN_BY_DESCRIPTION,
    FT_OPEN_BY_SERIAL_NUMBER, FT_PURGE_RX, FT_PURGE_TX, FT_STATUS,
};

#[cfg(target_os = "windows")]
use libftd2xx_ffi::FT_GetComPortNumber;

use std::convert::TryFrom;
use std::ffi::c_void;
use std::mem;
use std::time::Duration;
use std::vec::Vec;

macro_rules! ft_result {
    ($value:expr, $status:expr) => {
        if $status != 0 {
            Err($status.into())
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
/// # Ok::<(), libftd2xx::FtStatus>(())
/// ```
pub fn num_devices() -> Result<u32, FtStatus> {
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
/// but it seems to work correctly on Linux.
///
/// # Example
///
/// ```no_run
/// use libftd2xx::library_version;
///
/// let version = library_version()?;
/// println!("libftd2xx C library version: {}", version);
/// # Ok::<(), libftd2xx::FtStatus>(())
/// ```
pub fn library_version() -> Result<Version, FtStatus> {
    let mut version: u32 = 0;
    let status: FT_STATUS = unsafe { FT_GetLibraryVersion(&mut version) };

    ft_result!(Version::with_raw(version), status)
}

fn create_device_info_list() -> Result<u32, FtStatus> {
    let mut num_devices: u32 = 0;
    let status: FT_STATUS = unsafe { FT_CreateDeviceInfoList(&mut num_devices) };
    ft_result!(num_devices, status)
}

/// This function returns a device information vector with information about
/// the D2XX devices connected to the system.
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
/// # Ok::<(), libftd2xx::FtStatus>(())
/// ```
pub fn list_devices() -> Result<Vec<DeviceInfo>, FtStatus> {
    let mut devices: Vec<DeviceInfo> = Vec::new();
    let mut num_devices: u32 = create_device_info_list()?;
    let num_devices_usize: usize = usize::try_from(num_devices).unwrap();
    if num_devices == 0 {
        return Ok(devices);
    }

    let mut list_info_vec: Vec<FT_DEVICE_LIST_INFO_NODE> = Vec::with_capacity(num_devices_usize);

    let status: FT_STATUS = unsafe {
        list_info_vec.set_len(num_devices_usize);
        FT_GetDeviceInfoList(
            list_info_vec.as_mut_ptr() as *mut FT_DEVICE_LIST_INFO_NODE,
            &mut num_devices,
        )
    };

    if status != 0 {
        Err(status.into())
    } else {
        while let Some(info_node) = list_info_vec.pop() {
            let (vid, pid) = vid_pid_from_id(info_node.ID);
            devices.push(DeviceInfo {
                port_open: info_node.Flags & 0x1 == 0x1,
                speed: Some((info_node.Flags & 0x2).into()),
                device_type: info_node.Type.into(),
                product_id: pid,
                vendor_id: vid,
                serial_number: slice_into_string(&info_node.SerialNumber),
                description: slice_into_string(&info_node.Description),
            });
        }
        Ok(devices)
    }
}

/// Generic FTDI device.
///
/// This structure can be used for all FTDI devices.
/// A device-specific structure is only necessary to access the EEPROM traits
/// for that device.
pub struct Ftdi {
    handle: FT_HANDLE,
}

/// FT232H device.
///
/// # Example
///
/// Converting from an unknown FTDI device.
///
/// ```no_run
/// use std::convert::TryFrom;
/// use libftd2xx::{Ftdi, Ft232h};
///
/// let mut ftdi = Ftdi::new()?;
/// let ft232h: Ft232h = Ft232h::try_from(&mut ftdi)?;
/// # Ok::<(), libftd2xx::DeviceTypeError>(())
/// ```
pub struct Ft232h {
    handle: FT_HANDLE,
}

/// FT4232H device.
///
/// # Example
///
/// Converting from an unknown FTDI device.
///
/// ```no_run
/// use std::convert::TryFrom;
/// use libftd2xx::{Ftdi, Ft4232h};
///
/// let mut ftdi = Ftdi::new()?;
/// let ft4232h: Ft4232h = Ft4232h::try_from(&mut ftdi)?;
/// # Ok::<(), libftd2xx::DeviceTypeError>(())
/// ```
pub struct Ft4232h {
    handle: FT_HANDLE,
}

/// FTD2XX functions common to all devices.
pub trait FtdiCommon {
    /// FTDI device type.
    const DEVICE_TYPE: DeviceType;

    /// Get the FTDI device handle.
    fn handle(&mut self) -> FT_HANDLE;

    /// Get device information for an open device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// let info = ft.device_info()?;
    /// println!("Device information: {:?}", info);
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn device_info(&mut self) -> Result<DeviceInfo, FtStatus> {
        let mut device_type: u32 = 0;
        let mut device_id: u32 = 0;
        let mut serial_number: [i8; STRING_LEN] = [0; STRING_LEN];
        let mut description: [i8; STRING_LEN] = [0; STRING_LEN];
        let status: FT_STATUS = unsafe {
            FT_GetDeviceInfo(
                self.handle(),
                &mut device_type,
                &mut device_id,
                serial_number.as_mut_ptr(),
                description.as_mut_ptr(),
                std::ptr::null_mut(),
            )
        };
        let (vid, pid) = vid_pid_from_id(device_id);
        ft_result!(
            DeviceInfo {
                port_open: true,
                speed: None,
                device_type: device_type.into(),
                product_id: pid,
                vendor_id: vid,
                serial_number: slice_into_string(&serial_number),
                description: slice_into_string(&description),
            },
            status
        )
    }

    /// Returns the D2XX driver version number.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// let version = ft.driver_version()?;
    /// println!("Driver Version: {}", version);
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn driver_version(&mut self) -> Result<Version, FtStatus> {
        let mut version: u32 = 0;
        let status: FT_STATUS = unsafe { FT_GetDriverVersion(self.handle(), &mut version) };

        ft_result!(Version::with_raw(version), status)
    }

    /// This function sends a reset command to the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.reset()?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn reset(&mut self) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe { FT_ResetDevice(self.handle()) };
        ft_result!((), status)
    }

    /// Set the USB request transfer size.
    ///
    /// This function can be used to change the transfer sizes from the default
    /// transfer size of 4096 bytes to better suit the application requirements.
    ///
    /// Transfer sizes must be set to a multiple of 64 bytes between 64 bytes
    /// and 64k bytes.  Other values will result in panic.
    ///
    /// When [`set_usb_parameters`] is called, the change comes into effect
    /// immediately and any data that was held in the driver at the time of the
    /// change is lost.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_usb_parameters(16384)?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    ///
    /// [`set_usb_parameters`]: #method.set_usb_parameters
    fn set_usb_parameters(&mut self, in_transfer_size: u32) -> Result<(), FtStatus> {
        const MAX: u32 = 64 * 1024;
        const MIN: u32 = 64;
        assert!(
            in_transfer_size <= MAX,
            "in_transfer_size of {} exceeds maximum of {}",
            in_transfer_size,
            MAX
        );
        assert!(
            in_transfer_size >= MIN,
            "in_transfer_size of {} exceeds minimum of {}",
            in_transfer_size,
            MIN
        );
        assert!(
            in_transfer_size % MIN == 0,
            "in_transfer_size of {} not a multiple of {}",
            in_transfer_size,
            MIN
        );
        let status: FT_STATUS =
            unsafe { FT_SetUSBParameters(self.handle(), in_transfer_size, in_transfer_size) };
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
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    ///
    /// // disable all special characters
    /// ft.set_chars(0, false, 0, false)?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn set_chars(
        &mut self,
        event_char: u8,
        event_enable: bool,
        error_char: u8,
        error_enable: bool,
    ) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe {
            FT_SetChars(
                self.handle(),
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
    /// The timeout values are limited to 4,294,967,295 (`std::u32::MAX`)
    /// milliseconds.
    ///
    /// The timeout values have a 1 millisecond resolution.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    /// use std::time::Duration;
    ///
    /// let mut ft = Ftdi::new()?;
    ///
    /// // Set read timeout of 5sec, write timeout of 1sec
    /// ft.set_timeouts(Duration::from_millis(5000), Duration::from_millis(1000))?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn set_timeouts(
        &mut self,
        read_timeout: Duration,
        write_timeout: Duration,
    ) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe {
            FT_SetTimeouts(
                self.handle(),
                u32::try_from(read_timeout.as_millis()).expect("read_timeout integer overflow"),
                u32::try_from(write_timeout.as_millis()).expect("write_timeout integer overflow"),
            )
        };
        ft_result!((), status)
    }

    /// This method allows the maximum time in milliseconds that a USB request
    /// can remain outstandingto be set.
    ///
    /// The deadman timeout is referred to in FTDI application note
    /// [AN232B-10 Advanced Driver Options] as the USB timeout.
    /// It is unlikely that this method will be required by most users.
    ///
    /// The default duration is 5 seconds.
    ///
    /// The timeout value is limited to 4,294,967,295 (`std::u32::MAX`)
    /// milliseconds.
    ///
    /// The timeout value has a 1 millisecond resolution.
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    /// use std::time::Duration;
    ///
    /// let mut ft = Ftdi::new()?;
    ///
    /// // set deadman timeout to 5 seconds
    /// ft.set_deadman_timeout(Duration::from_secs(5))?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    ///
    /// [AN232B-10 Advanced Driver Options]: https://www.ftdichip.com/Support/Documents/AppNotes/AN_107_AdvancedDriverOptions_AN_000073.pdf
    fn set_deadman_timeout(&mut self, timeout: Duration) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe {
            FT_SetDeadmanTimeout(
                self.handle(),
                u32::try_from(timeout.as_millis()).expect("timeout integer overflow"),
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
    /// The resolution for the latency timer is 1 millisecond.
    ///
    /// **Note** the python FTDI library, [pyftdi] reports that values lower
    /// than 16 ms may result in data loss.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    /// use std::time::Duration;
    ///
    /// let mut ft = Ftdi::new()?;
    ///
    /// // Set latency timer to 16 milliseconds
    /// ft.set_latency_timer(Duration::from_millis(16))?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    ///
    /// [pyftdi]: https://github.com/eblot/pyftdi/tree/master
    fn set_latency_timer(&mut self, timer: Duration) -> Result<(), FtStatus> {
        let millis = timer.as_millis();
        debug_assert!(millis >= 2, "duration must be >= 2ms, got {:?}", timer);
        debug_assert!(millis <= 255, "duration must be <= 255ms, got {:?}", timer);
        let millis = u8::try_from(millis).unwrap();
        let status: FT_STATUS = unsafe { FT_SetLatencyTimer(self.handle(), millis) };
        ft_result!((), status)
    }

    /// Get the current value of the latency timer.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    /// use std::time::Duration;
    ///
    /// let mut ft = Ftdi::new()?;
    /// let timer = Duration::from_millis(32);
    /// ft.set_latency_timer(timer)?;
    /// assert_eq!(ft.latency_timer()?, timer);
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn latency_timer(&mut self) -> Result<Duration, FtStatus> {
        let mut timer: u8 = 0;
        let status: FT_STATUS = unsafe { FT_GetLatencyTimer(self.handle(), &mut timer as *mut u8) };
        ft_result!(Duration::from_millis(timer as u64), status)
    }

    /// This function disables flow control for the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_flow_control_none()?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn set_flow_control_none(&mut self) -> Result<(), FtStatus> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle(), FT_FLOW_NONE as u16, 0, 0) };

        ft_result!((), status)
    }

    /// This function sets RTS/CTS flow control for the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_flow_control_rts_cts()?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn set_flow_control_rts_cts(&mut self) -> Result<(), FtStatus> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle(), FT_FLOW_RTS_CTS as u16, 0, 0) };

        ft_result!((), status)
    }

    /// This function sets DTS/DSR flow control for the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_flow_control_dtr_dsr()?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn set_flow_control_dtr_dsr(&mut self) -> Result<(), FtStatus> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle(), FT_FLOW_DTR_DSR as u16, 0, 0) };

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
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_flow_control_xon_xoff(0x11, 0x13)?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn set_flow_control_xon_xoff(&mut self, xon: u8, xoff: u8) -> Result<(), FtStatus> {
        let status: FT_STATUS =
            unsafe { FT_SetFlowControl(self.handle(), FT_FLOW_XON_XOFF as u16, xon, xoff) };

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
    /// use libftd2xx::{Ftdi, BitMode, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.set_bit_mode(0xFF, BitMode::AsyncBitbang)?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn set_bit_mode(&mut self, mask: u8, mode: BitMode) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe { FT_SetBitMode(self.handle(), mask, mode as u8) };

        ft_result!((), status)
    }

    /// Gets the number of bytes in the receive queue.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut buf: [u8; 4096] = [0; 4096];
    /// let mut ft = Ftdi::new()?;
    /// let rx_bytes = ft.queue_status()?;
    ///
    /// if (rx_bytes > 0) {
    ///     ft.read(&mut buf[0..rx_bytes])?;
    /// }
    /// # Ok::<(), libftd2xx::TimeoutError>(())
    /// ```
    fn queue_status(&mut self) -> Result<usize, FtStatus> {
        let mut queue_status: u32 = 0;
        let status: FT_STATUS = unsafe { FT_GetQueueStatus(self.handle(), &mut queue_status) };

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
    /// and returns [`TimeoutError`] error.
    ///
    /// # Examples
    ///
    /// ## Read all available data
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut buf: [u8; 4096] = [0; 4096];
    /// let mut ft = Ftdi::new()?;
    /// let rx_bytes = ft.queue_status()?;
    ///
    /// if rx_bytes > 0 {
    ///     ft.read(&mut buf[0..rx_bytes])?;
    /// }
    /// # Ok::<(), libftd2xx::TimeoutError>(())
    /// ```
    ///
    /// ## Read with a timeout of 5 seconds
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon, TimeoutError};
    /// use std::time::Duration;
    ///
    /// const BUF_LEN: usize = 4096;
    /// let mut buf: [u8; BUF_LEN] = [0; BUF_LEN];
    /// let mut ft = Ftdi::new()?;
    ///
    /// ft.set_timeouts(Duration::from_millis(5000), Duration::from_millis(0))?;
    ///
    /// let valid_data = match ft.read(&mut buf) {
    ///     Err(e) => match e {
    ///         TimeoutError::Timeout{actual: actual, expected: expected} => {
    ///             eprintln!("Read timeout occured after 5s! {:?}", e);
    ///             &buf[0..actual]
    ///         }
    ///         TimeoutError::FtStatus(status) => {
    ///             panic!("FTDI Status Error: {:?}", status);
    ///         },
    ///     },
    ///     _ => &buf[0..buf.len()],
    /// };
    /// # Ok::<(), libftd2xx::TimeoutError>(())
    /// ```
    ///
    /// [`read`]: #method.read
    /// [`queue_status`]: #method.queue_status
    /// [`set_timeouts`]: #method.set_timeouts
    /// [`TimeoutError`]: ./enum.TimeoutError.html
    fn read(&mut self, buf: &mut [u8]) -> Result<(), TimeoutError> {
        let mut bytes_returned: u32 = 0;
        let len: u32 = u32::try_from(buf.len()).unwrap();
        let status: FT_STATUS = unsafe {
            FT_Read(
                self.handle(),
                buf.as_mut_ptr() as *mut c_void,
                len,
                &mut bytes_returned,
            )
        };

        if status != 0 {
            return Err(TimeoutError::FtStatus(status.into()));
        }

        let num_read = usize::try_from(bytes_returned).unwrap();
        if num_read != buf.len() {
            Err(TimeoutError::Timeout {
                expected: buf.len(),
                actual: num_read,
            })
        } else {
            Ok(())
        }
    }

    /// Write data to the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// const BUF_SIZE: usize = 256;
    /// let buf: [u8; BUF_SIZE] = [0; BUF_SIZE];
    /// let mut ft = Ftdi::new()?;
    /// ft.write(&buf)?;
    /// # Ok::<(), libftd2xx::TimeoutError>(())
    /// ```
    fn write(&mut self, buf: &[u8]) -> Result<(), TimeoutError> {
        let mut bytes_written: u32 = 0;
        let len: u32 = u32::try_from(buf.len()).unwrap();
        let status: FT_STATUS = unsafe {
            FT_Write(
                self.handle(),
                buf.as_ptr() as *mut c_void,
                len,
                &mut bytes_written,
            )
        };
        if status != 0 {
            return Err(TimeoutError::FtStatus(status.into()));
        }

        let num_written = usize::try_from(bytes_written).unwrap();
        if num_written != buf.len() {
            Err(TimeoutError::Timeout {
                expected: buf.len(),
                actual: num_written,
            })
        } else {
            Ok(())
        }
    }

    /// This function purges the transmit buffers in the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.purge_tx()?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn purge_tx(&mut self) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe { FT_Purge(self.handle(), FT_PURGE_TX) };
        ft_result!((), status)
    }

    /// This function purges the receive buffers in the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.purge_rx()?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn purge_rx(&mut self) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe { FT_Purge(self.handle(), FT_PURGE_RX) };
        ft_result!((), status)
    }

    /// This function purges the transmit and receive buffers in the device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.purge_all()?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn purge_all(&mut self) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe { FT_Purge(self.handle(), FT_PURGE_TX | FT_PURGE_RX) };
        ft_result!((), status)
    }

    /// Close an open device.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.close()?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn close(&mut self) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe { FT_Close(self.handle()) };
        ft_result!((), status)
    }

    /// Get the COM port associated with a device.
    ///
    /// This method is only avaliable when using the Windows CDM driver as both
    /// the D2XX and VCP drivers can be installed at the same time.
    ///
    /// If no COM port is associated with the device `None` is returned.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// match ft.com_port_number()? {
    ///     Some(num) => println!("COM{}", num),
    ///     None => println!("no COM port"),
    /// }
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    #[cfg(target_os = "windows")]
    fn com_port_number(&mut self) -> Result<Option<u32>, FtStatus> {
        let mut num: i32 = -1;
        let status: FT_STATUS = unsafe { FT_GetComPortNumber(self.handle(), &mut num as *mut i32) };
        ft_result!(
            if num == -1 {
                None
            } else {
                Some(u32::try_from(num).unwrap())
            },
            status
        )
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
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// const LOCATION: u32 = 0x0;
    /// let mut ft = Ftdi::new()?;
    /// let value = ft.eeprom_word_read(LOCATION)?;
    /// println!("The value at EEPROM address 0x{:X} is 0x{:04X}", LOCATION, value);
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn eeprom_word_read(&mut self, offset: u32) -> Result<u16, FtStatus> {
        let mut value: u16 = 0;
        let status: FT_STATUS = unsafe { FT_ReadEE(self.handle(), offset, &mut value) };
        ft_result!(value, status)
    }

    /// Writes a value to an EEPROM location.
    ///
    /// # Arguments
    ///
    /// * `offset` - EEPROM location to write to.
    /// * `value` - Value to write.
    ///
    /// # Warning
    ///
    /// Writing bad values to the EEPROM can brick your device.
    /// Please take a moment to read the license for this crate before using
    /// this function.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.eeprom_word_write(0x0, 0x1234)?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn eeprom_word_write(&mut self, offset: u32, value: u16) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe { FT_WriteEE(self.handle(), offset, value) };
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
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// ft.eeprom_erase()?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn eeprom_erase(&mut self) -> Result<(), FtStatus> {
        let status: FT_STATUS = unsafe { FT_EraseEE(self.handle()) };
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
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// let ua_size = ft.eeprom_user_size()?;
    /// println!("EEPROM user area size: {} Bytes", ua_size);
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    fn eeprom_user_size(&mut self) -> Result<usize, FtStatus> {
        let mut value: u32 = 0;
        let status: FT_STATUS = unsafe { FT_EE_UASize(self.handle(), &mut value) };
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
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// let mut buf: [u8; 9] = [0; 9];
    /// let num_read = ft.eeprom_user_read(&mut buf)?;
    /// assert_eq!(buf.len(), num_read);
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    ///
    /// [`eeprom_user_size`]: #method.eeprom_user_size
    fn eeprom_user_read(&mut self, buf: &mut [u8]) -> Result<usize, FtStatus> {
        let mut num_read: u32 = 0;
        let len: u32 = u32::try_from(buf.len()).unwrap();
        let status: FT_STATUS =
            unsafe { FT_EE_UARead(self.handle(), buf.as_mut_ptr(), len, &mut num_read) };
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
    /// use libftd2xx::{Ftdi, FtdiCommon};
    ///
    /// let mut ft = Ftdi::new()?;
    /// let data = "Hello, World";
    /// ft.eeprom_user_write(&data.as_bytes())?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    ///
    /// [`eeprom_user_size`]: #method.eeprom_user_size
    fn eeprom_user_write(&mut self, buf: &[u8]) -> Result<(), FtStatus> {
        let len: u32 = u32::try_from(buf.len()).unwrap();
        let status: FT_STATUS =
            unsafe { FT_EE_UAWrite(self.handle(), buf.as_ptr() as *mut u8, len) };
        ft_result!((), status)
    }
}

/// FTDI device-specific EEPROM trait.
pub trait FtdiEeprom: FtdiCommon {
    /// EEPROM data structure for the specific device.
    type Eeprom;

    /// Read from the FTD2XX device EEPROM.
    ///
    /// # Example
    ///
    /// This example uses the FT232H.
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiEeprom, Ft4232h};
    /// use std::convert::TryFrom;
    ///
    /// let mut ftdi = Ftdi::new()?;
    /// let mut ft = Ft4232h::try_from(&mut ftdi)?;
    /// let eeprom = ft.eeprom_read()?;
    /// println!("FT4232H EEPROM contents: {:?}", eeprom);
    /// # Ok::<(), libftd2xx::DeviceTypeError>(())
    /// ```
    fn eeprom_read(&mut self) -> Result<Self::Eeprom, FtStatus>;

    /// Program the FTD2XX EEPROM.
    ///
    /// # Warning
    ///
    /// Writing bad values to the EEPROM can brick your device.
    /// Please take a moment to read the license for this crate before using
    /// this function.
    ///
    /// # Example
    ///
    /// This example uses the FT232H.
    ///
    /// ```no_run
    /// use libftd2xx::{Ftdi, FtdiEeprom, Ft4232h};
    /// use std::convert::TryFrom;
    ///
    /// let mut ftdi = Ftdi::with_serial_number("FTaaa")?;
    /// let mut ft = Ft4232h::try_from(&mut ftdi)?;
    /// let mut eeprom = ft.eeprom_read()?;
    ///
    /// let CURRENT: u16 = 150;
    /// println!("Setting maximum current to {} mA", CURRENT);
    /// eeprom.set_max_current(CURRENT);
    /// ft.eeprom_program(&eeprom)?;
    /// # Ok::<(), libftd2xx::DeviceTypeError>(())
    /// ```
    fn eeprom_program(&mut self, eeprom: &Self::Eeprom) -> Result<(), FtStatus>;
}

macro_rules! impl_eeprom_for {
    ($NAME:ident, $EEPROM:ident, $RAW:ident) => {
        impl FtdiEeprom for $NAME {
            type Eeprom = $EEPROM;

            fn eeprom_read(&mut self) -> Result<Self::Eeprom, FtStatus> {
                let mut manufacturer: [i8; STRING_LEN] = [0; STRING_LEN];
                let mut manufacturer_id: [i8; STRING_LEN] = [0; STRING_LEN];
                let mut description: [i8; STRING_LEN] = [0; STRING_LEN];
                let mut serial_number: [i8; STRING_LEN] = [0; STRING_LEN];

                let mut eeprom_data: $RAW =
                    unsafe { std::mem::MaybeUninit::uninit().assume_init() };
                eeprom_data.common.deviceType = Self::DEVICE_TYPE as u32;
                let eeprom_data_size = mem::size_of::<$RAW>();

                let status: FT_STATUS = unsafe {
                    FT_EEPROM_Read(
                        self.handle(),
                        &mut eeprom_data as *mut $RAW as *mut c_void,
                        u32::try_from(eeprom_data_size).unwrap(),
                        manufacturer.as_mut_ptr(),
                        manufacturer_id.as_mut_ptr(),
                        description.as_mut_ptr(),
                        serial_number.as_mut_ptr(),
                    )
                };

                let eeprom = Self::Eeprom::new(
                    eeprom_data,
                    slice_into_string(&manufacturer),
                    slice_into_string(&manufacturer_id),
                    slice_into_string(&description),
                    slice_into_string(&serial_number),
                );

                ft_result!(eeprom, status)
            }

            fn eeprom_program(&mut self, eeprom: &Self::Eeprom) -> Result<(), FtStatus> {
                let manufacturer = std::ffi::CString::new(eeprom.manufacturer()).unwrap();
                let manufacturer_id = std::ffi::CString::new(eeprom.manufacturer_id()).unwrap();
                let description = std::ffi::CString::new(eeprom.description()).unwrap();
                let serial_number = std::ffi::CString::new(eeprom.serial_number()).unwrap();
                let eeprom_data_size = mem::size_of::<$RAW>();

                let status: FT_STATUS = unsafe {
                    FT_EEPROM_Program(
                        self.handle(),
                        &mut eeprom.into() as *mut $RAW as *mut c_void,
                        u32::try_from(eeprom_data_size).unwrap(),
                        manufacturer.as_ptr() as *mut i8,
                        manufacturer_id.as_ptr() as *mut i8,
                        description.as_ptr() as *mut i8,
                        serial_number.as_ptr() as *mut i8,
                    )
                };

                ft_result!((), status)
            }
        }
    };
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
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    ///
    /// [`with_index`]: #method.with_index
    /// [`with_serial_number`]: #method.with_serial_number
    pub fn new() -> Result<Ftdi, FtStatus> {
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
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    ///
    /// [`with_serial_number`]: #method.with_serial_number
    pub fn with_index(index: i32) -> Result<Ftdi, FtStatus> {
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
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    pub fn with_serial_number(serial_number: &str) -> Result<Ftdi, FtStatus> {
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

    /// Open the device by its device description.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ftdi;
    ///
    /// Ftdi::with_description("Hello")?;
    /// # Ok::<(), libftd2xx::FtStatus>(())
    /// ```
    pub fn with_description(description: &str) -> Result<Ftdi, FtStatus> {
        let mut handle: FT_HANDLE = std::ptr::null_mut();
        let cstr_description = std::ffi::CString::new(description).unwrap();
        let status: FT_STATUS = unsafe {
            FT_OpenEx(
                cstr_description.as_ptr() as *mut c_void,
                FT_OPEN_BY_DESCRIPTION,
                &mut handle,
            )
        };

        ft_result!(Ftdi { handle: handle }, status)
    }
}

impl Ft232h {
    /// Open a `Ft232h` device and initialize the handle.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ft232h;
    ///
    /// Ft232h::with_serial_number("FT59UO4C")?;
    /// # Ok::<(), libftd2xx::DeviceTypeError>(())
    /// ```
    pub fn with_serial_number(serial_number: &str) -> Result<Ft232h, DeviceTypeError> {
        let mut unknown = Ftdi::with_serial_number(serial_number)?;
        Ft232h::try_from(&mut unknown)
    }

    /// Open a `Ft232h` device by its device description.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ft232h;
    ///
    /// Ft232h::with_description("Hello")?;
    /// # Ok::<(), libftd2xx::DeviceTypeError>(())
    /// ```
    pub fn with_description(serial_number: &str) -> Result<Ft232h, DeviceTypeError> {
        let mut unknown = Ftdi::with_description(serial_number)?;
        Ft232h::try_from(&mut unknown)
    }
}

impl Ft4232h {
    /// Open a `Ft4232h` device and initialize the handle.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ft4232h;
    ///
    /// Ft4232h::with_serial_number("FT4PWSEOA")?;
    /// # Ok::<(), libftd2xx::DeviceTypeError>(())
    /// ```
    pub fn with_serial_number(serial_number: &str) -> Result<Ft4232h, DeviceTypeError> {
        let mut unknown = Ftdi::with_serial_number(serial_number)?;
        Ft4232h::try_from(&mut unknown)
    }

    /// Open a `Ft4232h` device by its device description.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libftd2xx::Ft4232h;
    ///
    /// Ft4232h::with_description("FT4232H-56Q MiniModule A")?;
    /// # Ok::<(), libftd2xx::DeviceTypeError>(())
    /// ```
    pub fn with_description(serial_number: &str) -> Result<Ft4232h, DeviceTypeError> {
        let mut unknown = Ftdi::with_description(serial_number)?;
        Ft4232h::try_from(&mut unknown)
    }
}

macro_rules! impl_boilerplate_for {
    ($DEVICE:ident, $TYPE:expr) => {
        impl FtdiCommon for $DEVICE {
            const DEVICE_TYPE: DeviceType = $TYPE;

            fn handle(&mut self) -> FT_HANDLE {
                self.handle
            }
        }
    };
}

macro_rules! impl_try_from_for {
    ($DEVICE:ident) => {
        impl TryFrom<&mut Ftdi> for $DEVICE {
            type Error = DeviceTypeError;

            fn try_from(ft: &mut Ftdi) -> Result<Self, Self::Error> {
                let device_type: DeviceType = ft.device_info()?.device_type;
                if device_type != Self::DEVICE_TYPE {
                    Err(DeviceTypeError::DeviceType {
                        expected: $DEVICE::DEVICE_TYPE,
                        detected: device_type,
                    })
                } else {
                    Ok($DEVICE {
                        handle: ft.handle(),
                    })
                }
            }
        }
    };
}

impl_boilerplate_for!(Ftdi, DeviceType::Unknown);
impl_boilerplate_for!(Ft232h, DeviceType::FT232H);
impl_boilerplate_for!(Ft4232h, DeviceType::FT4232H);

impl_try_from_for!(Ft232h);
impl_try_from_for!(Ft4232h);

impl_eeprom_for!(Ft232h, Eeprom232h, FT_EEPROM_232H);
impl_eeprom_for!(Ft4232h, Eeprom4232h, FT_EEPROM_4232H);

impl FtdiMpsse for Ft232h {}
impl FtdiMpsse for Ft4232h {}
