#![deny(missing_docs, warnings)]

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
use libftd2xx_ffi::{FT_EEPROM_232H, FT_EEPROM_4232H};

use super::{EepromStringsError, EepromValueError};
use std::{convert::TryFrom, fmt};

/// Maximum length of common FTDI strings.
pub const STRING_LEN: usize = 64;

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

/// USB device speed.
///
/// This is used in the [`DeviceInfo`] struct.
///
/// [`DeviceInfo`]: ./struct.DeviceInfo.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
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

/// FTDI device information.
///
/// This is returned by [`list_devices`] and [`device_info`].
///
/// [`list_devices`]: ./fn.list_devices.html
/// [`device_info`]: ./struct.Ftdi.html#method.device_info
#[derive(Clone, Eq, PartialEq, Default)]
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

/// EEPROM structure for the FT232H.
///
/// This is used by the [`eeprom_read`] and [`eeprom_program`] methods.
///
/// [`eeprom_read`]: ./trait.FtdiEeprom.html#tymethod.eeprom_read
/// [`eeprom_program`]: ./trait.FtdiEeprom.html#tymethod.eeprom_program
#[derive(Debug, Clone)]
pub struct Eeprom232h {
    eeprom: FT_EEPROM_232H,
    manufacturer: String,
    manufacturer_id: String,
    description: String,
    serial_number: String,
}

#[allow(clippy::wrong_self_convention)]
impl Eeprom232h {
    /// FT1248 clock polarity.
    pub fn ft1248_cpol(&self) -> ClockPolarity {
        self.eeprom.FT1248Cpol.into()
    }

    /// Set FT1248 clock polarity.
    pub fn set_ft1248_cpol(&mut self, value: ClockPolarity) {
        self.eeprom.FT1248Cpol = value as u8
    }

    /// FT1248 byte order.
    pub fn ft1248_byteorder(&self) -> ByteOrder {
        self.eeprom.FT1248Lsb.into()
    }

    /// Set FT1248 byte order.
    pub fn set_ft1248_byteorder(&mut self, value: ByteOrder) {
        self.eeprom.FT1248Lsb = value as u8
    }

    /// FT1248 flow control enable.
    pub fn ft1248_flow_control(&self) -> bool {
        self.eeprom.FT1248FlowControl != 0
    }

    /// Set FT1248 flow control enable.
    pub fn set_ft1248_flow_control(&mut self, value: bool) {
        self.eeprom.FT1248FlowControl = if value { 1 } else { 0 }
    }

    /// FT245 FIFO interface mode.
    pub fn is_fifo(&self) -> bool {
        self.eeprom.IsFifo != 0
    }

    /// Set FT245 FIFO interface mode.
    pub fn set_is_fifo(&mut self, value: bool) {
        self.eeprom.IsFifo = if value { 1 } else { 0 }
    }

    /// FT245 FIFO CPU target mode.
    pub fn is_fifo_target(&self) -> bool {
        self.eeprom.IsFifoTar != 0
    }

    /// Set FT245 FIFO CPU target mode.
    pub fn set_is_fifo_target(&mut self, value: bool) {
        self.eeprom.IsFifoTar = if value { 1 } else { 0 }
    }

    /// Fast serial interface mode.
    pub fn is_fast_serial(&self) -> bool {
        self.eeprom.IsFastSer != 0
    }

    /// Set Fast serial interface mode.
    pub fn set_is_fast_serial(&mut self, value: bool) {
        self.eeprom.IsFastSer = if value { 1 } else { 0 }
    }

    /// FT1248 interface mode.
    pub fn is_ft1248(&self) -> bool {
        self.eeprom.IsFT1248 != 0
    }

    /// Set FT1248 interface mode.
    pub fn set_is_ft1248(&mut self, value: bool) {
        self.eeprom.IsFT1248 = if value { 1 } else { 0 }
    }

    /// Power save enable.
    ///
    /// Use a pin to save power for self-powered designs.
    pub fn power_save_enable(&self) -> bool {
        self.eeprom.PowerSaveEnable != 0
    }

    /// Set power save enable.
    pub fn set_power_save_enable(&mut self, value: bool) {
        self.eeprom.PowerSaveEnable = if value { 1 } else { 0 }
    }
}

/// EEPROM structure for the FT4232H.
///
/// This is used by the [`eeprom_read`] and [`eeprom_program`] methods.
///
/// [`eeprom_read`]: ./trait.FtdiEeprom.html#tymethod.eeprom_read
/// [`eeprom_program`]: ./trait.FtdiEeprom.html#tymethod.eeprom_program
#[derive(Debug, Clone)]
pub struct Eeprom4232h {
    eeprom: FT_EEPROM_4232H,
    manufacturer: String,
    manufacturer_id: String,
    description: String,
    serial_number: String,
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
                        self.eeprom.[<$FIELD:upper SlowSlew>] != 0
                    }

                    #[doc = "Set slow slew for bus " $FIELD "."]
                    pub fn [<set_ $FIELD:lower _slow_slew>](&mut self, value: bool) {
                        self.eeprom.[<$FIELD:upper SlowSlew>] = if value { 1 } else { 0 }
                    }

                    #[doc = "Schmitt input for bus " $FIELD "."]
                    ///
                    /// `true` if the pins on this bus are Schmitt input.
                    pub fn [<$FIELD:lower _schmitt_input>](&self) -> bool {
                        self.eeprom.[<$FIELD:upper SchmittInput>] != 0
                    }

                    #[doc = "Set Schmitt input for bus " $FIELD "."]
                    pub fn [<set_ $FIELD:lower _schmitt_input>](&mut self, value: bool) {
                        self.eeprom.[<$FIELD:upper SchmittInput>] = if value { 1 } else { 0 }
                    }

                    #[doc = "Drive current for bus " $FIELD "."]
                    ///
                    /// This is the drive current for the pins on this bus.
                    pub fn [<$FIELD:lower _drive_current>](&self) -> Result<DriveCurrent, EepromValueError> {
                        DriveCurrent::try_from(self.eeprom.[<$FIELD:upper DriveCurrent>])
                    }

                    #[doc = "Drive current unchecked for bus " $FIELD "."]
                    ///
                    /// Valid values are 4mA, 8mA, 12mA, or 16mA,
                    /// represented by 4u8, 8u8, 12u8, or 16u8 respectively.
                    ///
                    /// This is the **unchecked** raw value retrived from the EEPROM and it may
                    /// not be a valid value.
                    pub fn [<$FIELD:lower _drive_current_unchecked>](&self) -> u8 {
                        self.eeprom.[<$FIELD:upper SchmittInput>]
                    }

                    #[doc = "Set drive current for bus " $FIELD "."]
                    pub fn [<set_ $FIELD:lower _drive_current>](&mut self, value: DriveCurrent) {
                        self.eeprom.[<$FIELD:upper SchmittInput>] = value as u8
                    }
                }
            )*
        }
    };
}

macro_rules! set_string {
    ($SELF:ident, $NAME:ident, $VALUE:expr, $($OTHER:ident,)+) => {
        if $VALUE.len() > EepromStringsError::MAX_LEN
            || $($SELF.$OTHER.len() + )* 0 + $VALUE.len() > EepromStringsError::MAX_TOTAL_LEN {
            Err(EepromStringsError {
                $NAME: $VALUE.len(),
                $(
                    $OTHER: $SELF.$OTHER.len(),
                )*
            })
        } else {
            $SELF.$NAME = $VALUE;
            Ok(())
        }
    };
}

macro_rules! impl_driver_type {
    ($NAME:ident) => {
        impl $NAME {
            /// Get the device driver type.
            pub fn driver_type(&self) -> Result<DriverType, EepromValueError> {
                DriverType::try_from(self.eeprom.DriverType)
            }

            /// Get the unchecked device driver type.
            ///
            /// This is the **unchecked** raw value retrieved from the
            /// EEPROM and it may not be a valid value.
            pub fn driver_type_unchecked(&self) -> u8 {
                self.eeprom.DriverType
            }

            /// Set the device driver type.
            pub fn set_driver_type(&mut self, value: DriverType) {
                self.eeprom.DriverType = value as u8
            }
        }
    };

    ($NAME:ident, $($FIELD:ident),+) => {
        impl $NAME {
            paste::item! {
                $(
                    #[doc = "Get the driver type for port " $FIELD "."]
                    pub fn [<$FIELD:lower _driver_type>](&self) -> Result<DriverType, EepromValueError> {
                        DriverType::try_from(self.eeprom.[<$FIELD:upper DriverType>])
                    }

                    #[doc = "Get the unchecked driver type for port " $FIELD "."]
                    ///
                    /// This is the **unchecked** raw value retrieved from the
                    /// EEPROM and it may not be a valid value.
                    pub fn [<$FIELD:lower _driver_typ_uncheckede>](&self) -> u8 {
                        self.eeprom.[<$FIELD:upper DriverType>]
                    }

                    #[doc = "Set the driver type for port " $FIELD "."]
                    pub fn [<set_ $FIELD:lower _driver_type>](&mut self, value: DriverType) {
                        self.eeprom.[<$FIELD:upper DriverType>] = value as u8
                    }
                )*
            }
        }
    };
}

macro_rules! impl_header {
    ($NAME:ident, $RAW:ident) => {
        impl $NAME {
            paste::item! {
                #[doc = "Create a new `" $NAME "` EEPROM structure."]
                pub fn new(
                    eeprom: $RAW,
                    manufacturer: String,
                    manufacturer_id: String,
                    description: String,
                    serial_number: String,
                ) -> $NAME {
                    $NAME {
                        eeprom,
                        manufacturer,
                        manufacturer_id,
                        description,
                        serial_number,
                    }
                }
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
                set_string!(
                    self,
                    manufacturer,
                    value,
                    manufacturer_id,
                    description,
                    serial_number,
                )
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
                set_string!(
                    self,
                    manufacturer_id,
                    value,
                    manufacturer,
                    description,
                    serial_number,
                )
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
                set_string!(
                    self,
                    description,
                    value,
                    manufacturer,
                    manufacturer_id,
                    serial_number,
                )
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
                set_string!(
                    self,
                    serial_number,
                    value,
                    manufacturer,
                    manufacturer_id,
                    description,
                )
            }

            /// FTDI USB device vendor ID.
            ///
            /// This is typically `0x0403`.
            pub fn vendor_id(&self) -> u16 {
                self.eeprom.common.VendorId
            }

            /// Set the FTDI USB device vendor ID.
            pub fn set_vendor_id(&mut self, value: u16) {
                self.eeprom.common.VendorId = value
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
                self.eeprom.common.ProductId
            }

            /// Set the FTDI USB product ID.
            pub fn set_product_id(&mut self, value: u16) {
                self.eeprom.common.ProductId = value
            }

            /// Serial Number Enable.
            ///
            /// `true` if the serial number is to be used.
            ///
            /// The documentation is unclear what *exactly* this means.
            pub fn serial_number_enable(&self) -> bool {
                self.eeprom.common.SerNumEnable != 0
            }

            /// Set Serial Number Enable.
            pub fn set_serial_number_enable(&mut self, value: bool) {
                self.eeprom.common.SerNumEnable = if value { 1 } else { 0 }
            }

            /// Maximum bus current.
            ///
            /// The unit for this value is milliamps, and the value range is
            /// 0-500 mA.
            pub fn max_current(&self) -> u16 {
                self.eeprom.common.MaxPower
            }

            /// Set maximum bus current.
            ///
            /// Values greater than 500 mA (`500u16`) will result in panic.
            pub fn set_max_current(&mut self, value: u16) {
                assert!(value <= 500, "{} exceeds 500 mA limit", value);
                self.eeprom.common.MaxPower = value
            }

            /// Device power source.
            ///
            /// * `true` if the device is self-powered.
            /// * `false` if the device is powered by the bus.
            pub fn self_powered(&self) -> bool {
                self.eeprom.common.SelfPowered != 0
            }

            /// Set device power source.
            pub fn set_self_powered(&mut self, value: bool) {
                self.eeprom.common.SelfPowered = if value { 1 } else { 0 }
            }

            /// Remote wakeup capabilities.
            ///
            /// * `true` if the device is capable of remote wakeup.
            /// * `false` if the device is not capable of remote wakeup.
            pub fn remote_wakeup(&self) -> bool {
                self.eeprom.common.RemoteWakeup != 0
            }
            /// Set device power source.
            pub fn set_remote_wakeup(&mut self, value: bool) {
                self.eeprom.common.RemoteWakeup = if value { 1 } else { 0 }
            }

            /// Pull down in suspend mode.
            ///
            /// * `true` if pull-down in suspend is enabled.
            /// * `false` if pull-down in suspend is disabled.
            pub fn pull_down_enable(&self) -> bool {
                self.eeprom.common.PullDownEnable != 0
            }

            /// Set device power source.
            pub fn set_pull_down_enable(&mut self, value: bool) {
                self.eeprom.common.PullDownEnable = if value { 1 } else { 0 }
            }
        }

        impl From<&$NAME> for $RAW {
            fn from(value: &$NAME) -> $RAW {
                value.eeprom.clone()
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
                        self.eeprom.[<$FIELD:upper RIIsTXDEN>] != 0
                    }

                    #[doc = "Use port " $FIELD " as RS485 TX data enable."]
                    pub fn [<set_ $FIELD:lower _ri_is_tx_data_enable>](&mut self, value: bool) {
                        self.eeprom.[<$FIELD:upper RIIsTXDEN>] = if value { 1 } else { 0 }
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
                        self.eeprom.$FIELD
                    }

                    #[doc = "Get the value of the " $FIELD " pin."]
                    pub fn [<$FIELD:lower>](&self) -> Result<$ENUM, EepromValueError> {
                        $ENUM::try_from(self.eeprom.$FIELD)
                    }

                    #[doc = "Get the value of the " $FIELD " pin."]
                    pub fn [<set_ $FIELD:lower>](&mut self, value: $ENUM) {
                        self.eeprom.$FIELD = value as u8;
                    }
                }
            )*
        }
    };
}

// this is where most of the boilerplate is implemented
impl_header!(Eeprom232h, FT_EEPROM_232H);
impl_bus_pins!(Eeprom232h, AD, AC);
impl_cbus!(
    Eeprom232h, Cbus232h, Cbus0, Cbus1, Cbus2, Cbus3, Cbus4, Cbus5, Cbus6, Cbus7, Cbus8, Cbus9,
);
impl_driver_type!(Eeprom232h);

impl_header!(Eeprom4232h, FT_EEPROM_4232H);
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
