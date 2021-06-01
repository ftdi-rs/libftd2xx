use libftd2xx::*;

#[test]
fn all_commands() {
    let val1 = 1;
    let val2 = 2;
    let val11 = 11;
    let val12 = 12;
    let val42 = 42;
    mpsse! {
        let (data, DATA_READ_LEN) = {
            enable_loopback();
            disable_loopback();
            enable_3phase_data_clocking();
            disable_3phase_data_clocking();
            set_gpio_lower(val1, 0x1);
            set_gpio_upper(val2, 0x2);
            const LOWER_INDEX = gpio_lower();
            const UPPER_INDEX = gpio_upper();
            send_immediate();
            wait_on_io_high();
            wait_on_io_low();
            clock_data_out(ClockDataOut::MsbPos, [val11, 22, 33, 44]);
            const DATA_IN_RANGE = clock_data_in(ClockDataIn::MsbPos, 4);
            const DATA_RANGE = clock_data(ClockData::MsbPosIn, [val12, 22, 32, 42]);
            clock_bits_out(ClockBitsOut::MsbPos, val42, 8);
            const BITS_IN_INDEX = clock_bits_in(ClockBitsIn::MsbPos, 8);
            const BITS_INDEX = clock_bits(ClockBits::MsbPosIn, val42, 8);
        };
    }
    assert_eq!(data.len(), 40);
    assert_eq!(
        data,
        [
            MpsseCmd::EnableLoopback as u8,
            MpsseCmd::DisableLoopback as u8,
            MpsseCmd::Enable3PhaseClocking as u8,
            MpsseCmd::Disable3PhaseClocking as u8,
            MpsseCmd::SetDataBitsLowbyte as u8,
            val1,
            0x1,
            MpsseCmd::SetDataBitsHighbyte as u8,
            val2,
            0x2,
            MpsseCmd::GetDataBitsLowbyte as u8,
            MpsseCmd::GetDataBitsHighbyte as u8,
            MpsseCmd::SendImmediate as u8,
            MpsseCmd::WaitOnIOHigh as u8,
            MpsseCmd::WaitOnIOLow as u8,
            ClockDataOut::MsbPos as u8,
            3 as u8,
            0 as u8,
            11 as u8,
            22 as u8,
            33 as u8,
            44 as u8,
            ClockDataIn::MsbPos as u8,
            3 as u8,
            0 as u8,
            ClockData::MsbPosIn as u8,
            3 as u8,
            0 as u8,
            12 as u8,
            22 as u8,
            32 as u8,
            42 as u8,
            ClockBitsOut::MsbPos as u8,
            7 as u8,
            42 as u8,
            ClockBitsIn::MsbPos as u8,
            7 as u8,
            ClockBits::MsbPosIn as u8,
            7 as u8,
            42 as u8,
        ]
    );
    assert_eq!(DATA_READ_LEN, 12);
    assert_eq!(LOWER_INDEX, 0);
    assert_eq!(UPPER_INDEX, 1);
    assert_eq!(DATA_IN_RANGE, 2..6);
    assert_eq!(DATA_RANGE, 6..10);
    assert_eq!(BITS_IN_INDEX, 10);
    assert_eq!(BITS_INDEX, 11);
}

#[test]
fn all_commands_const() {
    mpsse! {
        const (DATA, DATA_READ_LEN) = {
            enable_loopback();
            disable_loopback();
            enable_3phase_data_clocking();
            disable_3phase_data_clocking();
            set_gpio_lower(0x1, 0x1);
            set_gpio_upper(0x2, 0x2);
            const LOWER_INDEX = gpio_lower();
            const UPPER_INDEX = gpio_upper();
            send_immediate();
            wait_on_io_high();
            wait_on_io_low();
            clock_data_out(ClockDataOut::MsbPos, [11, 22, 33, 44]);
            const DATA_IN_RANGE = clock_data_in(ClockDataIn::MsbPos, 4);
            const DATA_RANGE = clock_data(ClockData::MsbPosIn, [12, 22, 32, 42]);
            clock_bits_out(ClockBitsOut::MsbPos, 42, 8);
            const BITS_IN_INDEX = clock_bits_in(ClockBitsIn::MsbPos, 8);
            const BITS_INDEX = clock_bits(ClockBits::MsbPosIn, 42, 8);
        };
    }
    assert_eq!(DATA.len(), 40);
    assert_eq!(
        DATA,
        [
            MpsseCmd::EnableLoopback as u8,
            MpsseCmd::DisableLoopback as u8,
            MpsseCmd::Enable3PhaseClocking as u8,
            MpsseCmd::Disable3PhaseClocking as u8,
            MpsseCmd::SetDataBitsLowbyte as u8,
            0x1,
            0x1,
            MpsseCmd::SetDataBitsHighbyte as u8,
            0x2,
            0x2,
            MpsseCmd::GetDataBitsLowbyte as u8,
            MpsseCmd::GetDataBitsHighbyte as u8,
            MpsseCmd::SendImmediate as u8,
            MpsseCmd::WaitOnIOHigh as u8,
            MpsseCmd::WaitOnIOLow as u8,
            ClockDataOut::MsbPos as u8,
            3 as u8,
            0 as u8,
            11 as u8,
            22 as u8,
            33 as u8,
            44 as u8,
            ClockDataIn::MsbPos as u8,
            3 as u8,
            0 as u8,
            ClockData::MsbPosIn as u8,
            3 as u8,
            0 as u8,
            12 as u8,
            22 as u8,
            32 as u8,
            42 as u8,
            ClockBitsOut::MsbPos as u8,
            7 as u8,
            42 as u8,
            ClockBitsIn::MsbPos as u8,
            7 as u8,
            ClockBits::MsbPosIn as u8,
            7 as u8,
            42 as u8,
        ]
    );
    assert_eq!(DATA_READ_LEN, 12);
    assert_eq!(LOWER_INDEX, 0);
    assert_eq!(UPPER_INDEX, 1);
    assert_eq!(DATA_IN_RANGE, 2..6);
    assert_eq!(DATA_RANGE, 6..10);
    assert_eq!(BITS_IN_INDEX, 10);
    assert_eq!(BITS_INDEX, 11);
}

#[test]
#[should_panic(expected = "data length must be in 1..=(u16::MAX + 1)")]
fn clock_data_assert_lower() {
    mpsse! {
        let (_data, DATA_READ_LEN) = {
            clock_data_in(ClockDataIn::MsbPos, 0);
        };
    }
}

#[test]
#[should_panic(expected = "data length must be in 1..=(u16::MAX + 1)")]
fn clock_data_assert_upper() {
    mpsse! {
        let (_data, DATA_READ_LEN) = {
            clock_data_in(ClockDataIn::MsbPos, (u16::MAX as usize) + 2);
        };
    }
}

#[test]
#[should_panic(expected = "data length must be in 1..=8")]
fn clock_bits_out_assert_lower() {
    mpsse! {
        let (_data, DATA_READ_LEN) = {
            clock_bits_out(ClockBitsOut::MsbPos, 42, 0);
        };
    }
}

#[test]
#[should_panic(expected = "data length must be in 1..=8")]
fn clock_bits_out_assert_upper() {
    mpsse! {
        let (_data, DATA_READ_LEN) = {
            clock_bits_out(ClockBitsOut::MsbPos, 42, 9);
        };
    }
}

#[test]
#[should_panic(expected = "data length must be in 1..=8")]
fn clock_bits_in_assert_lower() {
    mpsse! {
        let (_data, DATA_READ_LEN) = {
            clock_bits_in(ClockBitsIn::MsbPos, 0);
        };
    }
}

#[test]
#[should_panic(expected = "data length must be in 1..=8")]
fn clock_bits_in_assert_upper() {
    mpsse! {
        let (_data, DATA_READ_LEN) = {
            clock_bits_in(ClockBitsIn::MsbPos, 9);
        };
    }
}

#[test]
#[should_panic(expected = "data length must be in 1..=8")]
fn clock_bits_assert_lower() {
    mpsse! {
        let (_data, DATA_READ_LEN) = {
            clock_bits(ClockBits::MsbPosIn, 42, 0);
        };
    }
}

#[test]
#[should_panic(expected = "data length must be in 1..=8")]
fn clock_bits_assert_upper() {
    mpsse! {
        let (_data, DATA_READ_LEN) = {
            clock_bits(ClockBits::MsbPosIn, 42, 9);
        };
    }
}

#[test]
fn user_abstracted_macro() {
    macro_rules! mpsse {
        // Practical abstraction of CS line for SPI devices.
        ($passthru:tt {cs_low(); $($tail:tt)*} -> [$($out:tt)*]) => {
            mpsse!($passthru {
                set_gpio_lower(0x0, 0xb);
                $($tail)*
            } -> [$($out)*]);
        };
        ($passthru:tt {cs_high(); $($tail:tt)*} -> [$($out:tt)*]) => {
            mpsse!($passthru {
                set_gpio_lower(0x8, 0xb);
                $($tail)*
            } -> [$($out)*]);
        };

        // Hypothetical device-specific command. Leverages both user and libftd2xx commands.
        ($passthru:tt
         {const $idx_id:ident = command_42([$($data:expr),* $(,)*]); $($tail:tt)*} ->
         [$($out:tt)*]) => {
            mpsse!($passthru {
                cs_low();
                const $idx_id = clock_data(::libftd2xx::ClockData::MsbPosIn, [0x42, $($data,)*]);
                cs_high();
                $($tail)*
            } -> [$($out)*]);
        };

        // Everything else handled by libftd2xx crate implementation.
        ($($tokens:tt)*) => {
            ::libftd2xx::mpsse!($($tokens)*);
        };
    }

    mpsse! {
        const (COMMAND_DATA, READ_LEN) = {
            wait_on_io_high();
            const COMMAND_42_RESULT_RANGE = command_42([11, 22, 33]);
            send_immediate();
        };
    }
    assert_eq!(COMMAND_DATA.len(), 15);
    assert_eq!(
        COMMAND_DATA,
        [
            MpsseCmd::WaitOnIOHigh as u8,
            MpsseCmd::SetDataBitsLowbyte as u8,
            0x0,
            0xb,
            ClockData::MsbPosIn as u8,
            3 as u8,
            0 as u8,
            0x42 as u8,
            11 as u8,
            22 as u8,
            33 as u8,
            MpsseCmd::SetDataBitsLowbyte as u8,
            0x8,
            0xb,
            MpsseCmd::SendImmediate as u8,
        ]
    );
    assert_eq!(READ_LEN, 4);
    assert_eq!(COMMAND_42_RESULT_RANGE, 0..4);
}
