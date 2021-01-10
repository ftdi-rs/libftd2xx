pub trait NumberBoilerplate {
    fn zero() -> Self;
}

impl NumberBoilerplate for i8 {
    fn zero() -> i8 {
        0i8
    }
}

impl NumberBoilerplate for u8 {
    fn zero() -> u8 {
        0u8
    }
}

// Converts an i8 or u8 slice into a string.  Non UTF-8 will be lost.
//
// The FTDI strings have unique requiements:
// * They may contain interior nul bytes.
// * They might not be nul terminated.
pub fn slice_into_string<T>(array: &[T]) -> String
where
    T: NumberBoilerplate + std::cmp::PartialEq,
{
    let mut idx: usize = array.len();
    for (i, element) in array.iter().enumerate() {
        if *element == NumberBoilerplate::zero() {
            idx = i;
            break;
        }
    }

    // Safety: The trait bounds for T are only implemented for u8 and i8, which
    // are equal size, and are therefore safe to transmute.
    debug_assert_eq!(std::mem::size_of::<T>(), std::mem::size_of::<u8>());
    String::from_utf8_lossy(unsafe { std::mem::transmute::<&[T], &[u8]>(&array[0..idx]) })
        .to_string()
}

#[cfg(test)]
mod slice_into_string {
    use super::*;

    #[test]
    fn empty() {
        let data: [i8; 0] = [];
        assert_eq!(slice_into_string(&data), String::from(""));
    }

    #[test]
    fn positive_path() {
        let data: [u8; 2] = [0x61, 0x00];
        assert_eq!(slice_into_string(&data), String::from("a"));
    }

    #[test]
    fn interior_nul() {
        let data: [i8; 3] = [0x61, 0x00, 0x61];
        assert_eq!(slice_into_string(&data), String::from("a"));
    }

    #[test]
    fn no_nul() {
        let data: [i8; 3] = [0x61; 3];
        assert_eq!(slice_into_string(&data), String::from("aaa"));
    }

    #[test]
    fn non_utf8() {
        let data: [i8; 2] = [0xFEu8 as i8, 0x00];
        assert_eq!(slice_into_string(&data), String::from("�"));
    }
}
