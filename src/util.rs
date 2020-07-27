#![deny(missing_docs, warnings)]

// Converts an i8 slice into a string.  Non UTF-8 will be lost.
//
// The FTDI strings have unique requiements:
// * They may contain interior nul bytes.
// * They might not be nul terminated.
pub fn slice_into_string(array: &[i8]) -> String {
    let mut idx: usize = array.len();
    for (i, element) in array.iter().enumerate() {
        if *element == 0 {
            idx = i;
            break;
        }
    }
    String::from_utf8_lossy(unsafe { &*(&array[0..idx] as *const [i8] as *const [u8]) }).to_string()
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
