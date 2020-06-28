use libftd2xx::list_devices;

fn main() {
    let mut devices = list_devices().unwrap();

    while let Some(device) = devices.pop() {
        println!("device: {}", device);
    }
}
