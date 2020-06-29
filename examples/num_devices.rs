use libftd2xx::num_devices;

fn main() {
    let num_devices = num_devices().unwrap();
    println!("Number of devices: {}", num_devices);
}
