use libftd2xx::get_num_devices;

fn main() {
    let num_devices = get_num_devices().unwrap();
    println!("Number of devices: {}", num_devices);
}
