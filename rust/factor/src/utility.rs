pub fn gcd(mut x: u128, mut y: u128) -> u128 {
    while x != 0 {
        (x, y) = (y, y % x);
    }
    y
}
