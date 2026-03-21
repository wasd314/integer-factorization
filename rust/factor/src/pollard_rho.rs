use crate::{modint::u128::ModInt, primality::is_prime, utility::gcd};

/// Pollard's rho with Floyd's cycle detection.
pub fn find_factor(n: u128) -> u128 {
    assert!(n >= 2);
    if is_prime(n) {
        return n;
    }
    if n.is_multiple_of(2) {
        return 2;
    }
    // n: odd composite
    let mo = ModInt::new(n);
    let mut rc = 0;
    let batch = n.isqrt().isqrt().isqrt();
    loop {
        rc += 1;
        let f = |rx| mo.add(mo.mul(rx, rx), rc);
        let (mut rx, mut ry) = (rc, rc);
        let mut d = 1;
        let mut checkpoint = (rx, ry);
        while d == 1 {
            let mut combined = 1;
            for _ in 0..batch {
                rx = f(rx);
                ry = f(f(ry));
                combined = mo.mul(combined, rx.abs_diff(ry));
            }
            d = gcd(n, combined);
            if d == 1 {
                checkpoint = (rx, ry);
            } else if d != n {
                return d;
            }
        }
        (rx, ry) = checkpoint;
        for _ in 0..batch {
            rx = f(rx);
            ry = f(f(ry));
            let d = gcd(n, rx.abs_diff(ry));
            if d != 1 && d != n {
                return d;
            }
        }
    }
}
