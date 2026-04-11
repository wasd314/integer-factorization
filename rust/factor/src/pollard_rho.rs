use crate::{
    modint::u128::{DynamicModInt as Mint, gcd},
    wrapper::Factorize,
};

/// Floyd's cycle detection for Pollard's rho.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Floyd;

/// Brent's cycle detection for Pollard's rho.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Brent;

#[derive(Debug, Clone, Copy)]
pub struct PollardRho<T> {
    #[allow(unused)]
    cycle_detection: T,
    pub batch_gcd: bool,
}

impl<T> PollardRho<T> {
    pub fn new(cycle_detection: T, batch_gcd: bool) -> Self {
        Self {
            cycle_detection,
            batch_gcd,
        }
    }
}

impl Factorize for PollardRho<Floyd> {
    fn find_factor(&mut self, n: u128) -> u128 {
        // n: odd composite
        let mo = Mint::new(n);
        let mut rc = 0;
        loop {
            rc += 1;
            let f = |rx| mo.add(mo.mul(rx, rx), rc);
            if self.batch_gcd {
                let batch = n.isqrt().isqrt().isqrt();
                let (mut rx, mut ry) = (rc, rc);
                let mut d = 1;
                // combine batch
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
                // replay batch
                (rx, ry) = checkpoint;
                for _ in 0..batch {
                    rx = f(rx);
                    ry = f(f(ry));
                    let d = gcd(n, rx.abs_diff(ry));
                    if d != 1 && d != n {
                        return d;
                    }
                }
            } else {
                // not batch
                let (mut rx, mut ry) = (rc, rc);
                while {
                    rx = f(rx);
                    ry = f(f(ry));
                    let d = gcd(n, rx.abs_diff(ry));
                    if d != 1 && d != n {
                        return d;
                    }
                    d == 1
                } {}
            }
        }
    }
}

impl Factorize for PollardRho<Brent> {
    fn find_factor(&mut self, n: u128) -> u128 {
        // n: odd composite
        let mo = Mint::new(n);
        let mut rc = 0;
        loop {
            rc += 1;
            let f = |rx| mo.add(mo.mul(rx, rx), rc);
            if self.batch_gcd {
                let batch_bit = (u128::BITS - n.leading_zeros()) as u128 / 8;
                let batch = 1u128 << batch_bit;

                let mut rx = rc;
                // combine head
                let mut combined = 1;
                for i in 0..batch_bit {
                    // rx = f^{o 2^i} (0) = a[2^i]
                    let mut ry = rx;
                    for _ in 1..=1 << i {
                        ry = f(ry);
                        combined = mo.mul(combined, rx.abs_diff(ry));
                    }
                    rx = ry;
                }
                let d = gcd(n, combined);
                if d == n {
                    // replay head
                    let mut rx = rc;
                    for i in 0.. {
                        // rx = f^{o 2^i} (0) = a[2^i]
                        let mut ry = rx;
                        for _ in 1..=1 << i {
                            ry = f(ry);
                            let d = gcd(n, rx.abs_diff(ry));
                            if d != 1 && d != n {
                                return d;
                            }
                        }
                        rx = ry;
                    }
                } else if d != 1 {
                    return d;
                }

                // combine batch
                let mut checkpoint = (rx, rx);
                'outer: for i in batch_bit.. {
                    // rx = f^{o 2^i} (0) = a[2^i]
                    let mut ry = rx;
                    for _ in 0..1 << (i - batch_bit) {
                        let mut combined = 1;
                        for _ in 0..batch {
                            ry = f(ry);
                            combined = mo.mul(combined, rx.abs_diff(ry));
                        }
                        let d = gcd(n, combined);
                        if d == n {
                            break 'outer;
                        } else if d != 1 {
                            return d;
                        }
                        checkpoint = (rx, ry);
                    }
                    rx = ry;
                }
                // replay batch
                let (rx, mut ry) = checkpoint;
                for _ in 0..batch {
                    ry = f(ry);
                    let d = gcd(n, rx.abs_diff(ry));
                    if d != 1 && d != n {
                        return d;
                    }
                }
            } else {
                // not batch
                let mut rx = rc;
                for i in 0.. {
                    // rx = f^{o 2^i} (0) = a[2^i]
                    let mut ry = rx;
                    for _j in 1..=1 << i {
                        ry = f(ry);
                        // ry = a[2^i + j]
                        let d = gcd(n, rx.abs_diff(ry));
                        if d != 1 && d != n {
                            return d;
                        }
                    }
                    rx = ry;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn check(n: u128, batch_gcd: bool) {
        let mut f1 = PollardRho::new(Floyd, batch_gcd);
        let mut f2 = PollardRho::new(Brent, batch_gcd);
        let ans1 = f1.factorize(n);
        let ans2 = f2.factorize(n);
        assert_eq!(ans1, ans2);
        let prod = ans1.iter().product::<u128>();
        assert_eq!(prod, n);
    }

    #[test]
    fn factor_small() {
        for n in [
            12345701 * 12345709,
            1234567891 * 1234567907,
            123456789059 * 123456789061,
        ] {
            check(n, true);
            check(n, false);
        }
    }
}
