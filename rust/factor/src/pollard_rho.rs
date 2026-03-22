use std::marker::PhantomData;

use crate::{modint::u128::ModInt, utility::gcd, wrapper::Factorize};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Brent {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Floyd {}

#[derive(Debug, Clone, Copy)]
pub struct PollardRho<T> {
    _cd: PhantomData<fn() -> T>,
    pub batch_gcd: bool,
}

impl<T> PollardRho<T> {
    pub fn new(batch_gcd: bool) -> Self {
        Self {
            _cd: PhantomData,
            batch_gcd,
        }
    }
}

impl Factorize for PollardRho<Floyd> {
    /// Pollard's rho with Floyd's cycle detection.
    fn find_factor(&mut self, n: u128) -> u128 {
        // n: odd composite
        let mo = ModInt::new(n);
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
