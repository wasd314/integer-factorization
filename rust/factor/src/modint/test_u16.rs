#![cfg(test)]
//! Test implementation of Montgomery ModInt.

use std::num::Wrapping;

type U0 = u8;
type U1 = u16;

#[derive(Debug, Clone, Copy)]
struct ModInt {
    /// N, modulus
    n: U1,
    /// R^1 % N, where R := 2^`U1::BITS`
    r1: U1,
    /// R^2 % N
    r2: U1,
    /// -(N^-1) % R
    n_: U1,
}

/// `(x * y) >> U1::BITS`
fn multiply_high(x: U1, y: U1) -> U1 {
    let hx = (x >> U0::BITS) as U0;
    let lx = x as U0;
    let hy = (y >> U0::BITS) as U0;
    let ly = y as U0;
    let mul_high = |x1: U0, x2: U0| (x1 as U1 * x2 as U1) >> U0::BITS;
    let mut ans = hx as U1 * hy as U1;
    ans += mul_high(hx, ly);
    ans += mul_high(lx, hy);
    let m = hx.wrapping_mul(ly) as U1 + lx.wrapping_mul(hy) as U1 + mul_high(lx, ly);
    ans += m >> U0::BITS;
    ans
}

impl ModInt {
    fn new(n: U1) -> Self {
        assert_eq!(n >> (U1::BITS - 1), 0);
        assert_eq!(n & 1, 1, "n = {n} should be odd");

        let n_ = {
            // n * n == 1 mod 2^2
            let mut n_inv = Wrapping(n);
            for _ in 0..u16::BITS.ilog2() - 1 {
                n_inv *= Wrapping(2) - n_inv * Wrapping(n);
            }
            (-n_inv).0
        };
        let r1 = n.wrapping_neg() % n;
        let r2 = {
            let mut r2 = r1;
            for _ in 0..U1::BITS {
                r2 <<= 1;
                if r2 >= n {
                    r2 -= n;
                }
            }
            r2
        };

        Self { n, r1, r2, n_ }
    }

    fn mod_n(&self, x: U1) -> U1 {
        if x < self.n {
            x
        } else if x - self.n < self.n {
            x - self.n
        } else if x - self.n * 2 < self.n {
            x - self.n * 2
        } else {
            x % self.n
        }
    }

    /// Reduce(rx * ry) -> r(xy)
    fn multiply_reduce(&self, rx: U1, ry: U1) -> U1 {
        let t_ = rx.wrapping_mul(ry).wrapping_mul(self.n_);
        let t = multiply_high(rx, ry)
            + multiply_high(t_, self.n)
            + if rx.wrapping_mul(ry) != 0 { 1 } else { 0 };
        self.mod_n(t)
    }
    /// Reduce: x * R^{-1} % N
    fn reduce(&self, rx: U1) -> U1 {
        self.multiply_reduce(rx, 1)
    }
    /// Montgomery representation of x.
    /// x -> rx = Reduce(x * r^2)
    fn mr(&self, x: U1) -> U1 {
        self.multiply_reduce(x % self.n, self.r2)
    }
    fn val(&self, rx: U1) -> U1 {
        self.reduce(rx)
    }

    fn add(&self, rx: U1, ry: U1) -> U1 {
        self.mod_n(rx + ry)
    }
    fn sub(&self, rx: U1, ry: U1) -> U1 {
        if rx >= ry { rx - ry } else { rx + self.n - ry }
    }
    fn neg(&self, rx: U1) -> U1 {
        self.sub(0, rx)
    }
    fn mul(&self, rx: U1, ry: U1) -> U1 {
        self.multiply_reduce(rx, ry)
    }
    fn pow(&self, rx: U1, mut e: U1) -> U1 {
        let mut ans = self.r1;
        let mut b = rx;
        while e > 0 {
            if e & 1 != 0 {
                ans = self.mul(ans, b);
            }
            b = self.mul(b, b);
            e >>= 1;
        }
        ans
    }
}

#[test]
fn check_modint_new() {
    for n0 in (1..1 << (U1::BITS - 1)).filter(|n| n % 2 == 1) {
        let ModInt { n, r1, r2, n_ } = ModInt::new(n0);
        let n1 = n0 as u32;
        let r: u32 = 1 << U1::BITS;
        assert_eq!(n, n0, "ModInt({n}): n");
        let true_r1 = r % n1;
        assert_eq!(r1, true_r1 as U1, "ModInt({n}): r1");
        assert_eq!(r2, (true_r1 * true_r1 % n1) as U1, "ModInt({n}): r2");
        assert!((n_ as u32) < r, "ModInt({n}): n_ range");
        assert_eq!(
            (n_ as u32 * n1) % r,
            r - 1,
            "ModInt({n}): n_({n_}) * N should be -1 mod R"
        );
    }
}

#[test]
fn check_modint_op() {
    for n0 in (1..1 << (U1::BITS - 1)).filter(|n| n % 2 == 1) {
        let mont = ModInt::new(n0);
        let pow = |rx: U1, e: U1| {
            let mut ans = mont.mr(1);
            for _ in 0..e {
                ans = mont.mul(ans, rx);
            }
            mont.mod_n(ans)
        };
        for rx in (0..5.min(n0)).flat_map(|x| [x, mont.mr(x), mont.reduce(x)]) {
            assert_eq!(mont.mod_n(rx + mont.neg(rx)), 0);
            assert_eq!(mont.add(rx, mont.neg(rx)), 0);
            assert_eq!(mont.val(mont.mr(rx)), rx);
            assert_eq!(mont.mr(mont.val(rx)), rx);
            for e in 0..10 {
                assert_eq!(mont.pow(rx, e), pow(rx, e));
            }
        }
    }
}

#[test]
fn check_multiply_high() {
    for x in (1..1000).map(|x| U1::MAX / x) {
        for y in (1..1000).map(|x| U1::MAX / x) {
            let true_ans = (x as u32 * y as u32) >> U1::BITS;
            assert_eq!(multiply_high(x, y), true_ans as U1, "check for {x} * {y}");
        }
    }
}
