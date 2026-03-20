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
            let mut bit = 2;
            while bit < u16::BITS {
                n_inv *= Wrapping(2) - n_inv * Wrapping(n);
                bit <<= 1;
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
}

fn check1(n0: u16) {
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

#[test]
fn check_modint() {
    for n in (1..1 << U1::BITS - 1).filter(|n| n % 2 == 1) {
        check1(n);
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
