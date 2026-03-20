mod test_u16;

macro_rules! impl_modint {
    ($mod_name:ident: $u0:ty, $u1:ty) => {
        pub mod $mod_name {
            use std::num::Wrapping;

            #[derive(Debug, Clone, Copy)]
            pub struct ModInt {
                /// N, modulus
                n: U1,
                /// R^1 % N, where R := 2^`U1::BITS`
                r1: U1,
                /// R^2 % N
                r2: U1,
                /// -(N^-1) % R
                n_: U1,
            }

            pub type U0 = $u0;
            pub type U1 = $u1;

            /// `(x * y) >> U1::BITS`
            pub fn multiply_high(x: U1, y: U1) -> U1 {
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
                pub fn new(n: U1) -> Self {
                    assert_eq!(n >> (U1::BITS - 1), 0);
                    assert_eq!(n & 1, 1, "n = {n} should be odd");

                    let n_ = {
                        // n * n == 1 mod 2^2
                        let mut n_inv = Wrapping(n);
                        for _ in 0..U1::BITS.ilog2() - 1 {
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

                pub fn mod_n(&self, x: U1) -> U1 {
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
                pub fn multiply_reduce(&self, rx: U1, ry: U1) -> U1 {
                    let t_ = rx.wrapping_mul(ry).wrapping_mul(self.n_);
                    let t = multiply_high(rx, ry)
                        + multiply_high(t_, self.n)
                        + if rx.wrapping_mul(ry) != 0 { 1 } else { 0 };
                    self.mod_n(t)
                }
                /// Reduce: x * R^{-1} % N
                pub fn reduce(&self, rx: U1) -> U1 {
                    self.multiply_reduce(rx, 1)
                }
                /// Montgomery representation of x.
                /// x -> rx = Reduce(x * r^2)
                pub fn mr(&self, x: U1) -> U1 {
                    self.multiply_reduce(x % self.n, self.r2)
                }
                pub fn val(&self, rx: U1) -> U1 {
                    self.reduce(rx)
                }

                pub fn add(&self, rx: U1, ry: U1) -> U1 {
                    self.mod_n(rx + ry)
                }
                pub fn sub(&self, rx: U1, ry: U1) -> U1 {
                    if rx >= ry { rx - ry } else { rx + self.n - ry }
                }
                pub fn neg(&self, rx: U1) -> U1 {
                    self.sub(0, rx)
                }
                pub fn mul(&self, rx: U1, ry: U1) -> U1 {
                    self.multiply_reduce(rx, ry)
                }
                pub fn pow(&self, rx: U1, mut e: U1) -> U1 {
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

            #[cfg(test)]
            mod tests {
                use super::*;

                #[test]
                fn check_modint_op() {
                    for n0 in (1..1 << (U1::BITS - 1).min(10))
                        .flat_map(|x| [x, !x >> 1])
                        .filter(|n| n % 2 == 1)
                    {
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
            }
        }
    };
}
impl_modint!(u128: u64, u128);
impl_modint!(u64: u32, u64);
impl_modint!(u32: u16, u32);
impl_modint!(u16: u8, u16);
