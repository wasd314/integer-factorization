mod test_u16;

macro_rules! impl_modint {
    // impl body
    (@ body: $u1:ty, $i1:ty) => {
        use std::num::Wrapping;

        #[derive(Debug, Clone, Copy)]
        pub struct ModInt {
            /// N, modulus
            pub n: $u1,
            /// R^1 % N, where R := 2^`U1::BITS`, or MR(1)
            pub r1: $u1,
            /// R^2 % N
            pub r2: $u1,
            /// -(N^-1) % R
            pub n_: $u1,
        }

        pub fn gcd(mut x: $u1, mut y: $u1) -> $u1 {
            while x != 0 {
                (x, y) = (y % x, x);
            }
            y
        }

        /// `(x * y) >> U1::BITS`
        pub fn multiply_high(x: $u1, y: $u1) -> $u1 {
            x.carrying_mul(y, 0).1
        }

        impl ModInt {
            pub fn new(n: $u1) -> Self {
                assert_eq!(n >> (<$u1>::BITS - 1), 0);
                assert_eq!(n & 1, 1, "n = {n} should be odd");

                let n_ = {
                    // n * n == 1 mod 2^2
                    let mut n_inv = Wrapping(n);
                    for _ in 0..<$u1>::BITS.ilog2() - 1 {
                        n_inv *= Wrapping(2) - n_inv * Wrapping(n);
                    }
                    (-n_inv).0
                };
                let r1 = n.wrapping_neg() % n;
                let r2 = {
                    let mut r2 = r1;
                    for _ in 0..<$u1>::BITS {
                        r2 <<= 1;
                        if r2 >= n {
                            r2 -= n;
                        }
                    }
                    r2
                };

                Self { n, r1, r2, n_ }
            }

            pub fn mod_n(&self, x: $u1) -> $u1 {
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

            /// Reduce(rx * ry) = r(xy)
            pub fn multiply_reduce(&self, rx: $u1, ry: $u1) -> $u1 {
                let t_ = rx.wrapping_mul(ry).wrapping_mul(self.n_);
                let t =
                    multiply_high(rx, ry) + multiply_high(t_, self.n) + rx.wrapping_mul(ry).min(1);
                self.mod_n(t)
            }
            /// Reduce: x * R^{-1} % N
            pub fn reduce(&self, rx: $u1) -> $u1 {
                self.multiply_reduce(rx, 1)
            }
            /// Montgomery representation of x.
            /// x -> rx = Reduce(x * r^2)
            pub fn mr(&self, x: $u1) -> $u1 {
                self.multiply_reduce(x % self.n, self.r2)
            }
            pub fn val(&self, rx: $u1) -> $u1 {
                self.reduce(rx)
            }
            pub fn one(&self) -> $u1 {
                self.r1
            }

            pub fn add(&self, rx: $u1, ry: $u1) -> $u1 {
                self.mod_n(rx + ry)
            }
            pub fn sub(&self, rx: $u1, ry: $u1) -> $u1 {
                if rx >= ry { rx - ry } else { rx + self.n - ry }
            }
            pub fn neg(&self, rx: $u1) -> $u1 {
                self.sub(0, rx)
            }
            pub fn mul(&self, rx: $u1, ry: $u1) -> $u1 {
                self.multiply_reduce(rx, ry)
            }
            pub fn pow(&self, rx: $u1, mut e: $u1) -> $u1 {
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
            /// rx の逆元もしくは gcd(x, n).
            pub fn inv(&self, rx: $u1) -> Result<$u1, $u1> {
                let mut x = (self.reduce(rx), 1, 0);
                let mut y = (self.n, 0, 1);
                while x.0 > 0 {
                    let q = y.0 / x.0;
                    let r = y.0 - x.0 * q;
                    (x, y) = ((r, y.1 - x.1 * q as i16, y.2 - x.2 * q as i16), x);
                }
                let (g, i) = (y.0, y.1.rem_euclid(self.n as _));
                if g == 1 { Ok(self.mr(i as _)) } else { Err(g) }
            }
            pub fn div(&self, rx: $u1, ry: $u1) -> Result<$u1, $u1> {
                let inv_ry = self.inv(ry)?;
                Ok(self.mul(rx, inv_ry))
            }
        }
    };
    // impl tests with $u1, $i1
    (@ test: $u1:ty, $i1:ty) => {
                #[test]
        fn check_modint_op() {
            for n in (1..(1 << (<$u1>::BITS - 1)).min(1000))
                .flat_map(|x| [x, !x >> 1])
                .filter(|n| n % 2 == 1)
            {
                let mont = ModInt::new(n);
                let pow = |rx: $u1, e: $u1| {
                    let mut ans = mont.mr(1);
                    for _ in 0..e {
                        ans = mont.mul(ans, rx);
                    }
                    mont.mod_n(ans)
                };
                for rx in (0..5.min(n)).flat_map(|x| [x, mont.mr(x), mont.reduce(x)]) {
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
        fn check_modint_inv() {
            for n in (1..1000).filter(|n| n % 2 == 1) {
                let mo = ModInt::new(n);
                for rx in 0..n {
                    let g = gcd(rx, n);
                    match mo.inv(rx) {
                        Ok(ry) => {
                            assert_eq!(g, 1, "inv of rx = {rx} mod {n}");
                            assert_eq!(mo.mul(rx, ry), mo.r1, "inv of rx = {rx} mod {n}");
                        }
                        Err(g_) => {
                            assert_eq!(g_, g, "inv of rx = {rx} mod {n}");
                        }
                    }
                }
            }
        }
    };
    // impl tests using $u2
    (@ test: $u1:ty, $i1:ty, $u2:ty) => {
        #[test]
        fn check_modint_new() {
            for n in (1..(1 << (<$u1>::BITS - 1)).min(1000)).filter(|n| n % 2 == 1) {
                let ModInt { n, r1, r2, n_ } = ModInt::new(n);
                let n1 = n as $u2;
                let r: $u2 = 1 << <$u1>::BITS;
                assert_eq!(n, n, "ModInt({n}): n");
                let true_r1 = r % n1;
                assert_eq!(r1, true_r1 as $u1, "ModInt({n}): r1");
                assert_eq!(r2, (true_r1 * true_r1 % n1) as $u1, "ModInt({n}): r2");
                assert!((n_ as $u2) < r, "ModInt({n}): n_ range");
                assert_eq!(
                    (n_ as $u2 * n1) % r,
                    r - 1,
                    "ModInt({n}): n_({n_}) * N should be -1 mod R"
                );
            }
        }

        #[test]
        fn check_multiply_high() {
            for x in (1..1000).map(|x| <$u1>::MAX / x) {
                for y in (1..1000).map(|x| <$u1>::MAX / x) {
                    let true_ans = (x as $u2 * y as $u2) >> <$u1>::BITS;
                    assert_eq!(multiply_high(x, y), true_ans as $u1, "check for {x} * {y}");
                }
            }
        }
    };
    // impl mod
    ($mod_name:ident: $u1:ty, $i1:ty) => {
        pub mod $mod_name {
            impl_modint!(@ body: $u1, $i1);

            #[cfg(test)]
            mod tests {
                use super::*;
                impl_modint!(@ test: $u1, $i1);
            }
        }
    };
    // impl mod
    ($mod_name:ident: $u1:ty, $i1:ty, $u2:ty) => {
        pub mod $mod_name {
            impl_modint!(@ body: $u1, $i1);

            #[cfg(test)]
            mod tests {
                use super::*;
                impl_modint!(@ test: $u1, $i1);
                impl_modint!(@ test: $u1, $i1, $u2);
            }
        }
    };
}
impl_modint!(u128: u128, i128);
impl_modint!(u64: u64, i64, u128);
impl_modint!(u32: u32, i32, u64);
impl_modint!(u16: u16, i16, u32);
