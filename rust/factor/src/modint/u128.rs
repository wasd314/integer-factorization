use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

type U1 = u128;
type U0 = u64;
type I1 = i128;

#[derive(Debug, Clone, Copy)]
pub struct DynamicModInt {
    /// N, modulus
    pub n: U1,
    /// R^1 % N, where R := 2^`U1::BITS`
    pub r1: U1,
    /// R^2 % N
    pub r2: U1,
    /// -(N^-1) % R
    pub n_: U1,
}

pub fn gcd(mut x: U1, mut y: U1) -> U1 {
    while x != 0 {
        (x, y) = (y % x, x);
    }
    y
}
/// (g, x) s.t.
/// - g = gcd(a, b)
/// - a * x = g (mod b)
/// - 0 <= x < b/g
pub const fn inv_gcd(a: U1, b: U1) -> (U1, U1) {
    let a = a.rem_euclid(b);
    // invariants:
    // [1] at.0 - at.1 * x = 0 (mod b)
    // [2] bt.0 - bt.1 * x = 0 (mod b)
    // [3] at.0 * |bt.1| + bt.0 * |at.1| <= b
    let mut at = (a, 1);
    let mut bt = (b, 0);
    while at.0 > 0 {
        let q = bt.0 / at.0;
        let r = bt.0 - at.0 * q;
        // [1]':
        // at'.0 - at'.1 * x
        // = (bt.0 - at.0 * q) - (bt.1 - at.1 * q) * x
        // = (bt.0 - bt.1 * x) - (at.0 - at.1 * x) * q
        // = 0 (mod b).
        // [2]': [1]
        // [3]':
        // at'.0 * |bt'.1| + bt'.0 * |at'.1|
        // = (bt.0 - at.0 * q) * |at.1| + at.0 * |bt.1 - at.1 * q|
        // <= bt.0 * |at.1| - at.0 * q * |at.1| + at.0 * (|bt.1| + |at.1| * q)
        // = bt.0 * |at.1| + at.0 * |bt.1|
        // <= b.
        (at, bt) = ((r, bt.1 - at.1 * q as I1), at);
    }
    // prev [3]: bt.0 * |bt_.1| + bt_.0 * |bt.1| <= b
    // g = bt.0 < bt_.0: g * |bt.1| < 0 + bt_.0 * |bt.1| <= b
    // |bt.0| < b/g
    let (g, x) = bt;
    (g, if x >= 0 { x } else { x + (b / g) as I1 } as _)
}

/// `(x * y) >> U1::BITS`
fn multiply_high(x: U1, y: U1) -> U1 {
    x.carrying_mul(y, 0).1
}
/// `(x * y) >> U1::BITS`
const fn multiply_high_const(x: U1, y: U1) -> U1 {
    let hx = (x >> U0::BITS) as U0;
    let lx = x as U0;
    let hy = (y >> U0::BITS) as U0;
    let ly = y as U0;
    const fn mul_high(x1: U0, x2: U0) -> U1 {
        (x1 as U1 * x2 as U1) >> U0::BITS
    }
    let mut ans = hx as U1 * hy as U1;
    ans += mul_high(hx, ly);
    ans += mul_high(lx, hy);
    let m = hx.wrapping_mul(ly) as U1 + lx.wrapping_mul(hy) as U1 + mul_high(lx, ly);
    ans += m >> U0::BITS;
    ans
}

impl DynamicModInt {
    pub const fn new(n: U1) -> Self {
        assert!(n >> (U1::BITS - 1) == 0);
        assert!(n & 1 == 1, "n should be odd");

        let n_ = {
            // n * n == 1 mod 2^2
            let mut n_inv = n;
            let mut i = U1::BITS.ilog2() - 1;
            while i > 0 {
                // n_inv *= Wrapping(2) - n_inv * Wrapping(n);
                n_inv = n_inv.wrapping_mul((2 as U1).wrapping_sub(n_inv.wrapping_mul(n)));
                i -= 1;
            }
            n_inv.wrapping_neg()
        };
        let r1 = n.wrapping_neg() % n;
        let r2 = {
            let mut r2 = r1;
            let mut i = U1::BITS;
            while i > 0 {
                r2 <<= 1;
                if r2 >= n {
                    r2 -= n;
                }
                i -= 1;
            }
            r2
        };

        Self { n, r1, r2, n_ }
    }

    pub const fn mod_n(&self, x: U1) -> U1 {
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
    pub fn multiply_reduce(&self, rx: U1, ry: U1) -> U1 {
        if rx == self.r1 {
            return self.mod_n(ry);
        }
        if ry == self.r1 {
            return self.mod_n(rx);
        }
        let t_ = rx.wrapping_mul(ry).wrapping_mul(self.n_);
        let t = multiply_high(rx, ry) + multiply_high(t_, self.n) + rx.wrapping_mul(ry).min(1);
        self.mod_n(t)
    }
    pub const fn multiply_reduce_const(&self, rx: U1, ry: U1) -> U1 {
        if rx == self.r1 {
            return self.mod_n(ry);
        }
        if ry == self.r1 {
            return self.mod_n(rx);
        }
        let t_ = rx.wrapping_mul(ry).wrapping_mul(self.n_);
        let t = multiply_high_const(rx, ry)
            + multiply_high_const(t_, self.n)
            + if rx.wrapping_mul(ry) == 0 { 0 } else { 1 };
        self.mod_n(t)
    }
    /// Reduce(x) = x * R^{-1} % N
    pub fn reduce(&self, rx: U1) -> U1 {
        self.multiply_reduce(rx, 1)
    }
    /// Reduce(x) = x * R^{-1} % N
    pub const fn reduce_const(&self, rx: U1) -> U1 {
        self.multiply_reduce_const(rx, 1)
    }
    /// Montgomery representation of x.
    /// rx = Reduce(x * r^2)
    pub fn mr(&self, x: U1) -> U1 {
        self.multiply_reduce(self.mod_n(x), self.r2)
    }
    /// Montgomery representation of x.
    /// rx = Reduce(x * r^2)
    pub const fn mr_const(&self, x: U1) -> U1 {
        self.multiply_reduce_const(self.mod_n(x), self.r2)
    }
    /// x = Reduce(rx)
    pub fn val(&self, rx: U1) -> U1 {
        self.reduce(rx)
    }
    /// x = Reduce(rx)
    pub const fn val_const(&self, rx: U1) -> U1 {
        self.reduce_const(rx)
    }
    /// r * 1
    pub const fn one(&self) -> U1 {
        self.r1
    }

    pub const fn add(&self, rx: U1, ry: U1) -> U1 {
        self.mod_n(rx + ry)
    }
    pub const fn sub(&self, rx: U1, ry: U1) -> U1 {
        if rx >= ry { rx - ry } else { rx + self.n - ry }
    }
    pub const fn neg(&self, rx: U1) -> U1 {
        self.sub(0, rx)
    }
    pub fn mul(&self, rx: U1, ry: U1) -> U1 {
        self.multiply_reduce(rx, ry)
    }
    pub const fn mul_const(&self, rx: U1, ry: U1) -> U1 {
        self.multiply_reduce_const(rx, ry)
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
    pub const fn pow_const(&self, rx: U1, mut e: U1) -> U1 {
        let mut ans = self.r1;
        let mut b = rx;
        while e > 0 {
            if e & 1 != 0 {
                ans = self.mul_const(ans, b);
            }
            b = self.mul_const(b, b);
            e >>= 1;
        }
        ans
    }
    /// rx の逆元もしくは gcd(x, n).
    pub fn inv(&self, rx: U1) -> Result<U1, U1> {
        let (g, i) = inv_gcd(self.reduce(rx), self.n);
        if g == 1 { Ok(self.mr(i)) } else { Err(g) }
    }
    /// rx の逆元もしくは gcd(x, n).
    pub const fn inv_const(&self, rx: U1) -> Result<U1, U1> {
        let (g, i) = inv_gcd(self.reduce_const(rx), self.n);
        if g == 1 { Ok(self.mr_const(i)) } else { Err(g) }
    }
    pub fn div(&self, rx: U1, ry: U1) -> Result<U1, U1> {
        let inv_ry = self.inv(ry)?;
        Ok(self.mul(rx, inv_ry))
    }
    pub const fn div_const(&self, rx: U1, ry: U1) -> Result<U1, U1> {
        match self.inv_const(ry) {
            Ok(inv_ry) => Ok(self.mul_const(rx, inv_ry)),
            Err(d) => Err(d),
        }
    }
    pub fn batch_inv(&self, rx: &[U1]) -> Result<Vec<U1>, U1> {
        let n = rx.len();
        let mut acc = vec![self.one(); n + 1];
        for i in 0..n {
            acc[i + 1] = self.mul(acc[i], rx[i]);
        }
        let mut inv_acc = vec![self.one(); n + 1];
        inv_acc[n] = self.inv(*acc.last().unwrap())?;
        for i in (0..n).rev() {
            inv_acc[i] = self.mul(inv_acc[i + 1], rx[i]);
        }
        Ok((0..n).map(|i| self.mul(acc[i], inv_acc[i + 1])).collect())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct StaticModInt<const M: U1>(U1);

pub trait Modulus: Sized {
    const MOD: U1;
    const MON: DynamicModInt;
}

impl<const M: U1> Modulus for StaticModInt<M> {
    const MOD: U1 = M;
    const MON: DynamicModInt = DynamicModInt::new(M);
}

impl<const M: U1> StaticModInt<M> {
    pub const fn raw(rx: U1) -> Self {
        Self(rx)
    }
    pub fn new(x: U1) -> Self {
        Self::raw(Self::MON.mr(x))
    }
    pub const fn new_const(x: U1) -> Self {
        Self::raw(Self::MON.mr_const(x))
    }
    pub const fn one() -> Self {
        Self::raw(Self::MON.one())
    }

    pub fn val(&self) -> U1 {
        Self::MON.val(self.0)
    }
    pub const fn val_const(&self) -> U1 {
        Self::MON.val_const(self.0)
    }

    pub const fn add(self, rhs: Self) -> Self {
        Self::raw(Self::MON.add(self.0, rhs.0))
    }
    pub const fn sub(&self, rhs: Self) -> Self {
        Self::raw(Self::MON.sub(self.0, rhs.0))
    }
    pub const fn mul_const(&self, rhs: Self) -> Self {
        Self::raw(Self::MON.mul_const(self.0, rhs.0))
    }
    pub const fn div_const(&self, rhs: Self) -> Result<Self, U1> {
        match Self::MON.div_const(self.0, rhs.0) {
            Ok(x) => Ok(Self::raw(x)),
            Err(d) => Err(d),
        }
    }
    pub const fn neg(self) -> Self {
        Self::raw(Self::MON.neg(self.0))
    }
    pub fn pow(&self, e: U1) -> Self {
        Self::raw(Self::MON.pow(self.0, e))
    }
    pub const fn pow_const(&self, e: U1) -> Self {
        Self::raw(Self::MON.pow_const(self.0, e))
    }
    pub fn inv(&self) -> Result<Self, U1> {
        let ri = Self::MON.inv(self.0)?;
        Ok(Self::raw(ri))
    }
    pub const fn inv_const(&self) -> Result<Self, U1> {
        match Self::MON.inv_const(self.0) {
            Ok(ri) => Ok(Self::raw(ri)),
            Err(d) => Err(d),
        }
    }
}

impl<const M: U1> Add<StaticModInt<M>> for StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn add(self, rhs: StaticModInt<M>) -> Self::Output {
        Self::raw(Self::MON.add(self.0, rhs.0))
    }
}
impl<const M: U1> Add<&StaticModInt<M>> for StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn add(self, rhs: &StaticModInt<M>) -> Self::Output {
        Self::raw(Self::MON.add(self.0, rhs.0))
    }
}
impl<const M: U1> Add<StaticModInt<M>> for &StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn add(self, rhs: StaticModInt<M>) -> Self::Output {
        StaticModInt::raw(StaticModInt::<M>::MON.add(self.0, rhs.0))
    }
}
impl<const M: U1> Add<&StaticModInt<M>> for &StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn add(self, rhs: &StaticModInt<M>) -> Self::Output {
        StaticModInt::raw(StaticModInt::<M>::MON.add(self.0, rhs.0))
    }
}

impl<const M: U1> Sub<StaticModInt<M>> for StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn sub(self, rhs: StaticModInt<M>) -> Self::Output {
        Self::raw(Self::MON.sub(self.0, rhs.0))
    }
}
impl<const M: U1> Sub<&StaticModInt<M>> for StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn sub(self, rhs: &StaticModInt<M>) -> Self::Output {
        Self::raw(Self::MON.sub(self.0, rhs.0))
    }
}
impl<const M: U1> Sub<StaticModInt<M>> for &StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn sub(self, rhs: StaticModInt<M>) -> Self::Output {
        StaticModInt::raw(StaticModInt::<M>::MON.sub(self.0, rhs.0))
    }
}
impl<const M: U1> Sub<&StaticModInt<M>> for &StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn sub(self, rhs: &StaticModInt<M>) -> Self::Output {
        StaticModInt::raw(StaticModInt::<M>::MON.sub(self.0, rhs.0))
    }
}

impl<const M: U1> Mul<StaticModInt<M>> for StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn mul(self, rhs: StaticModInt<M>) -> Self::Output {
        Self::raw(Self::MON.mul(self.0, rhs.0))
    }
}
impl<const M: U1> Mul<&StaticModInt<M>> for StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn mul(self, rhs: &StaticModInt<M>) -> Self::Output {
        Self::raw(Self::MON.mul(self.0, rhs.0))
    }
}
impl<const M: U1> Mul<StaticModInt<M>> for &StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn mul(self, rhs: StaticModInt<M>) -> Self::Output {
        StaticModInt::raw(StaticModInt::<M>::MON.mul(self.0, rhs.0))
    }
}
impl<const M: U1> Mul<&StaticModInt<M>> for &StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn mul(self, rhs: &StaticModInt<M>) -> Self::Output {
        StaticModInt::raw(StaticModInt::<M>::MON.mul(self.0, rhs.0))
    }
}

impl<const M: U1> Div<StaticModInt<M>> for StaticModInt<M> {
    type Output = Result<StaticModInt<M>, U1>;
    fn div(self, rhs: StaticModInt<M>) -> Self::Output {
        Ok(Self::raw(Self::MON.div(self.0, rhs.0)?))
    }
}
impl<const M: U1> Div<&StaticModInt<M>> for StaticModInt<M> {
    type Output = Result<StaticModInt<M>, U1>;
    fn div(self, rhs: &StaticModInt<M>) -> Self::Output {
        Ok(Self::raw(Self::MON.div(self.0, rhs.0)?))
    }
}
impl<const M: U1> Div<StaticModInt<M>> for &StaticModInt<M> {
    type Output = Result<StaticModInt<M>, U1>;
    fn div(self, rhs: StaticModInt<M>) -> Self::Output {
        Ok(StaticModInt::raw(
            StaticModInt::<M>::MON.div(self.0, rhs.0)?,
        ))
    }
}
impl<const M: U1> Div<&StaticModInt<M>> for &StaticModInt<M> {
    type Output = Result<StaticModInt<M>, U1>;
    fn div(self, rhs: &StaticModInt<M>) -> Self::Output {
        Ok(StaticModInt::raw(
            StaticModInt::<M>::MON.div(self.0, rhs.0)?,
        ))
    }
}

impl<const M: U1> Neg for StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn neg(self) -> Self::Output {
        Self::raw(Self::MON.neg(self.0))
    }
}
impl<const M: U1> Neg for &StaticModInt<M> {
    type Output = StaticModInt<M>;
    fn neg(self) -> Self::Output {
        StaticModInt::raw(StaticModInt::<M>::MON.neg(self.0))
    }
}

impl<const M: U1> AddAssign<StaticModInt<M>> for StaticModInt<M> {
    fn add_assign(&mut self, rhs: StaticModInt<M>) {
        *self = *self + rhs;
    }
}
impl<const M: U1> AddAssign<&StaticModInt<M>> for StaticModInt<M> {
    fn add_assign(&mut self, rhs: &StaticModInt<M>) {
        *self = *self + rhs;
    }
}
impl<const M: U1> SubAssign<StaticModInt<M>> for StaticModInt<M> {
    fn sub_assign(&mut self, rhs: StaticModInt<M>) {
        *self = *self - rhs;
    }
}
impl<const M: U1> SubAssign<&StaticModInt<M>> for StaticModInt<M> {
    fn sub_assign(&mut self, rhs: &StaticModInt<M>) {
        *self = *self - rhs;
    }
}
impl<const M: U1> MulAssign<StaticModInt<M>> for StaticModInt<M> {
    fn mul_assign(&mut self, rhs: StaticModInt<M>) {
        *self = *self * rhs;
    }
}
impl<const M: U1> MulAssign<&StaticModInt<M>> for StaticModInt<M> {
    fn mul_assign(&mut self, rhs: &StaticModInt<M>) {
        *self = *self * rhs;
    }
}
impl<const M: U1> DivAssign<StaticModInt<M>> for StaticModInt<M> {
    fn div_assign(&mut self, rhs: StaticModInt<M>) {
        *self = self.div(rhs).expect("should be invertible");
    }
}
impl<const M: U1> DivAssign<&StaticModInt<M>> for StaticModInt<M> {
    fn div_assign(&mut self, rhs: &StaticModInt<M>) {
        *self = self.div(rhs).expect("should be invertible");
    }
}

macro_rules! impl_from {
    (u: $($ts:ty),*) => {
        $(
            impl<const M: U1> From<$ts> for StaticModInt<M> {
                fn from(value: $ts) -> Self {
                    Self::new((value as u128).rem_euclid(M))
                }
            }
        )*
    };
    (i: $($ts:ty),*) => {
        $(
            impl<const M: U1> From<$ts> for StaticModInt<M> {
                fn from(value: $ts) -> Self {
                    Self::new((value as i128).rem_euclid(M as _) as _)
                }
            }
        )*
    };
}
impl_from!(u: u8, u16, u32, u64, u128);
impl_from!(i: i8, i16, i32, i64, i128);

#[cfg(test)]
mod tests {
    use crate::utility::Sfc64;

    use super::*;

    const fn check_eq<const M: U1>(a: StaticModInt<M>, b: StaticModInt<M>) {
        assert!(a.0 == b.0);
    }

    #[test]
    fn op() {
        type Mint = StaticModInt<97>;
        for a in 0..Mint::MOD {
            let ma = Mint::new(a);
            for b in 0..Mint::MOD {
                let mb = Mint::new(b);
                assert_eq!(ma + mb, Mint::new(a + b));
                assert_eq!(ma.add(mb), Mint::new(a + b));
            }
        }
    }

    #[test]
    const fn op_const() {
        type Mint = StaticModInt<97>;
        let mut a = 0;
        while a < Mint::MOD {
            let ma = Mint::new_const(a);
            let mut b = 0;
            while b < Mint::MOD {
                let mb = Mint::new_const(b);
                // assert!(ma + mb == Mint::new(a + b));
                assert!(ma.add(mb).0 == Mint::new_const(a + b).0);
                check_eq(ma.add(mb), Mint::new_const(a + b));
                b += 1;
            }
            a += 1;
        }
    }
    #[test]
    fn test_batch_inv() {
        let mut rng = Sfc64::new(0);
        for _ in 0..100 {
            const M: u128 = 1001001001;
            let mo = DynamicModInt::new(M);
            let n = rng.next_range(0..100) as usize;
            let rxs = rng
                .next_vector(0..M, n)
                .into_iter()
                .map(|x| mo.mr(x))
                .collect::<Vec<_>>();
            let Ok(rys) = mo.batch_inv(&rxs) else {
                continue;
            };
            assert_eq!(rxs.len(), rys.len());
            for (rx, ry) in rxs.into_iter().zip(rys) {
                assert_eq!(mo.mul(rx, ry), mo.one());
            }
        }
        for _ in 0..100 {
            const M: u128 = 1001;
            let mo = DynamicModInt::new(M);
            let n = rng.next_range(0..100) as usize;
            let rxs = rng
                .next_vector(0..M, n)
                .into_iter()
                .map(|x| mo.mr(x))
                .collect::<Vec<_>>();
            let Ok(rys) = mo.batch_inv(&rxs) else {
                continue;
            };
            assert_eq!(rxs.len(), rys.len());
            for (rx, ry) in rxs.into_iter().zip(rys) {
                assert_eq!(mo.mul(rx, ry), mo.one());
            }
        }
    }
}
