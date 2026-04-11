use std::ops::{Add, AddAssign, Index, IndexMut, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{
    convolution::u128::{DynamicConvolution, convolution_arbitrary},
    modint::u128::{DynamicModInt, StaticModInt as Mint},
};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Fps<T>(Vec<T>);

impl<T> Fps<T> {
    pub fn new(a: Vec<T>) -> Self {
        Self(a)
    }
    /// 係数列の長さを返す
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// 0であるか
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// 係数列を in-place に反転する．
    ///
    /// N > 0 なら，F を F(X ← 1/X) * X ** (N - 1) に変える．
    ///
    /// 係数列の末尾に 0 があるかを確認しない．
    pub fn reverse(&mut self) {
        self.0.reverse();
    }
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut()
    }
    pub fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }
}

impl<T: Clone + Default> Fps<T> {
    pub fn resize(&mut self, len: usize) {
        self.0.resize(len, T::default());
    }
    pub fn prefix(&self, len: usize) -> Self {
        if len <= self.len() {
            Self::new(self.0[..len].to_owned())
        } else {
            let mut f = self.clone();
            f.resize(len);
            f
        }
    }
    /// cloneして，係数列を反転したものを返す．
    ///
    /// N > 0 なら，F(X ← 1/X) * X ** (N - 1) を返す．
    ///
    /// 最高次の係数が 0 であるかを確認しない．
    pub fn reversed(&self) -> Self {
        let mut f = self.clone();
        f.reverse();
        f
    }
}

impl<const M: u128> Fps<Mint<M>> {
    /// 係数列末尾の 0 を全て落とす
    pub fn shrink(&mut self) {
        let f = &mut self.0;
        while f.last() == Some(&Mint::raw(0)) {
            f.pop();
        }
    }

    pub fn inv_until(&self, len: usize) -> Self {
        let Ok(g0) = self[0].inv() else {
            panic!("self[0] should be invertible");
        };
        let mut g = Self::new(vec![g0]);
        while g.len() < len {
            let m = g.len();
            let f = self.prefix(m * 2);
            g = (-f * &g + Mint::new(2)) * g;
            g.resize(m * 2);
        }
        g.resize(len);
        g
    }
    pub fn inv(&self) -> Self {
        self.inv_until(self.len())
    }
}

impl<T> Index<usize> for Fps<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}
impl<T> IndexMut<usize> for Fps<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl<const M: u128> AddAssign<&Fps<Mint<M>>> for Fps<Mint<M>> {
    fn add_assign(&mut self, rhs: &Fps<Mint<M>>) {
        if self.len() < rhs.len() {
            self.resize(rhs.len());
        }
        for (i, e) in rhs.iter().enumerate() {
            self[i] += e;
        }
    }
}
impl<const M: u128> AddAssign<Fps<Mint<M>>> for Fps<Mint<M>> {
    fn add_assign(&mut self, rhs: Fps<Mint<M>>) {
        *self += &rhs;
    }
}
impl<const M: u128> AddAssign<Mint<M>> for Fps<Mint<M>> {
    fn add_assign(&mut self, rhs: Mint<M>) {
        if self.is_empty() {
            self.resize(1);
        }
        self[0] += rhs;
    }
}

impl<const M: u128> Add<Fps<Mint<M>>> for Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn add(mut self, rhs: Fps<Mint<M>>) -> Self::Output {
        self += rhs;
        self
    }
}
impl<const M: u128> Add<&Fps<Mint<M>>> for Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn add(mut self, rhs: &Fps<Mint<M>>) -> Self::Output {
        self += rhs;
        self
    }
}
impl<const M: u128> Add<Fps<Mint<M>>> for &Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn add(self, rhs: Fps<Mint<M>>) -> Self::Output {
        let mut f = self.clone();
        f += rhs;
        f
    }
}
impl<const M: u128> Add<&Fps<Mint<M>>> for &Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn add(self, rhs: &Fps<Mint<M>>) -> Self::Output {
        let mut f = self.clone();
        f += rhs;
        f
    }
}
impl<const M: u128> Add<Mint<M>> for Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn add(mut self, rhs: Mint<M>) -> Self::Output {
        self += rhs;
        self
    }
}
impl<const M: u128> Add<Mint<M>> for &Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn add(self, rhs: Mint<M>) -> Self::Output {
        let mut f = self.clone();
        f += rhs;
        f
    }
}

impl<const M: u128> SubAssign<&Fps<Mint<M>>> for Fps<Mint<M>> {
    fn sub_assign(&mut self, rhs: &Fps<Mint<M>>) {
        if self.len() < rhs.len() {
            self.resize(rhs.len());
        }
        for (i, e) in rhs.iter().enumerate() {
            self[i] -= e;
        }
    }
}
impl<const M: u128> SubAssign<Fps<Mint<M>>> for Fps<Mint<M>> {
    fn sub_assign(&mut self, rhs: Fps<Mint<M>>) {
        *self -= &rhs;
    }
}
impl<const M: u128> SubAssign<Mint<M>> for Fps<Mint<M>> {
    fn sub_assign(&mut self, rhs: Mint<M>) {
        if self.is_empty() {
            self.resize(1);
        }
        self[0] -= rhs;
    }
}
impl<const M: u128> Sub<Fps<Mint<M>>> for Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn sub(mut self, rhs: Fps<Mint<M>>) -> Self::Output {
        self -= rhs;
        self
    }
}
impl<const M: u128> Sub<&Fps<Mint<M>>> for Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn sub(mut self, rhs: &Fps<Mint<M>>) -> Self::Output {
        self -= rhs;
        self
    }
}
impl<const M: u128> Sub<Fps<Mint<M>>> for &Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn sub(self, rhs: Fps<Mint<M>>) -> Self::Output {
        let mut f = self.clone();
        f -= rhs;
        f
    }
}
impl<const M: u128> Sub<&Fps<Mint<M>>> for &Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn sub(self, rhs: &Fps<Mint<M>>) -> Self::Output {
        let mut f = self.clone();
        f -= rhs;
        f
    }
}
impl<const M: u128> Sub<Mint<M>> for Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn sub(mut self, rhs: Mint<M>) -> Self::Output {
        self -= rhs;
        self
    }
}
impl<const M: u128> Sub<Mint<M>> for &Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn sub(self, rhs: Mint<M>) -> Self::Output {
        let mut f = self.clone();
        f -= rhs;
        f
    }
}

impl<const M: u128> Mul<Fps<Mint<M>>> for Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn mul(self, rhs: Fps<Mint<M>>) -> Self::Output {
        &self * &rhs
    }
}
impl<const M: u128> Mul<&Fps<Mint<M>>> for Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn mul(self, rhs: &Fps<Mint<M>>) -> Self::Output {
        &self * rhs
    }
}
impl<const M: u128> Mul<Fps<Mint<M>>> for &Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn mul(self, rhs: Fps<Mint<M>>) -> Self::Output {
        self * &rhs
    }
}
impl<const M: u128> Mul<&Fps<Mint<M>>> for &Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn mul(self, rhs: &Fps<Mint<M>>) -> Self::Output {
        Fps::new(convolution_arbitrary(&self.0, &rhs.0))
    }
}

impl<const M: u128> MulAssign<Fps<Mint<M>>> for Fps<Mint<M>> {
    fn mul_assign(&mut self, rhs: Fps<Mint<M>>) {
        *self = &*self * rhs;
    }
}
impl<const M: u128> MulAssign<&Fps<Mint<M>>> for Fps<Mint<M>> {
    fn mul_assign(&mut self, rhs: &Fps<Mint<M>>) {
        *self = &*self * rhs;
    }
}
impl<const M: u128> Neg for Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn neg(mut self) -> Self::Output {
        for a in self.iter_mut() {
            *a = -*a;
        }
        self
    }
}
impl<const M: u128> Neg for &Fps<Mint<M>> {
    type Output = Fps<Mint<M>>;
    fn neg(self) -> Self::Output {
        let f = self.clone();
        -f
    }
}

impl<T, U: Into<T>> From<Vec<U>> for Fps<T> {
    fn from(value: Vec<U>) -> Self {
        Self::new(value.into_iter().map(U::into).collect())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct DynamicFps(pub DynamicModInt);

impl DynamicFps {
    pub fn new(mo: DynamicModInt) -> Self {
        Self(mo)
    }
    /// 係数列末尾の 0 を全て落とす
    pub fn shrink(&self, f: &mut Vec<u128>) {
        while f.last() == Some(&0) {
            f.pop();
        }
    }
    pub fn prefix(&self, f: &[u128], len: usize) -> Vec<u128> {
        if len <= f.len() {
            f[..len].to_owned()
        } else {
            let mut f = f.to_owned();
            f.resize(len, 0);
            f
        }
    }
    pub fn add_assign(&self, a: &mut Vec<u128>, b: &[u128]) {
        if a.len() < b.len() {
            a.resize(b.len(), 0);
        }
        for (i, bi) in b.iter().enumerate() {
            a[i] = self.0.add(a[i], *bi);
        }
    }
    pub fn mul(&self, a: &[u128], b: &[u128]) -> Vec<u128> {
        self.0.convolution_arbitrary(a, b)
    }
    pub fn neg(&self, a: &[u128]) -> Vec<u128> {
        a.iter().map(|x| self.0.neg(*x)).collect()
    }
    pub fn eval(&self, f: &[u128], rc: u128) -> u128 {
        f.iter()
            .rev()
            .fold(0, |acc, fi| self.0.add(self.0.mul(acc, rc), *fi))
    }
}

impl DynamicFps {
    pub fn inv_until(&self, f: &[u128], len: usize) -> Result<Vec<u128>, u128> {
        assert!(!f.is_empty());
        let g0 = self.0.inv(f[0])?;
        let mut g = vec![g0];
        while g.len() < len {
            let m = g.len();
            let f_ = self.prefix(f, m * 2);
            let mut h = self.mul(&self.neg(&f_), &g);
            h[0] = self.0.add(h[0], self.0.mr(2));
            g = self.mul(&g, &h);
            g.resize(m * 2, 0);
        }
        g.resize(len, 0);
        Ok(g)
    }
    pub fn inv(&self, f: &[u128]) -> Result<Vec<u128>, u128> {
        self.inv_until(f, f.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Mint9 = Mint<998244353>;
    type Fps9 = Fps<Mint9>;

    #[test]
    fn test_inv() {
        let f = Fps9::from(vec![1; 10]);
        let mut g = f.inv();
        g.shrink();
        assert_eq!(g, Fps9::from(vec![1, -1]));

        let f = Fps9::from(vec![5, 4, 3, 2, 1]);
        assert_eq!(
            f.inv(),
            Fps9::from(vec![598946612, 718735934, 862483121, 635682004, 163871793])
        );
    }
}
