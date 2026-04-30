use std::{
    collections::VecDeque,
    fmt::{Debug, Display},
    iter,
};

use crate::{
    convolution::u128::DynamicConvolution,
    modint::u128::{DynamicModInt as Mint, gcd},
    multipoint_evaluation::u128::DynamicMultipointEvaluation,
    utility::{Sfc64, Sieve, bisect_left},
    wrapper::Factorize,
};

/// Montgomery curve B y^2 = x^3 + A x^2 + x mod n.
///
/// 点は (X, Z) をそれぞれ Montgomery form で管理する．
#[derive(Debug, Clone, Copy)]
pub struct Curve {
    /// (A + 2)/4, in Montgomery form
    a24: u128,
    mo: Mint,
}

type Point = (u128, u128);

impl Curve {
    fn _add(&self, rx: u128, ry: u128) -> u128 {
        self.mo.add(rx, ry)
    }
    fn _sub(&self, rx: u128, ry: u128) -> u128 {
        self.mo.sub(rx, ry)
    }
    fn _mul(&self, rx: u128, ry: u128) -> u128 {
        self.mo.mul(rx, ry)
    }

    /// a24 = (A + 2)/4 in Montgomery form なる curve.
    pub fn new(a24: u128, mo: Mint) -> Self {
        Self { a24, mo }
    }
    /// Suyama's parametrization.
    ///
    /// Ok((curve, initial P)) または Err(divisor) を返す．
    pub fn init_suyama(s: u128, mo: Mint) -> Result<(Self, Point), u128> {
        let rs = mo.mr(s);
        let u = mo.sub(mo.mul(rs, rs), mo.mr(5));
        let v = mo.mul(rs, mo.mr(4));
        // (a+2)/4 = (u-v)^3 (3u + v) / (16 u^3 v)
        let t1 = mo.pow(mo.sub(u, v), 3);
        let t2 = mo.add(mo.mul(u, mo.mr(3)), v);
        let t3 = mo.mul(mo.pow(u, 3), v);
        let num = mo.mul(t1, t2);
        let den = mo.mul(mo.mr(16), t3);
        let a24 = mo.div(num, den)?;
        let p = (mo.pow(u, 3), mo.pow(v, 3));
        Ok((Self::new(a24, mo), p))
    }

    /// 単位元．
    pub fn zero(&self) -> Point {
        (self.mo.r1, 0)
    }
    /// [2] P = P + P.
    pub fn double(&self, p: Point) -> Point {
        let (x, z) = p;
        let add = self._add(x, z);
        let sub = self._sub(x, z);
        let add2 = self._mul(add, add);
        let sub2 = self._mul(sub, sub);
        let nx = self._mul(add2, sub2);

        let xz4 = self._sub(add2, sub2);
        let c1 = self._mul(self.a24, xz4);
        let c2 = self._add(sub2, c1);
        let nz = self._mul(xz4, c2);
        (nx, nz)
    }
    /// P + Q given with diff = P - Q.
    pub fn add(&self, p: Point, q: Point, diff: Point) -> Point {
        let v0 = self._add(p.0, p.1);
        let v1 = self._sub(q.0, q.1);
        let t1 = self._mul(v0, v1);
        let v0 = self._sub(p.0, p.1);
        let v1 = self._add(q.0, q.1);
        let t2 = self._mul(v0, v1);
        let add = self._add(t1, t2);
        let add2 = self._mul(add, add);
        let sub = self._sub(t1, t2);
        let sub2 = self._mul(sub, sub);
        (self._mul(diff.1, add2), self._mul(diff.0, sub2))
    }
    /// [m] P.
    pub fn scale(&self, p: Point, m: u128) -> Point {
        match m {
            0 => return self.zero(),
            1 => return p,
            2 => return self.double(p),
            _ => {}
        }
        if p.1 == 0 {
            return self.zero();
        }
        let m1 = m - 1;
        // (0, 1)
        let (mut p0, mut p1) = (self.zero(), p);
        for i in (0..u128::BITS - m1.leading_zeros()).rev() {
            // n, n+1, 1 => 2n+1
            let p3 = self.add(p1, p0, p);
            if m1 >> i & 1 == 1 {
                // (n, n+1) => (2n+1, 2n+2)
                (p0, p1) = (p3, self.double(p1));
            } else {
                // (n, n+1) => (2n, 2n+1)
                (p0, p1) = (self.double(p0), p3);
            }
        }
        // (m1, m+1 = m)
        p1
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EcmBound {
    pub b1: u128,
    pub b2: u128,
}

pub trait BoundStrategy: Clone {
    /// use `.0` bound for `.1` times
    fn generate_bound(&self, n: u128) -> impl Iterator<Item = (EcmBound, usize)>;
}
pub trait Stage2Strategy {
    fn check_stage2(
        &self,
        bound: EcmBound,
        mo: Mint,
        c: &Curve,
        point: (u128, u128),
    ) -> Option<u128>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExponentialBound {
    initial: EcmBound,
    rate: u128,
    rep: usize,
}

impl ExponentialBound {
    pub fn new(initial: EcmBound, rate: u128, rep: usize) -> Self {
        Self { initial, rate, rep }
    }
}
impl BoundStrategy for ExponentialBound {
    fn generate_bound(&self, _n: u128) -> impl Iterator<Item = (EcmBound, usize)> {
        iter::repeat(0).scan(self.initial, |acc, _| {
            let ans = Some((*acc, self.rep));
            acc.b1 *= self.rate;
            acc.b2 *= self.rate;
            ans
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Stage1Only;

impl Stage2Strategy for Stage1Only {
    fn check_stage2(
        &self,
        _bound: EcmBound,
        _mo: Mint,
        _c: &Curve,
        _point: (u128, u128),
    ) -> Option<u128> {
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckOdd;

impl Stage2Strategy for CheckOdd {
    fn check_stage2(
        &self,
        bound: EcmBound,
        mo: Mint,
        c: &Curve,
        point: (u128, u128),
    ) -> Option<u128> {
        // Stage 2
        const D: usize = 210;
        const COPRIME_RS: [usize; 48] = [
            1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
            101, 103, 107, 109, 113, 121, 127, 131, 137, 139, 143, 149, 151, 157, 163, 167, 169,
            173, 179, 181, 187, 191, 193, 197, 199, 209,
        ];
        let b1 = bound.b1 - bound.b1 % D as u128;
        // rem[r] = c.scale(point, b1 + r)
        let mut rem = vec![c.zero(); D * 2];
        rem[1] = c.scale(point, b1 + 1);
        rem[3] = c.scale(point, b1 + 3);
        let p2 = c.double(point);
        for i in 2..D {
            rem[2 * i + 1] = c.add(rem[2 * i - 1], p2, rem[2 * i - 3]);
        }
        let pd = c.scale(point, D as u128);
        let w2 = bound.b2 as usize / D - bound.b1 as usize / D;
        let mut acc = Vec::with_capacity((w2 + 2) * COPRIME_RS.len());
        acc.push(1);
        for r in COPRIME_RS {
            // check scale(point, r + d * i)
            let (mut p0, mut p1) = (rem[r], rem[D + r]);
            acc.push(mo.mul(acc[acc.len() - 1], p0.1));
            acc.push(mo.mul(acc[acc.len() - 1], p1.1));
            for _ in 0..w2 {
                (p0, p1) = (p1, c.add(p1, pd, p0));
                acc.push(mo.mul(acc[acc.len() - 1], p1.1));
            }
        }
        let g = gcd(acc[acc.len() - 1], mo.n);
        if 1 < g && g < mo.n {
            return Some(g);
        }
        let i = bisect_left(acc.len(), |i| gcd(acc[i], mo.n) > 1);
        if i < acc.len() {
            let g = gcd(acc[i], mo.n);
            if g < mo.n {
                return Some(g);
            }
        }
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UseMultiEval;

impl Stage2Strategy for UseMultiEval {
    fn check_stage2(
        &self,
        bound: EcmBound,
        mo: Mint,
        c: &Curve,
        point: (u128, u128),
    ) -> Option<u128> {
        let d = bound.b2.isqrt() as usize;
        let mut baby = vec![c.zero(); d + 1];
        baby[1] = point;
        baby[2] = c.double(baby[1]);
        for i in 3..=d {
            baby[i] = c.add(baby[i - 1], baby[1], baby[i - 2]);
        }
        let mut giant = vec![c.zero(); d + 1];
        giant[1] = baby[d];
        giant[2] = c.double(giant[1]);
        for i in 3..=d {
            giant[i] = c.add(giant[i - 1], giant[1], giant[i - 2]);
        }
        let baby = match mo.batch_div(&baby) {
            Ok(e) => e,
            Err(d) => {
                return if 1 < d && d < mo.n { Some(d) } else { None };
            }
        };
        let giant = match mo.batch_div(&giant) {
            Ok(e) => e,
            Err(d) => {
                return if 1 < d && d < mo.n { Some(d) } else { None };
            }
        };

        // product of (x - c) for c in baby
        let f_baby = {
            let mut q = baby
                .iter()
                .map(|c| vec![mo.neg(*c), mo.one()])
                .collect::<VecDeque<_>>();
            q.push_back(vec![mo.one()]);
            while q.len() >= 2
                && let Some(f1) = q.pop_front()
                && let Some(f2) = q.pop_front()
            {
                q.push_back(mo.convolution_arbitrary(&f1, &f2));
            }
            q.pop_front().unwrap()
        };
        let vals = match DynamicMultipointEvaluation::new(mo, giant).eval(&f_baby) {
            Ok(e) => e,
            Err(d) => {
                return if 1 < d && d < mo.n { Some(d) } else { None };
            }
        };
        vals.iter().find_map(|&rx| mo.inv(rx).err())
    }
}

#[derive(Debug, Clone)]
pub struct Ecm<T, U> {
    rng: Sfc64,
    sieve: Sieve,
    bound_strategy: T,
    stage2_strategy: U,
}

impl<T: BoundStrategy, U: Stage2Strategy> Ecm<T, U> {
    pub fn new(seed: u64, bound_strategy: T, stage2_strategy: U) -> Self {
        Self {
            rng: Sfc64::new(seed),
            sieve: Sieve::new(1),
            bound_strategy,
            stage2_strategy,
        }
    }
    pub fn check_curve(&mut self, bound: EcmBound, mo: Mint, s: u128) -> Option<u128> {
        let (c, mut point) = match Curve::init_suyama(s, mo) {
            Ok(t) => t,
            Err(d) => return Some(d),
        };

        // Stage 1
        for &p in self.sieve.prime.iter() {
            let mut pe = p;
            while pe * p < bound.b1 {
                pe *= p;
            }
            point = c.scale(point, pe);
        }
        let g = gcd(mo.n, point.1);
        if 1 < g && g < mo.n {
            return Some(g);
        }

        // Stage 2
        self.stage2_strategy.check_stage2(bound, mo, &c, point)
    }
}

impl<T: BoundStrategy, U: Stage2Strategy> Factorize for Ecm<T, U> {
    fn find_factor(&mut self, n: u128) -> u128 {
        let mo = Mint::new(n);
        for (bound, rep) in self.bound_strategy.clone().generate_bound(n) {
            if bound.b1 as usize > self.sieve.lpf.len() {
                self.sieve = Sieve::new(bound.b1 as _)
            }
            for _i in 0..rep {
                let s = self.rng.next_range(6..n - 5);
                if let Some(d) = self.check_curve(bound, mo, s)
                    && 1 < d
                    && d < n
                {
                    // eprintln!("\tfound at {_i}");
                    return d;
                }
            }
            // eprintln!("\textend");
        }
        unreachable!()
    }
}

impl<T: Debug, U: Debug> Display for Ecm<T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Ecm")
            .field("bound_strategy", &self.bound_strategy)
            .field("stage2_strategy", &self.stage2_strategy)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_scale() {
        let n = (1 << 61) - 1;
        // let n = 10007;
        let mo = Mint::new(n);
        let mut rng = Sfc64::new(n as _);
        let d = 100;
        let same = |p: (u128, u128), q: (u128, u128)| mo.mul(p.0, q.1) == mo.mul(p.1, q.0);
        for _ in 0..100 {
            let s = rng.next_range(6..n - 6);
            let Ok((c, p)) = Curve::init_suyama(s, mo) else {
                continue;
            };
            assert!(same(c.double(p), c.scale(p, 2)));
            let (mut p0, mut p1) = (c.zero(), p);
            for i in 2..d {
                let p2 = c.add(p1, p, p0);
                assert!(same(p2, c.scale(p, i as u128)), "s = {s}, {p:?} * {i}");
                assert!(
                    same(c.double(p2), c.scale(p, 2 * i as u128)),
                    "s = {s}, {p:?} * {i} * 2"
                );
                (p0, p1) = (p1, p2);
            }
        }
    }
}
