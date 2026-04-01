use std::fmt::Display;

use crate::{
    dynamic_modint::u128::{ModInt, gcd},
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
    mo: ModInt,
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
    pub fn new(a24: u128, mo: ModInt) -> Self {
        Self { a24, mo }
    }
    /// Suyama's parametrization.
    ///
    /// Ok((curve, initial P)) または Err(divisor) を返す．
    pub fn init_suyama(s: u128, mo: ModInt) -> Result<(Self, Point), u128> {
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

#[derive(Debug, Clone)]
pub struct Ecm {
    rng: Sfc64,
    b1: u128,
    b2: u128,
    sieve: Sieve,
}

impl Ecm {
    pub fn new(seed: u64, b1: u128, b2: u128) -> Self {
        Self {
            rng: Sfc64::new(seed),
            b1,
            b2,
            sieve: Sieve::new(b1 as _),
        }
    }
    pub fn check_curve(&mut self, mo: ModInt, s: u128) -> Option<u128> {
        let (c, mut point) = match Curve::init_suyama(s, mo) {
            Ok(t) => t,
            Err(d) => return Some(d),
        };
        // Stage 1
        for &p in self.sieve.prime.iter() {
            let mut pe = p;
            while pe * p < self.b1 {
                pe *= p;
            }
            point = c.scale(point, pe);
        }
        let g = gcd(mo.n, point.1);
        if 1 < g && g < mo.n {
            return Some(g);
        }
        if self.b1 == self.b2 {
            return None;
        }

        // Stage 2
        const D: usize = 210;
        const COPRIME_RS: [usize; 48] = [
            1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
            101, 103, 107, 109, 113, 121, 127, 131, 137, 139, 143, 149, 151, 157, 163, 167, 169,
            173, 179, 181, 187, 191, 193, 197, 199, 209,
        ];
        let b1 = self.b1 - self.b1 % D as u128;
        // rem[r] = c.scale(point, b1 + r)
        let mut rem = vec![c.zero(); D * 2];
        rem[1] = c.scale(point, b1 + 1);
        rem[3] = c.scale(point, b1 + 3);
        let p2 = c.double(point);
        for i in 2..D {
            rem[2 * i + 1] = c.add(rem[2 * i - 1], p2, rem[2 * i - 3]);
        }
        let pd = c.scale(point, D as u128);
        let w2 = self.b2 as usize / D - self.b1 as usize / D;
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

impl Factorize for Ecm {
    fn find_factor(&mut self, n: u128) -> u128 {
        let mo = ModInt::new(n);
        let (mut c0, mut c1, mut cn) = (0, 0, 0);
        loop {
            for _i in 1usize..=4000 {
                let s = self.rng.next_range(6..n - 5);
                if let Some(d) = self.check_curve(mo, s) {
                    if d == 0 {
                        c0 += 1;
                    } else if d == 1 {
                        c1 += 1;
                    } else if d == n {
                        cn += 1;
                    } else {
                        eprintln!("[{_i}] found: {d}");
                        return d;
                    }
                }
                if _i.is_multiple_of(500) {
                    eprintln!("[{_i}] ({c0}, {c1}, {cn})");
                }
            }
            self.b1 *= 2;
            self.sieve = Sieve::new(self.b1 as _);
            self.b2 *= 2;
            eprintln!(
                "({c0}, {c1}, {cn}), extended to {}, {}",
                self.b1, self.b2
            );
        }
    }
}

impl Display for Ecm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Ecm")
            .field("b1", &self.b1)
            .field("b2", &self.b2)
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
        let mo = ModInt::new(n);
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
