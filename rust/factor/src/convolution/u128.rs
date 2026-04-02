use crate::modint::u128::{Modulus, StaticModInt};

/// NTT 順変換．
///
/// 入力が natural order のとき，出力は bit-reversal order．
pub fn butterfly<const M: u128>(a: &mut [StaticModInt<M>]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let h = n.ilog2();
    let fore = StaticModInt::<M>::CACHE.fore;
    for ph in 0..h {
        let w = 1 << ph;
        let p = 1 << (h - ph - 1);
        let mut now = StaticModInt::<M>::one();
        for s in 0..w {
            let offset = s << (h - ph);
            for i in 0..p {
                let l = a[offset + i];
                let r = a[offset + i + p] * now;
                a[offset + i] = l + r;
                a[offset + i + p] = l - r;
            }
            now *= fore[s.trailing_ones() as usize];
        }
    }
}

/// NTT 逆変換．
///
/// 入力が bit-reversal order のとき，出力は natural order．
pub fn butterfly_inv<const M: u128>(a: &mut [StaticModInt<M>], divide_n: bool) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let h = n.ilog2();
    let back = StaticModInt::<M>::CACHE.back;
    for ph in (0..h).rev() {
        let w = 1 << ph;
        let p = 1 << (h - ph - 1);
        let mut now = StaticModInt::<M>::one();
        for s in 0..w {
            let offset = s << (h - ph);
            for i in 0..p {
                // let l = a[offset + i];
                // let r = a[offset + i + p] * now;
                // a[offset + i] = l + r;
                // a[offset + i + p] = l - r;
                let l = a[offset + i];
                let r = a[offset + i + p];
                a[offset + i] = l + r;
                a[offset + i + p] = (l - r) * now;
            }
            now *= back[s.trailing_ones() as usize];
        }
    }
    if divide_n {
        let ni = StaticModInt::new(n as _).inv().unwrap();
        for ai in a.iter_mut() {
            *ai *= ni;
        }
    }
}

pub fn convolution_proth<const M: u128>(
    a: &[StaticModInt<M>],
    b: &[StaticModInt<M>],
) -> Vec<StaticModInt<M>> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let (la, lb) = (a.len(), b.len());
    let lc = la + lb - 1;
    let n = lc.next_power_of_two();
    assert!(M & (n as u128 - 1) == 1, "length {lc} is too long for NTT mod {M}");

    let (mut a, mut b) = (a.to_owned(), b.to_owned());
    a.resize(n, StaticModInt::raw(0));
    b.resize(n, StaticModInt::raw(0));
    butterfly(&mut a);
    butterfly(&mut b);
    for (a, b) in a.iter_mut().zip(&b) {
        *a *= b;
    }
    butterfly_inv(&mut a, true);
    a.resize(lc, StaticModInt::raw(0));
    a
}

pub fn convolution_naive<const M: u128>(
    a: &[StaticModInt<M>],
    b: &[StaticModInt<M>],
) -> Vec<StaticModInt<M>> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let (la, lb) = (a.len(), b.len());
    let lc = la + lb - 1;
    let mut c = vec![StaticModInt::raw(0); lc];
    for (i, ai) in a.iter().enumerate() {
        for (j, bj) in b.iter().enumerate() {
            c[i + j] += ai * bj;
        }
    }
    c
}

#[cfg(test)]
mod tests {
    use crate::utility::Sfc64;

    use super::*;

    #[test]
    fn test_butterfly_id() {
        type Mint = StaticModInt<97>;
        let mut rng = Sfc64::new(0);
        for h in 0..6 {
            for _ in 0..100 {
                let mut a = vec![Mint::new(0); 1 << h];
                for ai in a.iter_mut() {
                    *ai = Mint::new(rng.next_range(0..Mint::MOD));
                }

                let mut a_ = a.clone();
                butterfly(&mut a_);
                butterfly_inv(&mut a_, true);
                assert_eq!(a_, a);

                let mut a_ = a.clone();
                butterfly_inv(&mut a_, true);
                butterfly(&mut a_);
                assert_eq!(a_, a);
            }
        }
    }

    #[test]
    fn test_convolution_proth() {
        type Mint = StaticModInt<65537>;
        let mut rng = Sfc64::new(0);
        for _ in 0..100 {
            let mut a = vec![Mint::new(0); rng.next_range(0..100) as _];
            for e in a.iter_mut() {
                *e = Mint::new(rng.next_range(0..Mint::MOD));
            }
            let mut b = vec![Mint::new(0); rng.next_range(0..100) as _];
            for e in b.iter_mut() {
                *e = Mint::new(rng.next_range(0..Mint::MOD));
            }
            assert_eq!(convolution_proth(&a, &b), convolution_naive(&a, &b));
        }
    }
}
