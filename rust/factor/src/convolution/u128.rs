use crate::{
    modint::u128::StaticModInt,
    primality::{is_prime, is_prime_const},
};

pub mod transpose;

/// v_2 (M - 1) =: h として，mod M の位数 2^h の正整数
pub const fn power_2_generator<const M: u128>() -> StaticModInt<M> {
    let mut g = StaticModInt::<M>::one();
    let h = (M - 1).trailing_zeros();
    let e = 1 << (h - 1);
    loop {
        g = g.add(StaticModInt::one());
        if g.pow_const(e).val_const() == M - 1 {
            return g;
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ButterflyCache<T> {
    pub fore: [T; u128::BITS as _],
    pub back: [T; u128::BITS as _],
}

impl<const M: u128> ButterflyCache<StaticModInt<M>> {
    pub const fn new() -> Self {
        // [i]: ord = 2^i
        let mut roots = [StaticModInt::raw(0); u128::BITS as _];
        let mut inv_roots = [StaticModInt::raw(0); u128::BITS as _];
        let g = power_2_generator::<M>();
        let h = (M - 1).trailing_zeros() as usize;
        roots[h] = g;
        if let Ok(ig) = g.inv_const() {
            inv_roots[h] = ig;
        }

        // for i in (0..h).rev()
        let mut i = h;
        while i > 0 {
            i -= 1;
            roots[i] = roots[i + 1].mul_const(roots[i + 1]);
            inv_roots[i] = inv_roots[i + 1].mul_const(inv_roots[i + 1]);
        }

        // [i]: 1^{ 1/2 + 3/2^{i+2} } = -1 * 1^{ 3/2^{i+2} }
        let mut fore = [StaticModInt::raw(0); u128::BITS as _];
        let mut back = [StaticModInt::raw(0); u128::BITS as _];
        // for i in (0..h-1).rev()
        let mut i = h - 1;
        while i > 0 {
            i -= 1;
            fore[i] = roots[i + 1].mul_const(roots[i + 2]).neg();
            back[i] = inv_roots[i + 1].mul_const(inv_roots[i + 2]).neg();
        }

        Self { fore, back }
    }
}
impl<const M: u128> Default for ButterflyCache<StaticModInt<M>> {
    fn default() -> Self {
        Self::new()
    }
}

pub trait HaveCache: Sized {
    const CACHE: Option<ButterflyCache<Self>>;
}

impl<const M: u128> HaveCache for StaticModInt<M> {
    const CACHE: Option<ButterflyCache<Self>> = if is_prime_const(M) {
        Some(ButterflyCache::new())
    } else {
        None
    };
}

/// NTT 順変換．
///
/// 入力が natural order のとき，出力は bit-reversal order．
pub fn butterfly<const M: u128>(a: &mut [StaticModInt<M>]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let h = n.ilog2();
    let fore = StaticModInt::<M>::CACHE.expect("M should be prime").fore;
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
    let back = StaticModInt::<M>::CACHE.expect("M should be prime").back;
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
    assert!(
        (M - 1) & (n as u128 - 1) == 0,
        "length {lc} is too long for NTT mod {M} (0x{M:x})"
    );

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

/// convolution_proth の入出力から StaticModInt を剥がしたもの
pub fn convolution_raw<const M: u128>(a: &[u128], b: &[u128]) -> Vec<u128> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let a = a
        .iter()
        .copied()
        .map(StaticModInt::<M>::new)
        .collect::<Vec<_>>();
    let b = b
        .iter()
        .copied()
        .map(StaticModInt::<M>::new)
        .collect::<Vec<_>>();
    convolution_proth(&a, &b)
        .into_iter()
        .map(|e| e.val())
        .collect::<Vec<_>>()
}

/// 任意 mod 畳み込み．
pub fn convolution_arbitrary<const M: u128>(
    a: &[StaticModInt<M>],
    b: &[StaticModInt<M>],
) -> Vec<StaticModInt<M>> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    if is_prime(M) {
        let (la, lb) = (a.len(), b.len());
        let lc = la + lb - 1;
        let n = lc.next_power_of_two() as u128;
        if (M - 1) & (n - 1) == 0 {
            return convolution_proth(a, b);
        }
    }
    const M1: u128 = 7 << 120 | 1;
    const M2: u128 = 51 << 119 | 1;
    const M3: u128 = 71 << 119 | 1;
    type Mint2 = StaticModInt<M2>;
    type Mint3 = StaticModInt<M3>;

    const M1_INV_M2: Mint2 = match Mint2::new_const(M1).inv_const() {
        Ok(e) => e,
        Err(_) => panic!(),
    };
    const M1M2_INV_M3: Mint3 = match Mint3::new_const(M1)
        .mul_const(Mint3::new_const(M2))
        .inv_const()
    {
        Ok(e) => e,
        Err(_) => panic!(),
    };

    let a = a.iter().map(|e| e.val()).collect::<Vec<_>>();
    let b = b.iter().map(|e| e.val()).collect::<Vec<_>>();
    let c1 = convolution_raw::<M1>(&a, &b);
    let c2 = convolution_raw::<M2>(&a, &b);
    let c3 = convolution_raw::<M3>(&a, &b);

    c1.into_iter()
        .zip(c2)
        .zip(c3)
        .map(|((c1, c2), c3)| {
            let x1 = c1;
            let x2 = ((Mint2::new(c2) - Mint2::new(x1)) * M1_INV_M2).val();
            let x3 = ((Mint3::new(c3) - Mint3::new(x1) - Mint3::new(x2) * Mint3::new(M1))
                * M1M2_INV_M3)
                .val();
            StaticModInt::new(x1)
                + StaticModInt::new(M1) * StaticModInt::new(x2)
                + StaticModInt::new(M1) * StaticModInt::new(M2) * StaticModInt::new(x3)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::{modint::u128::Modulus, utility::Sfc64};

    use super::*;

    fn gen_vector<const M: u128>(rng: &mut Sfc64, n: usize) -> Vec<StaticModInt<M>> {
        let mut a = vec![StaticModInt::new(0); n];
        for ai in a.iter_mut() {
            *ai = StaticModInt::new(rng.next_range(0..M));
        }
        a
    }

    #[test]
    fn test_butterfly_small() {
        type Mint = StaticModInt<97>;
        let g = power_2_generator::<{ Mint::MOD }>();

        for h in 1..6 {
            let rev = (0u8..1 << h)
                .map(|i| (i.reverse_bits() >> 3) as u128)
                .collect::<Vec<_>>();
            for i in 0..1 << h {
                let mut a = vec![Mint::new(0); 1 << h];
                a[i] = Mint::new(1);
                butterfly(&mut a);
                let b = (0..1 << h)
                    .map(|j| g.pow(i as u128 * rev[j]))
                    .collect::<Vec<_>>();
                assert_eq!(a, b, "h = {h}, i = {i}");

                butterfly_inv(&mut a, true);
                for (j, aj) in a.iter().enumerate() {
                    assert_eq!(*aj, Mint::new(if j == i { 1 } else { 0 }));
                }
            }
        }
    }

    #[test]
    fn test_butterfly_id() {
        type Mint = StaticModInt<97>;
        let mut rng = Sfc64::new(0);
        for h in 0..6 {
            for _ in 0..100 {
                let a: Vec<Mint> = gen_vector(&mut rng, 1 << h);

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
            let n1 = rng.next_range(0..100) as usize;
            let a: Vec<Mint> = gen_vector(&mut rng, n1);
            let n2 = rng.next_range(0..100) as usize;
            let b: Vec<Mint> = gen_vector(&mut rng, n2);
            assert_eq!(convolution_proth(&a, &b), convolution_naive(&a, &b));
        }
    }

    #[test]
    fn test_convolution_arbitrary() {
        let mut rng = Sfc64::new(0);
        for _ in 0..100 {
            type Mint = StaticModInt<65537>;
            let n1 = rng.next_range(0..100) as usize;
            let a: Vec<Mint> = gen_vector(&mut rng, n1);
            let n2 = rng.next_range(0..100) as usize;
            let b: Vec<Mint> = gen_vector(&mut rng, n2);
            assert_eq!(convolution_arbitrary(&a, &b), convolution_naive(&a, &b));
        }
        for _ in 0..100 {
            type Mint = StaticModInt<{ 1 << 126 | 1 }>;
            let n1 = rng.next_range(0..100) as usize;
            let a: Vec<Mint> = gen_vector(&mut rng, n1);
            let n2 = rng.next_range(0..100) as usize;
            let b: Vec<Mint> = gen_vector(&mut rng, n2);
            assert_eq!(convolution_arbitrary(&a, &b), convolution_naive(&a, &b));
        }
    }

    #[test]
    fn test_power_2_generator() {
        assert_eq!(power_2_generator::<3>().val(), 2);
        assert_eq!(power_2_generator::<5>().val(), 2);
        assert_eq!(power_2_generator::<7>().val(), 6);
        assert_eq!(power_2_generator::<11>().val(), 10);
        assert_eq!(power_2_generator::<13>().val(), 5);
        assert_eq!(power_2_generator::<17>().val(), 3);
        assert_eq!(power_2_generator::<19>().val(), 18);
        assert_eq!(power_2_generator::<23>().val(), 22);
        assert_eq!(power_2_generator::<29>().val(), 12);
        assert_eq!(power_2_generator::<31>().val(), 30);
        assert_eq!(power_2_generator::<37>().val(), 6);
        assert_eq!(power_2_generator::<41>().val(), 3);
        assert_eq!(power_2_generator::<43>().val(), 42);
        assert_eq!(power_2_generator::<47>().val(), 46);
        assert_eq!(power_2_generator::<53>().val(), 23);
        assert_eq!(power_2_generator::<59>().val(), 58);
        assert_eq!(power_2_generator::<61>().val(), 11);
        assert_eq!(power_2_generator::<67>().val(), 66);
        assert_eq!(power_2_generator::<71>().val(), 70);
        assert_eq!(power_2_generator::<73>().val(), 10);
        assert_eq!(power_2_generator::<79>().val(), 78);
        assert_eq!(power_2_generator::<83>().val(), 82);
        assert_eq!(power_2_generator::<89>().val(), 12);
        assert_eq!(power_2_generator::<97>().val(), 19);
    }
}
