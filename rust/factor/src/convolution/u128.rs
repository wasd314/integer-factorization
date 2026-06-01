use crate::{
    garner::u128::{Garner3, M1, M2, M3},
    modint::u128::{DynamicModInt, Modulus, StaticModInt},
    primality::{is_prime, is_prime_const},
};

/// v_2 (M - 1) =: h として，mod M の位数 2^h の正整数．
///
/// M は素数なら存在する．
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
pub fn ntt<const M: u128>(a: &mut [StaticModInt<M>]) {
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
pub fn ntt_inv<const M: u128>(a: &mut [StaticModInt<M>], divide_n: bool) {
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
    ntt(&mut a);
    ntt(&mut b);
    for (a, b) in a.iter_mut().zip(&b) {
        *a *= b;
    }
    ntt_inv(&mut a, true);
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

/// convolution_proth の入出力から StaticModInt を剥がしたもの．
///
/// 入出力とも Montgomery 表現ではない．
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

    let a = a.iter().map(|e| e.val()).collect::<Vec<_>>();
    let b = b.iter().map(|e| e.val()).collect::<Vec<_>>();
    let c1 = convolution_raw::<M1>(&a, &b);
    let c2 = convolution_raw::<M2>(&a, &b);
    let c3 = convolution_raw::<M3>(&a, &b);
    let g: Garner3 = Garner3::new(StaticModInt::<M>::MON);
    g.reconstruct_vector(c1, c2, c3)
        .into_iter()
        .map(StaticModInt::raw)
        .collect()
}

/// NTT 順変換の転置．
///
/// 入力が natural order のとき，出力は bit-reversal order．
pub fn ntt_transpose<const M: u128>(a: &mut [StaticModInt<M>]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    ntt_inv(a, false);
    a[1..].reverse();
}

/// NTT 逆変換の転置．
///
/// 入力が bit-reversal order のとき，出力は natural order．
pub fn ntt_inv_transpose<const M: u128>(a: &mut [StaticModInt<M>], divide_n: bool) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    a[1..].reverse();
    ntt(a);
    if divide_n {
        let ni = StaticModInt::new(n as _).inv().unwrap();
        for ai in a.iter_mut() {
            *ai *= ni;
        }
    }
}

/// Middle product.
///
/// la-1 次多項式 `a` と lc-1 次多項式 `c` に対し，rev(a) * c の [la-1, lc) 次の係数を取り出した lc-la 次多項式 `b` を返す．
/// 固定した `a` に対する線型写像 `b` ⟼ `a`*`b` の転置写像．
///
/// `b[i] = sum[j in 0..=la-1] a[j] * c[i + j]`.
///
/// # Constraints
///
/// - la > 0
/// - la ≦ lc
pub fn middle_product_proth<const M: u128>(
    a: &[StaticModInt<M>],
    c: &[StaticModInt<M>],
) -> Vec<StaticModInt<M>> {
    let (la, lc) = (a.len(), c.len());
    assert!(0 < la && la <= lc);
    let n = lc.next_power_of_two();
    assert!(
        (M - 1) & (n as u128 - 1) == 0,
        "length {lc} is too long for NTT mod {M} (0x{M:x})"
    );

    let (mut a, mut c) = (a.to_owned(), c.to_owned());
    a.reverse();
    a.resize(n, StaticModInt::raw(0));
    c.resize(n, StaticModInt::raw(0));
    ntt(&mut a);
    ntt(&mut c);
    for (a, c) in a.iter_mut().zip(&c) {
        *a *= c;
    }
    ntt_inv(&mut a, true);
    a[la - 1..lc].to_owned()
}

/// middle_product_proth の入出力から StaticModInt を剥がしたもの．
///
/// 入出力とも Montgomery 表現ではない．
pub fn middle_product_raw<const M: u128>(a: &[u128], c: &[u128]) -> Vec<u128> {
    let a = a
        .iter()
        .copied()
        .map(StaticModInt::<M>::new)
        .collect::<Vec<_>>();
    let c = c
        .iter()
        .copied()
        .map(StaticModInt::<M>::new)
        .collect::<Vec<_>>();
    middle_product_proth(&a, &c)
        .into_iter()
        .map(|e| e.val())
        .collect::<Vec<_>>()
}

/// 任意 mod Middle product．
///
/// la-1 次多項式 `a` と lc-1 次多項式 `c` に対し，rev(a) * c の [la-1, lc) 次の係数を取り出した lc-la 次多項式 `b` を返す．
/// 固定した `a` に対する線型写像 `b` ⟼ `a`*`b` の転置写像．
///
/// `b[i] = sum[j in 0..=la-1] a[j] * c[i + j]`.
///
/// # Constraints
///
/// - la > 0
/// - la ≦ lc
pub fn middle_product_arbitrary<const M: u128>(
    a: &[StaticModInt<M>],
    c: &[StaticModInt<M>],
) -> Vec<StaticModInt<M>> {
    if is_prime_const(M) {
        let lc = c.len();
        let n = lc.next_power_of_two() as u128;
        if (M - 1) & (n - 1) == 0 {
            return middle_product_proth(a, c);
        }
    }

    let a = a.iter().map(|e| e.val()).collect::<Vec<_>>();
    let c = c.iter().map(|e| e.val()).collect::<Vec<_>>();
    let c1 = middle_product_raw::<M1>(&a, &c);
    let c2 = middle_product_raw::<M2>(&a, &c);
    let c3 = middle_product_raw::<M3>(&a, &c);

    let g: Garner3 = Garner3::new(StaticModInt::<M>::MON);
    g.reconstruct_vector(c1, c2, c3)
        .into_iter()
        .map(StaticModInt::raw)
        .collect()
}

pub trait DynamicConvolution {
    /// 愚直な畳み込み．
    ///
    /// 入出力とも Montgomery 表現．
    fn convolution_naive(&self, a: &[u128], b: &[u128]) -> Vec<u128>;
    /// Karatsuba 法を用いた任意 mod 畳み込み．
    ///
    /// 入出力とも Montgomery 表現．
    fn convolution_karatsuba(&self, a: &[u128], b: &[u128]) -> Vec<u128>;
    /// 任意 mod 畳み込み．
    ///
    /// 入出力とも Montgomery 表現．
    fn convolution_arbitrary(&self, a: &[u128], b: &[u128]) -> Vec<u128>;
    /// 任意 mod Middle product．
    ///
    /// 入出力とも Montgomery 表現．
    fn middle_product_arbitrary(&self, a: &[u128], c: &[u128]) -> Vec<u128>;
}

impl DynamicConvolution for DynamicModInt {
    fn convolution_naive(&self, a: &[u128], b: &[u128]) -> Vec<u128> {
        if a.is_empty() || b.is_empty() {
            return vec![];
        }
        let (la, lb) = (a.len(), b.len());
        let lc = la + lb - 1;
        let mut c = vec![0; lc];
        for (i, ai) in a.iter().enumerate() {
            for (j, bj) in b.iter().enumerate() {
                c[i + j] = self.add(c[i + j], self.mul(*ai, *bj));
            }
        }
        c
    }

    fn convolution_karatsuba(&self, a: &[u128], b: &[u128]) -> Vec<u128> {
        if a.is_empty() || b.is_empty() {
            return vec![];
        }
        let (a, b) = if a.len() > b.len() { (b, a) } else { (a, b) };
        if b.len() == 1 {
            return vec![self.mul(a[0], b[0])];
        }
        // a.len() <= b.len()
        let n = b.len().div_ceil(2);
        let cl = a.len() + b.len() - 1;
        if a.len() <= n {
            let mut c0 = self.convolution_karatsuba(a, &b[..n]);
            let c1 = self.convolution_karatsuba(a, &b[n..]);
            c0.resize(cl, 0);
            for (i, e) in c1.into_iter().enumerate() {
                c0[n + i] = self.add(c0[n + i], e);
            }
            c0
        } else {
            let mut c0 = self.convolution_karatsuba(&a[..n], &b[..n]);
            let c2 = self.convolution_karatsuba(&a[n..], &b[n..]);
            let mut da = a[..n].to_owned();
            for (i, e) in a[n..].iter().enumerate() {
                da[i] = self.add(da[i], *e);
            }
            let mut db = b[..n].to_owned();
            for (i, e) in b[n..].iter().enumerate() {
                db[i] = self.add(db[i], *e);
            }
            let mut c1 = self.convolution_karatsuba(&da, &db);
            c1.resize(c1.len().max(c0.len()).max(c2.len()), 0);
            // c1 -= c0
            for (i, e) in c0.iter().enumerate() {
                c1[i] = self.sub(c1[i], *e);
            }
            // c1 -= c2
            for (i, e) in c2.iter().enumerate() {
                c1[i] = self.sub(c1[i], *e);
            }
            // total
            c0.resize(cl, 0);
            for (i, e) in c1.iter().enumerate() {
                c0[n + i] = self.add(c0[n + i], *e);
            }
            for (i, e) in c2.iter().enumerate() {
                c0[n * 2 + i] = self.add(c0[n * 2 + i], *e);
            }
            c0
        }
    }

    fn convolution_arbitrary(&self, a: &[u128], b: &[u128]) -> Vec<u128> {
        if a.is_empty() || b.is_empty() {
            return vec![];
        }

        let a = a.iter().map(|&rx| self.val(rx)).collect::<Vec<_>>();
        let b = b.iter().map(|&rx| self.val(rx)).collect::<Vec<_>>();
        let c1 = convolution_raw::<M1>(&a, &b);
        let c2 = convolution_raw::<M2>(&a, &b);
        let c3 = convolution_raw::<M3>(&a, &b);

        let g: Garner3 = Garner3::new(*self);
        g.reconstruct_vector(c1, c2, c3)
    }
    fn middle_product_arbitrary(&self, a: &[u128], c: &[u128]) -> Vec<u128> {
        let a = a.iter().map(|&rx| self.val(rx)).collect::<Vec<_>>();
        let c = c.iter().map(|&rx| self.val(rx)).collect::<Vec<_>>();
        let c1 = middle_product_raw::<M1>(&a, &c);
        let c2 = middle_product_raw::<M2>(&a, &c);
        let c3 = middle_product_raw::<M3>(&a, &c);

        let g: Garner3 = Garner3::new(*self);
        g.reconstruct_vector(c1, c2, c3)
    }
}

#[cfg(test)]
mod tests {
    use crate::{modint::u128::Modulus, utility::Sfc64};

    use super::*;

    fn gen_vector<const M: u128>(rng: &mut Sfc64, n: usize) -> Vec<StaticModInt<M>> {
        rng.next_vector(0..M, n)
            .into_iter()
            .map(StaticModInt::new)
            .collect()
    }

    #[test]
    fn test_ntt_small() {
        type Mint = StaticModInt<97>;
        let g = power_2_generator::<{ Mint::MOD }>();

        for h in 1..6 {
            let rev = (0u8..1 << h)
                .map(|i| (i.reverse_bits() >> 3) as u128)
                .collect::<Vec<_>>();
            for i in 0..1 << h {
                let mut a = vec![Mint::new(0); 1 << h];
                a[i] = Mint::new(1);
                ntt(&mut a);
                let b = (0..1 << h)
                    .map(|j| g.pow(i as u128 * rev[j]))
                    .collect::<Vec<_>>();
                assert_eq!(a, b, "h = {h}, i = {i}");

                ntt_inv(&mut a, true);
                for (j, aj) in a.iter().enumerate() {
                    assert_eq!(*aj, Mint::new(if j == i { 1 } else { 0 }));
                }
            }
        }
    }

    #[test]
    fn test_ntt_identity() {
        type Mint = StaticModInt<97>;
        let mut rng = Sfc64::new(0);
        for h in 0..6 {
            for _ in 0..100 {
                let a: Vec<Mint> = gen_vector(&mut rng, 1 << h);

                let mut a_ = a.clone();
                ntt(&mut a_);
                ntt_inv(&mut a_, true);
                assert_eq!(a_, a);

                let mut a_ = a.clone();
                ntt_inv(&mut a_, true);
                ntt(&mut a_);
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
    fn test_dynamic_convolution_arbitrary() {
        let mut rng = Sfc64::new(0);
        for mo in [
            DynamicModInt::new(998244353),
            DynamicModInt::new(1001001001),
            DynamicModInt::new(1 << 126 | 1),
            DynamicModInt::new((1 << 127) - 1),
        ] {
            for _ in 0..100 {
                let n1 = rng.next_range(0..100) as usize;
                let a = rng
                    .next_vector(0..mo.n, n1)
                    .into_iter()
                    .map(|x| mo.mr(x))
                    .collect::<Vec<_>>();
                let n2 = rng.next_range(0..100) as usize;
                let b = rng
                    .next_vector(0..mo.n, n2)
                    .into_iter()
                    .map(|x| mo.mr(x))
                    .collect::<Vec<_>>();
                assert_eq!(
                    mo.convolution_arbitrary(&a, &b),
                    mo.convolution_naive(&a, &b)
                );
                assert_eq!(
                    mo.convolution_karatsuba(&a, &b),
                    mo.convolution_naive(&a, &b)
                );
            }
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

    #[test]
    fn check_matrix_ntt() {
        type Mint = StaticModInt<97>;
        // ntt
        for h in 1..6 {
            let n = 1 << h;
            // from primal ^ T
            let mut m_primal = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                ntt(&mut a);
                m_primal[i] = a;
            }
            // from transposed
            let mut m_transposed = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                ntt_transpose(&mut a);
                for j in 0..n {
                    m_transposed[j][i] = a[j];
                }
            }
            assert_eq!(m_primal, m_transposed);
        }
        // ntt_inv, true
        for h in 1..6 {
            let n = 1 << h;
            // from primal ^ T
            let mut m_primal = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                ntt_inv(&mut a, true);
                m_primal[i] = a;
            }
            // from transposed
            let mut m_transposed = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                ntt_inv_transpose(&mut a, true);
                for j in 0..n {
                    m_transposed[j][i] = a[j];
                }
            }
            assert_eq!(m_primal, m_transposed);
        }
        // ntt_inv, false
        for h in 1..6 {
            let n = 1 << h;
            // from primal ^ T
            let mut m_primal = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                ntt_inv(&mut a, false);
                m_primal[i] = a;
            }
            // from transposed
            let mut m_transposed = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                ntt_inv_transpose(&mut a, false);
                for j in 0..n {
                    m_transposed[j][i] = a[j];
                }
            }
            assert_eq!(m_primal, m_transposed);
        }
    }

    #[test]
    fn check_matrix_middle_product() {
        type Mint = StaticModInt<65537>;
        let mut rng = Sfc64::new(0);
        for _ in 0..100 {
            let la = rng.next_range(1..10) as usize;
            let a: Vec<Mint> = gen_vector(&mut rng, la);
            let lb = rng.next_range(1..10) as usize;
            let lc = la + lb - 1;
            // from primal ^ T
            let mut m_primal = vec![vec![Mint::default(); lc]; lb];
            for i in 0..lb {
                let mut b = vec![Mint::default(); lb];
                b[i] = Mint::new(1);
                let c = convolution_proth(&a, &b);
                m_primal[i] = c;
            }
            // from transposed
            let mut m_transposed = vec![vec![Mint::default(); lc]; lb];
            for i in 0..lc {
                let mut c = vec![Mint::default(); lc];
                c[i] = Mint::new(1);
                let b = middle_product_proth(&a, &c);
                for j in 0..lb {
                    m_transposed[j][i] = b[j];
                }
            }
            assert_eq!(m_primal, m_transposed);
        }
    }

    #[test]
    fn test_middle_product() {
        let mut rng = Sfc64::new(0);
        for _ in 0..100 {
            type Mint = StaticModInt<65537>;
            let la = rng.next_range(1..10) as usize;
            let mut a: Vec<Mint> = gen_vector(&mut rng, la);
            let lc = la + rng.next_range(0..10) as usize;
            let c: Vec<Mint> = gen_vector(&mut rng, lc);

            let b1 = middle_product_proth(&a, &c);
            a.reverse();
            let b2 = convolution_proth(&a, &c)[la - 1..lc].to_owned();
            assert_eq!(b1, b2);
        }
        for _ in 0..100 {
            type Mint = StaticModInt<65537>;
            let la = rng.next_range(1..10) as usize;
            let mut a: Vec<Mint> = gen_vector(&mut rng, la);
            let lc = la + rng.next_range(0..10) as usize;
            let c: Vec<Mint> = gen_vector(&mut rng, lc);

            let b1 = middle_product_arbitrary(&a, &c);
            a.reverse();
            let b2 = convolution_arbitrary(&a, &c)[la - 1..lc].to_owned();
            assert_eq!(b1, b2);
        }
        for _ in 0..100 {
            type Mint = StaticModInt<{ 1 << 126 | 1 }>;
            let la = rng.next_range(1..10) as usize;
            let mut a: Vec<Mint> = gen_vector(&mut rng, la);
            let lc = la + rng.next_range(0..10) as usize;
            let c: Vec<Mint> = gen_vector(&mut rng, lc);

            let b1 = middle_product_arbitrary(&a, &c);
            a.reverse();
            let b2 = convolution_arbitrary(&a, &c)[la - 1..lc].to_owned();
            assert_eq!(b1, b2);
        }
    }
}
