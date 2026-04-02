use crate::convolution::u128 as primal;
use crate::modint::u128::StaticModInt;
use crate::primality::is_prime_const;

/// NTT 順変換の転置．
///
/// 入力が natural order のとき，出力は bit-reversal order．
pub fn butterfly<const M: u128>(a: &mut [StaticModInt<M>]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    primal::butterfly_inv(a, false);
    a[1..].reverse();
}

/// NTT 逆変換の転置．
///
/// 入力が bit-reversal order のとき，出力は natural order．
pub fn butterfly_inv<const M: u128>(a: &mut [StaticModInt<M>], divide_n: bool) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    a[1..].reverse();
    primal::butterfly(a);
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
    primal::butterfly(&mut a);
    primal::butterfly(&mut c);
    for (a, c) in a.iter_mut().zip(&c) {
        *a *= c;
    }
    primal::butterfly_inv(&mut a, true);
    a[la - 1..lc].to_owned()
}

/// middle_product_proth の入出力から StaticModInt を剥がしたもの
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
    let c = c.iter().map(|e| e.val()).collect::<Vec<_>>();
    let c1 = middle_product_raw::<M1>(&a, &c);
    let c2 = middle_product_raw::<M2>(&a, &c);
    let c3 = middle_product_raw::<M3>(&a, &c);

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
    use super::*;
    use crate::utility::Sfc64;

    fn gen_vector<const M: u128>(rng: &mut Sfc64, n: usize) -> Vec<StaticModInt<M>> {
        let mut a = vec![StaticModInt::new(0); n];
        for ai in a.iter_mut() {
            *ai = StaticModInt::new(rng.next_range(0..M));
        }
        a
    }

    #[test]
    fn check_matrix_butterfly() {
        type Mint = StaticModInt<97>;
        // butterfly
        for h in 1..6 {
            let n = 1 << h;
            // from primal ^ T
            let mut m_primal = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                primal::butterfly(&mut a);
                m_primal[i] = a;
            }
            // from transposed
            let mut m_transposed = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                butterfly(&mut a);
                for j in 0..n {
                    m_transposed[j][i] = a[j];
                }
            }
            assert_eq!(m_primal, m_transposed);
        }
        // butterfly_inv, true
        for h in 1..6 {
            let n = 1 << h;
            // from primal ^ T
            let mut m_primal = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                primal::butterfly_inv(&mut a, true);
                m_primal[i] = a;
            }
            // from transposed
            let mut m_transposed = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                butterfly_inv(&mut a, true);
                for j in 0..n {
                    m_transposed[j][i] = a[j];
                }
            }
            assert_eq!(m_primal, m_transposed);
        }
        // butterfly_inv, false
        for h in 1..6 {
            let n = 1 << h;
            // from primal ^ T
            let mut m_primal = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                primal::butterfly_inv(&mut a, false);
                m_primal[i] = a;
            }
            // from transposed
            let mut m_transposed = vec![vec![Mint::default(); n]; n];
            for i in 0..n {
                let mut a = vec![Mint::default(); n];
                a[i] = Mint::new(1);
                butterfly_inv(&mut a, false);
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
                let c = primal::convolution_proth(&a, &b);
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
            let b2 = primal::convolution_proth(&a, &c)[la - 1..lc].to_owned();
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
            let b2 = primal::convolution_arbitrary(&a, &c)[la - 1..lc].to_owned();
            assert_eq!(b1, b2);
        }
    }
}
