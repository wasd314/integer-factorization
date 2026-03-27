use crate::modint::dynamic::u128::ModInt;

/// Miller–Rabin primality test.
pub fn is_sprp(n: u128, bases: &[u128]) -> bool {
    if n.is_multiple_of(2) || n == 1 {
        return false;
    }
    let mont = ModInt::new(n);
    let one = mont.r1;
    let neg_one = mont.neg(one);
    let e = (n - 1).trailing_zeros();
    let o = n >> e;
    for b in bases {
        let mut rx = mont.pow(mont.mr(*b), o);
        if rx == one || rx == neg_one {
            continue;
        }
        for _ in 1..e {
            rx = mont.mul(rx, rx);
            if rx == neg_one {
                break;
            }
        }
        if rx != neg_one {
            return false;
        }
    }
    true
}

/// Primality test based on Miller–Rabin primality test.
pub fn is_prime(n: u128) -> bool {
    if n <= 2 {
        return n == 2;
    }
    if n.is_multiple_of(2) {
        return false;
    }
    if n < 2047 {
        is_sprp(n, &[2])
    } else if n < 9080191 {
        is_sprp(n, &[31, 73])
    } else if n < 4759123141 {
        is_sprp(n, &[2, 7, 61])
    } else if n < 1122004669633 {
        is_sprp(n, &[2, 13, 23, 1662803])
    } else if n < 3770579582154547 {
        is_sprp(n, &[2, 880937, 2570940, 610386380, 4130785767])
    } else if n < 18446744073709551616 {
        is_sprp(n, &[2, 325, 9375, 28178, 450775, 9780504, 1795265022])
    } else if n < 318665857834031151167461 {
        is_sprp(n, &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37])
    } else if n < 3317044064679887385961981 {
        is_sprp(n, &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41])
    } else {
        // first 20 primes (not verified)
        is_sprp(
            n,
            &[
                2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
            ],
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_small_spsp() {
        let composites = (3..10000)
            .filter(|n| n % 2 == 1 && !is_prime(*n))
            .collect::<Vec<_>>();
        let spsp = |bases| {
            composites
                .iter()
                .copied()
                .filter(|n| is_sprp(*n, bases))
                .collect::<Vec<_>>()
        };
        // https://oeis.org/A001262
        assert_eq!(spsp(&[2]), vec![2047, 3277, 4033, 4681, 8321]);
        // https://oeis.org/A020229
        assert_eq!(spsp(&[3]), vec![121, 703, 1891, 3281, 8401, 8911]);
        // https://oeis.org/A020231
        assert_eq!(spsp(&[5]), vec![781, 1541, 5461, 5611, 7813]);
        // https://oeis.org/A020233
        assert_eq!(spsp(&[7]), vec![25, 325, 703, 2101, 2353, 4525]);
        // https://oeis.org/A020236
        assert_eq!(spsp(&[10]), vec![9, 91, 1729, 4187, 6533, 8149, 8401]);
    }
    #[test]
    fn check_spsp() {
        assert!(!is_sprp(1, &[2]));
        assert!(is_sprp(2047, &[2]));
        assert!(is_sprp(2047, &[2047 + 2]));
        assert!(is_sprp(9080191, &[31, 73]));
        assert!(is_sprp(4759123141, &[2, 7, 61]));
        assert!(is_sprp(1122004669633, &[2, 13, 23, 1662803]));
        assert!(is_sprp(
            3770579582154547,
            &[2, 880937, 2570940, 610386380, 4130785767]
        ));
        assert!(is_sprp(
            318665857834031151167461,
            &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
        ));
        assert!(is_sprp(
            3317044064679887385961981,
            &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
        ));
    }
}
