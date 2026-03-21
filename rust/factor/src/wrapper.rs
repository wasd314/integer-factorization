use crate::primality::is_prime;

/// 素因数を 1 つ返す．
///
/// `f`: 非自明な約数を返すとする．
pub fn find_prime_factor<F: FnMut(u128) -> u128>(mut n: u128, f: &mut F) -> u128 {
    assert!(n >= 2);
    if n.is_multiple_of(2) {
        return 2;
    }
    while !is_prime(n) {
        let d = f(n);
        n = if is_prime(d) {
            d
        } else if is_prime(n / d) {
            n / d
        } else {
            d.min(n / d)
        };
    }
    n
}

/// 素因数分解をする．
///
/// `f`: 非自明な約数を返すとする．
pub fn factorize<F: FnMut(u128) -> u128>(mut n: u128, f: &mut F) -> Vec<u128> {
    assert_ne!(n, 0);
    let mut ans = vec![2; n.trailing_zeros() as _];
    n >>= n.trailing_zeros();
    while n > 1 {
        let p = find_prime_factor(n, f);
        while n.is_multiple_of(p) {
            n /= p;
            ans.push(p);
        }
    }
    ans
}
