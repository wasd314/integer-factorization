use crate::primality::is_prime;

pub trait Factorize {
    /// `n` の非自明な約数を探す．
    ///
    /// `n` は 3 以上の奇数が渡されると仮定して実装して良い．
    fn try_find_factor(&mut self, n: u128) -> Option<u128> {
        Some(self.find_factor(n))
    }

    /// `n` の非自明な約数を返す．
    ///
    /// `n` は 3 以上の奇数が渡されると仮定して実装して良い．
    fn find_factor(&mut self, n: u128) -> u128 {
        loop {
            if let Some(d) = self.try_find_factor(n)
                && 1 < d
                && d < n
            {
                return d;
            }
        }
    }

    /// `n` の素因数を 1 つ返す．
    ///
    /// `n >= 2` を仮定する．
    fn find_prime_factor(&mut self, mut n: u128) -> u128 {
        assert!(n >= 2);
        if n.is_multiple_of(2) {
            return 2;
        }
        while !is_prime(n) {
            let d = self.find_factor(n);
            assert_ne!(d, 1);
            assert_ne!(d, n);
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

    /// `n` の素因数分解をする．
    ///
    /// `n >= 1` を仮定する．
    fn factorize(&mut self, mut n: u128) -> Vec<u128> {
        assert!(n >= 1);
        let mut ans = vec![2; n.trailing_zeros() as _];
        n >>= n.trailing_zeros();
        while n > 1 {
            let p = self.find_prime_factor(n);
            while n.is_multiple_of(p) {
                n /= p;
                ans.push(p);
            }
        }
        ans.sort();
        ans
    }
}
