/// for n > 0, floor(y^{1/n}).
pub const fn nth_root_floor1(y: u128, n: u32) -> u128 {
    assert!(n > 0);
    if n == 1 || y <= 1 {
        return y;
    }
    if n == 2 {
        return y.isqrt();
    }
    // x < 2 <==> y < 2^n, x >= 1.
    if y.unbounded_shr(n) == 0 {
        return 1;
    }
    // y >= 2^n, n >= 3
    let mut x = 0;
    // y < 2^B ==> x < 2^ceil(B/n)
    let mut i = (y.ilog2() + 1).div_ceil(n);
    while i > 0 {
        i -= 1;
        let nx: u128 = x | 1 << i;
        if let Some(ny) = nx.checked_pow(n)
            && ny <= y
        {
            x = nx;
        }
    }
    x
}

/// for n > 0, floor(y^{1/n}).
pub const fn nth_root_floor2(y: u128, n: u32) -> u128 {
    assert!(n > 0);
    if n == 1 || y <= 1 {
        return y;
    }
    // if n == 2 {
    //     return y.isqrt();
    // }
    // x < 2 <==> y < 2^n, x >= 1.
    if y.unbounded_shr(n) == 0 {
        return 1;
    }
    // y >= 2^n, n >= 3
    // y < 2^B ==> x < 2^ceil(B/n)
    let mut x: u128 = 1 << (y.ilog2() + 1).div_ceil(n);
    loop {
        let q = if let Some(xp) = x.checked_pow(n - 1) {
            y / xp
        } else {
            0
        };
        if x <= q {
            break x;
        }
        let nx = x - (x - q).div_ceil(n as _);
        if nx >= x {
            break x;
        }
        x = nx;
    }
}

pub use self::nth_root_floor1 as nth_root_floor;

/// `Some((x, n))` s.t. x^n == y, x >= 2, n >= 2, largest n; else `None`.
pub const fn find_perfect_power(y: u128) -> Option<(u128, u32)> {
    if y < 4 {
        return None;
    }
    // for n in (2..=u128::BITS).rev() {...}
    let mut n = y.ilog2() + 1;
    while n > 2 {
        n -= 1;
        let x = nth_root_floor(y, n);
        if matches!(x.checked_pow(n), Some(ny) if ny == y) {
            return Some((x, n));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// check x^n <= y < (x+1)^n.
    fn check_nth_root(y: u128, n: u32) {
        let x = nth_root_floor1(y, n);
        assert!(
            x.checked_pow(n).is_some_and(|ny| ny <= y),
            "{:?} => {x}, {:?}",
            (y, n),
            x.overflowing_pow(n)
        );
        assert_eq!(nth_root_floor1(y, n), nth_root_floor2(y, n));
        if x < !0 {
            assert!(
                (x + 1).checked_pow(n).is_none_or(|ny| ny > y),
                "{:?} => {x}, {:?}",
                (y, n),
                (x + 1).overflowing_pow(n)
            );
        }
    }
    fn check_root(y: u128) {
        for n in 1..u128::BITS * 2 {
            check_nth_root(y, n);
        }
    }

    #[test]
    fn test_nth_root() {
        for y in 0..1000 {
            check_root(y);
            check_root(!y);
        }
        for n in 1..=u128::BITS {
            let x0 = nth_root_floor1(!0, n);
            for x in (0..=x0).take(100).chain((0..=x0).rev().take(100)) {
                let y0 = x.checked_pow(n).unwrap();
                for i in -5..=5 {
                    let y = y0.saturating_add_signed(i);
                    check_root(y);
                }
            }
        }
    }

    #[test]
    fn test_perfect_power() {
        for n in 2..u128::BITS {
            let x0 = nth_root_floor1(!0, n);
            for x in (2..=x0).take(100).chain((2..=x0).rev().take(100)) {
                let y0 = x.checked_pow(n).unwrap();
                assert_ne!(find_perfect_power(y0), None, "{x}^{n}");
            }
        }
    }
}
