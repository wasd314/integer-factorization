use crate::primality::{
    lucas::{is_lucas_sprp, is_lucas_sprp_const},
    miller_rabin::{is_sprp, is_sprp_const},
};

pub mod lucas;
pub mod miller_rabin;

/// Baillie–PSW primality test.
pub fn is_prime(n: u128) -> bool {
    if n <= 2 {
        return n == 2;
    }
    if n & 1 == 0 {
        return false;
    }
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
        if n == p {
            return true;
        }
        if n.is_multiple_of(p) {
            return false;
        }
    }
    is_sprp(n, &[2]) && is_lucas_sprp(n)
}

/// Baillie–PSW primality test.
pub const fn is_prime_const(n: u128) -> bool {
    if n <= 2 {
        return n == 2;
    }
    if n & 1 == 0 {
        return false;
    }
    let ps = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
    let mut i = ps.len();
    while i > 0 {
        i -= 1;
        let p = ps[i];
        if n == p {
            return true;
        }
        if n.is_multiple_of(p) {
            return false;
        }
    }
    is_sprp_const(n, &[2]) && is_lucas_sprp_const(n)
}
