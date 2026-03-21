use crate::primality::{lucas::is_lucas_sprp, miller_rabin::is_sprp};

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
