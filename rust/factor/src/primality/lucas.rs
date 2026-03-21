use crate::modint::u128::ModInt;

/// Legendre symbol.
///
/// assume p = mp.n: odd prime.
pub fn legendre(a: u128, mp: &ModInt) -> i8 {
    let a = mp.mod_n(a);
    if a == 0 {
        return 0;
    }
    let p = mp.n;
    let ra = mp.mr(a);
    let b = mp.pow(ra, p >> 1);
    if b == mp.r1 { 1 } else { -1 }
}

/// Jacobi symbol.
///
/// assume p = mp.n: odd.
pub fn jacobi(a: i128, mut n: u128) -> i8 {
    assert!(!n.is_multiple_of(2));
    let mut a = a.rem_euclid(n as _) as u128;
    let mut ans = 1;
    while a != 0 {
        let e = a.trailing_zeros();
        a >>= e;
        if !e.is_multiple_of(2) && (n & 7 == 3 || n & 7 == 5) {
            ans = -ans;
        }
        (a, n) = (n, a);
        if a & 3 == 3 && n & 3 == 3 {
            ans = -ans;
        }
        a %= n;
    }
    // current n == gcd(a, n)
    if n == 1 { ans } else { 0 }
}

/// Lucas sequence (U(P, Q), V(P, Q)) の n 項目．
pub fn calc_lucas(p: u128, q: u128, mut n: u128, mo: &ModInt) -> (u128, u128) {
    let (rp, rq) = (mo.mr(p), mo.mr(q));

    let mat_mul = |a: [[u128; 2]; 2], b: [[u128; 2]; 2]| {
        let mut c = [[0; 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                c[i][j] = mo.add(mo.mul(a[i][0], b[0][j]), mo.mul(a[i][1], b[1][j]));
            }
        }
        c
    };
    let mut total = [[mo.r1, 0], [0, mo.r1]];
    let mut m = [[0, mo.r1], [mo.neg(rq), rp]];
    while n > 0 {
        if n & 1 == 1 {
            total = mat_mul(total, m);
        }
        m = mat_mul(m, m);
        n >>= 1;
    }
    // total[0][0] * 0 + total[0][1] * 1
    let ru = total[0][1];
    // total[0][0] * 2 + total[0][1] * P
    let rv = mo.add(mo.add(total[0][0], total[0][0]), mo.mul(total[0][1], rp));
    (ru, rv)
}

/// Strong Lucas probable prime test with parameters (P, Q) defined by Selfridge's Method A.
pub fn is_lucas_sprp(n: u128) -> bool {
    if n.is_multiple_of(2) || n == 1 {
        return false;
    }
    let det = {
        let mut d = 5;
        loop {
            match jacobi(d, n) {
                -1 => break Some(d),
                0 if n > d.unsigned_abs() => break None,
                _ => {}
            }
            if d == -15 && n.isqrt().pow(2) == n {
                break None;
            }
            d = if d > 0 { -2 } else { 2 } - d;
        }
    };
    let Some(det) = det else { return false };
    let (p, q) = (1, (1 - det) / 4);
    let q = q.rem_euclid(n as _) as _;
    let mo = ModInt::new(n);

    // n - (D/n) = n + 1
    let e = (n + 1).trailing_zeros();
    let o = (n + 1) >> e;
    let (mut ru, mut rv) = calc_lucas(p, q, o, &mo);
    let rq0 = mo.mr(q);
    let mut rq = mo.pow(rq0, o);
    if ru == 0 || rv == 0 {
        return true;
    }
    for _ in 1..e {
        (ru, rv) = (mo.mul(ru, rv), mo.sub(mo.mul(rv, rv), mo.add(rq, rq)));
        rq = mo.mul(rq, rq);
        if rv == 0 {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use crate::primality::miller_rabin::is_prime;

    use super::*;

    #[test]
    fn test_legendre() {
        for n in (3..60).filter(|n| is_prime(*n)) {
            let mp = ModInt::new(n);
            for a in 0..100 {
                assert_eq!(legendre(a, &mp), jacobi(a as _, n), "check ({a}/{n})");
            }
        }
    }

    #[test]
    fn small_jacobi() {
        // check (a/n) for n <= 59 odd, a <= 30
        let table = (1..60)
            .filter(|x| x % 2 == 1)
            .map(|n| {
                let s = (1..31)
                    .map(|k| format!("{}", jacobi(k, n)))
                    .collect::<Vec<_>>()
                    .join("\t");
                format!("{n}\t{s}")
            })
            .collect::<Vec<_>>()
            .join("\n");
        // https://en.wikipedia.org/wiki/Jacobi_symbol
        let expected = "1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1
3	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0
5	1	-1	-1	1	0	1	-1	-1	1	0	1	-1	-1	1	0	1	-1	-1	1	0	1	-1	-1	1	0	1	-1	-1	1	0
7	1	1	-1	1	-1	-1	0	1	1	-1	1	-1	-1	0	1	1	-1	1	-1	-1	0	1	1	-1	1	-1	-1	0	1	1
9	1	1	0	1	1	0	1	1	0	1	1	0	1	1	0	1	1	0	1	1	0	1	1	0	1	1	0	1	1	0
11	1	-1	1	1	1	-1	-1	-1	1	-1	0	1	-1	1	1	1	-1	-1	-1	1	-1	0	1	-1	1	1	1	-1	-1	-1
13	1	-1	1	1	-1	-1	-1	-1	1	1	-1	1	0	1	-1	1	1	-1	-1	-1	-1	1	1	-1	1	0	1	-1	1	1
15	1	1	0	1	0	0	-1	1	0	0	-1	0	-1	-1	0	1	1	0	1	0	0	-1	1	0	0	-1	0	-1	-1	0
17	1	1	-1	1	-1	-1	-1	1	1	-1	-1	-1	1	-1	1	1	0	1	1	-1	1	-1	-1	-1	1	1	-1	-1	-1	1
19	1	-1	-1	1	1	1	1	-1	1	-1	1	-1	-1	-1	-1	1	1	-1	0	1	-1	-1	1	1	1	1	-1	1	-1	1
21	1	-1	0	1	1	0	0	-1	0	-1	-1	0	-1	0	0	1	1	0	-1	1	0	1	-1	0	1	1	0	0	-1	0
23	1	1	1	1	-1	1	-1	1	1	-1	-1	1	1	-1	-1	1	-1	1	-1	-1	-1	-1	0	1	1	1	1	-1	1	-1
25	1	1	1	1	0	1	1	1	1	0	1	1	1	1	0	1	1	1	1	0	1	1	1	1	0	1	1	1	1	0
27	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0	1	-1	0
29	1	-1	-1	1	1	1	1	-1	1	-1	-1	-1	1	-1	-1	1	-1	-1	-1	1	-1	1	1	1	1	-1	-1	1	0	1
31	1	1	-1	1	1	-1	1	1	1	1	-1	-1	-1	1	-1	1	-1	1	1	1	-1	-1	-1	-1	1	-1	-1	1	-1	-1
33	1	1	0	1	-1	0	-1	1	0	-1	0	0	-1	-1	0	1	1	0	-1	-1	0	0	-1	0	1	-1	0	-1	1	0
35	1	-1	1	1	0	-1	0	-1	1	0	1	1	1	0	0	1	1	-1	-1	0	0	-1	-1	-1	0	-1	1	0	1	0
37	1	-1	1	1	-1	-1	1	-1	1	1	1	1	-1	-1	-1	1	-1	-1	-1	-1	1	-1	-1	-1	1	1	1	1	-1	1
39	1	1	0	1	1	0	-1	1	0	1	1	0	0	-1	0	1	-1	0	-1	1	0	1	-1	0	1	0	0	-1	-1	0
41	1	1	-1	1	1	-1	-1	1	1	1	-1	-1	-1	-1	-1	1	-1	1	-1	1	1	-1	1	-1	1	-1	-1	-1	-1	-1
43	1	-1	-1	1	-1	1	-1	-1	1	1	1	-1	1	1	1	1	1	-1	-1	-1	1	-1	1	1	1	-1	-1	-1	-1	-1
45	1	-1	0	1	0	0	-1	-1	0	0	1	0	-1	1	0	1	-1	0	1	0	0	-1	-1	0	0	1	0	-1	1	0
47	1	1	1	1	-1	1	1	1	1	-1	-1	1	-1	1	-1	1	1	1	-1	-1	1	-1	-1	1	1	-1	1	1	-1	-1
49	1	1	1	1	1	1	0	1	1	1	1	1	1	0	1	1	1	1	1	1	0	1	1	1	1	1	1	0	1	1
51	1	-1	0	1	1	0	-1	-1	0	-1	1	0	1	1	0	1	0	0	1	1	0	-1	1	0	1	-1	0	-1	1	0
53	1	-1	-1	1	-1	1	1	-1	1	1	1	-1	1	-1	1	1	1	-1	-1	-1	-1	-1	-1	1	1	-1	-1	1	1	-1
55	1	1	-1	1	0	-1	1	1	1	0	0	-1	1	1	0	1	1	1	-1	0	-1	0	-1	-1	0	1	-1	1	-1	0
57	1	1	0	1	-1	0	1	1	0	-1	-1	0	-1	1	0	1	-1	0	0	-1	0	-1	-1	0	1	-1	0	1	1	0
59	1	-1	1	1	1	-1	1	-1	1	-1	-1	1	-1	-1	1	1	1	-1	1	1	1	1	-1	-1	1	1	1	1	1	-1";
        assert_eq!(table, expected);
    }

    #[test]
    fn small_lucas() {
        let spsp = (1..100000)
            .filter(|&n| n % 2 == 1 && is_lucas_sprp(n) && !is_prime(n))
            .collect::<Vec<_>>();
        // https://oeis.org/A217255
        assert_eq!(
            spsp,
            vec![
                5459, 5777, 10877, 16109, 18971, 22499, 24569, 25199, 40309, 58519, 75077, 97439
            ]
        );
    }
}
