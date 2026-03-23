use std::ops::RangeBounds;

pub fn gcd(mut x: u128, mut y: u128) -> u128 {
    while x != 0 {
        (x, y) = (y % x, x);
    }
    y
}

/// 線形篩
#[derive(Debug)]
pub struct Sieve {
    pub lpf: Vec<usize>,
}
impl Sieve {
    pub fn new(n: usize) -> Self {
        let mut prime = vec![];
        let mut lpf = vec![0; n];
        for d in 2..n {
            if lpf[d] == 0 {
                lpf[d] = d;
                prime.push(d);
            }
            let pd = lpf[d];
            for &p in prime.iter().take_while(|&&p| p * d < n && p <= pd) {
                lpf[p * d] = p;
            }
        }
        Self { lpf }
    }
    pub fn is_prime(&self, n: usize) -> bool {
        self.lpf[n] == n
    }
    pub fn prime_range(&self, rb: impl RangeBounds<usize>) -> impl Iterator<Item = usize> {
        self.lpf.iter().enumerate().filter_map(move |(i, &e)| {
            if i >= 2 && rb.contains(&i) && i == e {
                Some(i)
            } else {
                None
            }
        })
    }
}

/// SplitMix 64-bit PRNG, for seeding.
///
/// cf. <https://prng.di.unimi.it/splitmix64.c>
#[derive(Debug, Clone, Copy)]
pub struct SplitMix(u64);

impl SplitMix {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
}

/// Small Fast Chaotic PRNG.
#[derive(Debug, Clone, Copy)]
pub struct Sfc64 {
    a: u64,
    b: u64,
    c: u64,
    counter: u64,
}

impl Sfc64 {
    pub fn new(seed: u64) -> Self {
        let mut sm = SplitMix::new(seed);
        let mut g = Self {
            a: sm.next_u64(),
            b: sm.next_u64(),
            c: sm.next_u64(),
            counter: 1,
        };
        for _ in 0..20 {
            g.next_u64();
        }
        g
    }
    pub fn next_u64(&mut self) -> u64 {
        let ans = self.a.wrapping_add(self.b).wrapping_add(self.counter);
        self.counter += 1;
        self.a = self.b ^ (self.b >> 11);
        self.b = self.c.wrapping_add(self.c << 3);
        self.c = self.c.rotate_left(24).wrapping_add(ans);
        ans
    }
    pub fn next_u128(&mut self) -> u128 {
        (self.next_u64() as u128) << 64 | self.next_u64() as u128
    }
    pub fn next_range(&mut self, rg: impl RangeBounds<u128>) -> u128 {
        let l = match rg.start_bound() {
            std::ops::Bound::Included(&l) => l,
            std::ops::Bound::Excluded(&l) => l - 1,
            std::ops::Bound::Unbounded => 0,
        };
        let r = match rg.end_bound() {
            std::ops::Bound::Included(&r) => r.wrapping_add(1),
            std::ops::Bound::Excluded(&r) => r,
            std::ops::Bound::Unbounded => 0,
        };
        if l == r {
            return self.next_u128();
        }
        let d = r.wrapping_sub(l);
        if d == 1 {
            return l;
        }
        // l..r = l + (0..d)
        let shr = (d - 1).leading_zeros();
        loop {
            let x = self.next_u128() >> shr;
            if x < d {
                break l.wrapping_add(x);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gcd() {
        let ans = (0..30)
            .map(|i| {
                (0..30)
                    .map(|j| gcd(i, j).to_string())
                    .collect::<Vec<_>>()
                    .join("\t")
            })
            .collect::<Vec<_>>()
            .join("\n");
        let expected =
            "0	1	2	3	4	5	6	7	8	9	10	11	12	13	14	15	16	17	18	19	20	21	22	23	24	25	26	27	28	29
1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1
2	1	2	1	2	1	2	1	2	1	2	1	2	1	2	1	2	1	2	1	2	1	2	1	2	1	2	1	2	1
3	1	1	3	1	1	3	1	1	3	1	1	3	1	1	3	1	1	3	1	1	3	1	1	3	1	1	3	1	1
4	1	2	1	4	1	2	1	4	1	2	1	4	1	2	1	4	1	2	1	4	1	2	1	4	1	2	1	4	1
5	1	1	1	1	5	1	1	1	1	5	1	1	1	1	5	1	1	1	1	5	1	1	1	1	5	1	1	1	1
6	1	2	3	2	1	6	1	2	3	2	1	6	1	2	3	2	1	6	1	2	3	2	1	6	1	2	3	2	1
7	1	1	1	1	1	1	7	1	1	1	1	1	1	7	1	1	1	1	1	1	7	1	1	1	1	1	1	7	1
8	1	2	1	4	1	2	1	8	1	2	1	4	1	2	1	8	1	2	1	4	1	2	1	8	1	2	1	4	1
9	1	1	3	1	1	3	1	1	9	1	1	3	1	1	3	1	1	9	1	1	3	1	1	3	1	1	9	1	1
10	1	2	1	2	5	2	1	2	1	10	1	2	1	2	5	2	1	2	1	10	1	2	1	2	5	2	1	2	1
11	1	1	1	1	1	1	1	1	1	1	11	1	1	1	1	1	1	1	1	1	1	11	1	1	1	1	1	1	1
12	1	2	3	4	1	6	1	4	3	2	1	12	1	2	3	4	1	6	1	4	3	2	1	12	1	2	3	4	1
13	1	1	1	1	1	1	1	1	1	1	1	1	13	1	1	1	1	1	1	1	1	1	1	1	1	13	1	1	1
14	1	2	1	2	1	2	7	2	1	2	1	2	1	14	1	2	1	2	1	2	7	2	1	2	1	2	1	14	1
15	1	1	3	1	5	3	1	1	3	5	1	3	1	1	15	1	1	3	1	5	3	1	1	3	5	1	3	1	1
16	1	2	1	4	1	2	1	8	1	2	1	4	1	2	1	16	1	2	1	4	1	2	1	8	1	2	1	4	1
17	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	17	1	1	1	1	1	1	1	1	1	1	1	1
18	1	2	3	2	1	6	1	2	9	2	1	6	1	2	3	2	1	18	1	2	3	2	1	6	1	2	9	2	1
19	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	19	1	1	1	1	1	1	1	1	1	1
20	1	2	1	4	5	2	1	4	1	10	1	4	1	2	5	4	1	2	1	20	1	2	1	4	5	2	1	4	1
21	1	1	3	1	1	3	7	1	3	1	1	3	1	7	3	1	1	3	1	1	21	1	1	3	1	1	3	7	1
22	1	2	1	2	1	2	1	2	1	2	11	2	1	2	1	2	1	2	1	2	1	22	1	2	1	2	1	2	1
23	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	23	1	1	1	1	1	1
24	1	2	3	4	1	6	1	8	3	2	1	12	1	2	3	8	1	6	1	4	3	2	1	24	1	2	3	4	1
25	1	1	1	1	5	1	1	1	1	5	1	1	1	1	5	1	1	1	1	5	1	1	1	1	25	1	1	1	1
26	1	2	1	2	1	2	1	2	1	2	1	2	13	2	1	2	1	2	1	2	1	2	1	2	1	26	1	2	1
27	1	1	3	1	1	3	1	1	9	1	1	3	1	1	3	1	1	9	1	1	3	1	1	3	1	1	27	1	1
28	1	2	1	4	1	2	7	4	1	2	1	4	1	14	1	4	1	2	1	4	7	2	1	4	1	2	1	28	1
29	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	1	29";
        assert_eq!(ans, expected);
    }

    #[test]
    fn test_sieve() {
        let s = Sieve::new(50);
        assert_eq!(
            s.lpf,
            vec![
                0, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3, 2, 17, 2, 19, 2, 3, 2, 23, 2, 5,
                2, 3, 2, 29, 2, 31, 2, 3, 2, 5, 2, 37, 2, 3, 2, 41, 2, 43, 2, 3, 2, 47, 2, 7
            ]
        );
        assert_eq!(
            s.prime_range(..).collect::<Vec<_>>(),
            vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
        );
        assert_eq!(
            s.prime_range(20..).collect::<Vec<_>>(),
            vec![23, 29, 31, 37, 41, 43, 47]
        );
        assert_eq!(
            s.prime_range(..=19).collect::<Vec<_>>(),
            vec![2, 3, 5, 7, 11, 13, 17, 19]
        );
        assert_eq!(
            s.prime_range(19..39).collect::<Vec<_>>(),
            vec![19, 23, 29, 31, 37]
        );
    }

    #[test]
    fn test_split_mix() {
        let mut rng = SplitMix::new(0);
        assert_eq!(rng.next_u64(), 16294208416658607535);
        assert_eq!(rng.next_u64(), 7960286522194355700);
        assert_eq!(rng.next_u64(), 487617019471545679);
    }

    #[test]
    fn test_range() {
        let mut rng = Sfc64::new(0);
        for l in 0..10 {
            for r in l + 1..l + 100 {
                for _ in 0..10000 {
                    let x = rng.next_range(l..r);
                    assert!((l..r).contains(&x), "x = {x} not in ({l}..{r})");
                }
            }
        }
    }
}
