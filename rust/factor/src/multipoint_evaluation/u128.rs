use crate::{
    convolution::u128::{DynamicConvolution, middle_product_arbitrary},
    fps::u128::{DynamicFps, Fps},
    modint::u128::{DynamicModInt, StaticModInt as Mint},
};

fn middle_product<const M: u128>(a: &Fps<Mint<M>>, c: &Fps<Mint<M>>) -> Fps<Mint<M>> {
    Fps::new(middle_product_arbitrary(a.as_slice(), c.as_slice()))
}

/// 一般の標本点列に対する Multipoint evaluation.
///
/// 標本点列ごとに前計算を行う．
pub struct MultipointEvaluation<T> {
    m0: usize,
    m: usize,
    sub_prods: Vec<Fps<T>>,
}

impl<const M: u128> MultipointEvaluation<Mint<M>> {
    /// 標本点列ごとの前計算を行う．
    ///
    /// # Complexity
    ///
    /// 標本点数`points.len()`を M として，Θ(M (log M)^2) 時間．
    pub fn new(mut points: Vec<Mint<M>>) -> Self {
        let m0 = points.len();
        let m = m0.next_power_of_two();
        points.reserve(m - m0);
        for _ in m0..m {
            points.push(Mint::new(0));
        }
        let points = points;

        // subproduct tree
        let mut sub_prods = vec![Fps::default(); m * 2];
        for i in 0..m {
            sub_prods[m + i] = Fps::new(vec![-points[i], Mint::new(1)]);
        }
        for i in (1..m).rev() {
            sub_prods[i] = &sub_prods[i * 2] * &sub_prods[i * 2 + 1];
        }
        Self { m0, m, sub_prods }
    }

    /// Multipoint evaluation 本計算．
    ///
    /// 多項式 `f` を受け取り，`f` に `X = points[i]` を代入したときの値を列挙する．
    ///
    /// # Complexity
    ///
    /// `f.len()`を N, L := M + N として，Θ(M (log M)^2 + L log L) 時間．
    pub fn eval(&self, f: &Fps<Mint<M>>) -> Vec<Mint<M>> {
        let m0 = self.m0;
        let m = self.m;
        let sub_prods = &self.sub_prods;

        let n = f.len();
        if m0 == 0 {
            return vec![];
        }
        if n == 0 {
            return vec![Mint::new(0); m0];
        }
        let f = {
            let t1 = &sub_prods[1];
            let r_t1 = t1.reversed();
            let inv_rt1 = r_t1.inv_until(n);
            let f = f.prefix(m + n - 1);
            let mut f_ = middle_product(&inv_rt1, &f);
            f_.reverse();
            f_
        };

        // UpTree^T
        let mut dp = vec![Fps::default(); 2 * m];
        dp[1] = f;
        for i in 1..m {
            let g1 = middle_product(&sub_prods[2 * i + 1], &dp[i]);
            dp[2 * i] += g1;
            let g0 = middle_product(&sub_prods[2 * i], &dp[i]);
            dp[2 * i + 1] += g0;
        }
        dp[m..m + m0].iter().map(|e| e[0]).collect()
    }
}

/// 一般の標本点列に対する Multipoint evaluation（実行時任意 mod）．
///
/// 標本点列ごとに前計算を行う．
pub struct DynamicMultipointEvaluation {
    df: DynamicFps,
    m0: usize,
    m: usize,
    sub_prods: Vec<Vec<u128>>,
}

impl DynamicMultipointEvaluation {
    /// 標本点列ごとの前計算を行う．
    ///
    /// # Complexity
    ///
    /// 標本点数`points.len()`を M として，Θ(M (log M)^2) 時間．
    pub fn new(mo: DynamicModInt, mut points: Vec<u128>) -> Self {
        let m0 = points.len();
        let m = m0.next_power_of_two();
        points.reserve(m - m0);
        points.resize(m, 0);
        let points = points;

        // subproduct tree
        let mut sub_prods = vec![vec![]; m * 2];
        for i in 0..m {
            // sub_prods[m + i] = Fps::new(vec![-points[i], Mint::new(1)]);
            sub_prods[m + i] = vec![mo.neg(points[i]), mo.one()];
        }
        let df = DynamicFps::new(mo);
        for i in (1..m).rev() {
            sub_prods[i] = df.mul(&sub_prods[i * 2], &sub_prods[i * 2 + 1]);
        }
        Self {
            df,
            m0,
            m,
            sub_prods,
        }
    }

    /// Multipoint evaluation 本計算．
    ///
    /// 多項式 `f` を受け取り，`f` に `X = points[i]` を代入したときの値を列挙する．
    ///
    /// # Complexity
    ///
    /// `f.len()`を N, L := M + N として，Θ(M (log M)^2 + L log L) 時間．
    pub fn eval(&self, f: &[u128]) -> Result<Vec<u128>, u128> {
        let m0 = self.m0;
        let m = self.m;
        let sub_prods = &self.sub_prods;

        let n = f.len();
        if m0 == 0 {
            return Ok(vec![]);
        }
        if n == 0 {
            return Ok(vec![0; m0]);
        }
        let f = {
            let mut t1 = sub_prods[1].clone();
            t1.reverse();
            let inv_rt1 = self.df.inv_until(&t1, n)?;
            let f_ = self.df.prefix(f, m + n - 1);
            let mut f_ = self.df.0.middle_product_arbitrary(&inv_rt1, &f_);
            f_.reverse();
            f_
        };

        // UpTree^T
        let mut dp = vec![vec![]; 2 * m];
        dp[1] = f;
        for i in 1..m {
            let g1 = self
                .df
                .0
                .middle_product_arbitrary(&sub_prods[2 * i + 1], &dp[i]);
            self.df.add_assign(&mut dp[2 * i], &g1);
            let g0 = self
                .df
                .0
                .middle_product_arbitrary(&sub_prods[2 * i], &dp[i]);
            self.df.add_assign(&mut dp[2 * i + 1], &g0);
        }
        Ok(dp[m..m + m0].iter().map(|e| e[0]).collect())
    }
}

/// 一般の標本点列に対する Multipoint evaluation.
pub struct MultipointEvaluationNaive<T> {
    points: Vec<T>,
}

impl<const M: u128> MultipointEvaluationNaive<Mint<M>> {
    /// 標本点列ごとの前計算を行う．
    ///
    /// # Complexity
    ///
    /// Θ(1) 時間．
    pub fn new(points: Vec<Mint<M>>) -> Self {
        Self { points }
    }

    /// Multipoint evaluation 本計算．
    ///
    /// 多項式 `f` を受け取り，`f` に `X = points[i]` を代入したときの値を列挙する．
    ///
    /// # Complexity
    ///
    /// `f.len()`を N として，Θ(N M) 時間．
    pub fn eval(&self, f: &Fps<Mint<M>>) -> Vec<Mint<M>> {
        self.points.iter().map(|&x| f.eval(x)).collect()
    }
}

/// 一般の標本点列に対する Multipoint evaluation（実行時任意 mod）．
///
/// 標本点列ごとに前計算を行う．
pub struct DynamicMultipointEvaluationNaive {
    df: DynamicFps,
    points: Vec<u128>,
}

impl DynamicMultipointEvaluationNaive {
    /// 標本点列ごとの前計算を行う．
    ///
    /// # Complexity
    ///
    /// Θ(1) 時間．
    pub fn new(mo: DynamicModInt, points: Vec<u128>) -> Self {
        let df = DynamicFps::new(mo);
        Self { df, points }
    }

    /// Multipoint evaluation 本計算．
    ///
    /// 多項式 `f` を受け取り，`f` に `X = points[i]` を代入したときの値を列挙する．
    ///
    /// # Complexity
    ///
    /// `f.len()`を N, L := M + N として，Θ(M (log M)^2 + L log L) 時間．
    pub fn eval(&self, f: &[u128]) -> Result<Vec<u128>, u128> {
        Ok(self.points.iter().map(|&x| self.df.eval(f, x)).collect())
    }
}

#[cfg(test)]
mod tests {
    use crate::utility::Sfc64;

    use super::*;

    fn show<const M: u128>(a: &[Mint<M>]) -> String {
        a.iter()
            .map(|x| format!("{}", x.val()))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn verify_general<const M: u128>(f: &Fps<Mint<M>>, p: &[Mint<M>]) {
        let expected: Vec<_> = p.iter().map(|pi| f.eval(*pi)).collect();
        let me = MultipointEvaluation::new(p.to_owned());
        let found = me.eval(f);
        if found != expected {
            eprintln!("f: {}", show(f.as_slice()));
            eprintln!("p: {}", show(p));
            eprintln!("found: {}", show(&found));
            eprintln!("expected: {}", show(&expected));
        }
        assert_eq!(found, expected, "failed for f = {f:?}, p = {p:?}");
    }

    #[test]
    fn handmade() {
        const M: u128 = 998244353;
        let p: Vec<Mint<M>> = (1..5).map(Mint::new).collect();
        verify_general(&Fps::from(vec![1, 0, 1]), &p);
        verify_general(&Fps::from(vec![1, 2, 3]), &p);
        verify_general(&Fps::from(vec![4, 5, 6]), &p);
        verify_general(&Fps::from(vec![4]), &p);
        verify_general(&Fps::default(), &p);
        verify_general(&Fps::from(vec![1, 2, 3, 4]), &p);
        verify_general(&(1..20).collect(), &p);
        verify_general(&(1..20).rev().collect(), &p);
    }

    fn gen_vector<const M: u128>(rng: &mut Sfc64, n: usize) -> Vec<Mint<M>> {
        rng.next_vector(0..M, n)
            .into_iter()
            .map(Mint::new)
            .collect()
    }

    #[test]
    #[ignore]
    fn general_stress_f() {
        let mut rng = Sfc64::new(0);
        for _ in 0..1000 {
            const M: u128 = 998244353;
            let n = rng.next_range(0..20) as usize;
            let f = Fps::new(gen_vector(&mut rng, n));
            let n = rng.next_range(0..20) as usize;
            let p = gen_vector(&mut rng, n);
            verify_general::<M>(&f, &p);
        }
        for _ in 0..1000 {
            const M: u128 = 1001001001;
            let n = rng.next_range(0..20) as usize;
            let f = Fps::new(gen_vector(&mut rng, n));
            let n = rng.next_range(0..20) as usize;
            let p = gen_vector(&mut rng, n);
            verify_general::<M>(&f, &p);
        }
    }

    #[test]
    #[ignore]
    fn general_stress_dynamic() {
        let mut rng = Sfc64::new(0);
        for mo in [
            DynamicModInt::new(998244353),
            DynamicModInt::new(1001001001),
        ] {
            for _ in 0..1000 {
                let n = rng.next_range(0..20) as usize;
                let f = rng.next_vector(0..mo.n, n);
                let n = rng.next_range(0..20) as usize;
                let p = rng.next_vector(0..mo.n, n);
                let expected = DynamicMultipointEvaluationNaive::new(mo, p.clone()).eval(&f);
                if let Ok(found) = DynamicMultipointEvaluation::new(mo, p.clone()).eval(&f) {
                    assert_eq!(Ok(found), expected);
                }
            }
        }
    }
}
