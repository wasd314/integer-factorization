use std::collections::VecDeque;

use criterion::{
    AxisScale, BenchmarkId, Criterion, PlotConfiguration, criterion_group, criterion_main,
};
use factor::{
    convolution::u128::DynamicConvolution, modint::u128::DynamicModInt,
    multipoint_evaluation::u128::DynamicMultipointEvaluation, utility::Sfc64,
};

fn diff_product(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff_product");
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    group.plot_config(plot_config);

    let mut rng = Sfc64::new(0);
    const M: u128 = 7 << 120 | 1;
    let mo = DynamicModInt::new(M);
    let set_size = |est| if est < 1.0 { 100 } else { 20 };
    let ns = {
        let mut ns = vec![];
        ns.extend((9..=14).map(|i| 1 << i));
        ns.extend([1400, 3600, 11000]);
        ns.sort();
        ns
    };
    for n in ns {
        let est_fast = 0.1 * (n as f64 / 10f64.powf(3.5));
        let est_naive = 0.1 * (n as f64 / 10f64.powf(3.5)).powi(2);

        group.sample_size(set_size(est_fast));
        group.bench_function(BenchmarkId::new("fast_main", n), |b| {
            let baby = rng.next_vector(0..mo.n, n);
            let giant = rng.next_vector(0..mo.n, n);
            // product of (x - bj) for bj in baby
            let f_baby = {
                let mut q = baby
                    .iter()
                    .map(|c| vec![mo.neg(*c), mo.one()])
                    .collect::<VecDeque<_>>();
                q.push_back(vec![mo.one()]);
                while q.len() >= 2
                    && let Some(f1) = q.pop_front()
                    && let Some(f2) = q.pop_front()
                {
                    q.push_back(mo.convolution_arbitrary(&f1, &f2));
                }
                q.pop_front().unwrap()
            };
            b.iter(|| DynamicMultipointEvaluation::new(mo, giant.clone()).eval(&f_baby));
        });
        group.bench_function(BenchmarkId::new("fast", n), |b| {
            let baby = rng.next_vector(0..mo.n, n);
            let giant = rng.next_vector(0..mo.n, n);
            b.iter(|| {
                // product of (x - bj) for bj in baby
                let f_baby = {
                    let mut q = baby
                        .iter()
                        .map(|c| vec![mo.neg(*c), mo.one()])
                        .collect::<VecDeque<_>>();
                    q.push_back(vec![mo.one()]);
                    while q.len() >= 2
                        && let Some(f1) = q.pop_front()
                        && let Some(f2) = q.pop_front()
                    {
                        q.push_back(mo.convolution_arbitrary(&f1, &f2));
                    }
                    q.pop_front().unwrap()
                };
                DynamicMultipointEvaluation::new(mo, giant.clone()).eval(&f_baby)
            });
        });

        // if est_naive < 20.0
        {
            group.sample_size(set_size(est_naive));
            group.bench_function(BenchmarkId::new("naive", n), |b| {
                let baby = rng.next_vector(0..mo.n, n);
                let giant = rng.next_vector(0..mo.n, n);

                b.iter(|| {
                    // prod(ai - bj for bj in baby) for ai in giant
                    giant
                        .iter()
                        .map(|&ai| {
                            baby.iter()
                                .fold(mo.one(), |acc, &bj| mo.mul(acc, mo.sub(ai, bj)))
                        })
                        .collect::<Vec<_>>()
                });
            });
        }
    }
    group.finish();
}

criterion_group!(benches, diff_product);
criterion_main!(benches);
