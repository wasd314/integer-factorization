use std::time::Duration;

use criterion::{
    AxisScale, BenchmarkId, Criterion, PlotConfiguration, criterion_group, criterion_main,
};
use factor::{
    fps::u128::Fps,
    modint::u128::{DynamicModInt, StaticModInt as Mint},
    multipoint_evaluation::u128::{
        DynamicMultipointEvaluation, DynamicMultipointEvaluationNaive, MultipointEvaluation,
        MultipointEvaluationNaive,
    },
    utility::Sfc64,
};

fn gen_vector<const M: u128>(rng: &mut Sfc64, n: usize) -> Vec<Mint<M>> {
    rng.next_vector(0..M, n)
        .into_iter()
        .map(Mint::new)
        .collect()
}

fn compare_eval(c: &mut Criterion) {
    let mut group = c.benchmark_group("multipoint_evaluation");
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    group.plot_config(plot_config);

    // group.warm_up_time(Duration::from_millis(1000));
    // group.measurement_time(Duration::from_millis(2000));
    group.sample_size(10);
    let mut rng = Sfc64::new(0);
    const M: u128 = 7 << 120 | 1;
    let mo = DynamicModInt::new(M);

    for ln in 3..19 {
        let n = 1 << ln;
        group.bench_function(BenchmarkId::new("static_fast", n), |b| {
            let f = Fps::new(gen_vector::<M>(&mut rng, n));
            let points = gen_vector::<M>(&mut rng, n);
            // let f0 = Fps::new(vec![]);
            // let mut i = 0;
            // b.iter(|| {
            //     MultipointEvaluation::new(points.clone()).eval(if i == 0 { &f } else { &f0 });
            //     i = (i + 1) % 20
            // });
            b.iter(|| MultipointEvaluation::new(points.clone()).eval(&f));
        });
        group.bench_function(BenchmarkId::new("dynamic_fast", n), |b| {
            let f = rng.next_vector(0..mo.n, n);
            let points = rng.next_vector(0..mo.n, n);
            b.iter(|| DynamicMultipointEvaluation::new(mo, points.clone()).eval(&f));
        });
        if ln <= 14 {
            group.bench_function(BenchmarkId::new("static_naive", n), |b| {
                let f = Fps::new(gen_vector::<M>(&mut rng, n));
                let points = gen_vector::<M>(&mut rng, n);
                b.iter(|| MultipointEvaluationNaive::new(points.clone()).eval(&f));
            });
            group.bench_function(BenchmarkId::new("dynamic_naive", n), |b| {
                let f = rng.next_vector(0..mo.n, n);
                let points = rng.next_vector(0..mo.n, n);
                b.iter(|| DynamicMultipointEvaluationNaive::new(mo, points.clone()).eval(&f));
            });
        }
    }
    group.finish();
}

criterion_group!(benches, compare_eval);
criterion_main!(benches);
