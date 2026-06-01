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

    let mut rng = Sfc64::new(0);
    const M: u128 = 7 << 120 | 1;
    let mo = DynamicModInt::new(M);
    let set_size = |est| if est < 1.0 { 100 } else { 20 };

    for ln in 10..=14 {
        let n = 1 << ln;
        let est_fast = 0.1 * (n as f64 / 10f64.powf(3.5));
        let est_naive = 0.1 * (n as f64 / 10f64.powf(3.5)).powi(2);

        group.sample_size(set_size(est_fast));
        group.bench_function(BenchmarkId::new("static_fast", n), |b| {
            let f = Fps::new(gen_vector::<M>(&mut rng, n));
            let points = gen_vector::<M>(&mut rng, n);
            b.iter(|| MultipointEvaluation::new(points.clone()).eval(&f));
        });
        group.bench_function(BenchmarkId::new("dynamic_fast", n), |b| {
            let f = rng.next_vector(0..mo.n, n);
            let points = rng.next_vector(0..mo.n, n);
            b.iter(|| DynamicMultipointEvaluation::new(mo, points.clone()).eval(&f));
        });

        if est_naive < 20.0 {
            group.sample_size(set_size(est_naive));
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
