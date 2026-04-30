use criterion::{
    AxisScale, BenchmarkId, Criterion, PlotConfiguration, criterion_group, criterion_main,
};
use factor::{
    ecm::{CheckOdd, Ecm, EcmBound, ExponentialBound, UseMultiEval},
    pollard_rho::{Brent, PollardRho},
    wrapper::Factorize,
};

fn compare_all(c: &mut Criterion) {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("compare_all");
    group.plot_config(plot_config);

    let b1 = 10000;
    let b2 = b1 * 1000;
    let bound = ExponentialBound::new(EcmBound { b1, b2 }, 2, 5000);
    for n in [
        100003 * 100019u128,
        1000003 * 1000033,
        12345701 * 12345709,
        1234567891 * 1234567907,
        123456789059 * 123456789061,
        123456789012419 * 123456789012421,
        1000000000000000003 * 1000000000000000009,
        9223372036854775837 * 9223372036854775907,
    ] {
        let param = n;
        if n.ilog2() > 100 {
            group.sample_size(10);
        }
        group.bench_with_input(BenchmarkId::new("UseMultiEval", param), &n, |b, &n| {
            b.iter(|| {
                let mut f = Ecm::new(n as u64, bound, UseMultiEval);
                f.factorize(n);
            });
        });
        group.bench_with_input(BenchmarkId::new("CheckOdd", param), &n, |b, &n| {
            b.iter(|| {
                let mut f = Ecm::new(n as u64, bound, CheckOdd);
                f.factorize(n);
            });
        });
        group.bench_with_input(
            BenchmarkId::new("PollardRhoBrentBatch", param),
            &n,
            |b, &n| {
                b.iter(|| {
                    let mut f = PollardRho::new(Brent, true);
                    f.factorize(n);
                });
            },
        );
        if n.ilog2() < 100 {
            group.bench_with_input(
                BenchmarkId::new("PollardRhoBrentNoBatch", param),
                &n,
                |b, &n| {
                    b.iter(|| {
                        let mut f = PollardRho::new(Brent, false);
                        f.factorize(n);
                    });
                },
            );
        }
    }
    group.finish();
}

criterion_group!(benches, compare_all);
criterion_main!(benches);
