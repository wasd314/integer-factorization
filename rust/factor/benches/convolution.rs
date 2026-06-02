use std::time::Duration;

use criterion::{
    AxisScale, BenchmarkId, Criterion, PlotConfiguration, criterion_group, criterion_main,
};
use factor::{convolution::u128::DynamicConvolution, modint::u128::DynamicModInt, utility::Sfc64};

fn compare_convolution(c: &mut Criterion) {
    let mut group = c.benchmark_group("dynamic_convolution");
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    group.plot_config(plot_config);
    group.warm_up_time(Duration::from_millis(100));
    group.measurement_time(Duration::from_millis(200));
    let mut rng = Sfc64::new(0);
    const M: u128 = 7 << 120 | 1;
    let mo = DynamicModInt::new(M);
    let set_size = |est| if est < 0.1 { 100 } else { 20 };

    for n in (1..=13).flat_map(|ln| [2 << ln, 3 << ln]) {
        // n*8 -> time*10
        let est_fast = 1e-4 * (n as f64 / 100.0).powf(1.1);
        let est_naive = 1e-4 * (n as f64 / 100.0).powi(2);

        group.sample_size(set_size(est_fast));
        group.bench_function(BenchmarkId::new("convolution_ntt", n), |b| {
            let f = rng.next_vector(0..mo.n, n);
            let g = rng.next_vector(0..mo.n, n);
            b.iter(|| mo.convolution_arbitrary(&f, &g));
        });
        group.bench_function(BenchmarkId::new("convolution_karatsuba", n), |b| {
            let f = rng.next_vector(0..mo.n, n);
            let g = rng.next_vector(0..mo.n, n);
            b.iter(|| mo.convolution_karatsuba(&f, &g));
        });
        group.bench_function(BenchmarkId::new("middle_product_ntt", n), |b| {
            let f = rng.next_vector(0..mo.n, n);
            let g = rng.next_vector(0..mo.n, n * 2 - 1);
            b.iter(|| mo.middle_product_arbitrary(&f, &g));
        });
        group.bench_function(BenchmarkId::new("middle_product_karatsuba", n), |b| {
            let f = rng.next_vector(0..mo.n, n);
            let g = rng.next_vector(0..mo.n, n * 2 - 1);
            b.iter(|| mo.middle_product_karatsuba(&f, &g));
        });

        if n <= 2200 {
            group.sample_size(set_size(est_naive));
            group.bench_function(BenchmarkId::new("convolution_naive", n), |b| {
                let f = rng.next_vector(0..mo.n, n);
                let g = rng.next_vector(0..mo.n, n);
                b.iter(|| mo.convolution_naive(&f, &g));
            });
            group.bench_function(BenchmarkId::new("middle_product_naive", n), |b| {
                let f = rng.next_vector(0..mo.n, n);
                let g = rng.next_vector(0..mo.n, n * 2 - 1);
                b.iter(|| mo.middle_product_naive(&f, &g));
            });
        }
    }
    group.finish();
}

criterion_group!(benches, compare_convolution);
criterion_main!(benches);
