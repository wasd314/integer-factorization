use std::time::Duration;

use criterion::{
    BenchmarkId, Criterion, criterion_group, criterion_main,
};
use factor::perfect_power::{nth_root_floor1, nth_root_floor2};

fn compare_nth_root(c: &mut Criterion) {
    for n in [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] {
        let mut group = c.benchmark_group(format!("compare_nth_root_{n}"));
        group.warm_up_time(Duration::from_millis(1000));
        group.measurement_time(Duration::from_millis(2000));

        for y in (1..u128::BITS).filter(|i| i % 5 == 0) {
            group.bench_with_input(BenchmarkId::new("nth_root1", y), &y, |b, &y| {
                b.iter(|| nth_root_floor1(1 << y, n));
            });
            group.bench_with_input(BenchmarkId::new("nth_root2", y), &y, |b, &y| {
                b.iter(|| nth_root_floor2(1 << y, n));
            });
        }
        group.finish();
    }
}

criterion_group!(benches, compare_nth_root);
criterion_main!(benches);
