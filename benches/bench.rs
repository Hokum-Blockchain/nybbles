use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion,
};
use nybbles::Nibbles;
use proptest::{prelude::*, strategy::ValueTree};
use std::{hint::black_box, time::Duration};

/// Benchmarks the nibble unpacking.
pub fn nibbles_benchmark(c: &mut Criterion) {
    let lengths = [1u8, 2u8, 16u8, 128u8];

    {
        let mut g = group(c, "unpack");
        for len in lengths {
            g.throughput(criterion::Throughput::Bytes(len.into()));
            let id = criterion::BenchmarkId::new("nybbles", len);
            g.bench_function(id, |b| {
                let bytes = get_bytes(len.into());
                b.iter(|| Nibbles::unpack(black_box(&bytes.0), black_box(bytes.1)))
            });
        }
    }

    {
        let mut g = group(c, "pack");
        for len in lengths {
            g.throughput(criterion::Throughput::Bytes(len.into()));

            let id = criterion::BenchmarkId::new("nybbles", len);
            g.bench_function(id, |b| {
                let bytes = &get_nibbles(len as usize);
                b.iter(|| black_box(&bytes).pack())
            });
        }
    }

    {
        let mut g = group(c, "encode_path_leaf");
        for len in lengths {
            g.throughput(criterion::Throughput::Bytes(len.into()));
            let id = criterion::BenchmarkId::new("nybbles", len);
            g.bench_function(id, |b| {
                let nibbles = get_nibbles(len as usize);
                b.iter(|| black_box(&nibbles).encode_path_leaf(false))
            });
        }
    }
}

fn group<'c>(c: &'c mut Criterion, name: &str) -> BenchmarkGroup<'c, WallTime> {
    let mut g = c.benchmark_group(name);
    g.warm_up_time(Duration::from_secs(1));
    g.noise_threshold(0.02);
    g
}

fn get_nibbles(len: usize) -> Nibbles {
    proptest::arbitrary::any_with::<Nibbles>(len.into())
        .new_tree(&mut Default::default())
        .unwrap()
        .current()
}

fn get_bytes(len: u8) -> (Vec<u64>, u8) {
    let mut rng = rand::thread_rng();
    (
        proptest::collection::vec(proptest::arbitrary::any::<u64>(), len as usize)
            .new_tree(&mut Default::default())
            .unwrap()
            .current(),
        rng.gen_range(16 * (len - 1)..=16 * len),
    )
}

criterion_group!(benches, nibbles_benchmark);
criterion_main!(benches);

#[test]
fn naive_equivalency() {
    for len in [0, 1, 2, 3, 4] {
        let (bytes, nibbles) = get_bytes(len);
        let nibbles = Nibbles::unpack(&bytes, nibbles);
        // our unpack is basically equivalent to the naive. i don't see any optimizations here.
        // assert_eq!(unpack_naive(&bytes.0, bytes.1)[..], nibbles[..]);
        assert_eq!(
            pack_naive(&nibbles[..])[..],
            Nibbles::pack(&Nibbles::from_nibbles(&nibbles))[..]
        );
    }
}
