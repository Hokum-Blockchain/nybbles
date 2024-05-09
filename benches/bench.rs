use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion,
};
use nybbles::Nibbles;
use proptest::{prelude::*, strategy::ValueTree};
use std::{hint::black_box, time::Duration};

/// Benchmarks the nibble unpacking.
pub fn nibbles_benchmark(c: &mut Criterion) {
    let lengths = [16u64, 32, 256, 2048];

    {
        let mut g = group(c, "unpack");
        for len in lengths {
            g.throughput(criterion::Throughput::Bytes(len));

            let id = criterion::BenchmarkId::new("naive", len);
            g.bench_function(id, |b| {
                let bytes = get_bytes(len as usize);
                b.iter(|| unpack_naive(black_box(&bytes.0), black_box(bytes.1)))
            });

            let id = criterion::BenchmarkId::new("nybbles", len);
            g.bench_function(id, |b| {
                let bytes = get_bytes(len as usize);
                b.iter(|| Nibbles::unpack(black_box(&bytes.0), black_box(bytes.1)))
            });
        }
    }

    {
        let mut g = group(c, "pack");
        for len in lengths {
            g.throughput(criterion::Throughput::Bytes(len));

            let id = criterion::BenchmarkId::new("naive", len);
            g.bench_function(id, |b| {
                let bytes = &get_nibbles(len as usize)[..];
                b.iter(|| pack_naive(black_box(bytes)))
            });

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
            g.throughput(criterion::Throughput::Bytes(len));
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

fn get_bytes(len: usize) -> (Vec<u64>, u8) {
    let rng = rand::thread_rng();
    (
        proptest::collection::vec(proptest::arbitrary::any::<u64>(), len)
            .new_tree(&mut Default::default())
            .unwrap()
            .current(),
        rng.gen_range(16 * (len - 1)..=16 * len),
    )
}

fn unpack_naive(bytes: &[u64], nibbles: u8) -> Vec<u64> {
    bytes.iter().flat_map(|byte| [byte >> 4, byte & 0x0f]).collect()
}

fn pack_naive(bytes: &[u64]) -> Vec<u64> {
    let chunks = bytes.chunks_exact(2);
    let rem = chunks.remainder();
    chunks.map(|chunk| (chunk[0] << 4) | chunk[1]).chain(rem.iter().copied()).collect()
}

criterion_group!(benches, nibbles_benchmark);
criterion_main!(benches);

#[test]
fn naive_equivalency() {
    for len in [0, 1, 2, 3, 4] {
        let (bytes, nibbles) = get_bytes(len);
        let nibbles = Nibbles::unpack(&bytes, nibbles);
        assert_eq!(unpack_naive(&bytes.0, bytes.1)[..], nibbles[..]);
        assert_eq!(pack_naive(&nibbles[..])[..], nibbles.pack()[..]);
    }
}
