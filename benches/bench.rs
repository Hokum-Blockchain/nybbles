use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion,
};
use nybbles::Nibbles;
use proptest::{prelude::*, strategy::ValueTree};
use std::{hint::black_box, time::Duration};

/// Benchmarks the nibble unpacking.
pub fn nibbles_benchmark(c: &mut Criterion) {
    let lengths = [1u8, 2u8, 4u8, 32u8, 128u8];

    {
        let mut g = group(c, "unpack");
        for len in lengths {
            g.throughput(criterion::Throughput::Bytes(len.into()));
            let id = criterion::BenchmarkId::new("nybbles", len);
            g.bench_function(id, |b| {
                let bytes = &get_bytes(len.into())[..];
                b.iter(|| Nibbles::unpack(black_box(bytes), black_box((len as usize) << 4)))
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

fn get_bytes(len: u8) -> Vec<u64> {
    proptest::collection::vec(proptest::arbitrary::any::<u64>(), len as usize)
        .new_tree(&mut Default::default())
        .unwrap()
        .current()
}

fn unpack_naive(bytes: &[u64], len: usize) -> Vec<u8> {
    (0..len).map(|l| ((bytes.as_ref()[l / 16] >> (60 - 4 * (l % 16))) & 0xf) as u8).collect()
}

criterion_group!(benches, nibbles_benchmark);
criterion_main!(benches);

#[test]
fn naive_equivalency() {
    for len in [1usize, 2, 4, 32, 128] {
        let bytes = get_bytes(len);
        let nibbles = Nibbles::unpack(&bytes, 16 * len);
        // our unpack is basically equivalent to the naive. i don't see any optimizations here.
        assert_eq!(unpack_naive(&bytes.0, bytes.1)[..], nibbles[..]);
        assert_eq!(
            pack_naive(&nibbles[..])[..],
            Nibbles::pack(&Nibbles::from_nibbles(&nibbles))[..]
        );
        println!("OK");
    }
}
