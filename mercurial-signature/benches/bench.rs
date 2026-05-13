use std::time::Duration;

use ark_serialize::CanonicalSerialize;
use ark_std::test_rng;
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use mercurial_signature::{PublicKey, PublicParams, SecretKey, UniformRand, G1};
use rand::Rng;

criterion_group! {
    name = signature;
    config = Criterion::default().sample_size(10).measurement_time(Duration::from_secs(2));
    targets = bench_sign, bench_verify,
}

criterion_main!(signature,);

fn bench_sign(c: &mut Criterion) {
    let mut rng = test_rng();

    let mut group = c.benchmark_group("bench_sign");
    for size in [10, 100, 1000] {
        let (pp, _, sk, message) = setup(&mut rng, size);

        let message_size = message.iter().map(|m| m.compressed_size()).sum::<usize>();
        group.throughput(Throughput::Bytes(message_size as u64));

        group.bench_with_input(format!("size={}", size), &size, |b, _| {
            b.iter(|| sk.sign(&mut rng, &pp, &message.as_ref()))
        });
    }
}

fn bench_verify(c: &mut Criterion) {
    let mut rng = test_rng();

    let mut group = c.benchmark_group("bench_verify");
    for size in [10, 100, 1000] {
        let (pp, pk, sk, message) = setup(&mut rng, size);
        let sig = sk.sign(&mut rng, &pp, &message);

        let message_size = message.iter().map(|m| m.compressed_size()).sum::<usize>();
        group.throughput(Throughput::Bytes(message_size as u64));

        group.bench_with_input(format!("size={}", size), &size, |b, _| {
            b.iter(|| pk.verify(&pp, &message.as_ref(), &sig))
        });
    }
}

fn setup(rng: &mut impl Rng, size: u32) -> (PublicParams, PublicKey, SecretKey, Vec<G1>) {
    let pp = PublicParams::new(rng);
    let (pk, sk) = pp.key_gen(rng, size);
    let message = (0..size).map(|_| G1::rand(rng)).collect::<Vec<G1>>();
    (pp, pk, sk, message)
}
