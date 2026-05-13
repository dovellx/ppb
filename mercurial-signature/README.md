[![version]][crates.io] [![workflow status]][workflow]

[version]: https://img.shields.io/crates/v/mercurial-signature.svg
[crates.io]: https://crates.io/crates/mercurial-signature
[workflow status]: https://github.com/AlvinHon/mercurial-signature/actions/workflows/build_and_test.yml/badge.svg?branch=main
[workflow]: https://github.com/AlvinHon/mercurial-signature/actions/workflows/build_and_test.yml

# Mercurial Signature

This is a simple implementation of the Mercurial signature scheme which is instroduced in the paper [Delegatable Anonymous Credentials from Mercurial Signatures](https://eprint.iacr.org/2018/923), by Elizabeth C. Crites and Anna Lysyanskaya.

> A mercurial signature, which allows a signature `sig` on a message `m` under public key `pk` to be transformed into a signature `sig'` on an equivalent but unlinkable message `m'` under an equivalent but unlinkable public key `pk'`.

The crate implements the signature scheme with use of the elliptic curve `Bls12-381`. It uses the dependencies from [Arkworks](https://github.com/arkworks-rs/) which is a rust ecosystem for cryptography.

Note: this repository has not been thoroughly audited. Please take your own risk if you use it in production environment.

## Example

```rust
use mercurial_signature::{change_representation, Fr, PublicParams, UniformRand, G1};

let mut rng = rand::thread_rng();
let pp = PublicParams::new(&mut rng);
let (mut pk, mut sk) = pp.key_gen(&mut rng, 10);
let mut message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
let mut sig = sk.sign(&mut rng, &pp, &message);

// Convert keys and signatures (i.e. randomization)
let p = Fr::rand(&mut rng);
pk.convert(p);
sk.convert(p); // not necessary for the following steps.
sig.convert(&mut rng, p);
// public key, secret key and the signatre are different now.

// Change the message and signature (i.e. randomization)
let u = Fr::rand(&mut rng);
change_representation(&mut rng, &mut message, &mut sig, u);
// message and the signature are different now.

// Verification can still pass.
assert!(pk.verify(&pp, &message, &sig));
```