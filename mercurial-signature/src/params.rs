use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use rand_core::RngCore;

use crate::{public_key::PublicKey, secret_key::SecretKey};

#[derive(Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PublicParams<E: Pairing> {
    // generators
    pub p1: E::G1,
    pub p2: E::G2,
}

impl<E: Pairing> PublicParams<E> {
    /// Generate public parameters.
    pub fn new<R: RngCore>(rng: &mut R) -> Self {
        let p1 = E::G1::rand(rng);
        let p2 = E::G2::rand(rng);
        PublicParams { p1, p2 }
    }

    /// Generate a key pair.
    pub fn key_gen<R: RngCore>(&self, rng: &mut R, size: u32) -> (PublicKey<E>, SecretKey<E>) {
        let x = (0..size)
            .map(|_| E::ScalarField::rand(rng))
            .collect::<Vec<E::ScalarField>>();
        let bx: Vec<E::G2> = x.iter().map(|xi| self.p2.mul(xi)).collect();
        (PublicKey { bx }, SecretKey { x })
    }
}
