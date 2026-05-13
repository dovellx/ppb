use ark_ec::pairing::Pairing;
use ark_std::{One, UniformRand, Zero};
use std::ops::Mul;

use crate::{params::PublicParams, signature::Signature};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand_core::RngCore;

#[derive(Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct SecretKey<E: Pairing> {
    // sk = (x1,...,xl)
    pub(crate) x: Vec<E::ScalarField>,
}

impl<E: Pairing> SecretKey<E> {
    /// Length of the secret key.
    pub fn length(&self) -> usize {
        self.x.len()
    }

    /// Sign a message.
    ///
    /// ## Safety
    /// This function panics if the length of the secret key and the message are different.
    ///
    /// ## Example
    ///
    /// ```rust
    /// use mercurial_signature::{change_representation, Fr, PublicParams, UniformRand, G1};
    ///
    /// let mut rng = rand::thread_rng();
    /// let pp = PublicParams::new(&mut rng);
    /// let (pk, sk) = pp.key_gen(&mut rng, 10);
    /// let message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
    /// let sig = sk.sign(&mut rng, &pp, &message);
    /// assert!(pk.verify(&pp, &message, &sig));
    /// ```
    pub fn sign<R: RngCore>(
        &self,
        rng: &mut R,
        pp: &PublicParams<E>,
        message: &[E::G1],
    ) -> Signature<E> {
        if self.x.len() < message.len() {
            panic!("The length of the secret key must be equal or greater than the length of the message.");
        }

        let y = E::ScalarField::rand(rng);
        // z = (x1 M1 + ... + xl Ml) * y
        let z = message
            .iter()
            .zip(self.x.iter())
            .fold(E::G1::zero(), |acc, (m, xi)| acc + m.mul(y * xi));
        // y1 = p1^(1/y)
        let y1 = pp.p1.mul(E::ScalarField::one() / y);
        // y2 = p2^(1/y)
        let y2 = pp.p2.mul(E::ScalarField::one() / y);
        Signature { z, y1, y2 }
    }

    /// Convert the secret key.
    /// This function converts the secret key to a new secret key that is equivalent to the original secret key.
    /// The input scalar `p` must be the same as the one used in the conversion of the public key and the signature.
    ///
    /// ## Example
    ///
    /// ```rust
    /// use mercurial_signature::{change_representation, Fr, PublicParams, UniformRand, G1};
    ///
    /// let mut rng = rand::thread_rng();
    /// let pp = PublicParams::new(&mut rng);
    /// let (mut pk, mut sk) = pp.key_gen(&mut rng, 10);
    /// let message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
    /// let mut sig = sk.sign(&mut rng, &pp, &message);
    ///
    /// let p = Fr::rand(&mut rng);
    /// pk.convert(p);
    /// sk.convert(p);
    /// sig.convert(&mut rng, p);
    /// assert!(pk.verify(&pp, &message, &sig));
    /// ```
    pub fn convert(&mut self, p: E::ScalarField) {
        self.x.iter_mut().for_each(|xi| *xi *= p);
    }
}
