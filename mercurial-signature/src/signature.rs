use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{One, UniformRand};
use rand_core::RngCore;

#[derive(Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Signature<E: Pairing> {
    pub(crate) z: E::G1,
    pub(crate) y1: E::G1,
    pub(crate) y2: E::G2,
}

impl<E: Pairing> Signature<E> {
    /// Convert the signature.
    /// This function converts the signature to a new signature that is equivalent to the original signature.
    /// The input scalar `p` must be the same as the one used in the conversion of the public key and the secret key.
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
    pub fn convert<R: RngCore>(&mut self, rng: &mut R, p: E::ScalarField) {
        let f = E::ScalarField::rand(rng);
        self.convert_with_f(p, f);
    }

    /// Convert the signature with a scalar `f`.
    pub(crate) fn convert_with_f(&mut self, p: E::ScalarField, f: E::ScalarField) {
        self.z *= p * f;
        self.y1 *= E::ScalarField::one() / f;
        self.y2 *= E::ScalarField::one() / f;
    }
}
