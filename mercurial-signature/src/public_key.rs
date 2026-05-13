use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::Zero;

use crate::{params::PublicParams, signature::Signature};

#[derive(Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PublicKey<E: Pairing> {
    // pk = (p2^x1,...,p2^xl) where (x1,...,xl) is the secret key
    pub(crate) bx: Vec<E::G2>,
}

impl<E: Pairing> PublicKey<E> {
    /// Length of the public key.
    pub fn length(&self) -> usize {
        self.bx.len()
    }

    /// Convert the public key.
    /// This function converts the public key to a new public key that is equivalent to the original public key.
    /// The input scalar `p` must be the same as the one used in the conversion of the secret key and the signature.
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
    pub fn verify(&self, pp: &PublicParams<E>, message: &[E::G1], sig: &Signature<E>) -> bool {
        // check length l
        if self.bx.len() < message.len() {
            return false;
        }

        // e(y1, p2) == e(p1, y2)
        let lhs = E::pairing(sig.y1, pp.p2);
        let rhs = E::pairing(pp.p1, sig.y2);
        if lhs != rhs {
            return false;
        }

        // e(z, y2) == e(m1, bx1) * ... * e(ml, bxl)
        let lhs = E::pairing(sig.z, sig.y2);
        let rhs = message
            .iter()
            .zip(self.bx.iter())
            .fold(E::pairing(E::G1::zero(), E::G2::zero()), |acc, (m, bxi)| {
                acc + E::pairing(*m, *bxi)
            });
        lhs == rhs
    }

    /// Convert the public key.
    /// This function converts the public key to a new public key that is equivalent to the original public key.
    /// The input scalar `p` must be the same as the one used in the conversion of the secret key and the signature.
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
        self.bx.iter_mut().for_each(|bxi| *bxi *= p);
    }
}
