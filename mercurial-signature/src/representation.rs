use crate::signature::Signature;
use ark_ec::pairing::Pairing;
use ark_std::UniformRand;
use rand_core::RngCore;

/// Change the representation of the message and the signature.
///
/// ## Example
///
///
/// ```rust
/// use mercurial_signature::{change_representation, Fr, PublicParams, UniformRand, G1};
///
/// let mut rng = rand::thread_rng();
/// let pp = PublicParams::new(&mut rng);
/// let (pk, sk) = pp.key_gen(&mut rng, 10);
/// let mut message = (0..10).map(|_| G1::rand(&mut rng)).collect::<Vec<G1>>();
/// let mut sig = sk.sign(&mut rng, &pp, &message);
///
/// let u = Fr::rand(&mut rng);
/// change_representation(&mut rng, &mut message, &mut sig, u);
/// assert!(pk.verify(&pp, &message, &sig));
/// ```
pub fn change_representation<E: Pairing, R: RngCore>(
    rng: &mut R,
    message: &mut [E::G1],
    signature: &mut Signature<E>,
    u: E::ScalarField,
) {
    let f = E::ScalarField::rand(rng);
    signature.convert_with_f(u, f);

    message.iter_mut().for_each(|mi| *mi *= u);
}
