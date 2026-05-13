use ark_ec::{pairing::Pairing, PrimeGroup};
use ark_ff::{Field, UniformRand, Zero};
use ark_std::rand::RngCore;

/// Secret key
pub struct SecretKey<G: Pairing> {
    pub capacity: usize,
    scalars: Vec<G::ScalarField>,
}

/// Public key
#[derive(Clone)]
pub struct PublicKey<G: Pairing> {
    pub capacity: usize,
    pub points: Vec<G::G2>,
}

/// Signature
pub struct Signature<G: Pairing> {
    pub z: G::G1,
    pub y: G::G1,
    pub yp: G::G2,
}

/// Generate a secret-public key pair
pub fn keygen<G: Pairing, R: RngCore>(capacity: usize, rng: &mut R) -> (SecretKey<G>, PublicKey<G>) {
    let scalars: Vec<G::ScalarField> = (0 .. capacity)
        .map(|_| G::ScalarField::rand(rng))
        .collect();
    let points = scalars
        .iter()
        .map(|s| G::G2::generator() * s)
        .collect();
    (SecretKey { capacity, scalars }, PublicKey { capacity, points })
}

impl<G: Pairing> SecretKey<G> {
    /// Sign a message
    pub fn sign<R: RngCore>(&self, msg: &Vec<G::G1>, rng: &mut R) -> Signature<G> {
        if msg.len() > self.capacity {
            panic!("The message is too long.");
        }

        let mut r = G::ScalarField::rand(rng);
        while r.is_zero() {
            r = G::ScalarField::rand(rng);
        }
        let r_inv = r.inverse().expect("Cannot be zero");

        let prod = msg
            .iter()
            .zip(self.scalars.iter())
            .map(|(m, x)| *m * *x)
            .fold(G::G1::zero(), |acc, val| acc + val);

        let z = prod * r;
        let y = G::G1::generator() * r_inv;
        let yp = G::G2::generator() * r_inv;

        Signature { z, y, yp }
    }

    pub fn sign_half<R: RngCore>(&self, msg: &Vec<G::G1>, rng: &mut R) -> Signature<G> {
        let half_capacity = self.capacity / 2;
        if msg.len() != half_capacity {
            panic!(
                "Message length must equal half of the secret key length (expected {}, got {}).",
                half_capacity,
                msg.len()
            );
        }
        let mut r = G::ScalarField::rand(rng);
        while r.is_zero() {
            r = G::ScalarField::rand(rng);
        }
        let r_inv = r.inverse().expect("Cannot be zero");
        let prod = msg
            .iter()
            .zip(self.scalars.iter().take(half_capacity))
            .map(|(m, x)| *m * *x)
            .fold(G::G1::zero(), |acc, val| acc + val);

        let z = prod * r;
        let y = G::G1::generator() * r_inv;
        let yp = G::G2::generator() * r_inv;

        Signature { z, y, yp }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_bls12_381;

    #[test]
    fn key_length() {
        let capacity = 4;
        let mut rng = ark_std::test_rng();
        let (sk, pk): (SecretKey<ark_bls12_381::Bls12_381>, PublicKey<ark_bls12_381::Bls12_381>) = keygen(capacity, &mut rng);
        assert_eq!(sk.scalars.len(), capacity, "The length of secret key should be {}.", capacity);
        assert_eq!(pk.points.len(), capacity, "The length of public key should be {}.", capacity);
    }

    #[test]
    fn secret_key_randomness() {
        let capacity = 4;
        let mut rng = ark_std::test_rng();
        let (sk, _): (SecretKey<ark_bls12_381::Bls12_381>, PublicKey<ark_bls12_381::Bls12_381>) = keygen(capacity, &mut rng);
        for i in 0 .. sk.scalars.len() {
            for j in i + 1 .. sk.scalars.len() {
                assert_ne!(sk.scalars[i], sk.scalars[j], "The {}-th part and {}-th part should not be equal", i, j);
            }
        }
    }

    #[test]
    fn secret_key_uniqueness() {
        let capacity = 4;
        let mut rng = ark_std::test_rng();
        let (sk1, _): (SecretKey<ark_bls12_381::Bls12_381>, PublicKey<ark_bls12_381::Bls12_381>) = keygen(capacity, &mut rng);
        let (sk2, _): (SecretKey<ark_bls12_381::Bls12_381>, PublicKey<ark_bls12_381::Bls12_381>) = keygen(capacity, &mut rng);
        assert_ne!(sk1.scalars, sk2.scalars, "Two secret keys should be different.");
    }
}