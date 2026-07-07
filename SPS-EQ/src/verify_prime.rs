use ark_ec::{PrimeGroup, pairing::Pairing};
use ark_ff::{Field, UniformRand, Zero};
use ark_std::rand::RngCore;

use crate::sign_prime::{PublicKeyprime, Signatureprime};

impl<G: Pairing> PublicKeyprime<G> {
    /// Verify a Signatureprime
    pub fn verify(&self, msg: &Vec<G::G2>, sig: &Signatureprime<G>) -> bool {
        if msg.len() > self.capacity {
            panic!("The message is too long.");
        }

        let lhs = G::multi_pairing(self.points.iter(), msg.iter());
        let rhs = G::pairing(&sig.y, &sig.z);
        if lhs != rhs {
            return false;
        }

        let lhs = G::pairing(&sig.y, &G::G2::generator());
        let rhs = G::pairing(&G::G1::generator(), &sig.yp);
        if lhs != rhs {
            return false;
        } else {
            return true;
        }
    }

    pub fn verify_half(&self, msg: &Vec<G::G2>, sig: &Signatureprime<G>) -> bool {
        let half_capacity = self.capacity / 2;
        if msg.len() != half_capacity {
            panic!(
                "Message length must equal half of the public key length (expected {}, got {}).",
                half_capacity,
                msg.len()
            );
        }
        let lhs = G::multi_pairing(self.points.iter().take(half_capacity), msg.iter());
        let rhs = G::pairing(&sig.y, &sig.z);
        if lhs != rhs {
            return false;
        }

        let lhs = G::pairing(&sig.y, &G::G2::generator());
        let rhs = G::pairing(&G::G1::generator(), &sig.yp);
        lhs == rhs
    }
}

impl<G: Pairing> Signatureprime<G> {
    pub fn chg_rep<R: RngCore>(
        &self,
        msg: &Vec<G::G2>,
        pk: &PublicKeyprime<G>,
        mu: G::ScalarField,
        rng: &mut R,
    ) -> (Signatureprime<G>, Vec<G::G2>) {
        let mut psi = G::ScalarField::rand(rng);
        while psi.is_zero() {
            psi = G::ScalarField::rand(rng);
        }
        let psi_inv = psi.inverse().expect("Cannot be zero");

        let z = self.z * (psi * mu);
        let yp = self.yp * psi_inv;
        let y = self.y * psi_inv;

        let msg = msg.iter().map(|m| *m * mu).collect();

        (Signatureprime { z, yp, y }, msg)
    }

    pub fn chg_rep_half<R: RngCore>(
        &self,
        msg: &Vec<G::G2>,
        pk: &PublicKeyprime<G>,
        mu: G::ScalarField,
        rng: &mut R,
    ) -> (Signatureprime<G>, Vec<G::G2>) {
        let mut psi = G::ScalarField::rand(rng);
        while psi.is_zero() {
            psi = G::ScalarField::rand(rng);
        }
        let psi_inv = psi.inverse().expect("Cannot be zero");

        let z = self.z * (psi * mu);
        let yp = self.yp * psi_inv;
        let y = self.y * psi_inv;

        let msg = msg.iter().map(|m| *m * mu).collect();

        (Signatureprime { z, yp, y }, msg)
    }

    pub fn convertsig<R: RngCore>(
        &self,
        msg: &Vec<G::G2>,
        pk: &PublicKeyprime<G>,
        rho: G::ScalarField,
        rng: &mut R,
    ) -> Signatureprime<G> {
        let mut psi = G::ScalarField::rand(rng);
        while psi.is_zero() {
            psi = G::ScalarField::rand(rng);
        }
        let psi_inv = psi.inverse().expect("Cannot be zero");
        let z = self.z * (psi * rho);
        let yp = self.yp * psi_inv;
        let y = self.y * psi_inv;
        Signatureprime { z, yp, y }
    }
}

#[cfg(test)]
mod tests {
    use crate::sign_prime::{PublicKeyprime, SecretKeyprime, keygen};

    use ark_bls12_381;
    use ark_ff::UniformRand;

    #[test]
    fn sign_correctness() {
        let capacity = 4;
        let mut rng = ark_std::test_rng();
        let (sk, pk): (
            SecretKeyprime<ark_bls12_381::Bls12_381>,
            PublicKeyprime<ark_bls12_381::Bls12_381>,
        ) = keygen(capacity, &mut rng);

        let msg = vec![ark_bls12_381::G2Projective::rand(&mut rng); 4];
        let msg_half = vec![ark_bls12_381::G2Projective::rand(&mut rng); 2];
        let sig = sk.sign(&msg, &mut rng);
        let sig_half = sk.sign_half(&msg_half, &mut rng);
        assert_eq!(pk.verify(&msg, &sig), true);
        assert_eq!(pk.verify_half(&msg_half, &sig_half), true);

        let diff_msg = vec![ark_bls12_381::G2Projective::rand(&mut rng); 4];
        assert_eq!(pk.verify(&diff_msg, &sig), false);
    }

    #[test]
    fn chg_correctness() {
        let capacity = 4;
        let mut rng = ark_std::test_rng();
        let (sk, pk): (
            SecretKeyprime<ark_bls12_381::Bls12_381>,
            PublicKeyprime<ark_bls12_381::Bls12_381>,
        ) = keygen(capacity, &mut rng);

        let msg = vec![ark_bls12_381::G2Projective::rand(&mut rng); 4];
        let msg_half = vec![ark_bls12_381::G2Projective::rand(&mut rng); 2];
        let sig = sk.sign(&msg, &mut rng);
        let sig_half = sk.sign_half(&msg_half, &mut rng);
        let mu = ark_bls12_381::Fr::rand(&mut rng);
        let (sig_prime, msg_prime) = sig.chg_rep(&msg, &pk, mu, &mut rng);
        let (sig_prime_half, msg_prime_half) = sig_half.chg_rep_half(&msg_half, &pk, mu, &mut rng);
        assert_eq!(pk.verify(&msg_prime, &sig_prime), true);
        assert_eq!(pk.verify_half(&msg_prime_half, &sig_prime_half), true);
    }
}
