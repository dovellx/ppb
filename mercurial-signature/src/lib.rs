#![doc = include_str!("../README.md")]

mod params;
mod public_key;
mod representation;
pub use representation::change_representation;
mod secret_key;
mod signature;

// type alias for the curve Bls12_381
pub type PublicParams = params::PublicParams<ark_bls12_381::Bls12_381>;
pub type PublicKey = public_key::PublicKey<ark_bls12_381::Bls12_381>;
pub type SecretKey = secret_key::SecretKey<ark_bls12_381::Bls12_381>;
pub type Signature = signature::Signature<ark_bls12_381::Bls12_381>;

// re-export the curve types
pub type G1 = ark_bls12_381::G1Projective;
pub type G2 = ark_bls12_381::G2Projective;
pub type Fr = ark_bls12_381::Fr;

// re-export for enabling rand() function
pub use ark_std::UniformRand;
