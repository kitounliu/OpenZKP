#![warn(clippy::all)]
use criterion::{black_box, Criterion};
use zkp_elliptic_curve::{Affine, ScalarFieldElement};
use zkp_elliptic_curve_crypto as ecc;
use zkp_macros_decl::{u256h};
use zkp_u256::U256;
use zkp_primefield::{FieldElement, Zero};
use zkp_stark::{
    Provable, Verifiable,
};

use zkp_stark::ecdsa::signature::*;

use rand_core::{OsRng, RngCore};


fn bench_prove(crit: &mut Criterion) {
    let mut rng = OsRng;

    let mut secret = [0u64; 4];
    secret[0] = rng.next_u64();
    secret[1] = rng.next_u64();
    secret[2] = rng.next_u64();
    secret[3] = rng.next_u64();

    let mut hash = [0u64; 4];
    hash[0] = rng.next_u64();
    hash[1] = rng.next_u64();
    hash[2] = rng.next_u64();
    hash[3] = rng.next_u64();

    let private_key = ecc::PrivateKey::from(U256::from_limbs(secret));
    let digest = ScalarFieldElement::from(U256::from_limbs(hash));
  //  println!("digest = {:?}", digest);
    let public_key = ecc::PublicKey::from(&private_key);
    let public_affine = public_key.as_affine();
    let public = match public_affine.clone() {
        Affine::Zero => (FieldElement::zero(), FieldElement::zero()),
        Affine::Point { x, y } => (x, y),
    };
    let sigma = private_key.sign(&digest);
    assert!(public_key.verify(&digest, &sigma));

    let sig =  (FieldElement::from(U256::from(sigma.r())),
                FieldElement::from(U256::from(sigma.w())));

 //   println!("Constructing claim");
    let claim = Claim {
        hash: FieldElement::from(U256::from(&digest)),
        who:  public.clone(),
    };
    let witness = Witness {
        signature: sig,
    };

    crit.bench_function("Creating a ecdsa proof", move |bench| {
        bench.iter(|| black_box( claim.prove(&witness).unwrap()))
    });
}


fn bench_verify(crit: &mut Criterion) {
    let mut rng = OsRng;

    let mut secret = [0u64; 4];
    secret[0] = rng.next_u64();
    secret[1] = rng.next_u64();
    secret[2] = rng.next_u64();
    secret[3] = rng.next_u64();

    let mut hash = [0u64; 4];
    hash[0] = rng.next_u64();
    hash[1] = rng.next_u64();
    hash[2] = rng.next_u64();
    hash[3] = rng.next_u64();

    let private_key = ecc::PrivateKey::from(U256::from_limbs(secret));
    let digest = ScalarFieldElement::from(U256::from_limbs(hash));
   // println!("digest = {:?}", digest);
    let public_key = ecc::PublicKey::from(&private_key);
    let public_affine = public_key.as_affine();
    let public = match public_affine.clone() {
        Affine::Zero => (FieldElement::zero(), FieldElement::zero()),
        Affine::Point { x, y } => (x, y),
    };
    let sigma = private_key.sign(&digest);
    assert!(public_key.verify(&digest, &sigma));

    let sig =  (FieldElement::from(U256::from(sigma.r())),
                FieldElement::from(U256::from(sigma.w())));

  //  println!("Constructing claim");
    let claim = Claim {
        hash: FieldElement::from(U256::from(&digest)),
        who:  public.clone(),
    };
    let witness = Witness {
        signature: sig,
    };

    let proof = claim.prove(&witness).unwrap();
    
    crit.bench_function("Verifying a single ecdsa proof", move |bench| {
        bench.iter(|| black_box( claim.verify(&proof).unwrap()))
    });
}

fn main() {
    let crit = &mut Criterion::default().configure_from_args();
    bench_verify(crit);
    bench_prove(crit);
    crit.final_summary();
}
