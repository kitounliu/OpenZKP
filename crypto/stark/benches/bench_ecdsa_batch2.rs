#![feature(test)]
extern crate test;

use test::{black_box, Bencher};
use rand_core::{OsRng, RngCore};

use zkp_elliptic_curve::{Affine, ScalarFieldElement};
use zkp_elliptic_curve_crypto as ecc;
use zkp_macros_decl::{u256h};
use zkp_u256::U256;
use zkp_primefield::{FieldElement, Zero};
use zkp_stark::{
    Provable, Verifiable,
};

use zkp_stark::ecdsa::signature_batch::*;

macro_rules! bench_verify_ecdsa_batch2 {
    ($name:ident, $num:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
                let total = $num;
                let mut hashes = Vec::with_capacity(total);
                let mut pks = Vec::with_capacity(total);
                let mut signatures = Vec::with_capacity(total);

                let mut rng = OsRng;
                for _ in 0..total {
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
                //    println!("digest = {:?}", digest);
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

                 //   println!("pk = ({:?}, {:?})", public.0, public.1);
                 //   println!("sig = (r = {:?}, w = {:?})", sig.0, sig.1);
                    hashes.push(FieldElement::from(U256::from(&digest)));
                    pks.push(public);
                    signatures.push(sig);

                }

                let claim = Claim_Batch { hashes, pks };
                let witness = Witness_Batch { signatures };

                // Verification included in prove
                let proof = claim.prove(&witness).unwrap();
                println!("The proof length for {} is {}", total, proof.as_bytes().len());

           b.iter(|| black_box(claim.verify(&proof).unwrap()))
        }
    };
}


//bench_verify_ecdsa_batch2!(bench_verify_ecdsa_batch2_002, 2);
bench_verify_ecdsa_batch2!(bench_verify_ecdsa_batch2_004, 4);
//bench_verify_ecdsa_batch2!(bench_verify_ecdsa_batch2_016, 16);
//bench_verify_ecdsa_batch2!(bench_verify_ecdsa_batch2_032, 32);
//bench_verify_ecdsa_batch2!(bench_verify_ecdsa_batch2_064, 64);
//bench_verify_ecdsa_batch2!(bench_verify_ecdsa_batch2_128, 128);
//bench_verify_ecdsa_batch2!(bench_verify_ecdsa_batch2_256, 256);
//bench_verify_ecdsa_batch2!(bench_verify_ecdsa_batch2_512, 512);
