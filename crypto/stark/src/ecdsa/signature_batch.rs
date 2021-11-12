use log::info;

use super::elliptic_helpers::*;
#[cfg(feature = "prover")]
use crate::{Constraints, Provable, RationalExpression, TraceTable, Verifiable, DensePolynomial, RationalExpression::*};
//use zkp_elliptic_curve::Order;
//use zkp_elliptic_curve_crypto as ecc;
use zkp_primefield::{FieldElement, Root};
use zkp_u256::U256;

const TRACE_LENGTH: usize = 1024;
const TRACE_WIDTH: usize = 7;

pub struct Claim_Batch {
    pub hashes: Vec<FieldElement>,
    pub pks:  Vec<(FieldElement, FieldElement)>,
}

pub struct Witness_Batch {
    pub signatures: Vec<(FieldElement, FieldElement)>,
}

impl From<&Claim_Batch> for Vec<u8> {
    fn from(input: &Claim_Batch) -> Self {
        let mut ret= Vec::new();
        for h in input.hashes.iter() {
            ret.extend_from_slice(&U256::from(h).to_bytes_be());
        }

        for pk in input.pks.iter() {
            ret.extend_from_slice(&U256::from(&pk.0).to_bytes_be());
            ret.extend_from_slice(&U256::from(&pk.1).to_bytes_be());
        }

        ret
    }
}

impl Verifiable for Claim_Batch {
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;

        assert_eq!(self.hashes.len(), self.pks.len());
        assert!(self.hashes.len().is_power_of_two());
        let trace_length_total = self.hashes.len() * TRACE_LENGTH;

        // Seed
        let seed = Vec::from(self);

        let trace_generator = FieldElement::root(trace_length_total).unwrap();

        // Constraint repetitions
        let g = Constant(trace_generator.clone());
        let on_row = |index| (X - g.pow(index)).inv();
        let every_row = || (X.pow(trace_length_total) - 1).inv();

        // X^k - 1 =  (X - g^0)(X - g^1024)...(X - g^(1024*k)) with k = trace_length_total/1024 - 1
        let on_loop_1024 = || {
            let poly = X.pow(trace_length_total/1024) - 1;
            poly.inv()
        };

        // X^k - 1 = (X - g^0)(X - g^256)...(X - g^(256*k)) with k = trace_length_total/256 - 1
        let on_loop_256 = || {
            let poly = X.pow(trace_length_total/256) - 1;
            poly.inv()
        };
        // On rows [1, 255], [257, 511] ...
        let on_loop_256_cmp = || {
            let numerator = X.pow(trace_length_total/256) - 1;
            let denom = X.pow(trace_length_total) - 1;
            numerator/denom
        };

        let row_double = point_double(
            Trace(1, -1),  Trace(2, -1),
            Trace(1, 0), Trace(2, 0));
        let row_add = point_add(
            Trace(1, -1),
            Trace(2, -1),
            Trace(3, -1),
            Trace(4, -1),
            Trace(3, 0),
            Trace(4, 0),
        );
        // rows remove shifting points q to make sure no identity point
        let row_sub_q = point_add(
            Trace(3, -1),
            Trace(4, -1),
            Constant(SHIFT_POINT.0.clone()),
            Constant(-SHIFT_POINT.1.clone()),
            Trace(5, -2),
            Trace(5,-1),
        );
        // rows for computing g^H(m) * pk^r
        let row_combine = point_add(
            Trace(5, 254), Trace(5, 255),
            Trace(5, 510), Trace(5, 511),
            Trace(1, 512), Trace(2, 512)
        );

        let mut v = vec![
            one_or_zero(Trace(0,0)) * every_row(),
            row_double[0].clone() * on_loop_256_cmp(),
            row_double[1].clone() * on_loop_256_cmp(),
            simple_conditional(row_add[0].clone(),
                               Trace(3, 0) - Trace(3, -1),
                               Trace(0, -1)) * on_loop_256_cmp(),
            simple_conditional(row_add[1].clone(),
                               Trace(4, 0) - Trace(4, -1),
                               Trace(0, -1)) * on_loop_256_cmp(),
            // bit accumulation
            (Trace(6, -1) - Trace(6, 0) * Constant(2.into())
                - Trace(0, -1)) * on_loop_256_cmp(),
            row_sub_q[0].clone() * on_loop_256(),
            row_sub_q[1].clone() * on_loop_256(),
            row_combine[0].clone() * on_loop_1024(),
            row_combine[1].clone() * on_loop_1024(),

            // Boundary Constraints
            (Trace(1, 0) - Constant(GENERATOR.0.clone()))*on_loop_1024(),
            (Trace(2, 0) - Constant(GENERATOR.1.clone()))*on_loop_1024(),
            (Trace(3, 0) - Constant(SHIFT_POINT.0.clone()))*on_loop_256(),
            (Trace(4, 0) - Constant(SHIFT_POINT.1.clone()))*on_loop_256(),

            // the first bit of H(m) and r
            (Trace(6, -1) - Trace(0, -1)) * on_loop_256(),

             // compare r
            (Trace(6, 256) - Trace(5, 766)) * on_loop_1024(),
        ];

        // compare H(m) and public keys

        for (i, (hash, pk)) in self.hashes.iter().zip(self.pks.iter()).enumerate() {
            let start = i * TRACE_LENGTH;
            // compare H(m)
            v.push((Trace(6, 0) - Constant(hash.clone())) * on_row(start));
            // compare public keys
            v.push((Trace(1, 0) - Constant(pk.0.clone()))*on_row(start + 256));
            v.push((Trace(2, 0) - Constant(pk.1.clone()))*on_row(start + 256));
        }

        Constraints::from_expressions((trace_length_total, TRACE_WIDTH), seed, v).unwrap()
    }
}

impl Provable<&Witness_Batch> for Claim_Batch {
    #[cfg(feature = "prover")]
    fn trace(&self, witness: &Witness_Batch) -> TraceTable {

        assert_eq!(self.hashes.len(), self.pks.len());
        assert_eq!(self.hashes.len(), witness.signatures.len());
        assert!(self.hashes.len().is_power_of_two());

        let trace_length_total = self.hashes.len() * TRACE_LENGTH;
        let mut trace = TraceTable::new(trace_length_total, TRACE_WIDTH);

        for (i, ((hash, pk), sig))
        in self.hashes.iter().zip(self.pks.iter()).zip(witness.signatures.iter()).enumerate() {

            let start = TRACE_LENGTH * i;
            // compute g^H(m) * Q
            let hm = U256::from(hash);
            scalar_mult(&mut trace, &GENERATOR, &hm, start, 0, false);
            let g_hm_q_x = trace[(start + 255, 3)].clone();
            let g_hm_q_y = trace[(start + 255, 4)].clone();
            // compute g^H(m) by removing Q
            let (g_hm_x, g_hm_y) = add(&g_hm_q_x, &g_hm_q_y, &SHIFT_POINT.0, &-&SHIFT_POINT.1);
            trace[(start + 254, 5)] = g_hm_x.clone();
            trace[(start + 255, 5)] = g_hm_y.clone();

            accumulate_bits_reverse(&mut trace, start, start + 255);
            //        accumulate_hash_bits(&mut trace);
            info!("H(m) in trace table: {:?}", trace[(start, 6)]);

            // obtain pk^r * Q
            let r = U256::from(&sig.0);
            scalar_mult(&mut trace, pk, &r, start + 256, 0, false);
            let pk_r_q_x = trace[(start + 511, 3)].clone();
            let pk_r_q_y = trace[(start + 511, 4)].clone();
            // compute pk^r by removing Q
            let (pk_r_x, pk_r_y) = add(&pk_r_q_x, &pk_r_q_y, &SHIFT_POINT.0, &-&SHIFT_POINT.1);
            trace[(start + 510, 5)] = pk_r_x.clone();
            trace[(start + 511, 5)] = pk_r_y.clone();

            accumulate_bits_reverse(&mut trace, start + 256, start + 511);
            // accumulate_r_bits(&mut trace);
            info!("r in trace table: {:?}", trace[(start + 256, 6)]);

            // compute t = g^H(m) * pk^r
            let (g_hm_pk_r_x, g_hm_pk_r_y) = add(&g_hm_x, &g_hm_y, &pk_r_x, &pk_r_y);
            // compute  t^w * Q
            let w = U256::from(&sig.1);
            scalar_mult(&mut trace, &(g_hm_pk_r_x, g_hm_pk_r_y), &w, start + 512, 0, false);
            // compute  t^w by removing Q
            let t_q_x = trace[(start + 767, 3)].clone();
            let t_q_y = trace[(start + 767, 4)].clone();
            let (t_x, t_y) = add(&t_q_x, &t_q_y, &SHIFT_POINT.0, &-&SHIFT_POINT.1);
            trace[(start + 766, 5)] = t_x;
            trace[(start + 767, 5)] = t_y;
            info!("r computed: {:?}", trace[(start + 766, 5)]);

            // fill in dummy computation
            // accumulate w bits
            accumulate_bits_reverse(&mut trace, start + 512, start + 767);
            info!("w in trace table: {:?}", trace[(start + 512, 6)]);
            dummy_computation_256(&mut trace, start + 768, 0, false);
        }

        trace
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use log::info;
    use rand_core::{OsRng, RngCore};

    use zkp_elliptic_curve::{Affine, ScalarFieldElement};
    use zkp_elliptic_curve_crypto as ecc;
 //   use zkp_macros_decl::{u256h};
    use zkp_u256::U256;
    use zkp_primefield::{FieldElement, Zero};

    #[test]
    fn test_ecdsa_batch_prove_verify() {
     //   env_logger::init();

        // total has to be power of two
        let total = 16;

        let mut rng = OsRng;

        let mut hashes = Vec::with_capacity(total);
        let mut pks = Vec::with_capacity(total);
        let mut signatures = Vec::with_capacity(total);

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

         //   println!("pk = ({:?}, {:?})", public.0, public.1);
         //   println!("sig = (r = {:?}, w = {:?})", sig.0, sig.1);
            hashes.push(FieldElement::from(U256::from(&digest)));
            pks.push(public);
            signatures.push(sig);

        }

        println!("Constructing claim batch");
        let claim = Claim_Batch { hashes, pks };
        let witness = Witness_Batch { signatures };

        println!("Proving...");
        // Verification included in prove
        let proof = claim.prove(&witness).unwrap();
        println!("The proof length is {}", proof.as_bytes().len());

    //    println!("Verifying...");
    //    claim.verify(&proof).unwrap();
    //    println!("Successful");
    }

    /*
    use super::*;
    use crate::{proof_params::ProofParams, proofs::stark_proof, verifier::check_proof};
    use zkp_elliptic_curve::Affine;
    use zkp_macros_decl::{field_element, u256h};

    #[test]
    fn test_sign_table() {
        let private_key =
            u256h!("03c1e9550e66958296d11b60f8e8e7a7ad990d07fa65d5f7652c4a6c87d4e3cc");
        let message_hash =
            u256h!("01921ce52df68f0185ade7572776513304bdd4a07faf6cf28cefc65a86fc496c");
        let public_affine = ecc::private_to_public(&private_key);
        let public = match public_affine.clone() {
            Affine::Zero => (FieldElement::ZERO, FieldElement::ZERO),
            Affine::Point { x, y } => (x, y),
        };

        let (r, w) = ecc::sign(&U256::from(message_hash.clone()), &private_key);

        let u_1 = message_hash.mulmod(&w, &elliptic_curve::ORDER);
        let u_2 = &r.mulmod(&w, &elliptic_curve::ORDER);

        let first_expected_affine = elliptic_curve::GENERATOR * u_1;
        let second_expected_affine = public_affine * u_2;
        let first_expected = match first_expected_affine.clone() {
            Affine::Zero => (FieldElement::ZERO, FieldElement::ZERO),
            Affine::Point { x, y } => (x, y),
        };
        let second_expected = match second_expected_affine.clone() {
            Affine::Zero => (FieldElement::ZERO, FieldElement::ZERO),
            Affine::Point { x, y } => (x, y),
        };

        let claim = Claim {
            hash: FieldElement::from(message_hash),
            who:  public,
        };
        let witness = Witness {
            signature: (FieldElement::from(r.clone()), FieldElement::from(w)),
        };
        let trace = witness.trace(&claim);

        let mut neg_shift = SHIFT_POINT.clone();
        neg_shift.1 = -neg_shift.1;
        // First check, checks that the proper scalar mults are put in place
        let shifted_trace1 = add(
            &trace[(255, 3)],
            &trace[(255, 4)],
            &neg_shift.0,
            &neg_shift.1,
        );
        let shifted_trace2 = add(
            &trace[(511, 3)],
            &trace[(511, 4)],
            &SHIFT_POINT.0,
            &SHIFT_POINT.1,
        );
        assert_eq!(first_expected, shifted_trace1.clone());
        assert_eq!(second_expected, shifted_trace2.clone());

        let mut final_check = add(
            &trace[(255, 3)],
            &trace[(255, 4)],
            &trace[(511, 3)],
            &trace[(511, 4)],
        );
        assert_eq!(FieldElement::from(r), final_check.0);
    }

    #[test]
    fn test_sign_proof() {
        let private_key =
            u256h!("03c1e9550e66958296d11b60f8e8e7a7ad990d07fa65d5f7652c4a6c87d4e3cc");
        let message_hash =
            u256h!("01921ce52df68f0185ade7572776513304bdd4a07faf6cf28cefc65a86fc496c");
        let public_affine = ecc::private_to_public(&private_key);
        let public = match public_affine.clone() {
            Affine::Zero => (FieldElement::ZERO, FieldElement::ZERO),
            Affine::Point { x, y } => (x, y),
        };

        let (r, w) = ecc::sign(&U256::from(message_hash.clone()), &private_key);

        let claim = Claim {
            hash: FieldElement::from(message_hash),
            who:  public,
        };
        let witness = Witness {
            signature: (FieldElement::from(r.clone()), FieldElement::from(w)),
        };

        let mut params = ProofParams::suggested(9);
        params.fri_layout = vec![3, 2];

        let potential_proof = stark_proof(&claim, &witness, &params);
        assert_eq!(
            check_proof(potential_proof.proof.as_slice(), &claim, &params),
            Ok(())
        );
    }

 */
}
