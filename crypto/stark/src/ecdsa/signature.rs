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

pub struct Claim {
    pub hash: FieldElement,
    pub who:  (FieldElement, FieldElement),
}

pub struct Witness {
    pub signature: (FieldElement, FieldElement),
}

impl From<&Claim> for Vec<u8> {
    fn from(input: &Claim) -> Self {
        let mut ret = U256::from(&input.hash).to_bytes_be().to_vec();
        ret.extend_from_slice(&U256::from(&input.who.0).to_bytes_be());
        ret.extend_from_slice(&U256::from(&input.who.1).to_bytes_be());
        ret
    }
}

impl Verifiable for Claim {
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;

        // Seed
        let seed = Vec::from(self);

        let trace_generator = FieldElement::root(TRACE_LENGTH).unwrap();

        // Constraint repetitions
        let g = Constant(trace_generator.clone());
        let on_row = |index| (X - g.pow(index)).inv();
        let every_row = || (X.pow(TRACE_LENGTH) - 1).inv();
        // (X - 1)(X - g^256)(X - g^512)(X - g^768) = X^4 - 1
        let on_loop_256 = || {
            let poly = X.pow(TRACE_LENGTH/256) - 1;
            poly.inv()
        };

        // (X - g)...(X-g^255)(X - g^257)...(x - g^511)(X - g^513)...(X - g^767)(X - g^769)...(X - g^1023)
        // = (X^1024 - 1)/(X^4 - 1)
        /*
        let on_loop_256_cmp = || {
            let numerator = X.pow(TRACE_LENGTH/256) - 1;
            let denom = X.pow(TRACE_LENGTH) - 1;
            numerator/denom
        };
         */

        // (X - g^255)(X - g^511) (X - g^767) (X - g^1023) =
        let on_loop_255 = || {
            let k = TRACE_LENGTH/256;
            let poly = X.pow(k) - g.pow(TRACE_LENGTH - k);
            poly.inv()
        };

        let on_loop_255_cmp = || {
            let k = TRACE_LENGTH/256;
            let numerator = X.pow(k) - g.pow(TRACE_LENGTH - k);
            let denom = X.pow(TRACE_LENGTH) - 1;
            numerator/denom
        };

        let row_double = point_double(
            Trace(1, 0),  Trace(2, 0),
            Trace(1, 1), Trace(2, 1));
        let row_add = point_add(
            Trace(1, 0),
            Trace(2, 0),
            Trace(3, 0),
            Trace(4, 0),
            Trace(3, 1),
            Trace(4, 1),
        );
        // rows remove shifting points q to make sure no identity point
        let row_sub_q = point_add(
            Trace(3, 0),
            Trace(4, 0),
            Constant(SHIFT_POINT.0.clone()),
            Constant(-SHIFT_POINT.1.clone()),
            Trace(5, -1),
            Trace(5,0),
        );
        // rows for computing g^H(m) * pk^r
        let row_combine = point_add(
            Trace(5, 0), Trace(5, 1),
            Trace(5, 256), Trace(5, 257),
            Trace(1, 258), Trace(2, 258)
        );

       // let test: Vec<_> = (0..1024).collect();
        Constraints::from_expressions((TRACE_LENGTH, TRACE_WIDTH), seed, vec![
            one_or_zero(Trace(0,0)) * every_row(),
            row_double[0].clone() * on_loop_255_cmp(),
            row_double[1].clone() * on_loop_255_cmp(),
            simple_conditional(row_add[0].clone(),
                               Trace(3, 1) - Trace(3, 0),
                               Trace(0, 0)) * on_loop_255_cmp(),
            simple_conditional(row_add[1].clone(),
                               Trace(4, 1) - Trace(4, 0),
                               Trace(0, 0)) * on_loop_255_cmp(),
            (Trace(6, 0) - Trace(6, 1) * Constant(2.into())
                - Trace(0, 0)) * on_loop_255_cmp(),
            row_sub_q[0].clone() * on_loop_255(),
            row_sub_q[1].clone() * on_loop_255(),
            row_combine[0].clone() * on_row(254),
            row_combine[1].clone() * on_row(254),

            // Boundary Constraints
            (Trace(1, 0) - Constant(GENERATOR.0.clone()))*on_row(0),
            (Trace(2, 0) - Constant(GENERATOR.1.clone()))*on_row(0),
            (Trace(1, 0) - Constant(self.who.0.clone()))*on_row(256),
            (Trace(2, 0) - Constant(self.who.1.clone()))*on_row(256),
            (Trace(3, 0) - Constant(SHIFT_POINT.0.clone()))*on_loop_256(),
            (Trace(4, 0) - Constant(SHIFT_POINT.1.clone()))*on_loop_256(),
            // the first bit of H(m) and r
            (Trace(6, 0) - Trace(0, 0)) * on_loop_255(),
            // compare H(m)
            (Trace(6, 0) - Constant(self.hash.clone())) * on_row(0),
            // compare r
            (Trace(6, 0) - Trace(5, 510)) * on_row(256),
        ]).unwrap()
    }
}

impl Provable<&Witness> for Claim {
    #[cfg(feature = "prover")]
    fn trace(&self, witness: &Witness) -> TraceTable {
        let mut trace = TraceTable::new(TRACE_LENGTH, TRACE_WIDTH);

        // compute g^H(m) * Q
        let hm = U256::from(&self.hash);
        scalar_mult(&mut trace, &GENERATOR, &hm, 0, 0, false);
        let g_hm_q_x = trace[(255, 3)].clone();
        let g_hm_q_y = trace[(255, 4)].clone();
        // compute g^H(m) by removing Q
        let (g_hm_x, g_hm_y) = add(&g_hm_q_x, &g_hm_q_y, &SHIFT_POINT.0, &-&SHIFT_POINT.1);
        trace[(254, 5)] = g_hm_x.clone();
        trace[(255, 5)] = g_hm_y.clone();

        accumulate_bits_reverse(&mut trace, 0, 255);
//        accumulate_hash_bits(&mut trace);
        info!("H(m) in trace table: {:?}", trace[(0, 6)]);

        // obtain pk^r * Q
        let r = U256::from(&witness.signature.0);
        scalar_mult(&mut trace, &self.who, &r, 256, 0, false);
        let pk_r_q_x = trace[(511, 3)].clone();
        let pk_r_q_y = trace[(511, 4)].clone();
        // compute pk^r by removing Q
        let (pk_r_x, pk_r_y) = add(&pk_r_q_x, &pk_r_q_y, &SHIFT_POINT.0, &-&SHIFT_POINT.1);
        trace[(510, 5)] = pk_r_x.clone();
        trace[(511, 5)] = pk_r_y.clone();

        accumulate_bits_reverse(&mut trace, 256, 511);
       // accumulate_r_bits(&mut trace);
        info!("r in trace table: {:?}", trace[(256, 6)]);

        // compute t = g^H(m) * pk^r
        let (g_hm_pk_r_x, g_hm_pk_r_y) = add(&g_hm_x, &g_hm_y, &pk_r_x, &pk_r_y);
        // compute  t^w * Q
        let w = U256::from(&witness.signature.1);
        scalar_mult(&mut trace, &(g_hm_pk_r_x, g_hm_pk_r_y), &w, 512, 0, false);
        // compute  t^w by removing Q
        let t_q_x = trace[(767, 3)].clone();
        let t_q_y = trace[(767, 4)].clone();
        let (t_x, t_y) = add(&t_q_x, &t_q_y, &SHIFT_POINT.0, &-&SHIFT_POINT.1);
        trace[(766, 5)] = t_x;
        trace[(767, 5)] = t_y;
        info!("r computed: {:?}", trace[(766, 5)]);

        // fill in dummy computation
        // accumulate w bits
        accumulate_bits_reverse(&mut trace, 512, 767);
        info!("w in trace table: {:?}", trace[(512, 6)]);
        dummy_computation_256(&mut trace, 768, 0, false);
        /*
        trace[(768, 0)] = 1.into();
        trace[(768, 6)] = 1.into();
        // compute g*Q
        let g_q = add(&GENERATOR.0, &GENERATOR.1, &SHIFT_POINT.0, &SHIFT_POINT.1);
        for i in 768..1024 {
            trace[(i, 1)] = trace[(i-768, 1)].clone();
            trace[(i, 2)] = trace[(i-768, 2)].clone();
            if i == 768 {
                trace[(i, 3)] = SHIFT_POINT.0;
                trace[(i, 4)] = SHIFT_POINT.1;
            } else {
                trace[(i, 3)] = g_q.0.clone();
                trace[(i, 4)] = g_q.1.clone();
            }
        }
        trace[(1022, 5)] = GENERATOR.0;
        trace[(1023, 5)] = GENERATOR.1;

         */

        trace
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use log::info;
//    use rand_core::{OsRng, RngCore};

    use zkp_elliptic_curve::{Affine, ScalarFieldElement};
    use zkp_elliptic_curve_crypto as ecc;
    use zkp_macros_decl::{u256h};
    use zkp_u256::U256;
    use zkp_primefield::{FieldElement, Zero};

    #[test]
    fn test_ecdsa_single_prove_verify() {
     //   env_logger::init();

        println!("Creating signature");
        let private_key = ecc::PrivateKey::from(u256h!("03c1e9550e66958296d11b60f8e8e7a7ad990d07fa65d5f7652c4a6c87d4e3cc"));
        let digest = ScalarFieldElement::from(u256h!(
            "01921ce52df68f0185ade7572776513304bdd4a07faf6cf28cefc65a86fc496c"
        ));
        let public_key = ecc::PublicKey::from(&private_key);
        let public_affine = public_key.as_affine();
        let public = match public_affine.clone() {
            Affine::Zero => (FieldElement::zero(), FieldElement::zero()),
            Affine::Point { x, y } => (x, y),
        };
        let sig = private_key.sign(&digest);
        assert!(public_key.verify(&digest, &sig));


        println!("Constructing claim");
        let claim = Claim {
            hash: FieldElement::from(U256::from(&digest)),
            who:  public.clone(),
        };
        let witness = Witness {
            signature: (FieldElement::from(U256::from(sig.r())), FieldElement::from(U256::from(sig.w()))),
        };

        println!("Claim.hash: {:?}", claim.hash);
        println!("Witness.r: {:?}", witness.signature.0);
        println!("Witness.w: {:?}", witness.signature.1);
        // assert_eq!(claim.check(&witness), Ok(()));

        println!("Proving...");
        let proof = claim.prove(&witness).unwrap();
        println!("The proof length is {}", proof.as_bytes().len());

        println!("Verifying...");
        claim.verify(&proof).unwrap();
        println!("Successful");

        println!("Verifying with wrong claim");
        let claim_wrong_hash = Claim {
            hash: FieldElement::from(1),
            who:  public,
        };
        assert!(claim_wrong_hash.verify(&proof).is_err());
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
