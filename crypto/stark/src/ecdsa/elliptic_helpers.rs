use crate::{RationalExpression, TraceTable, RationalExpression::*};
//use zkp_macros_decl::field_element;
use zkp_primefield::{FieldElement, Zero};
use zkp_u256::{Binary, SquareInline, U256};
use zkp_macros_decl::u256h;


// Adjustment to ECDSA to make it unlikely to hit a zero.
pub const SHIFT_POINT: (FieldElement, FieldElement) = (
    FieldElement::from_montgomery_const(u256h!(
        "0463d1e72d2ebf3416c727d5f24b5dc16b69f758cd49de911ad69b41a9ba0b3a"
    )),
    FieldElement::from_montgomery_const(u256h!(
        "01211aac6ce572de4298f85b038ef6a8aeae324054290152c5c9927f66d85eeb"
    )));

pub const GENERATOR: (FieldElement, FieldElement) = (
    FieldElement::from_montgomery_const(u256h!(
        "033840300bf6cec10429bf5184041c7b51a9bf65d4403deac9019623cf0273dd"
    )),
    FieldElement::from_montgomery_const(u256h!(
        "05a0e71610f55329fbd89a97cf4b33ad0939e3442869bbe7569d0da34235308a"
    )));

// Elliptic curve param.
const A : FieldElement = FieldElement::from_uint_const(&U256::ONE);

// Provide this function with the input point and the output location 
// and it produces a constraint for point doubling first on the x output and one one the y
// In default usage each input should be trace type.
pub fn point_double(input_x: RationalExpression, input_y: RationalExpression, output_x: RationalExpression, output_y: RationalExpression) -> [RationalExpression; 2] {
    let two = Constant(2.into());
    let three = Constant(3.into());
  //  let four = Constant(4.into());
  //  let eight = Constant(8.into());
    
    // These constraints take the lambda = (3x_old^2 + a)/ 2(y_old) and multiply through to clear divisions.
    // This is a multiplied through form of x_new = lambda^2 - 2x_old, which is asserted to be output_x
    let lambda_numb : RationalExpression = three*Exp(input_x.clone().into(), 2) + Constant(A.into());
    let lambda_denom : RationalExpression = two.clone()*input_y.clone();
    let new_x = Exp(lambda_numb.clone().into(), 2) - Exp(lambda_denom.clone().into(), 2)*(two*input_x.clone()+output_x.clone());
    // This is a multipled through form of y_new = lambda*(x_old - x_new) - y_old, which is asserted to be output y.
    let new_y = lambda_numb*(input_x - output_x.clone()) - lambda_denom.clone()*(input_y.clone() + output_y);
    [new_x, new_y]
}

// Provide this function the two points P and Q to add plus the asserted output location
// It provides constraints that express that Out = P + Q
pub fn point_add(x_p: RationalExpression, y_p: RationalExpression, x_q: RationalExpression, y_q: RationalExpression, x_out: RationalExpression, y_out: RationalExpression) -> [RationalExpression; 2] {
    // These constraints take the lambda = (y_q - y_p)/ (x_q - x_p) and multiply through to clear divisions.
    let lambda_numerator = y_q.clone() - y_p.clone();
    let lambda_denominator = x_q.clone() - x_p.clone();
    let new_x = Exp(lambda_numerator.clone().into(), 2) - Exp(lambda_denominator.clone().into(), 2)*(x_p.clone() + x_q.clone() + x_out.clone());
    let new_y = lambda_numerator*(x_p - x_out) - lambda_denominator*(y_p + y_out);
    [new_x, new_y]
}

// Full conditional bool check that location is a if test and b if !test [secured by the check that test = 1 or 0]
pub fn conditional(a: RationalExpression, b: RationalExpression, location: RationalExpression, test: RationalExpression) -> [RationalExpression; 2] {
    [one_or_zero(test.clone()), simple_conditional(a, b, test) - location]
}

// Tests if a rational expression is not one or zero
pub fn one_or_zero(test: RationalExpression) -> RationalExpression {
    test.clone()*(Constant(1.into()) - test.clone())
}

// Non secured conditional check, note each input should be it's own valid constraint [ie zero when right]
pub fn simple_conditional(a: RationalExpression, b: RationalExpression, test: RationalExpression) -> RationalExpression {
    a*test.clone() + (Constant(1.into()) - test.clone())*b
}

// This function takes in a target and a claimed bit decomposition vector and returns constraints which check that
// (1) the decomp is all ones and zeros and (2) that the target equals the sum of increasing powers of two of the decomp.
// Note given the size limit of field elements we expect that decomp is len < 256
pub fn bit_decomp_test(target: RationalExpression, decomp: Vec<RationalExpression>) -> [RationalExpression; 2] {
    let mut power: FieldElement = 1.into();
    let mut consistency = Constant(0.into());
    let mut sum = Constant(0.into());

    for bit in decomp.iter() {
        consistency = consistency + one_or_zero(bit.clone());
        sum = sum + bit.clone()*Constant(power.clone());
        power  *= FieldElement::from(2);
    }
    [consistency, sum - target]
}

// We make the assumption that zero will never be placed into N then add a col Q+N without knowing if it is right
pub fn scalar_mult(trace: &mut TraceTable, point: &(FieldElement, FieldElement), scalar: &U256, start: usize, offset: usize, neg: bool) {
    // Add an extra copy of the point then set q to it's negative.
    let mut n = point.clone();
    let mut q;
    if neg {
        q = (SHIFT_POINT.0, -SHIFT_POINT.1);
       // println!("neg point: {:?}", &q);
    } else {
       // println!("pos point: {:?}", &SHIFT_POINT);
        q = SHIFT_POINT.clone();
    }

    for i in 0..256 {
        trace[(start+i, offset + 1)] = n.0.clone();
        trace[(start+i, offset + 2)] = n.1.clone();
        trace[(start+i, offset + 3)] = q.0.clone();
        trace[(start+i, offset + 4)] = q.1.clone();
        if scalar.bit(i) {
            trace[(start + i, offset)] = 1.into();
            q = add(&n.0, &n.1, &q.0, &q.1);
        } else {
            trace[(start + i, offset)] = 0.into();
        }
        n = double(&n.0, &n.1);
    }
}

// We make the assumption that zero will never be placed into N then add a col Q+N without knowing if it is right
pub fn dummy_computation_256(trace: &mut TraceTable, start: usize, offset: usize, neg: bool) {
    // Add an extra copy of the point then set q to it's negative.
    let q;
    if neg {
        q = (SHIFT_POINT.0, -SHIFT_POINT.1);
        // println!("neg point: {:?}", &q);
    } else {
        // println!("pos point: {:?}", &SHIFT_POINT);
        q = SHIFT_POINT.clone();
    }

    trace[(start, offset)] = 1.into();
    trace[(start, offset+6)] = 1.into();

    let n = (trace[(0, offset + 1)].clone(), trace[(0, offset + 2)].clone());
    let nq = add(&n.0, &n.1, &q.0, &q.1);

    for i in 0..256 {
        trace[(start+i, offset + 1)] = trace[(i, offset + 1)].clone();
        trace[(start+i, offset + 2)] = trace[(i, offset + 2)].clone();
        if i == 0 {
            trace[(start+i, offset + 3)] = q.0.clone();
            trace[(start+i, offset + 4)] = q.1.clone();
        } else {
            trace[(start+i, offset + 3)] = nq.0.clone();
            trace[(start+i, offset + 4)] = nq.1.clone();
        }
    }
    trace[(start+254, offset+5)] = n.0.clone();
    trace[(start+255, offset+5)] = n.1.clone();
}

// accumulate bits stored in column 0 in reverse order and store the result in column 6
pub fn accumulate_bits_reverse(trace: &mut TraceTable, begin: usize, end: usize) {
    let col = 6;
    assert!(begin < end);
    trace[(end, col)] = trace[(end, col)].clone();
    for i in (begin..end).rev() {
        trace[(i, col)] = trace[(i+1, col)].double() + trace[(i, 0)].clone();
    }
}

// Note incorrect when given zero inputs
pub fn double(point_x: &FieldElement, point_y: &FieldElement) -> (FieldElement, FieldElement) {
    assert!(!(point_x.is_zero() && point_y.is_zero()));
    let lambda = ((point_x + point_x + point_x)*point_x + A)/(point_y + point_y);
    let new_x = (&lambda).square() - point_x - point_x;
    let new_y = lambda*(point_x - &new_x) - point_y;
    (new_x, new_y)
}

// Note incorrect when given zero inputs
pub fn add(x_p: &FieldElement, y_p: &FieldElement, x_q: &FieldElement, y_q: &FieldElement) -> (FieldElement, FieldElement) {
    assert!(!(x_p.is_zero() && y_p.is_zero()));
    assert!(!(x_q.is_zero() && y_q.is_zero()));
    let lambda = (y_q - y_p)/(x_q - x_p);
    let new_x = (&lambda).square() - (x_p + x_q);
    let new_y = lambda*(x_p - &new_x) - y_p;
    (new_x, new_y)
}

#[cfg(test)]
mod test {
    /*
    use super::*;
    use zkp_elliptic_curve::Affine;

    #[test]
    fn scalar_mult_in_table() {
        let p = (
            FieldElement::from(u256h!(
                "01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca"
            )),
            FieldElement::from(u256h!(
                "005668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f"
            )),
        );
        let c = u256h!("07374b7d69dc9825fc758b28913c8d2a27be5e7c32412f612b20c9c97afbe4dd");

        let expected_affine = Affine::Point{x: p.0.clone(), y: p.1.clone()} * &c;
        let mut expected : (FieldElement, FieldElement) = match expected_affine {
            Affine::Point {x, y} => (x, y),
            _ => (FieldElement::ZERO, FieldElement::ZERO),
        };
        expected = add(&expected.0, &expected.1, &SHIFT_POINT.0, &SHIFT_POINT.1);

        let mut trace = TraceTable::new(256, 5);
        scalar_mult(&mut trace, (p.0, p.1), &c, 0, 0, false);
        assert_eq!(trace[(255, 3)], expected.0);
        assert_eq!(trace[(255, 4)], expected.1);
    }

    #[test]
    fn test_table_double() {
        let a = (
            FieldElement::from(u256h!(
                "01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca"
            )),
            FieldElement::from(u256h!(
                "005668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f"
            )),
        );
        let b = (
            FieldElement::from(u256h!(
                "0759ca09377679ecd535a81e83039658bf40959283187c654c5416f439403cf5"
            )),
            FieldElement::from(u256h!(
                "06f524a3400e7708d5c01a28598ad272e7455aa88778b19f93b562d7a9646c41"
            )),
        );
        assert_eq!(double(&a.0, &a.1), b);
    }

    #[test]
    fn test_table_add() {
        let a = (
            FieldElement::from(u256h!(
                "01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca"
            )),
            FieldElement::from(u256h!(
                "005668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f"
            )),
        );
        let b = (
            FieldElement::from(u256h!(
                "00f24921907180cd42c9d2d4f9490a7bc19ac987242e80ac09a8ac2bcf0445de"
            )),
            FieldElement::from(u256h!(
                "018a7a2ab4e795405f924de277b0e723d90eac55f2a470d8532113d735bdedd4"
            )),
        );
        let c = (
            FieldElement::from(u256h!(
                "0457342950d2475d9e83a4de8beb3c0850181342ea04690d804b37aa907b735f"
            )),
            FieldElement::from(u256h!(
                "00011bd6102b929632ce605b5ae1c9c6c1b8cba2f83aa0c5a6d1247318871137"
            )),
        );
        assert_eq!(add(&a.0, &a.1, &b.0, &b.1), c);
    }

 */
}