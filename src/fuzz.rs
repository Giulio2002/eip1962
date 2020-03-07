use crate::weierstrass::*;
use crate::weierstrass::curve::{CurvePoint, WeierstrassCurve};
use crate::representation::{ElementRepr};
use crate::field::*;
use crate::public_interface;
use crate::square_root;
use crate::fp::{Fp};
use crate::public_interface::{ApiError};
use crate::traits::{FieldElement};
use crate::traits::ZeroAndOne;
use crate::integers::MaxGroupSizeUint;

pub(crate) struct ArithmeticProcessor<
    'a, 
    'b: 'a, 
    FE: FieldElement + ZeroAndOne + 'a,
    CP: CurveParameters<BaseFieldElement = FE> + 'a
> {
    curve: &'b WeierstrassCurve<'a, CP>,
    generator: &'b CurvePoint<'a, CP>,
    group_order: &'b [u64],
}

impl<
    'a, 
    'b: 'a, 
    FE: FieldElement + ZeroAndOne + 'a,
    CP: CurveParameters<BaseFieldElement = FE> + 'a
> ArithmeticProcessor<'a, 'b, FE, CP> {
    fn a_plus_a_equal_to_2a(&self) {
        let mut a_plus_a = self.generator.clone();
        let other_a = self.generator.clone();
        a_plus_a.add_assign(&other_a);

        let mut two_a = self.generator.clone();
        two_a.double();

        assert_eq!(a_plus_a.into_xy(), two_a.into_xy());
    }

    fn a_minus_a_equal_zero(&self) {
        let mut a_minus_a = self.generator.clone();
        let mut minus_a = self.generator.clone();
        minus_a.negate();

        a_minus_a.add_assign(&minus_a);

        assert!(a_minus_a.is_zero());
    }

    fn two_a_is_equal_to_two_a(&self) {
        let mut two_a = self.generator.clone();
        two_a.double();

        let other_two_a = self.generator.mul(&[2u64]);

        assert_eq!(other_two_a.into_xy(), two_a.into_xy());
    }

    fn three_a_is_equal_to_three_a(&self) {
        let mut two_a = self.generator.clone();
        two_a.double();

        let a = self.generator.clone();

        let mut t0 = two_a.clone();
        t0.add_assign(&a);

        let mut t1 = a.clone();
        t1.add_assign(&two_a);

        let t2 = self.generator.mul(&[3u64]);

        assert_eq!(t0.into_xy(), t1.into_xy());
        assert_eq!(t0.into_xy(), t2.into_xy());
    }

    fn a_plus_b_equal_to_b_plus_a(&self) {
        let mut b = self.generator.clone();
        b.double();

        let a = self.generator.clone();

        let mut a_plus_b = a.clone();
        a_plus_b.add_assign(&b);

        let mut b_plus_a = b.clone();
        b_plus_a.add_assign(&a);

        assert_eq!(a_plus_b.into_xy(), b_plus_a.into_xy());
    }

    fn a_mul_by_zero_is_zero(&self) {
        let a = self.generator.mul(&[0u64]);

        assert!(a.is_zero());
    }

    fn a_mul_by_group_order_is_zero(&self) {
        let a = self.generator.mul(&self.group_order);

        assert!(a.is_zero());
    }

    fn a_mul_by_scalar_wraps_over_group_order(&self) {
        let scalar = MaxGroupSizeUint::from(&[12345][..]);
        let group_order = MaxGroupSizeUint::from(&self.group_order[..]);
        let scalar_plus_group_order = scalar + group_order;
        let a = self.generator.mul(&scalar.as_ref());
        let b = self.generator.mul(&scalar_plus_group_order.as_ref());

        assert_eq!(a.into_xy(), b.into_xy());
    }

    fn a_mul_by_minus_scalar(&self) {
        let scalar = MaxGroupSizeUint::from(&[12345][..]);
        let group_order = MaxGroupSizeUint::from(&self.group_order[..]);
        let minus_scalar = group_order - scalar;
        let a = self.generator.mul(&minus_scalar.as_ref());
        let mut b = self.generator.mul(&scalar.as_ref());
        b.negate();

        assert_eq!(a.into_xy(), b.into_xy());
    }

    pub fn test(&self) {
        self.a_minus_a_equal_zero();
        self.a_plus_a_equal_to_2a();
        self.two_a_is_equal_to_two_a();
        self.three_a_is_equal_to_three_a();
        self.a_plus_b_equal_to_b_plus_a();
        self.a_mul_by_zero_is_zero();
        self.a_mul_by_group_order_is_zero();
        self.a_mul_by_scalar_wraps_over_group_order();
        self.a_mul_by_minus_scalar();
    }
}

trait Fuzzer {
    fn fuzz(bytes: &[u8]) -> Result<(), ApiError>;
}
// Redecleare macro (Momentairly)
macro_rules! expand_for_modulus_limbs {
    ($modulus_limbs: expr, $implementation: tt, $argument: expr, $func: tt) => {
        match $modulus_limbs {
            4 => {
                $implementation::<U256Repr>::$func(&$argument)
            },
            5 => {
                $implementation::<U320Repr>::$func(&$argument)
            },
            6 => {
                $implementation::<U384Repr>::$func(&$argument)
            },
            7 => {
                $implementation::<U448Repr>::$func(&$argument)
            },
            8 => {
                $implementation::<U512Repr>::$func(&$argument)
            },
            9 => {
                $implementation::<U576Repr>::$func(&$argument)
            },
            10 => {
                $implementation::<U640Repr>::$func(&$argument)
            },
            11 => {
                $implementation::<U704Repr>::$func(&$argument)
            },
            12 => {
                $implementation::<U768Repr>::$func($argument)
            },
            13 => {
                $implementation::<U832Repr>::$func(&$argument)
            },
            14 => {
                $implementation::<U896Repr>::$func(&$argument)
            },
            15 => {
                $implementation::<U960Repr>::$func(&$argument)
            },
            16 => {
                $implementation::<U1024Repr>::$func($argument)
            },

            field_limbs => {
                unimplemented!("unimplemented for {} modulus limbs", field_limbs);
            }
        }
    }
}
// version of Sqrt that return Result instead of Option
fn sqrt_for_three_mod_four<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp<'a, E, F>) -> Result<Fp<'a, E, F>, ApiError> {
    // this is a simple case: we compute the power 
    // we know that it's 3 mod 4, so just bit shift

    let mut modulus_minus_three_by_four = *element.field.modulus();
    modulus_minus_three_by_four.shr(2);

    let mut a = element.pow(&modulus_minus_three_by_four.as_ref());

    let mut minus_one = Fp::one(element.field);
    minus_one.negate();

    let mut tmp = a.clone();
    tmp.square();
    tmp.mul_assign(&element);

    if tmp == minus_one {
        panic!("not 3 mod 4");
    } else {
        a.mul_assign(&element);

        Ok(a)
    }
}

fn sqrt<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: Fp<'a, E, F>) -> Result<Fp<'a, E, F>, ApiError> {
    if square_root::modulus_is_three_mod_four(element.field) {
        sqrt_for_three_mod_four(&element)
    } else {
        panic!("Not 3 mod 4")
    }
}

pub struct Fuzz<FE: ElementRepr> {
    _marker_fe: std::marker::PhantomData<FE>,
}

impl<FE: ElementRepr> Fuzzer for Fuzz<FE> {
    
    fn fuzz(bytes: &[u8]) -> Result<(), ApiError> {
        let data = &bytes[1..];
        let (field, modulus_len, _, rest) = public_interface::decode_fp::parse_base_field_from_encoding::<FE>(&data)?;
        let (a, b, rest) = public_interface::decode_g1::parse_ab_in_base_field_from_encoding(&rest, 1, &field)?;
        let (_order_len, order, rest) = public_interface::decode_g1::parse_group_order_from_encoding(rest)?;
        let fp_params = CurveOverFpParameters::new(&field);
        let curve = WeierstrassCurve::new(&order.as_ref(), a, b, &fp_params).map_err(|_| {
            panic!("Curve shape is not supported")
        })?;
        // Point 0
        let (x_0, rest) = public_interface::decode_fp::decode_fp(data, modulus_len, curve.params.params())?;
        let mut y_0 = curve.b.clone();
        let mut ax = x_0.clone();
        ax.mul_assign(&curve.a);
        y_0.add_assign(&ax);

        let mut x_3 = x_0.clone();
        x_3.square();
        x_3.mul_assign(&x_0);
        y_0.add_assign(&x_3);
        y_0 = sqrt(y_0.clone())?;

        let p_0 = CurvePoint::point_from_xy(&curve, x_0, y_0);
        let tester = ArithmeticProcessor::<_, _>{
            curve: &curve,
            generator: &p_0,
            group_order: &curve.subgroup_order_repr
        };

        tester.test();
        Ok(())
    }
}

pub struct FuzzG1Api;

impl Fuzzer for FuzzG1Api {
    fn fuzz(bytes: &[u8]) -> Result<(), ApiError> {
        let (_, modulus, _) = public_interface::decode_utils::parse_modulus_and_length(&bytes)?;
        let modulus_limbs = public_interface::decode_utils::num_limbs_for_modulus(&modulus)?;

        expand_for_modulus_limbs!(modulus_limbs, Fuzz, bytes, fuzz); 

        Ok(())
    }
}

pub fn run(bytes: &[u8]) -> Result<(), ApiError> {
    FuzzG1Api::fuzz(bytes)
}