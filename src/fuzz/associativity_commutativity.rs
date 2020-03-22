use crate::weierstrass::*;
use crate::weierstrass::curve::{CurvePoint, WeierstrassCurve};
use crate::representation::{ElementRepr};
use crate::field::*;
use crate::public_interface;
use crate::public_interface::{ApiError};
use crate::traits::{FieldElement};
use crate::traits::ZeroAndOne;
use crate::square_root::*;
use crate::integers::{MaxFieldUint, MaxGroupSizeUint, MaxLoopParametersUint};

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
            default => {
                $implementation::<U1024Repr>::$func($argument)
            }
        }
    }
}
// Testing Part
pub(crate) struct Tester<
    'a, 
    'b: 'a, 
    FE: FieldElement + ZeroAndOne + 'a,
    CP: CurveParameters<BaseFieldElement = FE> + 'a
> {
    curve: &'b WeierstrassCurve<'a, CP>,
    a: &'b CurvePoint<'a, CP>,
    b: &'b CurvePoint<'a, CP>,
    c: &'b CurvePoint<'a, CP>,
    group_order: &'b [u64],
}

impl<
    'a, 
    'b: 'a, 
    FE: FieldElement + ZeroAndOne + 'a,
    CP: CurveParameters<BaseFieldElement = FE> + 'a
> Tester<'a, 'b, FE, CP> {

    fn a_plus_a_equal_to_2a(&self) {
        let mut a_plus_a = self.a.clone();
        let other_a = self.a.clone();
        a_plus_a.add_assign(&other_a);

        let mut two_a = self.a.clone();
        two_a.double();

        assert_eq!(a_plus_a.into_xy(), two_a.into_xy());
    }

    fn a_minus_a_equal_zero(&self) {
        let mut a_minus_a = self.a.clone();
        let mut minus_a = self.a.clone();
        minus_a.negate();

        a_minus_a.add_assign(&minus_a);

        assert!(a_minus_a.is_zero());
    }

    fn two_a_is_equal_to_two_a(&self) {
        let mut two_a = self.a.clone();
        two_a.double();

        let other_two_a = self.a.mul(&[2u64]);

        assert_eq!(other_two_a.into_xy(), two_a.into_xy());
    }

    fn three_a_is_equal_to_three_a(&self) {
        let mut two_a = self.a.clone();
        two_a.double();

        let a = self.a.clone();

        let mut t0 = two_a.clone();
        t0.add_assign(&a);

        let mut t1 = a.clone();
        t1.add_assign(&two_a);

        let t2 = self.a.mul(&[3u64]);

        assert_eq!(t0.into_xy(), t1.into_xy());
        assert_eq!(t0.into_xy(), t2.into_xy());
    }

    fn a_plus_b_equal_to_b_plus_a(&self) {
        let mut b = self.b.clone();
        let a = self.a.clone();

        let mut a_plus_b = a.clone();
        a_plus_b.add_assign(&b);

        let mut b_plus_a = b.clone();
        b_plus_a.add_assign(&a);

        assert_eq!(a_plus_b.into_xy(), b_plus_a.into_xy());
    }

    fn a_mul_by_zero_is_zero(&self) {
        let a = self.a.mul(&[0u64]);

        assert!(a.is_zero());
    }

    fn a_mul_by_group_order_is_zero(&self) {
        let a = self.a.mul(&self.group_order);

        assert!(a.is_zero());
    }

    fn a_mul_by_scalar_wraps_over_group_order(&self) {
        let scalar = MaxGroupSizeUint::from(&[12345][..]);
        let group_order = MaxGroupSizeUint::from(&self.group_order[..]);
        let scalar_plus_group_order = scalar + group_order;
        let a = self.a.mul(&scalar.as_ref());
        let b = self.a.mul(&scalar_plus_group_order.as_ref());

        assert_eq!(a.into_xy(), b.into_xy());
    }

    fn a_mul_by_minus_scalar(&self) {
        let scalar = MaxGroupSizeUint::from(&[12345][..]);
        let group_order = MaxGroupSizeUint::from(&self.group_order[..]);
        let minus_scalar = group_order - scalar;
        let a = self.a.mul(&minus_scalar.as_ref());
        let mut b = self.b.mul(&scalar.as_ref());
        b.negate();

        assert_eq!(a.into_xy(), b.into_xy());
    }

    fn associativity_a_b_c(&self) {
        let a = self.a.clone();
        let b = self.b.clone();
        let c = self.c.clone();
        // RHS = (B+C) + A
        let mut b_plus_c = c.clone();
        b_plus_c.add_assign(&b);
        let mut rhs =  b_plus_c.clone();
        rhs.add_assign(&a);
        // LHS = (B+A) + C
        let mut b_plus_a = a.clone();
        b_plus_a.add_assign(&b);
        let mut lhs =  b_plus_a.clone();
        lhs.add_assign(&c);

        assert_eq!(rhs.into_xy(), lhs.into_xy());        
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
        self.associativity_a_b_c();
    }
}

trait Fuzzer {
    fn fuzz(bytes: &[u8]) -> Result<(), ApiError>;
}

// version of Sqrt that return Result instead of Option
pub struct Fuzz<FE: ElementRepr> {
    _marker_fe: std::marker::PhantomData<FE>,
}

impl<FE: ElementRepr> Fuzzer for Fuzz<FE> {
    
    fn fuzz(bytes: &[u8]) -> Result<(), ApiError> {
        let data = &bytes[1..];
        let (_, modulus_len, mut modulus, rest) = public_interface::decode_fp::parse_base_field_from_encoding::<FE>(&data)?;
        modulus.as_mut()[0] = 3; // This is now 3 mod 4 (3&3 == 3)  
        let field = field_from_modulus::<FE>(&modulus).map_err(|_| {
            ApiError::InputError("Failed to create prime field from modulus".to_owned())
        })?;      
        let (a, b, rest) = public_interface::decode_g1::parse_ab_in_base_field_from_encoding(&rest, 1, &field)?;
        let (_order_len, order, rest) = public_interface::decode_g1::parse_group_order_from_encoding(rest)?;
        let fp_params = CurveOverFpParameters::new(&field);
        let curve = WeierstrassCurve::new(&order.as_ref(), a, b, &fp_params).map_err(|_| {
            ApiError::InputError("Curve shape is not supported".to_owned())
        })?;
        // Point A
        let (x, rest) = public_interface::decode_fp::decode_fp(rest, modulus_len, curve.params.params())?;
        let mut y = curve.b.clone();
        let mut ax = x.clone();
        ax.mul_assign(&curve.a);
        y.add_assign(&ax);
        let mut x_3 = x.clone();
        x_3.square();
        x_3.mul_assign(&x);
        y.add_assign(&x_3);
        y = sqrt_result(y.clone())?;
        let a = CurvePoint::point_from_xy(&curve, x, y);
        // Point B 
        
        let (x, rest) = public_interface::decode_fp::decode_fp(rest, modulus_len, curve.params.params())?;
        y = curve.b.clone();
        ax = x.clone();
        ax.mul_assign(&curve.a);
        y.add_assign(&ax);
        let mut x_3 = x.clone();
        x_3.square();
        x_3.mul_assign(&x);
        y.add_assign(&x_3);
        y = sqrt_result(y.clone())?;
        let b = CurvePoint::point_from_xy(&curve, x, y);
        // Point C
        let (x, rest) = public_interface::decode_fp::decode_fp(rest, modulus_len, curve.params.params())?;
        let mut y = curve.b.clone();
        let mut ax = x.clone();
        ax.mul_assign(&curve.a);
        y.add_assign(&ax);
        let mut x_3 = x.clone();
        x_3.square();
        x_3.mul_assign(&x);
        y.add_assign(&x_3);
        y = sqrt_result(y.clone())?;
        let c = CurvePoint::point_from_xy(&curve, x, y);
        // Make Point Generator
        // Test through ArithmeticProcessor
        /*
        let tester = Tester::<_, _> {
            curve: &curve,
            a: &a,
            b: &b,
            c: &c,
            group_order: &curve.subgroup_order_repr
        };

        tester.test();*/
        Ok(())
    }
}

pub struct FuzzG1Api;

impl Fuzzer for FuzzG1Api {
    fn fuzz(bytes: &[u8]) -> Result<(), ApiError> {
        let (_, modulus, _) = public_interface::decode_utils::parse_modulus_and_length(&bytes[1..])?;
        let modulus_limbs = public_interface::decode_utils::num_limbs_for_modulus(&modulus)?;
        if modulus_limbs > 16 {
            Ok(())
        } else {
            expand_for_modulus_limbs!(modulus_limbs, Fuzz, bytes, fuzz); 

            Ok(())
        }
    }
}

pub fn run(bytes: &[u8]) -> Result<(), ApiError> {
    FuzzG1Api::fuzz(bytes)
}