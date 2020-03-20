use crate::weierstrass::*;
use crate::weierstrass::curve::{CurvePoint, WeierstrassCurve};
use crate::representation::{ElementRepr};
use crate::field::*;
use crate::public_interface;
use crate::public_interface::{ApiError};
use crate::traits::{FieldElement};
use crate::traits::ZeroAndOne;
use crate::square_root::*;

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
        // First Curve (G1)
        let (_, modulus_len_1, mut modulus, rest) = public_interface::decode_fp::parse_base_field_from_encoding::<FE>(&data)?;
        modulus.as_mut()[0] = 3; // This is now 3 mod 4 (3&3 == 3)
        let field = field_from_modulus::<FE>(&modulus).map_err(|_| {
            ApiError::InputError("Failed to create prime field from modulus".to_owned())
        })?;
        let (a, b, rest) = public_interface::decode_g1::parse_ab_in_base_field_from_encoding(&rest, 1, &field)?;
        let (_order_len, order, rest) = public_interface::decode_g1::parse_group_order_from_encoding(rest)?;
        let fp_params = CurveOverFpParameters::new(&field);

        let curve_g1 = WeierstrassCurve::new(&order.as_ref(), a, b, &fp_params).map_err(|_| {
            ApiError::InputError("Curve shape is not supported".to_owned())
        })?;
        // Second curve (G2)
        let (_,  modulus_len_2, mut modulus, rest) = public_interface::decode_fp::parse_base_field_from_encoding::<FE>(&data)?;
        modulus.as_mut()[0] = 3; // This is now 3 mod 4 (3&3 == 3)
        let field = field_from_modulus::<FE>(&modulus).map_err(|_| {
            ApiError::InputError("Failed to create prime field from modulus".to_owned())
        })?;
        let (extension_2, rest) = public_interface::decode_g2::create_fp2_extension(rest, &modulus, modulus_len_2, &field, false)?;
        let (a, b, rest) = public_interface::decode_g2::parse_ab_in_fp2_from_encoding(&rest, modulus_len_2, &extension_2)?;
        let (_order_len, order, rest) = public_interface::decode_g1::parse_group_order_from_encoding(rest)?;

        let fp2_params = CurveOverFp2Parameters::new(&extension_2);

        let curve_g2 = WeierstrassCurve::new(&order.as_ref(), a, b, &fp2_params).map_err(|_| {
            ApiError::InputError("Curve shape is not supported".to_owned())
        })?;
        // First X on G1 (x1_1)
        let (x1_1, rest) = public_interface::decode_fp::decode_fp(rest, modulus_len_1, curve_g1.params.params())?;
        // Second X on G1 (x1_2)
        let (x1_2, rest) = public_interface::decode_fp::decode_fp(rest, modulus_len_1, curve_g1.params.params())?;
        // First X on G2 (x2_1)
        let (x2_1, rest) = public_interface::decode_fp::decode_fp2(rest, modulus_len_2, curve_g2.params.params())?;
        // Second X on G2 (x2_2)
        let (x2_2, rest) = public_interface::decode_fp::decode_fp2(rest, modulus_len_2, curve_g2.params.params())?;
        // Multipliers (m_1, m_2)
        let (m_1, rest) = public_interface::decode_fp::decode_fp(rest, modulus_len_1, curve_g1.params.params())?;
        let (m_2, _) = public_interface::decode_fp::decode_fp(rest, modulus_len_1, curve_g1.params.params())?;
        // Check Linearity in G1 f(ar1+br2)=af(r1)+bf(r2)
        let mut x_lhs = x1_1.clone();
        x_lhs.mul_assign(&m_1);
        let mut x_m = x1_2.clone();
        x_m.mul_assign(&m_2);
        x_lhs.add_assign(&x_m);
        let mut lhs = curve_g1.b.clone();
        let mut ax = x_lhs.clone();
        ax.mul_assign(&curve_g1.a);
        lhs.add_assign(&ax);
        let mut x_3 = x_lhs.clone();
        x_3.square();
        x_3.mul_assign(&x_lhs);
        lhs.add_assign(&x_3);
        lhs = sqrt_result(lhs.clone())?;   
        
        let mut g_r = curve_g1.b.clone();
        let mut ax = x1_1.clone();
        ax.mul_assign(&curve_g1.a);
        g_r.add_assign(&ax);
        let mut x_3 = x1_1.clone();
        x_3.square();
        x_3.mul_assign(&x1_1);
        g_r.add_assign(&x_3);
        g_r = sqrt_result(g_r.clone())?;
        g_r.mul_assign(&m_1);
        let mut g_r2 = curve_g1.b.clone();
        let mut ax = x1_2.clone();
        ax.mul_assign(&curve_g1.a);
        g_r.add_assign(&ax);
        let mut x_3 = x1_2.clone();
        x_3.square();
        x_3.mul_assign(&x1_2);
        g_r2.add_assign(&x_3);
        g_r2 = sqrt_result(g_r2.clone())?;
        g_r2.mul_assign(&m_2);
        let mut rhs = g_r2.clone();
        rhs.mul_assign(&g_r);

        assert!(rhs == lhs);
        // Multipliers (m_1, m_2)
        let (m_1, rest) = public_interface::decode_fp::decode_fp2(rest, modulus_len_2, curve_g2.params.params())?;
        let (m_2, _) = public_interface::decode_fp::decode_fp2(rest, modulus_len_2, curve_g2.params.params())?;
        // Check Linearity in G2
        let mut x_lhs = x2_1.clone();
        x_lhs.mul_assign(&m_1);
        let mut x_m = x2_2.clone();
        x_m.mul_assign(&m_2);
        x_lhs.add_assign(&x_m);
        let mut lhs = curve_g2.b.clone();
        let mut ax_g2 = x_lhs.clone();
        ax_g2.mul_assign(&curve_g2.a);
        lhs.add_assign(&ax_g2);
        let mut x_3 = x_lhs.clone();
        x_3.square();
        x_3.mul_assign(&x_lhs);
        lhs.add_assign(&x_3);
        lhs = sqrt_for_three_mod_four_ext2_result(&lhs.clone())?;   
        
        let mut g_r = curve_g2.b.clone();
        let mut ax = x2_1.clone();
        ax.mul_assign(&curve_g2.a);
        g_r.add_assign(&ax);
        let mut x_3 = x2_1.clone();
        x_3.square();
        x_3.mul_assign(&x2_1);
        g_r.add_assign(&x_3);
        g_r = sqrt_for_three_mod_four_ext2_result(&g_r.clone())?;
        g_r.mul_assign(&m_1);
        let mut g_r2 = curve_g2.b.clone();
        let mut ax = x2_2.clone();
        ax.mul_assign(&curve_g2.a);
        g_r.add_assign(&ax);
        let mut x_3 = x2_2.clone();
        x_3.square();
        x_3.mul_assign(&x2_2);
        g_r2.add_assign(&x_3);
        g_r2 = sqrt_for_three_mod_four_ext2_result(&g_r2.clone())?;
        g_r2.mul_assign(&m_2);
        let mut rhs = g_r2.clone();
        rhs.mul_assign(&g_r);

        assert!(rhs == lhs);
        Ok(())
    }
}

pub struct FuzzG1Api;

impl Fuzzer for FuzzG1Api {
    fn fuzz(bytes: &[u8]) -> Result<(), ApiError> {
        let (_, modulus, _) = public_interface::decode_utils::parse_modulus_and_length(&bytes[1..])?;
        let modulus_limbs = public_interface::decode_utils::num_limbs_for_modulus(&modulus)?;

        expand_for_modulus_limbs!(modulus_limbs, Fuzz, bytes, fuzz); 

        Ok(())
    }
}

pub fn run(bytes: &[u8]) -> Result<(), ApiError> {
    FuzzG1Api::fuzz(bytes)
}