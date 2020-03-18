use crate::fp::Fp;
use crate::representation::ElementRepr;
use crate::field::*;
use crate::extension_towers::fp2::{Extension2, Fp2};
use crate::traits::FieldElement;
use crate::traits::ZeroAndOne;
use crate::public_interface::{ApiError};

pub(crate) fn modulus_is_one_mod_four<E: ElementRepr, F: SizedPrimeField<Repr = E>>(field: &F) -> bool {
    const MASK: u64 = 3; // last two bits

    let last_limb = field.modulus().as_ref()[0];

    last_limb & MASK == 1
}

pub fn modulus_is_three_mod_four<E: ElementRepr, F: SizedPrimeField<Repr = E>>(field: &F) -> bool {
    const MASK: u64 = 3; // last two bits

    let last_limb = field.modulus().as_ref()[0];

    last_limb & MASK == 3
}

pub(crate) fn modulus_is_one_mod_eight<E: ElementRepr, F: SizedPrimeField<Repr = E>>(field: &F) -> bool {
    const MASK: u64 = 8; // last three bits

    let last_limb = field.modulus().as_ref()[0];

    last_limb & MASK == 1
}

pub(crate) fn modulus_is_five_mod_eight<E: ElementRepr, F: SizedPrimeField<Repr = E>>(field: &F) -> bool {
    const MASK: u64 = 8; // last three bits

    let last_limb = field.modulus().as_ref()[0];

    last_limb & MASK == 5
}

pub(crate) fn modulus_is_one_mod_sixteen<E: ElementRepr, F: SizedPrimeField<Repr = E>>(field: &F) -> bool {
    const MASK: u64 = 16; // last four bits

    let last_limb = field.modulus().as_ref()[0];

    last_limb & MASK == 1
}

pub(crate) fn modulus_is_one_mod_four_ext2<E: ElementRepr, F: SizedPrimeField<Repr = E>>(field: &Extension2<E, F>) -> bool {
    modulus_is_one_mod_four(field.field)
}

pub(crate) fn modulus_is_three_mod_four_ext2<E: ElementRepr, F: SizedPrimeField<Repr = E>>(field: &Extension2<E, F>) -> bool {
    modulus_is_three_mod_four(field.field)
}

pub(crate) fn modulus_is_one_mod_sixteen_ext2<E: ElementRepr, F: SizedPrimeField<Repr = E>>(field: &Extension2<E, F>) -> bool {
    modulus_is_one_mod_sixteen(field.field)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LegendreSymbol {
    Zero = 0,
    QuadraticResidue = 1,
    QuadraticNonResidue = -1,
}

pub(crate) fn legendre_symbol_fp<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp<'a, E, F>) -> LegendreSymbol {
    let mut modulus_minus_one_by_two = *element.field.modulus();
    modulus_minus_one_by_two.shr(1);

    let a = element.pow(&modulus_minus_one_by_two.as_ref());

    if a.is_zero() {
        LegendreSymbol::Zero
    } else if a == Fp::one(element.field) {
        LegendreSymbol::QuadraticResidue
    } else {
        LegendreSymbol::QuadraticNonResidue
    }
}

pub(crate) fn legendre_symbol_fp2<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp2<'a, E, F>) -> LegendreSymbol {
    let mut modulus_minus_one_by_two = *element.extension_field.field.modulus();
    modulus_minus_one_by_two.shr(1);

    let a = element.pow(&modulus_minus_one_by_two.as_ref());

    if a.is_zero() {
        LegendreSymbol::Zero
    } else if a == Fp2::one(element.extension_field) {
        LegendreSymbol::QuadraticResidue
    } else {
        LegendreSymbol::QuadraticNonResidue
    }
}

fn sqrt_for_one_mod_sixteen<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp<'a, E, F>) -> Option<Fp<'a, E, F>> {
    // Requires to know a generator and roots of unity
    // postpone for now
    // we know that it's 1 mod 16, so we can use simple bit shifts

    match legendre_symbol_fp(&element) {
        LegendreSymbol::Zero => {
            // it's zero, so clone
            Some(element.clone())
        },
        LegendreSymbol::QuadraticNonResidue => {
            None
        },
        LegendreSymbol::QuadraticResidue => {
            None
        }
    }
}

pub(crate) fn sqrt_for_five_mod_eight<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp<'a, E, F>) -> Option<Fp<'a, E, F>> {
    // Precomputation
    let mut modulus_minus_five_by_eight = *element.field.modulus();
    modulus_minus_five_by_eight.shr(3);
    let mut t = Fp::one(element.field);
    t.add_assign(&Fp::one(element.field));
    t = t.pow(modulus_minus_five_by_eight);
    // Computation
    let a_1 = element.clone().pow(modulus_minus_five_by_eight);
    let mut a_0 = a_1.clone();
    a_0.square();
    a_0.mul_assign(&element);
    a_0.square();

    let mut minus_one = Fp::one(element.field);
    minus_one.negate();

    if a_0 == minus_one {
        None
    } else {
        let mut b = t.clone();
        b.mul_assign(&a_1);
        let mut ab = element.clone();
        ab.mul_assign(&b);
        let mut i = b.clone();
        i.mul_assign(&ab);
        i.double();
        let mut i_minus_one = i.clone();
        i_minus_one.add_assign(&minus_one);
        let mut x = ab.clone();
        x.mul_assign(&i_minus_one);
        Some(x)
    }
}

pub fn sqrt_for_three_mod_four<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp<'a, E, F>) -> Option<Fp<'a, E, F>> {
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
        None
    } else {
        a.mul_assign(&element);

        Some(a)
    }
}


fn sqrt_for_nine_mod_sixteen<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp<'a, E, F>) -> Option<Fp<'a, E, F>> {
    // Precomputation
    let mut minus_one = Fp::one(element.field);
    minus_one.negate();
    let mut c_0 = Fp::one(element.field);
    let mut adder = Fp::one(element.field);
    let mut xq_pow = *element.field.modulus();
    let mut c = Fp::one(element.field);
    xq_pow.shr(1);
    while c_0 == Fp::one(element.field) {
        c = c_0.clone();
        c.add_assign(&adder);
        c_0 = c.clone();
        c_0.pow(xq_pow);
        adder.add_assign(&Fp::one(element.field))
    }
    let mut d_pow = *element.field.modulus();
    d_pow.shr(3);
    let d = c.clone().pow(d_pow);
    let mut e = c.clone();
    e.square();
    let mut pow = *element.field.modulus();
    pow.shr(4);
    let mut t = Fp::one(element.field);
    t.add_assign(&Fp::one(element.field));
    t = t.pow(pow);
    // Computation
    let a_1 = element.clone().pow(pow);
    let mut a_0 = a_1.clone();
    a_0.square();
    a_0.mul_assign(&element);
    a_0.square();
    a_0.square();
    if a_0 == minus_one {
        None
    } else {
        let mut b = a_1.clone();
        b.mul_assign(&t);
        let mut i = b.clone();
        i.square();
        i.mul_assign(&element);
        i.double();
        let mut r = i.clone();
        r.square();
        let mut x = Fp::one(element.field); // Initialize X
        if r == minus_one {
            let mut ab = element.clone();
            ab.mul_assign(&b);
            let mut i_minus_one = i.clone();
            i_minus_one.add_assign(&minus_one);
            x = ab.clone();
            x.mul_assign(&i_minus_one)
        } else {
            let mut u = d.clone();
            u.mul_assign(&b);
            let mut ca = element.clone();
            ca.mul_assign(&c);
            let mut i_minus_one = i.clone();
            i_minus_one.add_assign(&minus_one);
            x = u.clone();
            x.mul_assign(&ca);
            x.mul_assign(&i_minus_one);
        }
        Some(x)
    }
}

pub(crate) fn sqrt_for_three_mod_four_ext2<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp2<'a, E, F>) -> Option<Fp2<'a, E, F>> {
    // this is a simple case: we compute the power 
    // we know that it's 3 mod 4, so just bit shifts by 1 or 2 bits are ok

    if element.is_zero() {
        Some(element.clone())
    } else {
        let mut modulus_minus_three_by_four = *element.extension_field.field.modulus();
        modulus_minus_three_by_four.shr(2);
        let mut a1 = element.pow(&modulus_minus_three_by_four.as_ref());

        let mut alpha = a1.clone();
        alpha.square();
        alpha.mul_assign(&element);

        let mut a0 = alpha.clone();
        a0.frobenius_map(1);
        a0.mul_assign(&alpha);

        let one_fp2 = Fp2::one(element.extension_field);

        let mut minus_one_fp2 = one_fp2.clone();
        minus_one_fp2.negate();

        if a0 == minus_one_fp2 {
            None
        } else {
            a1.mul_assign(&element);

            if alpha == minus_one_fp2 {
                let mut tmp = Fp2::zero(element.extension_field);
                tmp.c1 = Fp::one(element.extension_field.field);
                a1.mul_assign(&tmp);
            } else {
                let mut modulus_minus_one_by_two = *element.extension_field.field.modulus();
                modulus_minus_one_by_two.shr(1);

                alpha.add_assign(&one_fp2);

                alpha = alpha.pow(&modulus_minus_one_by_two.as_ref());
                a1.mul_assign(&alpha);
            }

            Some(a1)
        }
    }
}

pub(crate) fn sqrt<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp<'a, E, F>) -> Option<Fp<'a, E, F>> {
    if modulus_is_three_mod_four(element.field) {
        sqrt_for_three_mod_four(&element)
    } else {
        let mut s = element.clone();
        if modulus_is_one_mod_four(element.field) {
            if modulus_is_five_mod_eight(element.field) {
                s = sqrt_for_five_mod_eight(&element)?;
            } else if modulus_is_one_mod_eight(element.field) {
                if modulus_is_one_mod_sixteen(element.field) {
                    s = sqrt_for_one_mod_sixteen(&element)?;
                } else {
                    s = sqrt_for_nine_mod_sixteen(&element)?;
                }
            }

        }
        Some(s) 
    }

}

pub(crate) fn sqrt_ext2<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp2<'a, E, F>) -> Option<Fp2<'a, E, F>> {
    if modulus_is_three_mod_four_ext2(element.extension_field) {
        sqrt_for_three_mod_four_ext2(&element)
    } else {
        None
    }
}

fn sqrt_for_three_mod_four_result<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp<'a, E, F>) -> Result<Fp<'a, E, F>, ApiError> {
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

pub(crate) fn sqrt_result<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: Fp<'a, E, F>) -> Result<Fp<'a, E, F>, ApiError> {
    if modulus_is_three_mod_four(element.field) {
        sqrt_for_three_mod_four_result(&element)
    } else {
        panic!("Not 3 mod 4")
    }
}

pub(crate) fn sqrt_for_three_mod_four_ext2_result<'a, E: ElementRepr, F: SizedPrimeField<Repr = E>>(element: &Fp2<'a, E, F>) -> Result<Fp2<'a, E, F>, ApiError> {
    // this is a simple case: we compute the power 
    // we know that it's 3 mod 4, so just bit shifts by 1 or 2 bits are ok

    if element.is_zero() {
        Ok(element.clone())
    } else {
        let mut modulus_minus_three_by_four = *element.extension_field.field.modulus();
        modulus_minus_three_by_four.shr(2);
        let mut a1 = element.pow(&modulus_minus_three_by_four.as_ref());

        let mut alpha = a1.clone();
        alpha.square();
        alpha.mul_assign(&element);

        let mut a0 = alpha.clone();
        a0.frobenius_map(1);
        a0.mul_assign(&alpha);

        let one_fp2 = Fp2::one(element.extension_field);

        let mut minus_one_fp2 = one_fp2.clone();
        minus_one_fp2.negate();

        if a0 == minus_one_fp2 {
            panic!("unimplemented")
        } else {
            a1.mul_assign(&element);

            if alpha == minus_one_fp2 {
                let mut tmp = Fp2::zero(element.extension_field);
                tmp.c1 = Fp::one(element.extension_field.field);
                a1.mul_assign(&tmp);
            } else {
                let mut modulus_minus_one_by_two = *element.extension_field.field.modulus();
                modulus_minus_one_by_two.shr(1);

                alpha.add_assign(&one_fp2);

                alpha = alpha.pow(&modulus_minus_one_by_two.as_ref());
                a1.mul_assign(&alpha);
            }

            Ok(a1)
        }
    }
}
