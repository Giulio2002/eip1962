use crate::field::{SizedPrimeField};
use crate::fp::Fp;
use crate::extension_towers::fp2;
use crate::extension_towers::fp3;
use crate::representation::ElementRepr;
use crate::traits::ZeroAndOne;
use crate::integers::MaxFieldUint;
use crate::field::PrimeField;

use crate::errors::ApiError;
use super::decode_utils::*;
use crate::field::field_from_modulus;

pub fn parse_base_field_from_encoding<
    'a,
    FE: ElementRepr,
    >(encoding: &'a [u8]) -> Result<(PrimeField<FE>, usize, MaxFieldUint, &'a [u8]), ApiError>
{
    let ((modulus, modulus_len), rest) = get_base_field_params(&encoding)?;
    let field = field_from_modulus::<FE>(&modulus).map_err(|_| {
        ApiError::InputError("Failed to create prime field from modulus".to_owned())
    })?;
    if rest.len() < modulus_len {
        return Err(ApiError::InputError("Input is not long enough".to_owned()));
    }

    Ok((field, modulus_len, modulus, rest))
}

pub fn decode_fp<
    'a,
    FE: ElementRepr,
    F: SizedPrimeField<Repr = FE>
    >
(
    bytes: &'a [u8], 
    field_byte_len: usize,
    base_field: &'a F
) -> Result<(Fp<'a, FE, F>, &'a [u8]), ApiError>
{
    let (x_encoding, rest) = split(bytes, field_byte_len, "Input is not long enough to get Fp element")?;
    let x = Fp::from_be_bytes(base_field, x_encoding, true).map_err(|_| {
        ApiError::InputError("Failed to parse Fp element".to_owned())
    })?;

    Ok((x, rest))
}

pub(crate) fn decode_fp2<
    'a,
    FE: ElementRepr,
    F: SizedPrimeField<Repr = FE>
    >
(
    bytes: &'a [u8], 
    field_byte_len: usize,
    extension_field: &'a fp2::Extension2<'a, FE, F>
) -> Result<(fp2::Fp2<'a, FE, F>, &'a [u8]), ApiError>
{
    let (c0_encoding, rest) = split(bytes, field_byte_len, "Input is not long enough to Fp2_c0")?;
    let c0 = Fp::from_be_bytes(extension_field.field, c0_encoding, true).map_err(|_| {
        ApiError::InputError("Failed to parse Fp2 element".to_owned())
    })?;

    let (c1_encoding, rest) = split(rest, field_byte_len, "Input is not long enough to get Fp2_c1")?;
    let c1 = Fp::from_be_bytes(extension_field.field, c1_encoding, true).map_err(|_| {
        ApiError::InputError("Failed to parse Fp2 element".to_owned())
    })?;

    let mut x = fp2::Fp2::zero(extension_field);
    x.c0 = c0;
    x.c1 = c1;

    Ok((x, rest))
}

pub(crate) fn decode_fp3<
    'a,
    FE: ElementRepr,
    F: SizedPrimeField<Repr = FE>
    >
(
    bytes: &'a [u8], 
    field_byte_len: usize,
    extension_field: &'a fp3::Extension3<'a, FE, F>
) -> Result<(fp3::Fp3<'a, FE, F>, &'a [u8]), ApiError>
{
    let (c0_encoding, rest) = split(bytes, field_byte_len, "Input is not long enough to Fp3_c0")?;
    let c0 = Fp::from_be_bytes(extension_field.field, c0_encoding, true).map_err(|_| {
        ApiError::InputError("Failed to parse Fp3 element".to_owned())
    })?;

    let (c1_encoding, rest) = split(rest, field_byte_len, "Input is not long enough to Fp3_c1")?;
    let c1 = Fp::from_be_bytes(extension_field.field, c1_encoding, true).map_err(|_| {
        ApiError::InputError("Failed to parse Fp3 element".to_owned())
    })?;

    let (c2_encoding, rest) = split(rest, field_byte_len, "Input is not long enough to Fp3_c2")?;
    let c2 = Fp::from_be_bytes(extension_field.field, c2_encoding, true).map_err(|_| {
        ApiError::InputError("Failed to parse Fp3element".to_owned())
    })?;

    let mut x = fp3::Fp3::zero(extension_field);
    x.c0 = c0;
    x.c1 = c1;
    x.c2 = c2;

    Ok((x, rest))
}

pub(crate) fn serialize_fp_fixed_len<
    'a,
    FE: ElementRepr,
    F: SizedPrimeField<Repr = FE>
    >
(
    field_byte_len: usize,
    element: &'a Fp<'a, FE, F>
) -> Result<Vec<u8>, ApiError>
{
    let mut bytes: Vec<u8> = Vec::with_capacity(field_byte_len);
    let element = element.into_repr();
    element.write_be(&mut bytes).map_err(|_| {
        ApiError::OutputError("Failed to serialize Fp element".to_owned())
    })?;
    if bytes.len() > field_byte_len {
        bytes.reverse();
        bytes.truncate(field_byte_len);
        bytes.reverse();
    } else if bytes.len() < field_byte_len {
        bytes.reverse();
        bytes.resize(field_byte_len, 0u8);
        bytes.reverse();
    }

    Ok(bytes)
}

pub(crate) fn serialize_fp2_fixed_len<
    'a,
    FE: ElementRepr,
    F: SizedPrimeField<Repr = FE>
    >
    (
        field_byte_len: usize,
        element: &'a fp2::Fp2<'a, FE, F>
    ) -> Result<Vec<u8>, ApiError>
{
    let mut bytes = Vec::with_capacity(2*field_byte_len);
    bytes.extend(serialize_fp_fixed_len(field_byte_len, &element.c0)?);
    bytes.extend(serialize_fp_fixed_len(field_byte_len, &element.c1)?);

    Ok(bytes)
}

pub(crate) fn serialize_fp3_fixed_len<
    'a,
    FE: ElementRepr,
    F: SizedPrimeField<Repr = FE>
    >
    (
        field_byte_len: usize,
        element: &'a fp3::Fp3<'a, FE, F>
    ) -> Result<Vec<u8>, ApiError>
{
    let mut bytes = Vec::with_capacity(3*field_byte_len);
    bytes.extend(serialize_fp_fixed_len(field_byte_len, &element.c0)?);
    bytes.extend(serialize_fp_fixed_len(field_byte_len, &element.c1)?);
    bytes.extend(serialize_fp_fixed_len(field_byte_len, &element.c2)?);

    Ok(bytes)
}