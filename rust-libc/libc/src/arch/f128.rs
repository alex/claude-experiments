//! Conversions between `f64` and IEEE binary128, the `long double` of
//! AArch64. Pure integer code, so it is also compiled and tested on
//! hosts that do not use it.

/// Converts an IEEE binary128 value to `f64` (round to nearest even).
pub fn f128_to_f64(bits: u128) -> f64 {
    let sign = ((bits >> 127) as u64) << 63;
    let exp = ((bits >> 112) & 0x7fff) as i32;
    let mant = bits & ((1u128 << 112) - 1);
    if exp == 0x7fff {
        // Infinity, or a NaN (made quiet, payload dropped).
        let payload = if mant != 0 { 1u64 << 51 } else { 0 };
        return f64::from_bits(sign | 0x7ff0_0000_0000_0000 | payload);
    }
    if exp == 0 && mant == 0 {
        return f64::from_bits(sign);
    }
    // Normalise so the leading one is at bit 112: the value is then
    // `m * 2^(e - 112)`.
    let (m, e) = if exp == 0 {
        (mant, -16382)
    } else {
        (mant | (1u128 << 112), exp - 16383)
    };
    let shift = m.leading_zeros() as i32 - 15;
    let m = m << shift;
    let e = e - shift; // exponent of the leading bit
    if e > 1023 {
        return f64::from_bits(sign | 0x7ff0_0000_0000_0000);
    }
    // Significant bits an f64 keeps: 53 for normals, fewer below 2^-1022.
    let keep = if e >= -1022 { 53 } else { 1075 + e };
    if keep <= 0 {
        // At most half the smallest subnormal: it rounds to zero, or up
        // to that subnormal when strictly above half of it.
        let up = keep == 0 && m > (1u128 << 112);
        return f64::from_bits(sign | up as u64);
    }
    let drop = (113 - keep) as u32;
    let mut frac = (m >> drop) as u64;
    let rem = m & ((1u128 << drop) - 1);
    let half = 1u128 << (drop - 1);
    if rem > half || (rem == half && frac & 1 == 1) {
        frac += 1;
    }
    let bits = if e >= -1022 {
        if frac >> 53 != 0 {
            // Rounding carried to the next power of two.
            if e + 1 > 1023 {
                0x7ff0_0000_0000_0000
            } else {
                ((e + 1 + 1023) as u64) << 52
            }
        } else {
            (((e + 1023) as u64) << 52) | (frac & ((1 << 52) - 1))
        }
    } else {
        // Subnormal: `frac` is the encoding, a carry included (it then
        // encodes the smallest normal or a larger subnormal exactly).
        frac
    };
    f64::from_bits(sign | bits)
}

/// Converts an `f64` to IEEE binary128 bits (exactly).
pub fn f64_to_f128(x: f64) -> u128 {
    let b = x.to_bits();
    let sign = ((b >> 63) as u128) << 127;
    let exp = ((b >> 52) & 0x7ff) as i32;
    let mant = (b & ((1 << 52) - 1)) as u128;
    if exp == 0x7ff {
        return sign | (0x7fffu128 << 112) | if mant != 0 { 1u128 << 111 } else { 0 };
    }
    if exp == 0 {
        if mant == 0 {
            return sign;
        }
        // Subnormal double: normalise.
        let shift = mant.leading_zeros() as i32 - (128 - 53);
        let m = (mant << shift) & ((1u128 << 52) - 1);
        let e = 1 - 1023 - shift + 16383;
        return sign | ((e as u128) << 112) | (m << 60);
    }
    sign | (((exp - 1023 + 16383) as u128) << 112) | (mant << 60)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip() {
        for x in [
            0.0,
            -0.0,
            1.0,
            -2.5,
            core::f64::consts::PI,
            1e300,
            1e-300,
            5e-324,
            f64::MAX,
            f64::MIN_POSITIVE,
            f64::INFINITY,
            f64::NEG_INFINITY,
        ] {
            let back = f128_to_f64(f64_to_f128(x));
            assert_eq!(back.to_bits(), x.to_bits(), "{x}");
        }
        assert!(f128_to_f64(f64_to_f128(f64::NAN)).is_nan());
    }

    #[test]
    fn rounding() {
        // One third in binary128 (more precise than a double) rounds to 1/3.
        let third: u128 = 0x3ffd_5555_5555_5555_5555_5555_5555_5555;
        assert_eq!(f128_to_f64(third), 1.0 / 3.0);
        // Overflow saturates; far below the subnormals is zero.
        assert_eq!(f128_to_f64(0x43ff << 112), f64::INFINITY);
        assert_eq!(f128_to_f64(0x0001 << 112), 0.0);
        // 2^-1075 exactly is a tie and rounds to even (zero); a hair more
        // rounds up to the smallest subnormal.
        let e = |exp: i32| ((exp + 16383) as u128) << 112;
        assert_eq!(f128_to_f64(e(-1075)), 0.0);
        assert_eq!(f128_to_f64(e(-1075) | 1), f64::from_bits(1));
        // Just below 2^-1022 rounds up to the smallest normal.
        assert_eq!(
            f128_to_f64(e(-1023) | ((1u128 << 112) - 1)),
            f64::MIN_POSITIVE
        );
        // 1 + 2^-53 is a tie at the 53-bit boundary: even, so 1.0; a hair
        // more rounds up.
        assert_eq!(f128_to_f64(e(0) | (1u128 << 59)), 1.0);
        assert_eq!(f128_to_f64(e(0) | (1u128 << 59) | 1), 1.0 + f64::EPSILON);
        // Carry across a power of two: 2 - 2^-54 rounds to 2.
        assert_eq!(
            f128_to_f64(e(0) | (((1u128 << 112) - 1) & !((1u128 << 58) - 1))),
            2.0
        );
    }
}
