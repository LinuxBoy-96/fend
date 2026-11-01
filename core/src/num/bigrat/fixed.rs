use super::BigRat;
use super::sign::Sign;
use crate::error::{FendError, Interrupt};
use crate::interrupt::test_int;
use crate::num::biguint::BigUint;
use crate::result::FResult;

pub(super) const WORK_BITS: u64 = super::ROOT_BITS + 32;

const MAX_EXPONENT: u64 = 1 << 24;

const CONST_BITS: u64 = 512;

const LN_2: [u64; 8] = [
	0x2757_3b29_1169_b825,
	0xed2e_ae35_c138_2144,
	0x5595_52fb_4afa_1b10,
	0xe7b8_7620_6deb_ac98,
	0x8a0d_175b_8baa_fa2b,
	0x40f3_4326_7298_b62d,
	0xc9e3_b398_03f2_f6af,
	0xb172_17f7_d1cf_79ab,
];

fn shl(mut x: BigUint, n: u64) -> BigUint {
	x.lshift_u64(n);
	x
}

fn shr(mut x: BigUint, n: u64) -> BigUint {
	x.rshift_u64(n);
	x
}

fn pow2(n: u64) -> BigUint {
	shl(1.into(), n)
}

#[derive(Clone)]
struct Fixed {
	neg: bool,
	mag: BigUint,
}

impl Fixed {
	fn new(neg: bool, mag: BigUint) -> Self {
		let neg = neg && !mag.is_zero();
		Self { neg, mag }
	}

	fn one(bits: u64) -> Self {
		Self::new(false, pow2(bits))
	}

	fn from_rat<I: Interrupt>(x: &BigRat, bits: u64, int: &I) -> FResult<Self> {
		let mag = shl(x.num.clone(), bits).div(&x.den, int)?;
		Ok(Self::new(x.sign == Sign::Negative, mag))
	}

	fn into_rat(self, bits: u64) -> BigRat {
		BigRat {
			sign: if self.neg {
				Sign::Negative
			} else {
				Sign::Positive
			},
			num: self.mag,
			den: pow2(bits),
		}
	}

	fn add(self, other: &Self) -> Self {
		if self.neg == other.neg {
			Self::new(self.neg, self.mag.add(&other.mag))
		} else if self.mag >= other.mag {
			Self::new(self.neg, self.mag.sub(&other.mag))
		} else {
			Self::new(other.neg, other.mag.clone().sub(&self.mag))
		}
	}

	fn sub(self, other: &Self) -> Self {
		self.add(&Self::new(!other.neg, other.mag.clone()))
	}

	fn mul<I: Interrupt>(&self, other: &Self, bits: u64, int: &I) -> FResult<Self> {
		let mag = shr(self.mag.clone().mul(&other.mag, int)?, bits);
		Ok(Self::new(self.neg != other.neg, mag))
	}

	fn mul_int<I: Interrupt>(&self, n: u64, int: &I) -> FResult<Self> {
		Ok(Self::new(self.neg, self.mag.clone().mul(&n.into(), int)?))
	}

	fn div_int<I: Interrupt>(&self, n: u64, int: &I) -> FResult<Self> {
		Ok(Self::new(self.neg, self.mag.clone().div(&n.into(), int)?))
	}

	fn times_pow2(self, n: u64) -> Self {
		Self::new(self.neg, shl(self.mag, n))
	}

	fn over_pow2(self, n: u64) -> Self {
		Self::new(self.neg, shr(self.mag, n))
	}

	fn negate_if(self, neg: bool) -> Self {
		Self::new(self.neg != neg, self.mag)
	}

	fn is_zero(&self) -> bool {
		self.mag.is_zero()
	}
}

fn ln_2<I: Interrupt>(bits: u64, int: &I) -> FResult<Fixed> {
	if bits <= CONST_BITS {
		let constant = BigUint::Large(LN_2.to_vec());
		return Ok(Fixed::new(false, shr(constant, CONST_BITS - bits)));
	}
	let third = BigRat::from(1).div(&3.into(), int)?;
	let half = atanh_small(&third, bits + 8, int)?;
	Fixed::from_rat(&half.mul(&2.into(), int)?, bits, int)
}

fn scale_pow2(mut x: BigRat, k: i64) -> BigRat {
	if k >= 0 {
		x.num = shl(x.num, k.unsigned_abs());
	} else {
		x.den = shl(x.den, k.unsigned_abs());
	}
	x
}

fn times<I: Interrupt>(x: &BigRat, f: &Fixed, bits: u64, int: &I) -> FResult<BigRat> {
	Ok(BigRat {
		sign: if (x.sign == Sign::Negative) == f.neg {
			Sign::Positive
		} else {
			Sign::Negative
		},
		num: x.num.clone().mul(&f.mag, int)?,
		den: shl(x.den.clone(), bits),
	})
}

fn log2_estimate(x: &BigRat) -> f64 {
	x.num.log2() - x.den.log2()
}

fn f64_estimate(x: &BigRat) -> f64 {
	if x.num.is_zero() {
		0.0
	} else {
		log2_estimate(x).exp2()
	}
}

#[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss)]
fn exponent(value: f64) -> FResult<i64> {
	let rounded = value.round();
	if !rounded.is_finite() || rounded.abs() > MAX_EXPONENT as f64 {
		return Err(FendError::ValueTooLarge);
	}
	Ok(rounded as i64)
}

fn bit_width(n: u64) -> u64 {
	u64::from(n.bit_width())
}

fn is_negative(x: &BigRat) -> bool {
	x.sign == Sign::Negative && !x.num.is_zero()
}

fn abs(x: &BigRat) -> BigRat {
	BigRat {
		sign: Sign::Positive,
		num: x.num.clone(),
		den: x.den.clone(),
	}
}

fn is_small<I: Interrupt>(x: &BigRat, int: &I) -> FResult<bool> {
	Ok(x.num.clone().mul(&2.into(), int)? < x.den)
}

fn exp_fixed<I: Interrupt>(r: &Fixed, bits: u64, int: &I) -> FResult<Fixed> {
	const HALVINGS: u64 = 8;
	let work = bits + HALVINGS + 8;
	let r = r.clone().times_pow2(work - bits - HALVINGS);
	let mut sum = Fixed::one(work);
	let mut term = Fixed::one(work);
	for n in 1..=u64::MAX {
		test_int(int)?;
		term = term.mul(&r, work, int)?.div_int(n, int)?;
		if term.is_zero() {
			break;
		}
		sum = sum.add(&term);
	}
	for _ in 0..HALVINGS {
		sum = sum.mul(&sum, work, int)?;
	}
	Ok(sum.over_pow2(work - bits))
}

fn exp_bits<I: Interrupt>(x: &BigRat, bits: u64, int: &I) -> FResult<BigRat> {
	if x.num.is_zero() {
		return Ok(1.into());
	}
	let mut log2 = log2_estimate(x).exp2() * std::f64::consts::LOG2_E;
	if is_negative(x) {
		log2 = -log2;
	}
	let k = exponent(log2)?;
	let extra = bit_width(k.unsigned_abs()) + 2;
	let r = Fixed::from_rat(x, bits + extra, int)?
		.sub(
			&ln_2(bits + extra, int)?
				.mul_int(k.unsigned_abs(), int)?
				.negate_if(k < 0),
		)
		.over_pow2(extra);
	let m = exp_fixed(&r, bits, int)?;
	Ok(scale_pow2(m.into_rat(bits), k))
}

pub(super) fn exp<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	exp_bits(x, WORK_BITS, int)
}

fn atanh_small<I: Interrupt>(z: &BigRat, bits: u64, int: &I) -> FResult<BigRat> {
	let z2 = Fixed::from_rat(&z.clone().mul(z, int)?, bits, int)?;
	let mut sum = Fixed::one(bits);
	let mut power = Fixed::one(bits);
	for k in 1..=u64::MAX {
		test_int(int)?;
		power = power.mul(&z2, bits, int)?;
		let term = power.div_int(2 * k + 1, int)?;
		if term.is_zero() {
			break;
		}
		sum = sum.add(&term);
	}
	times(z, &sum, bits, int)
}

fn ln_bits<I: Interrupt>(x: &BigRat, bits: u64, int: &I) -> FResult<BigRat> {
	let e = exponent(log2_estimate(x))?;
	let m = scale_pow2(abs(x), -e);
	let (sign, num) = if m.num >= m.den {
		(Sign::Positive, m.num.clone().sub(&m.den))
	} else {
		(Sign::Negative, m.den.clone().sub(&m.num))
	};
	let z = BigRat {
		sign,
		num,
		den: m.num.add(&m.den),
	};
	let ln_m = atanh_small(&z, bits, int)?.mul(&2.into(), int)?;
	if e == 0 {
		return Ok(ln_m);
	}
	let extra = bit_width(e.unsigned_abs()) + 2;
	let sum = ln_2(bits + extra, int)?
		.mul_int(e.unsigned_abs(), int)?
		.negate_if(e < 0)
		.add(&Fixed::from_rat(&ln_m, bits + extra, int)?);
	Ok(sum.into_rat(bits + extra))
}

pub(super) fn ln<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	ln_bits(x, WORK_BITS, int)
}

pub(super) fn pow<I: Interrupt>(base: &BigRat, exponent: &BigRat, int: &I) -> FResult<BigRat> {
	let size = log2_estimate(exponent) + log2_estimate(base).abs().max(1.0).log2();
	let extra = self::exponent(size.max(0.0))?.unsigned_abs() + 2;
	let t = exponent
		.clone()
		.mul(&ln_bits(base, WORK_BITS + extra, int)?, int)?;
	exp(&t, int)
}

pub(super) fn sqrt<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	let x = x.clone().simplify(int)?;
	let num = x.num.clone().root_n(&2.into(), int)?;
	let den = x.den.clone().root_n(&2.into(), int)?;
	if num.exact && den.exact {
		return Ok(BigRat {
			sign: Sign::Positive,
			num: num.value,
			den: den.value,
		});
	}
	let size = i64::try_from(x.num.bits()).unwrap() - i64::try_from(x.den.bits()).unwrap();
	let s = i64::try_from(WORK_BITS).unwrap() + 1 - size.div_euclid(2);
	let scaled = if s >= 0 {
		shl(x.num, 2 * s.unsigned_abs()).div(&x.den, int)?
	} else {
		x.num.div(&shl(x.den, 2 * s.unsigned_abs()), int)?
	};
	let root = scaled.root_n(&2.into(), int)?.value;
	Ok(scale_pow2(root.into(), -s))
}

fn sinh_small<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	let bits = WORK_BITS;
	let x2 = Fixed::from_rat(&x.clone().mul(x, int)?, bits, int)?;
	let mut sum = Fixed::one(bits);
	let mut term = Fixed::one(bits);
	for k in 1..=u64::MAX {
		test_int(int)?;
		term = term
			.mul(&x2, bits, int)?
			.div_int((2 * k) * (2 * k + 1), int)?;
		if term.is_zero() {
			break;
		}
		sum = sum.add(&term);
	}
	times(x, &sum, bits, int)
}

pub(super) fn sinh<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	if x.num.is_zero() {
		return Ok(0.into());
	}
	if is_small(x, int)? {
		return sinh_small(x, int);
	}
	let e = exp(x, int)?;
	let inverse = BigRat::from(1).div(&e, int)?;
	e.add(-inverse, int)?.div(&2.into(), int)
}

pub(super) fn cosh<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	if x.num.is_zero() {
		return Ok(1.into());
	}
	let e = exp(x, int)?;
	let inverse = BigRat::from(1).div(&e, int)?;
	e.add(inverse, int)?.div(&2.into(), int)
}

pub(super) fn tanh<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	if x.num.is_zero() {
		return Ok(0.into());
	}
	if is_small(x, int)? {
		return sinh_small(x, int)?.div(&cosh(x, int)?, int);
	}
	#[allow(clippy::cast_precision_loss)]
	let negligible = f64_estimate(x) > (WORK_BITS + 8) as f64;
	let t = if negligible {
		BigRat::from(1)
	} else {
		let e = exp(&abs(x).mul(&2.into(), int)?, int)?;
		e.clone()
			.add(-BigRat::from(1), int)?
			.div(&e.add(1.into(), int)?, int)?
	};
	Ok(if is_negative(x) { -t } else { t })
}

pub(super) fn asinh<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	if x.num.is_zero() {
		return Ok(0.into());
	}
	let root = sqrt(&x.clone().mul(x, int)?.add(1.into(), int)?, int)?;
	if is_small(x, int)? {
		return atanh_small(&x.clone().div(&root, int)?, WORK_BITS, int);
	}
	let t = ln(&abs(x).add(root, int)?, int)?;
	Ok(if is_negative(x) { -t } else { t })
}

pub(super) fn acosh<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	let t = x.clone().add(-BigRat::from(1), int)?.div(&2.into(), int)?;
	if t.num.is_zero() {
		return Ok(0.into());
	}
	asinh(&sqrt(&t, int)?, int)?.mul(&2.into(), int)
}

pub(super) fn atanh<I: Interrupt>(x: &BigRat, int: &I) -> FResult<BigRat> {
	if x.num.is_zero() {
		return Ok(0.into());
	}
	if is_small(x, int)? {
		return atanh_small(x, WORK_BITS, int);
	}
	let one = BigRat::from(1);
	let ratio = one
		.clone()
		.add(x.clone(), int)?
		.div(&one.add(-x.clone(), int)?, int)?;
	ln(&ratio, int)?.div(&2.into(), int)
}

pub(super) fn ln_2_rat<I: Interrupt>(int: &I) -> FResult<BigRat> {
	Ok(ln_2(WORK_BITS, int)?.into_rat(WORK_BITS))
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn ln_2_constant_matches_its_series() {
		let int = &crate::interrupt::Never;
		let bits = CONST_BITS + 64;
		let series = ln_2(bits, int).unwrap().over_pow2(64);
		let constant = ln_2(CONST_BITS, int).unwrap();
		let diff = if series.mag >= constant.mag {
			series.mag.sub(&constant.mag)
		} else {
			constant.mag.sub(&series.mag)
		};
		assert!(diff <= 2.into());
	}
}
