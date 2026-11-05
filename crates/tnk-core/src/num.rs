//! Arbitrary-precision arithmetic behind a thin wrapper (`malachite`, pure Rust).
//!
//! Compact successor counts and built-in natural, integer, and rational operators use [`Nat`],
//! [`Int`], and [`Rat`], keeping backend values out of the DAG API. Floating-point operations use
//! IEEE `f64`.

use malachite::base::num::arithmetic::traits::{
    CheckedSub, DivRem, DivisibleBy, Gcd, Lcm, ModPow, Parity, Pow, UnsignedAbs,
};
use malachite::base::num::basic::traits::{NegativeOne, One, Zero};
use malachite::base::num::conversion::traits::{FromStringBase, RoundingFrom, ToStringBase};
use malachite::base::num::logic::traits::SignificantBits;
use malachite::base::rounding_modes::RoundingMode;
use malachite::{Integer, Natural, Rational};

/// A non-negative arbitrary-precision integer. `Clone`/`Eq`/`Ord`/`Debug` are derived from the
/// backend so `NodeTerm` and [`Term::Iter`](crate::term::Term::Iter) can carry an iteration count as
/// scalar data rather than allocating one unary node per successor. The backend remains private.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default, Hash)]
pub struct Nat(Natural);

impl Nat {
    /// `0`.
    pub fn zero() -> Self {
        Nat(Natural::ZERO)
    }
    /// `1` — the successor increment (`rebuild` folds nested `s_` layers one at a time).
    pub fn one() -> Self {
        Nat(Natural::ONE)
    }
    /// From a machine integer (used by parsed numerals and programmatic engine clients).
    pub(crate) fn from_u64(n: u64) -> Self {
        Nat(Natural::from(n))
    }
    pub(crate) fn is_zero(&self) -> bool {
        self.0 == Natural::ZERO
    }

    /// `self + other` (the S-theory `s^j(s^k(x)) = s^(j+k)(x)` flatten).
    pub fn add(&self, other: &Nat) -> Nat {
        Nat(&self.0 + &other.0)
    }
    /// `self - other`, or `None` when the natural-number result would be negative. Callers may then
    /// fall through to another overload or a user equation.
    pub(crate) fn checked_sub(&self, other: &Nat) -> Option<Nat> {
        (&self.0).checked_sub(&other.0).map(Nat)
    }
    // Signed arithmetic (`*`/`/`/`^`/`-`) lives on `Int` — `NAT` and `INT` both compute in `Int`, since
    // `Nat ⊂ Int` (a negative result with no `minus` hook is the NAT "fall through" case). `Nat` keeps
    // only what the S theory and the magnitude-based ops (gcd/lcm/divides) need.
    pub(crate) fn gcd(&self, other: &Nat) -> Nat {
        Nat((&self.0).gcd(&other.0))
    }
    pub(crate) fn lcm(&self, other: &Nat) -> Nat {
        Nat((&self.0).lcm(&other.0))
    }
    /// Whether `self` divides `other` (`self | other`); by `divisible_by`, `0 | other` iff `other == 0`
    /// (the prelude's `_divides_` takes an `NzNat` divisor, so the zero case is moot).
    pub(crate) fn divides(&self, other: &Nat) -> bool {
        (&other.0).divisible_by(&self.0)
    }
    /// Parse a base-10 numeral (the fresh-variable name predicates); `None` on any non-digit.
    pub(crate) fn from_decimal(s: &str) -> Option<Nat> {
        Natural::from_string_base(10, s).map(Nat)
    }
    /// As a machine `usize` if it fits — the S-theory sort-path index (always small).
    pub(crate) fn to_usize(&self) -> Option<usize> {
        usize::try_from(&self.0).ok()
    }
    /// As a machine `usize`, saturating at `usize::MAX` — a string index or count. A slice never
    /// holds more than `isize::MAX` bytes, so a saturated value lies past the end of every string,
    /// exactly as the original value does.
    pub(crate) fn to_usize_saturating(&self) -> usize {
        usize::try_from(&self.0).unwrap_or(usize::MAX)
    }
    /// As a machine `u64` if it fits — a machine-word argument such as a shift count or exponent;
    /// each caller decides what a wider value means.
    pub(crate) fn to_u64(&self) -> Option<u64> {
        u64::try_from(&self.0).ok()
    }
    /// Whether `self` is odd — the sign of `(-1)^self`.
    pub(crate) fn is_odd(&self) -> bool {
        (&self.0).odd()
    }

    /// `self << amount` / `self >> amount` (`_<<_` / `_>>_`) for a machine `u64` count; `>>` floors
    /// toward zero (shifts away the low bits).
    #[cfg(test)]
    pub(crate) fn shl(&self, amount: u64) -> Nat {
        Nat(&self.0 << amount)
    }
    #[cfg(test)]
    pub(crate) fn shr(&self, amount: u64) -> Nat {
        Nat(&self.0 >> amount)
    }
    /// Efficiently compute `self ^ exp mod modulus` for any base, or `None` when `modulus == 0`
    /// (`modExp` declares its third argument as `NzNat`). The backend's modular power requires a base
    /// already reduced modulo `modulus` and panics otherwise, so the base is reduced first:
    /// `b^e ≡ (b mod m)^e (mod m)`. Modulus 1 yields 0, including for `exp == 0`.
    pub(crate) fn mod_pow(&self, exp: &Nat, modulus: &Nat) -> Option<Nat> {
        if modulus.is_zero() {
            return None;
        }
        let base = &self.0 % &modulus.0;
        Some(Nat(base.mod_pow(&exp.0, &modulus.0)))
    }
    /// Base-10 rendering — for the pretty-printer's decimal numerals / iter counts (a `usize` would
    /// truncate a bignum count). Malachite's `Natural` is `Display`.
    pub fn to_decimal(&self) -> String {
        self.0.to_string()
    }
    /// `self % m` as a machine `usize` (the S sort-path cycle index; `m` is the small cycle length, so
    /// the remainder is `< m` and always fits). Panics if `m == 0` (a cycle length is always `>= 1`).
    pub(crate) fn rem_usize(&self, m: usize) -> usize {
        let r = &self.0 % Natural::from(m as u64);
        usize::try_from(&r).expect("remainder < m fits usize")
    }
}

/// A signed arbitrary-precision integer used by the `INT` built-ins. A numeral is `0`, `s^n(0)`
/// (positive), or `-(s^n(0))` (negative), so an [`Int`] decomposes into a sign and a [`Nat`]
/// [magnitude](Int::magnitude). `quo` and `rem` truncate toward zero, and the remainder takes the
/// dividend's sign; malachite provides this through `DivRem` rather than the floor-based `DivMod`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Int(Integer);

impl Int {
    /// A non-negative `Int` from a `Nat` magnitude (the fold's accumulator seed; `Int::from_nat(&zero)`
    /// is the zero value).
    pub(crate) fn from_nat(n: &Nat) -> Self {
        Int(Integer::from(n.0.clone()))
    }
    pub(crate) fn is_zero(&self) -> bool {
        self.0 == Integer::ZERO
    }
    pub(crate) fn is_negative(&self) -> bool {
        self.0 < Integer::ZERO
    }
    /// `|self|` as a `Nat` — the magnitude a numeral node stores (`s^|self|(0)`, negated if negative).
    pub(crate) fn magnitude(&self) -> Nat {
        Nat((&self.0).unsigned_abs())
    }
    /// `-self`.
    pub(crate) fn neg(&self) -> Int {
        Int(-&self.0)
    }

    pub(crate) fn add(&self, other: &Int) -> Int {
        Int(&self.0 + &other.0)
    }
    pub(crate) fn sub(&self, other: &Int) -> Int {
        Int(&self.0 - &other.0)
    }
    pub(crate) fn mul(&self, other: &Int) -> Int {
        Int(&self.0 * &other.0)
    }
    /// `self << amount` / `self >> amount` (`_<<_` / `_>>_ : Int Nat -> Int`) for a count of any
    /// width. Right shift is arithmetic and rounds toward −∞ (`-8 >> 1 = -4`, `-1 >> k = -1`); left
    /// shift scales exactly (`-5 << 2 = -20`).
    ///
    /// The backend's bit lengths are `u64`, so a count of `2^64` or more exceeds the bit length of
    /// every value: `>>` gives `0`, or `-1` for a negative value. `0 << k = 0` for every count, but
    /// any other value shifted left that far has no representation, and `shl_nat` returns `None`.
    pub(crate) fn shl_nat(&self, amount: &Nat) -> Option<Int> {
        if self.is_zero() {
            return Some(self.clone());
        }
        Some(Int(&self.0 << amount.to_u64()?))
    }
    pub(crate) fn shr_nat(&self, amount: &Nat) -> Int {
        match amount.to_u64() {
            Some(k) => Int(&self.0 >> k),
            None if self.is_negative() => Int(Integer::NEGATIVE_ONE),
            None => Int(Integer::ZERO),
        }
    }

    /// `(self / other, self % other)`, truncated toward zero, with the remainder taking the dividend's
    /// sign. The caller guarantees `other != 0`.
    pub(crate) fn div_rem(&self, other: &Int) -> (Int, Int) {
        let (q, r) = (&self.0).div_rem(&other.0);
        (Int(q), Int(r))
    }
    /// `self ^ exp` for a machine exponent. The backend sizes the result as `bits(|self|) · exp`
    /// without overflow checks; [`pow_nat`](Self::pow_nat) guards that product for `_^_`, and the
    /// remaining callers pass small exponents (a `u32` ACU multiplicity, a float's decimal scale).
    pub(crate) fn pow_u64(&self, exp: u64) -> Int {
        Int((&self.0).pow(exp))
    }
    /// `self ^ exp` (`_^_ : Int Nat -> Int`) for an exponent of any width, or `None` when the power
    /// has no representation. `0`, `1`, and `-1` have exact powers for every exponent (`(-1)^e` by
    /// parity); any other base raised to `2^64` or more has more than `2^64` bits.
    ///
    /// A machine-word exponent also declines when `bits(|self|) · e` overflows `u64`: the backend
    /// computes that product unchecked and would wrap into a wrong value, a panic, or a bogus
    /// allocation. The product overflows only for a power of more than `2^63` bits.
    pub(crate) fn pow_nat(&self, exp: &Nat) -> Option<Int> {
        let bits = (&self.0).significant_bits();
        let Some(e) = exp.to_u64() else {
            // `exp >= 2^64`, so `exp > 0`.
            return match bits {
                0 | 1 if self.is_negative() && !exp.is_odd() => Some(self.neg()), // (-1)^even = 1
                0 | 1 => Some(self.clone()), // 0^e = 0, 1^e = 1, (-1)^odd = -1
                _ => None,
            };
        };
        bits.checked_mul(e)?;
        // The backend also converts `e` to `usize` (lossless on 64-bit hosts).
        Some(self.pow_u64(e))
    }

    /// Render in base `base` with lowercase digits and a leading `-` for negative values.
    /// `base` must be in 2..=36.
    pub(crate) fn to_string_base(&self, base: u8) -> String {
        self.0.to_string_base(base)
    }
    /// Parse a signed base-`base` integer, returning `None` for invalid text.
    pub(crate) fn from_string_base(base: u8, s: &str) -> Option<Int> {
        Integer::from_string_base(base, s).map(Int)
    }

    /// Signed bitwise `_&_`, `_|_`, `_xor_`, and `~_` use two's-complement semantics with infinite
    /// sign extension. Thus `~x = -(x+1)` and negative operands sign-extend; non-negative operands
    /// agree with the corresponding [`Nat`] magnitudes.
    pub(crate) fn bitand(&self, other: &Int) -> Int {
        Int(&self.0 & &other.0)
    }
    pub(crate) fn bitor(&self, other: &Int) -> Int {
        Int(&self.0 | &other.0)
    }
    pub(crate) fn bitxor(&self, other: &Int) -> Int {
        Int(&self.0 ^ &other.0)
    }
    /// `~self = -(self + 1)` (bitwise NOT under two's complement).
    pub(crate) fn bitnot(&self) -> Int {
        Int(!&self.0)
    }
}
/// A canonical exact rational behind the kernel's numeric-backend boundary. SMT leaves use this
/// wrapper so their equality/order/hash semantics are mathematical while `malachite` remains private
/// to this module.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ExactRational(Rational);

impl ExactRational {
    pub(crate) fn parse(text: &str) -> Option<Self> {
        text.parse::<Rational>().ok().map(Self)
    }

    pub(crate) fn to_decimal_ratio(&self) -> String {
        self.0.to_string()
    }
}

/// Return the exact rational value of a finite `f64` as a signed numerator and positive denominator.
/// NaN and infinities return `None`; the result is fully reduced.
pub(crate) fn rational_of_f64(f: f64) -> Option<(Int, Nat)> {
    let r = Rational::try_from(f.abs()).ok()?; // magnitude; the sign is reapplied below
    let (num, den) = r.into_numerator_and_denominator();
    let num = Integer::from(num);
    Some((Int(if f < 0.0 { -num } else { num }), Nat(den)))
}

/// Return the nearest `f64` to `num / den` using round-to-nearest-even, or `None` when `den == 0`:
/// `num / 0` denotes no rational (the backend's constructor panics on a zero denominator).
pub(crate) fn f64_of_rational(num: &Int, den: &Nat) -> Option<f64> {
    if den.is_zero() {
        return None;
    }
    let r = Rational::from_integers(num.0.clone(), Integer::from(den.0.clone()));
    Some(f64::rounding_from(&r, RoundingMode::Nearest).0)
}

/// Parse the supported float surface: `[sign] ("Infinity" | digits with a `.` and/or an
/// `e[sign]digits` exponent)`. Bare integers, NaN spellings, abbreviated infinity spellings,
/// dangling exponents, and a lone decimal point remain unreduced; `f64::from_str` alone is too broad.
pub(crate) fn parse_double(s: &str) -> Option<f64> {
    if !looks_like_float(s) {
        return None;
    }
    s.parse::<f64>().ok()
}

fn looks_like_float(s: &str) -> bool {
    let t = s.strip_prefix(['+', '-']).unwrap_or(s);
    if t == "Infinity" {
        return true;
    }
    let (mantissa, exponent) = match t.split_once(['e', 'E']) {
        Some((m, e)) => (m, Some(e)),
        None => (t, None),
    };
    let (int_part, frac_part) = match mantissa.split_once('.') {
        Some((i, f)) => (i, Some(f)),
        None => (mantissa, None),
    };
    let all_digits = |p: &str| p.bytes().all(|b| b.is_ascii_digit());
    if !all_digits(int_part) || !frac_part.is_none_or(all_digits) {
        return false;
    }
    // At least one digit somewhere in the mantissa…
    if int_part.is_empty() && frac_part.is_none_or(str::is_empty) {
        return false;
    }
    // …and a `.` or an exponent to make it a float rather than an integer numeral.
    match exponent {
        Some(e) => {
            let e = e.strip_prefix(['+', '-']).unwrap_or(e);
            !e.is_empty() && all_digits(e)
        }
        None => frac_part.is_some(),
    }
}

/// Render an `f64` with 17 significant digits, a mantissa normalized to `[1, 10)` with at least one
/// fractional digit and no trailing zeros, and a signed exponent only when nonzero. Infinity and
/// NaN use the language spellings. The pretty-printer and `string(Float)` share this function.
pub fn double_to_string(f: f64) -> String {
    if f.is_nan() {
        return "NaN".to_string();
    }
    if f.is_infinite() {
        return if f < 0.0 { "-Infinity" } else { "Infinity" }.to_string();
    }
    if f == 0.0 {
        return "0.0".to_string(); // also catches -0.0
    }
    // Emit 17 significant digits with a normalized scientific mantissa.
    let sci = format!("{:.*e}", 16, f.abs());
    let (mantissa, exp) = sci
        .split_once('e')
        .expect("scientific notation has an exponent");
    let exp: i64 = exp.parse().expect("exponent is an integer");
    let (int_part, frac) = mantissa
        .split_once('.')
        .expect("a `.16e` mantissa has a decimal point");
    // Strip trailing zeros while retaining at least one fractional digit.
    let frac = frac.trim_end_matches('0');
    let frac = if frac.is_empty() { "0" } else { frac };
    let body = match exp {
        0 => format!("{int_part}.{frac}"),
        e if e > 0 => format!("{int_part}.{frac}e+{e}"),
        e => format!("{int_part}.{frac}e{e}"), // a negative exponent already carries its `-`
    };
    if f < 0.0 { format!("-{body}") } else { body }
}

#[cfg(test)]
mod tests {
    use super::Nat;

    fn n(x: u64) -> Nat {
        Nat::from_u64(x)
    }

    #[test]
    fn constants_predicates_and_order() {
        assert!(Nat::zero().is_zero());
        assert!(!Nat::one().is_zero());
        assert_eq!(Nat::zero(), n(0));
        assert_eq!(Nat::one(), n(1));
        assert!(n(2) < n(3) && n(3) > n(2) && n(3) == n(3));
        assert_eq!(std::cmp::min(n(2), n(5)), n(2), "min/max via derived Ord");
    }

    #[test]
    fn add_and_monus() {
        assert_eq!(n(2).add(&n(3)), n(5));
        assert_eq!(n(5).checked_sub(&n(3)), Some(n(2)));
        assert_eq!(n(3).checked_sub(&n(5)), None, "Natural monus is partial");
        assert_eq!(n(0).checked_sub(&n(0)), Some(n(0)));
    }

    #[test]
    fn to_usize_and_bignum_width() {
        assert_eq!(n(100).to_usize(), Some(100));
        // A count past machine width still round-trips through add (genuinely arbitrary-precision).
        let big = n(u64::MAX).add(&n(1));
        assert_eq!(big.to_usize(), None, "u64::MAX + 1 does not fit usize");
        assert_eq!(big.checked_sub(&n(1)), Some(n(u64::MAX)));
    }

    /// A string index or count past machine width saturates: it stays past the end of every string.
    #[test]
    fn to_usize_saturating_past_machine_width() {
        assert_eq!(n(0).to_usize_saturating(), 0);
        assert_eq!(n(100).to_usize_saturating(), 100);
        let two_64 = n(u64::MAX).add(&n(1));
        assert_eq!(two_64.to_usize_saturating(), usize::MAX);
        assert_eq!(two_64.add(&two_64).to_usize_saturating(), usize::MAX);
    }

    #[test]
    fn number_theory() {
        // `Nat` keeps only the magnitude-based ops; signed `*`/`/`/`^`/`-` are tested on `Int` below.
        assert_eq!(n(12).gcd(&n(18)), n(6));
        assert_eq!(n(4).lcm(&n(6)), n(12));
    }

    #[test]
    fn divides() {
        assert!(n(3).divides(&n(12)) && !n(5).divides(&n(12)));
        assert!(n(1).divides(&n(7)) && !n(7).divides(&n(1)));
    }

    #[test]
    fn bitwise_shifts_modpow() {
        // Shifts (`_<<_`/`_>>_`); `>>` floors, a huge shift clears all bits.
        assert_eq!(n(5).shl(3), n(40)); // 5 * 8
        assert_eq!(n(40).shr(3), n(5)); // 40 / 8
        assert_eq!(n(5).shr(100), n(0));
        assert_eq!(
            n(1).shl(64),
            n(u64::MAX).add(&n(1)),
            "1 << 64 = 2^64 (bignum)"
        );
        // Modular exponentiation (`modExp`).
        assert_eq!(n(2).mod_pow(&n(10), &n(1000)), Some(n(24))); // 1024 mod 1000
        assert_eq!(n(7).mod_pow(&n(0), &n(13)), Some(n(1))); // x^0 = 1
        assert_eq!(n(3).mod_pow(&n(100), &n(7)), Some(n(4))); // 3^100 ≡ 4 (mod 7)
    }

    /// `mod_pow` accepts any base: one at or above the modulus is reduced before the backend call
    /// (which requires `base < modulus`). Modulus 1 gives 0; modulus 0 has no residue ring.
    #[test]
    fn mod_pow_reduces_any_base() {
        assert_eq!(n(9).mod_pow(&n(1), &n(4)), Some(n(1)), "9 mod 4");
        assert_eq!(n(6).mod_pow(&n(2), &n(6)), Some(n(0)), "base == modulus");
        assert_eq!(
            n(23).mod_pow(&n(5), &n(7)),
            Some(n(4)),
            "23 ≡ 2, 2^5 = 32 ≡ 4"
        );
        assert_eq!(
            n(3).mod_pow(&n(4), &n(100)),
            Some(n(81)),
            "a reduced base is unchanged"
        );
        // Multi-limb bases, against a small and a multi-limb modulus.
        let two_64 = n(u64::MAX).add(&n(1));
        let base = two_64.add(&n(5)); // 2^64 + 5 ≡ 621 (mod 1000)
        assert_eq!(
            base.mod_pow(&n(2), &n(1000)),
            Some(n(641)),
            "621^2 mod 1000"
        );
        let modulus = two_64.add(&n(13));
        let two_65 = two_64.add(&two_64);
        assert_eq!(
            two_65.mod_pow(&n(1), &modulus),
            Some(n(u64::MAX - 12)),
            "2^65 mod (2^64 + 13) = 2^64 - 13"
        );
        // Modulus 1: every residue is 0, including x^0.
        assert_eq!(n(9).mod_pow(&n(3), &n(1)), Some(n(0)));
        assert_eq!(n(4).mod_pow(&n(0), &n(1)), Some(n(0)));
        // A zero modulus is outside `NzNat`.
        assert_eq!(n(4).mod_pow(&n(2), &n(0)), None);
    }

    /// `f64_of_rational` rounds to the nearest double and has no value for a zero denominator.
    #[test]
    fn f64_of_rational_needs_a_nonzero_denominator() {
        use super::{Int, f64_of_rational};
        let i = |x: u64| Int::from_nat(&n(x));
        assert_eq!(f64_of_rational(&i(1), &n(4)), Some(0.25));
        assert_eq!(f64_of_rational(&i(3).neg(), &n(2)), Some(-1.5));
        assert_eq!(f64_of_rational(&i(3), &n(0)), None);
        assert_eq!(f64_of_rational(&i(0), &n(0)), None);
    }

    #[test]
    fn signed_int() {
        use super::Int;
        let i = |x: u64| Int::from_nat(&n(x));
        let neg = |x: u64| i(x).sub(&i(2 * x)); // -x
        assert!(i(0).is_zero() && !i(3).is_negative());
        assert!(neg(3).is_negative(), "-3 is negative");
        assert_eq!(neg(3).magnitude(), n(3), "|-3| = 3");
        assert_eq!(i(2).add(&neg(5)), neg(3), "2 + (-5) = -3");
        assert_eq!(i(2).sub(&i(5)), neg(3), "2 - 5 = -3");
        assert_eq!(neg(2).mul(&neg(3)), i(6), "(-2)(-3) = 6");
        // quo/rem truncate toward zero; the remainder takes the dividend's sign.
        let (q, r) = i(7).div_rem(&neg(2));
        assert_eq!((q, r), (neg(3), i(1)), "7 quo -2 = -3, 7 rem -2 = 1");
        let (q, r) = neg(7).div_rem(&i(2));
        assert_eq!((q, r), (neg(3), neg(1)), "-7 quo 2 = -3, -7 rem 2 = -1");
        assert!(neg(2) < i(3) && i(3) > neg(2), "-2 < 3");
    }

    /// `_^_`, `_<<_`, and `_>>_` take natural counts of any width. Bases `0` and `±1`, `0 << k`,
    /// and `x >> k` are exact beyond `u64`; a power of any other base, or a nonzero value shifted
    /// left, by `2^64` or more has no representation.
    #[test]
    fn pow_and_shifts_take_counts_past_u64() {
        use super::Int;
        let i = |x: u64| Int::from_nat(&n(x));
        let max = n(u64::MAX); // odd, and still a machine word
        let two_64 = max.add(&n(1));
        let two_65 = two_64.add(&two_64);
        let two_65_1 = two_65.add(&n(1)); // odd
        for e in [&max, &two_64, &two_65, &two_65_1] {
            assert_eq!(i(0).pow_nat(e), Some(i(0)), "0^{e:?}");
            assert_eq!(i(1).pow_nat(e), Some(i(1)), "1^{e:?}");
            let parity = if e.is_odd() { i(1).neg() } else { i(1) };
            assert_eq!(i(1).neg().pow_nat(e), Some(parity), "(-1)^{e:?}");
            assert_eq!(i(0).shl_nat(e), Some(i(0)), "0 << {e:?}");
            assert_eq!(i(5).shr_nat(e), i(0), "5 >> {e:?}");
            assert_eq!(i(5).neg().shr_nat(e), i(1).neg(), "-5 >> {e:?} floors");
        }
        let big = Int::from_nat(&two_65_1);
        for e in [&two_64, &two_65, &two_65_1] {
            assert_eq!(i(2).pow_nat(e), None, "2^{e:?}");
            assert_eq!(i(2).neg().pow_nat(e), None, "(-2)^{e:?}");
            assert_eq!(i(1).shl_nat(e), None, "1 << {e:?}");
            assert_eq!(i(3).neg().shl_nat(e), None, "-3 << {e:?}");
            assert_eq!(big.shr_nat(e), i(0), "(2^65 + 1) >> {e:?}");
            assert_eq!(big.neg().shr_nat(e), i(1).neg(), "-(2^65 + 1) >> {e:?}");
        }
        // Machine-word counts compute as before.
        assert_eq!(i(0).pow_nat(&n(0)), Some(i(1)), "0^0 = 1");
        assert_eq!(i(2).pow_nat(&n(10)), Some(i(1024)));
        assert_eq!(i(3).neg().pow_nat(&n(3)), Some(i(27).neg()));
        assert_eq!(i(5).neg().shl_nat(&n(2)), Some(i(20).neg()));
        assert_eq!(i(1).shl_nat(&n(64)), Some(Int::from_nat(&two_64)));
        assert_eq!(i(8).neg().shr_nat(&n(1)), i(4).neg());
        assert_eq!(i(1).neg().shr_nat(&n(100)), i(1).neg());
    }

    /// The backend sizes `x^e` as `bits(|x|) · e` without overflow checks, so a machine-word
    /// exponent whose product overflows `u64` (a power of more than `2^63` bits) declines instead of
    /// wrapping into a wrong value, a panic, or an impossible allocation.
    #[test]
    fn pow_nat_declines_when_the_result_size_overflows() {
        use super::Int;
        let i = |x: u64| Int::from_nat(&n(x));
        let two_63 = n(1 << 63);
        assert_eq!(i(2).pow_nat(&two_63), None, "2 · 2^63 wraps to 0");
        assert_eq!(
            i(2).neg().pow_nat(&two_63.add(&n(1))),
            None,
            "(-2)^(2^63 + 1)"
        );
        assert_eq!(i(3).pow_nat(&n(u64::MAX)), None, "2 · (2^64 - 1) wraps");
        assert_eq!(
            i(7).pow_nat(&n(6_148_914_691_236_517_206)),
            None,
            "3 · e wraps to 2"
        );
        let two_64 = Int::from_nat(&n(u64::MAX).add(&n(1))); // 65 bits
        assert_eq!(two_64.pow_nat(&n(1 << 58)), None, "65 · 2^58 > 2^64");
        // Bases of at most one bit never overflow the product.
        assert_eq!(i(1).neg().pow_nat(&n(u64::MAX)), Some(i(1).neg()));
        assert_eq!(i(0).pow_nat(&n(u64::MAX)), Some(i(0)));
    }

    #[test]
    fn signed_bitwise() {
        use super::Int;
        let i = |x: u64| Int::from_nat(&n(x));
        let neg = |x: u64| i(x).sub(&i(2 * x)); // -x
        // Non-negative operands agree with ordinary unsigned bit ops (NAT rides this).
        assert_eq!(i(12).bitand(&i(10)), i(8)); // 1100 & 1010 = 1000
        assert_eq!(i(12).bitor(&i(10)), i(14)); // 1100 | 1010 = 1110
        assert_eq!(i(5).bitxor(&i(3)), i(6)); // 101 ^ 011 = 110
        assert_eq!(i(5).bitxor(&i(5)), i(0), "xor is self-inverse");
        // Two's-complement complement: ~x = -(x+1).
        assert_eq!(i(0).bitnot(), neg(1), "~0 = -1");
        assert_eq!(i(3).bitnot(), neg(4), "~3 = -4");
        assert_eq!(neg(1).bitnot(), i(0), "~(-1) = 0");
        // Signed operands sign-extend: -1 is all-ones, so (-1) & x = x, (-1) | x = -1.
        assert_eq!(neg(1).bitand(&i(12)), i(12), "(-1) & 12 = 12");
        assert_eq!(neg(1).bitor(&i(12)), neg(1), "(-1) | 12 = -1");
    }
}
