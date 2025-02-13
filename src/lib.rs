//! # Overview
//! The `bits` crate features a `BitArray` struct that represents a sequence of bits. It supports
//! the `&`, `|` and `^` binary operators and the `!` unary operator. Because copies could get
//! expensive, these operators are intended to be used by reference.
//!
//! If the lengths of the arguments to a binary operator differ:
//! * The `&` operator will **panic**.
//! * The '|' and '^' operators will produce a result with the same length as the longer argument, with `false` as the implicit value of the missing bits of the smaller argument.
//!
//! ```
//! use bits::*;
//!
//! let b1: BitArray = "1101".parse().unwrap();
//! let b2: BitArray = "0110".parse().unwrap();
//! 
//! assert_eq!(&b1 & &b2, "0100".parse().unwrap());
//! assert_eq!(&b1 | &b2, "1111".parse().unwrap());
//! assert_eq!(&b1 ^ &b2, "1011".parse().unwrap());
//! assert_eq!(!&b1, "0010".parse().unwrap());
//! assert_eq!(!&!&b2, b2);
//! 
//! let b3: BitArray = "10".parse().unwrap();
//! assert_eq!(&b1 | &b3, BitArray::ones(4));
//! assert_eq!(&b2 | &b3, b2);
//! assert_eq!(&b1 ^ &b3, BitArray::ones(4));
//! assert_eq!(&b2 ^ &b3, "0100".parse().unwrap());
//! ```
//!
//! `BitArray` objects can be built incrementally using the `add()` method. The first digit
//! added is the lowest-order bit. Each successive `add()` adds its bit as the next-highest order.
//!
//! ```
//! use bits::*;
//!
//! let mut b = BitArray::new();
//! b.add(true);
//! b.add(false);
//! b.add(true);
//! b.add(true);
//!
//! assert_eq!(b, "1101".parse().unwrap());
//! assert_eq!(num::BigUint::from(&b), num::BigUint::from(13 as u32));
//! ```
//!
//! `BitArray` objects can also be expanded and modified using the `set()` method.
//! Any gaps will be filled in with zeros.
//!
//! ```
//! use bits::*;
//!
//! let mut b = BitArray::new();
//! b.set(0, true);
//! b.set(2, true);
//! b.set(3, true);
//!
//! assert_eq!(b, "1101".parse().unwrap());
//! assert_eq!(num::BigUint::from(&b), num::BigUint::from(13 as u32));
//!
//! b.set(0, false);
//! b.set(3, false);
//! assert_eq!(b, "0100".parse().unwrap());
//! 
//! b.set(500, true);
//! assert!(b.is_set(500));
//! assert_eq!(b.len(), 501);
//! assert_eq!(b.count_bits_on(), 2);
//! ```
//!
//! `BitArray` objects can also be created by specifying a number of zeros or ones for
//! initialization.
//!
//! ```
//! use bits::*;
//!
//! let z = BitArray::zeros(10);
//! assert_eq!(z.len(), 10);
//! assert_eq!(z, "0000000000".parse().unwrap());
//!
//! let n = BitArray::ones(10);
//! assert_eq!(n.len(), 10);
//! assert_eq!(n, "1111111111".parse().unwrap());
//! ```
//!
//! Some miscellaneous utilities include the ability to count bits, compute distances, and create
//! combinations.
//!
//! ```
//! use bits::*;
//!
//! let b1: BitArray = "1101".parse().unwrap();
//! let b2: BitArray = "0110".parse().unwrap();
//!
//! assert_eq!(b1.count_bits_on(), 3);
//! assert_eq!(b2.count_bits_on(), 2);
//! assert_eq!(distance(&b1, &b2), 3);
//!
//! let c = BitArray::all_combinations(2);
//! let cv: Vec<BitArray> = ["00", "10", "01", "11"].iter().map(|s| s.parse().unwrap()).collect();
//! assert_eq!(c, cv);
//! ```

use num::{BigUint, One, Zero};
use smallvec::SmallVec;
use std::cmp::max;
use std::fmt::{Display, Formatter};
use std::io;
use std::ops::{BitAnd, BitOr, BitXor, Not};
use std::str::FromStr;

#[derive(Hash, Eq, PartialEq, Ord, PartialOrd, Clone, Debug, Default)]
pub struct BitArray {
    bits: SmallVec<[u64; 4]>,
    size: u64,
}

impl BitArray {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn zeros(num_zeros: u64) -> Self {
        let size = num_zeros;
        let mut num_words = num_zeros / 64;
        if num_zeros % 64 > 0 {
            num_words += 1;
        }
        println!("num_words:{}", num_words);
        let mut bits = SmallVec::new();
        for _ in 0..num_words {
            bits.push(0);
        }
        BitArray { bits, size }
    }

    pub fn ones(num_ones: u64) -> Self {
        !&BitArray::zeros(num_ones)
    }

    /// Returns the underlying `u64` words in which the bits are stored.
    /// Useful for serializations outside the Rust ecosystem.
    pub fn words(&self) -> Vec<u64> {
        self.bits.iter().copied().collect()
    }

    pub fn from(bits: &[bool]) -> Self {
        // I tried implementing From<&[bool]> but it demanded a slice length in the trait bound.
        bits.iter().collect()
    }

    pub fn iter(&self) -> BitArrayIterator {
        BitArrayIterator::iter_for(&self)
    }

    pub fn all_combinations(size: usize) -> Vec<Self> {
        if size == 0 {
            vec![BitArray::new()]
        } else {
            let mut result = Vec::new();
            for mut candidate in BitArray::all_combinations(size - 1) {
                let mut candidate1 = candidate.clone();
                candidate1.add(false);
                result.push(candidate1);
                candidate.add(true);
                result.push(candidate);
            }
            result
        }
    }

    fn make_mask(index: u64) -> u64 {
        1 << BitArray::find_offset(index)
    }

    fn find_offset(index: u64) -> u64 {
        index % (BitArray::bits_per_word() as u64)
    }

    fn find_word(index: u64) -> usize {
        (index as usize / BitArray::bits_per_word()) as usize
    }

    pub fn bits_per_word() -> usize {
        std::mem::size_of::<u64>() * 8
    }

    pub fn len(&self) -> u64 {
        self.size
    }

    pub fn add(&mut self, value: bool) {
        self.set(self.size, value);
    }

    pub fn set(&mut self, index: u64, value: bool) {
        while self.bits.len() < 1 + BitArray::find_word(index) {
            self.bits.push(0);
        }
        if self.size < 1 + index {
            self.size = 1 + index;
        }
        let mask = BitArray::make_mask(index);
        if value {
            self.bits[BitArray::find_word(index)] |= mask;
        } else {
            self.bits[BitArray::find_word(index)] &= !mask;
        }
    }

    pub fn is_set(&self, index: u64) -> bool {
        self.bits[BitArray::find_word(index)] & BitArray::make_mask(index) > 0
    }

    pub fn count_bits_on(&self) -> u64 {
        self.bits.iter().map(|word| word.count_ones() as u64).sum()
    }
}

pub fn distance(b1: &BitArray, b2: &BitArray) -> u64 {
    (b1 ^ b2).count_bits_on()
}

impl Display for BitArray {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        for value in self.iter().rev() {
            s.push(if value { '1' } else { '0' });
        }
        write!(f, "{}", s)
    }
}

impl FromIterator<bool> for BitArray {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut result = BitArray::new();
        for value in iter {
            result.add(value);
        }
        result
    }
}

impl<'a> FromIterator<&'a bool> for BitArray {
    fn from_iter<T: IntoIterator<Item = &'a bool>>(iter: T) -> Self {
        let mut result = BitArray::new();
        for value in iter {
            result.add(*value);
        }
        result
    }
}

fn create_from(one: &BitArray, two: &BitArray, identity: bool, op: fn(u64, u64) -> u64) -> BitArray {
    // This works as it stands for "or" and "xor". It would be tricky to make work for "and" but not impossible.
    assert!(!identity || one.len() == two.len());
    let mut result = BitArray::new();
    result.size = max(one.len(), two.len());
    let result_bits_len = max(one.bits.len(), two.bits.len());
    for i in 0..result_bits_len {
        if i >= one.bits.len() {
            result.bits.push(two.bits[i]);
        } else if i >= two.bits.len() {
            result.bits.push(one.bits[i]);
        } else {
            result.bits.push(op(one.bits[i], two.bits[i]));
        }
    }
    result
}

impl BitXor for &BitArray {
    type Output = BitArray;

    fn bitxor(self, rhs: Self) -> Self::Output {
        create_from(self, rhs, false, |a, b| a ^ b)
    }
}

impl BitAnd for &BitArray {
    type Output = BitArray;

    fn bitand(self, rhs: Self) -> Self::Output {
        create_from(self, rhs, true, |a, b| a & b)
    }
}

impl BitOr for &BitArray {
    type Output = BitArray;

    fn bitor(self, rhs: Self) -> Self::Output {
        create_from(self, rhs, false, |a, b| a | b)
    }
}

impl Not for &BitArray {
    type Output = BitArray;

    fn not(self) -> Self::Output {
        self.iter().map(|v| !v).collect()
    }
}

pub struct BitArrayIterator<'a> {
    forward_index: u64,
    back_index: u64,
    src: &'a BitArray,
}

impl<'a> BitArrayIterator<'a> {
    pub fn iter_for(src: &'a BitArray) -> Self {
        BitArrayIterator {
            forward_index: 0,
            back_index: src.len(),
            src,
        }
    }

    fn valid(&self) -> bool {
        self.forward_index < self.back_index
    }
}

impl<'a> Iterator for BitArrayIterator<'a> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.valid() {
            let result = Some(self.src.is_set(self.forward_index));
            self.forward_index += 1;
            result
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = (self.back_index - self.forward_index) as usize;
        (size, Some(size))
    }
}

impl<'a> DoubleEndedIterator for BitArrayIterator<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.valid() {
            self.back_index -= 1;
            let result = Some(self.src.is_set(self.back_index));
            result
        } else {
            None
        }
    }
}

impl<'a> ExactSizeIterator for BitArrayIterator<'a> {}

impl FromStr for BitArray {
    type Err = io::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = BitArray::new();
        for ch in s.chars().rev() {
            result.add(match ch {
                '0' => false,
                '1' => true,
                other => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("Illegal digit parsing BitArray: {}", other).as_str(),
                    ))
                }
            })
        }
        Ok(result)
    }
}

impl From<&BitArray> for BigUint {
    fn from(value: &BitArray) -> Self {
        let mut converted: BigUint = Zero::zero();
        for bit in value.iter().rev() {
            converted *= BigUint::from(2 as usize);
            if bit {
                converted += BigUint::one();
            }
        }
        converted
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bits() {
        let mut b = BitArray::new();
        assert_eq!(0, b.len());
        b.add(false);
        assert_eq!(1, b.len());
        assert!(!b.is_set(0));
        assert_eq!(0, b.count_bits_on());

        b.add(true);
        assert_eq!(2, b.len());
        assert!(b.is_set(1));
        assert_eq!(1, b.count_bits_on());

        for _ in 0..BitArray::bits_per_word() {
            b.add(true);
        }
        assert_eq!(BitArray::bits_per_word() + 2, b.len() as usize);
        for i in 1..b.len() {
            assert!(b.is_set(i));
        }
        assert_eq!(b.len() as u64 - 1, b.count_bits_on());

        let mut b2 = BitArray::new();
        for i in 0..b.len() {
            b2.add(i % 2 == 0);
        }

        let b3 = &b ^ &b2;
        assert_eq!((b.len() as u64 / 2) + 1, b3.count_bits_on());
        assert_eq!(b3.count_bits_on(), distance(&b, &b2));

        assert_ne!(b, b2);
        assert_ne!(b2, b3);
        assert_ne!(b, b3);

        assert_eq!(b, b.clone());
        assert_eq!(b2, b2.clone());
        assert_eq!(b3, b3.clone());
    }

    #[test]
    fn test_expand_set() {
        let mut b = BitArray::new();
        b.set(0, true);
        b.set(2, true);
        b.set(3, true);

        assert_eq!(b, "1101".parse().unwrap());
        assert_eq!(num::BigUint::from(&b), num::BigUint::from(13 as u32));

        b.set(0, false);
        b.set(3, false);
        assert_eq!(b, "0100".parse().unwrap());
    }

    #[test]
    fn test_from() {
        let mut b = BitArray::from(&[true, true, false, false, true]);
        b.set(2, true);
        assert_eq!(b, BitArray::from(&[true, true, true, false, true]));
    }

    #[test]
    fn test_all_combinations() {
        assert_eq!(
            BitArray::all_combinations(1),
            vec![BitArray::from(&[false]), BitArray::from(&[true])]
        );
        assert_eq!(
            BitArray::all_combinations(2),
            vec![
                BitArray::from(&[false, false]),
                BitArray::from(&[false, true]),
                BitArray::from(&[true, false]),
                BitArray::from(&[true, true])
            ]
        );
    }

    #[test]
    fn test_parse() {
        // Note:
        //
        // The low-order bit in a string is the rightmost bit, while the
        // low-order bit in the source array is the leftmost element.
        for (b, s) in [
            (
                BitArray::from(&[true, false, false, true, true, false, true]),
                "1011001",
            ),
            (
                BitArray::from(&[false, true, true, false, true, true, true]),
                "1110110",
            ),
        ] {
            assert_eq!(b, s.parse::<BitArray>().unwrap());
        }
    }

    #[test]
    fn test_convert() {
        for (s, v) in [
            ("1111", 15),
            ("0000", 0),
            ("1110", 14),
            ("1010", 10),
            ("0111", 7),
            ("0101", 5),
        ] {
            let b = s.parse::<BitArray>().unwrap();
            assert_eq!(num::BigUint::from(&b), num::BigUint::from(v as u32));
        }
    }

    #[test]
    fn test_iter() {
        for bool_vals in [
            [true, true, false, false, true],
            [false, true, false, false, false],
        ] {
            let b = BitArray::from(&bool_vals);
            for (i, val) in b.iter().enumerate() {
                assert_eq!(val, bool_vals[i]);
            }
            for (i, val) in b.iter().rev().enumerate() {
                let target_i = bool_vals.len() - (i + 1);
                assert_eq!(val, bool_vals[target_i]);
            }
            let bc: BitArray = bool_vals.iter().collect();
            assert_eq!(b, bc);
        }
    }

    #[test]
    fn test_negation() {
        let ones: BitArray = "11111".parse().unwrap();
        let zeros: BitArray = "00000".parse().unwrap();
        for (b_s, inv_b_s) in [("10110", "01001"), ("11111", "00000")] {
            let b: BitArray = b_s.parse().unwrap();
            let inv_b: BitArray = inv_b_s.parse().unwrap();
            assert_eq!(!&b, inv_b);
            assert_eq!(&b & &inv_b, zeros);
            assert_eq!(&b | &inv_b, ones);
        }
    }

    #[test]
    fn test_display() {
        for s in ["1010", "1111", "0101", "0000"] {
            let b: BitArray = s.parse().unwrap();
            assert_eq!(s, format!("{}", b).as_str());
        }
    }

    #[test]
    fn test_not() {
        let b: BitArray = "1011".parse().unwrap();
        let nb = !&b;
        let nnb = !&nb;
        assert_eq!(b, nnb);
        assert_ne!(b, nb);
    }

    #[test]
    fn test_zip() {
        let b1: BitArray = "1001".parse().unwrap();
        let b2: BitArray = "0010".parse().unwrap();
        let result: BitArray = b1
            .iter()
            .zip(b2.iter())
            .rev()
            .map(|(bit1, bit2)| bit1 || bit2)
            .collect();
        assert_eq!(result, "1101".parse().unwrap());
    }

    #[test]
    fn test_zeros_ones() {
        let z = BitArray::zeros(80);
        let n = BitArray::ones(80);

        assert_eq!(z.len(), 80);
        assert_eq!(
            z,
            "00000000000000000000000000000000000000000000000000000000000000000000000000000000"
                .parse()
                .unwrap()
        );
        assert_eq!(n.len(), 80);
        assert_eq!(
            n,
            "11111111111111111111111111111111111111111111111111111111111111111111111111111111"
                .parse()
                .unwrap()
        );
    }
}
