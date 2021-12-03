use std::fmt::{Display, Formatter};
use std::ops::{BitXor, Not};
use std::str::FromStr;
use smallvec::SmallVec;
use std::io;

#[derive(Hash, Eq, PartialEq, Ord, PartialOrd, Clone, Debug, Default)]
pub struct BitArray {
    bits: SmallVec<[u64;4]>,
    size: u64,
}

impl BitArray {
    pub fn new() -> Self { Default::default() }

    fn from(bits: &[bool]) -> Self {
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
        1 << BitArray::make_offset(index)
    }

    fn make_offset(index: u64) -> u64 {
        index % (BitArray::word_size() as u64)
    }

    fn make_word(index: u64) -> usize {
        (index as usize / BitArray::word_size()) as usize
    }

    pub fn word_size() -> usize {
        std::mem::size_of::<u64>()
    }

    pub fn len(&self) -> u64 {self.size}

    pub fn add(&mut self, value: bool) {
        if BitArray::make_offset(self.size) == 0 {
            self.bits.push(0);
        }
        self.set(self.size, value);
        self.size += 1;
    }

    pub fn set(&mut self, index: u64, value: bool) {
        let mask = BitArray::make_mask(index);
        if value {
            self.bits[BitArray::make_word(index)] |= mask;
        } else {
            self.bits[BitArray::make_word(index)] &= !mask;
        }
    }

    pub fn is_set(&self, index: u64) -> bool {
        self.bits[BitArray::make_word(index)] & BitArray::make_mask(index) > 0
    }

    pub fn count_bits_on(&self) -> u32 {
        self.bits.iter().map(|word| word.count_ones() as u32).sum()
    }
}

pub fn distance(b1: &BitArray, b2: &BitArray) -> u32 {
    (b1 ^ b2).count_bits_on()
}

impl Display for BitArray {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        for value in self.iter().rev() {
            s.push(if value {'1'} else {'0'});
        }
        write!(f, "{}", s)
    }
}

impl FromIterator<bool> for BitArray {
    fn from_iter<T: IntoIterator<Item=bool>>(iter: T) -> Self {
        let mut result = BitArray::new();
        for value in iter {
            result.add(value);
        }
        result
    }
}

impl <'a> FromIterator<&'a bool> for BitArray {
    fn from_iter<T: IntoIterator<Item=&'a bool>>(iter: T) -> Self {
        let mut result = BitArray::new();
        for value in iter {
            result.add(*value);
        }
        result
    }
}

impl BitXor for &BitArray {
    type Output = BitArray;

    fn bitxor(self, rhs: Self) -> Self::Output {
        assert_eq!(self.len(), rhs.len());
        let mut result = BitArray::new();
        for i in 0..self.bits.len() {
            result.bits.push(self.bits[i] ^ rhs.bits[i]);
        }
        result
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
    src: &'a BitArray
}

impl <'a> BitArrayIterator<'a> {
    pub fn iter_for(src: &'a BitArray) -> Self {
        BitArrayIterator { forward_index: 0, back_index: src.len(), src}
    }

    fn valid(&self) -> bool {
        self.forward_index < self.back_index
    }
}

impl <'a> Iterator for BitArrayIterator<'a> {
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

impl <'a> DoubleEndedIterator for BitArrayIterator<'a> {
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

impl <'a> ExactSizeIterator for BitArrayIterator<'a> {
    
}

impl FromStr for BitArray {
    type Err = io::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = BitArray::new();
        for ch in s.chars().rev() {
            result.add(match ch {
                '0' => false,
                '1' => true,
                other => return Err(io::Error::new(io::ErrorKind::InvalidData, format!("Illegal digit parsing BitArray: {}", other).as_str()))
            })
        }
        Ok(result)
    }
}

impl TryFrom<&BitArray> for u64 {
    type Error = io::Error;

    fn try_from(value: &BitArray) -> Result<Self, Self::Error> {
        if value.len() <= 64 {
            let mut converted = 0;
            for bit in value.iter().rev() {
                converted *= 2;
                if bit {
                    converted += 1;
                }
            }
            Ok(converted)
        } else {
            Err(io::Error::new(io::ErrorKind::InvalidData, format!("BitArray has {} elements; too large to fit into u64", value.len()).as_str()))
        }
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

        for _ in 0..BitArray::word_size() {
            b.add(true);
        }
        assert_eq!(BitArray::word_size() + 2, b.len() as usize);
        for i in 1..b.len() {
            assert!(b.is_set(i));
        }
        assert_eq!(b.len() as u32 - 1, b.count_bits_on());

        let mut b2 = BitArray::new();
        for i in 0..b.len() {
            b2.add(i % 2 == 0);
        }

        let b3 = &b ^ &b2;
        assert_eq!((b.len() as u32 / 2) + 1, b3.count_bits_on());
        assert_eq!(b3.count_bits_on(), distance(&b, &b2));

        assert_ne!(b, b2);
        assert_ne!(b2, b3);
        assert_ne!(b, b3);

        assert_eq!(b, b.clone());
        assert_eq!(b2, b2.clone());
        assert_eq!(b3, b3.clone());
    }

    #[test]
    fn test_from() {
        let mut b = BitArray::from(&[true, true, false, false, true]);
        b.set(2, true);
        assert_eq!(b, BitArray::from(&[true, true, true, false, true]));
    }

    #[test]
    fn test_all_combinations() {
        assert_eq!(BitArray::all_combinations(1), vec![BitArray::from(&[false]), BitArray::from(&[true])]);
        assert_eq!(BitArray::all_combinations(2), vec![BitArray::from(&[false, false]), BitArray::from(&[false, true]), BitArray::from(&[true, false]), BitArray::from(&[true, true])]);
    }

    #[test]
    fn test_parse() {
        // Note:
        //
        // The low-order bit in a string is the rightmost bit, while the
        // low-order bit in the source array is the leftmost element.
        for (b, s) in [
            (BitArray::from(&[true, false, false, true, true, false, true]), "1011001"),
            (BitArray::from(&[false, true, true, false, true, true, true]), "1110110")
        ] {
            assert_eq!(b, s.parse::<BitArray>().unwrap());
        }
    }

    #[test]
    fn test_convert() {
        for (s, v) in [("1111", 15), ("0000", 0), ("1110", 14), ("1010", 10), ("0111", 7), ("0101", 5)] {
            let b = s.parse::<BitArray>().unwrap();
            assert_eq!(u64::try_from(&b).unwrap(), v);
        }
    }

    #[test]
    fn test_iter() {
        for bool_vals in [[true, true, false, false, true], [false, true, false, false, false]] {
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
        for (b_s, inv_b_s) in [("10110", "01001"), ("11111", "00000")] {
            let b: BitArray = b_s.parse().unwrap();
            let inv_b: BitArray = inv_b_s.parse().unwrap();
            assert_eq!(!&b, inv_b);
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
        let result: BitArray = b1.iter()
            .zip(b2.iter())
            .rev()
            .map(|(bit1, bit2)| bit1 || bit2)
            .collect();
        assert_eq!(result, "1101".parse().unwrap());
    }
}
