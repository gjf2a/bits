use std::ops::BitXor;

#[derive(Clone, Debug, Default)]
pub struct BitArray {
    bits: Vec<u64>,
    size: u64,
}

impl BitArray {
    pub fn new() -> Self { Default::default() }

    fn get_mask(index: u64) -> u64 {
        1 << BitArray::get_offset(index)
    }

    fn get_offset(index: u64) -> u64 {
        index % (BitArray::word_size() as u64)
    }

    fn get_word(index: u64) -> usize {
        (index as usize / BitArray::word_size()) as usize
    }

    pub fn word_size() -> usize {
        std::mem::size_of::<u64>()
    }

    pub fn len(&self) -> u64 {self.size}

    pub fn add(&mut self, value: bool) {
        if BitArray::get_offset(self.size) == 0 {
            self.bits.push(0);
        }
        self.set(self.size, value);
        self.size += 1;
    }

    pub fn set(&mut self, index: u64, value: bool) {
        let mask = BitArray::get_mask(index);
        if value {
            self.bits[BitArray::get_word(index)] |= mask;
        } else {
            self.bits[BitArray::get_word(index)] &= !mask;
        }
    }

    pub fn is_set(&self, index: u64) -> bool {
        self.bits[BitArray::get_word(index)] & BitArray::get_mask(index) > 0
    }

    pub fn count_bits_on(&self) -> u32 {
        self.bits.iter().map(|word| word.count_ones() as u32).sum()
    }
}

impl PartialEq for BitArray {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && (0..self.bits.len()).all(|i| self.bits[i] == other.bits[i])
    }
}

impl Eq for BitArray {}

pub fn distance(b1: &BitArray, b2: &BitArray) -> u32 {
    (b1 ^ b2).count_bits_on()
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
}
