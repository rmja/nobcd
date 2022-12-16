#![cfg_attr(not(test), no_std)]
#![feature(const_refs_to_cell)]
#![feature(const_trait_impl)]

use core::ops::{Add, Div, Mul, Sub};

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct BcdNumber<const BYTES: usize> {
    data: [u8; BYTES],
}

#[derive(Debug)]
pub struct BcdError;

impl<const BYTES: usize> BcdNumber<BYTES> {
    const fn try_from(bcd: [u8; BYTES]) -> Result<Self, BcdError> {
        let mut index = 0;
        while index < BYTES {
            if get_nibbles(bcd[index]).is_err() {
                return Err(BcdError);
            }
            index += 1;
        }

        Ok(Self { data: bcd })
    }

    const fn from_value<T: ~const ValuePrimitive>(mut value: T) -> Self {
        let mut data = [0; BYTES];
        let mut index = BYTES - 1;

        while value > T::ZERO {
            let mut shifts = 0;
            while shifts < 8 {
                let next_value = value / T::TEN;
                let digit = value - next_value * T::TEN;
                let digit: u8 = digit.as_u8();

                data[index] |= digit << shifts;

                value = next_value;
                shifts += 4;
            }
            index = index.saturating_sub(1);
        }

        Self { data }
    }

    pub fn value<T: ValuePrimitive>(&self) -> T {
        let mut value = T::ZERO;
        for byte in self.data {
            let (high, low) = get_nibbles(byte).unwrap();
            let high: T = high.into();
            let low: T = low.into();
            value = (value * T::HUNDRED) + high * T::TEN + low;
        }
        value
    }

    pub const fn to_bcd_bytes(&self) -> [u8; BYTES] {
        self.data
    }
}

impl<const BYTES: usize> const TryFrom<[u8; BYTES]> for BcdNumber<BYTES> {
    type Error = BcdError;

    fn try_from(value: [u8; BYTES]) -> Result<Self, Self::Error> {
        Self::try_from(value)
    }
}

impl<const BYTES: usize> IntoIterator for BcdNumber<BYTES> {
    type Item = u8;

    type IntoIter = core::array::IntoIter<Self::Item, BYTES>;

    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}

const fn get_nibbles(byte: u8) -> Result<(u8, u8), BcdError> {
    let high = (byte & 0xF0) >> 4;
    let low = byte & 0x0F;
    if low <= 9 || high <= 9 {
        Ok((high, low))
    } else {
        Err(BcdError)
    }
}

#[const_trait]
pub trait ValuePrimitive:
    From<u8>
    + Copy
    + Clone
    + ~const Add<Self, Output = Self>
    + ~const Sub<Self, Output = Self>
    + ~const Mul<Self, Output = Self>
    + ~const Div<Self, Output = Self>
    + ~const PartialOrd<Self>
{
    const ZERO: Self;
    const TEN: Self;
    const HUNDRED: Self;

    fn as_u8(self) -> u8;
}

impl const ValuePrimitive for u8 {
    const ZERO: Self = 0;
    const TEN: Self = 10;
    const HUNDRED: Self = 100;

    fn as_u8(self) -> u8 {
        self as u8
    }
}

impl const ValuePrimitive for u16 {
    const ZERO: Self = 0;
    const TEN: Self = 10;
    const HUNDRED: Self = 100;

    fn as_u8(self) -> u8 {
        self as u8
    }
}

impl const ValuePrimitive for u32 {
    const ZERO: Self = 0;
    const TEN: Self = 10;
    const HUNDRED: Self = 100;

    fn as_u8(self) -> u8 {
        self as u8
    }
}

impl const ValuePrimitive for u64 {
    const ZERO: Self = 0;
    const TEN: Self = 10;
    const HUNDRED: Self = 100;

    fn as_u8(self) -> u8 {
        self as u8
    }
}

impl BcdNumber<1> {
    const MAX: u8 = 99;

    pub fn from_u8(value: u8) -> Self {
        assert!(value < Self::MAX);
        Self::from_value(value)
    }
}

impl BcdNumber<2> {
    const MAX: u16 = 9999;

    pub fn from_u16(value: u16) -> Self {
        assert!(value < Self::MAX);
        Self::from_value(value)
    }
}

impl BcdNumber<4> {
    const MAX: u32 = 99999999;

    pub fn from_u32(value: u32) -> Self {
        assert!(value < Self::MAX);
        Self::from_value(value)
    }
}

impl BcdNumber<8> {
    const MAX: u64 = 99999999_99999999;

    pub fn from_u64(value: u64) -> Self {
        assert!(value < Self::MAX);
        Self::from_value(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u8() {
        let bcd = BcdNumber::from_u8(12);
        assert_eq!(12u8, bcd.value());
        assert_eq!([0x12], bcd.to_bcd_bytes());
        assert_eq!(bcd, BcdNumber::try_from([0x12]).unwrap());
    }

    #[test]
    fn u16() {
        let bcd = BcdNumber::from_u16(1234);
        assert_eq!(1234u16, bcd.value());
        assert_eq!([0x12, 0x34], bcd.to_bcd_bytes());
        assert_eq!(bcd, BcdNumber::try_from([0x12, 0x34]).unwrap());
    }

    #[test]
    fn u32() {
        let bcd = BcdNumber::from_u32(12345678);
        assert_eq!(12345678u32, bcd.value());
        assert_eq!([0x12, 0x34, 0x56, 0x78], bcd.to_bcd_bytes());
        assert_eq!(bcd, BcdNumber::try_from([0x12, 0x34, 0x56, 0x78]).unwrap());
    }

    #[test]
    fn u64() {
        let bcd = BcdNumber::from_u64(1234567887654321);
        assert_eq!(1234567887654321u64, bcd.value());
        assert_eq!(
            [0x12, 0x34, 0x56, 0x78, 0x87, 0x65, 0x43, 0x21],
            bcd.to_bcd_bytes()
        );
        assert_eq!(
            bcd,
            BcdNumber::try_from([0x12, 0x34, 0x56, 0x78, 0x87, 0x65, 0x43, 0x21]).unwrap()
        );
    }
}
