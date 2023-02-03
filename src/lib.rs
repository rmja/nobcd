#![no_std]
#![feature(const_convert)]
#![feature(const_refs_to_cell)]
#![feature(const_trait_impl)]
#![feature(const_try)]

#[cfg(feature = "defmt")]
mod defmt_impl;

use core::{ops::{Add, Div, Mul, Sub}, fmt::Debug};

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct BcdNumber<const BYTES: usize> {
    data: [u8; BYTES],
}

impl<const BYTES: usize> Debug for BcdNumber<BYTES> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut first = true;
        for byte in self.data.into_iter().skip_while(|x| *x == 0) {
            if first {
                write!(f, "{:x?}", byte)?;
                first = false;
            }
            else {
                write!(f, "{:02x?}", byte)?;
            }
        }
        Ok(())
    }
}

#[cfg(feature = "defmt")]
impl<const BYTES: usize> defmt::Format for BcdNumber<BYTES> {
    fn format(&self, fmt: defmt::Formatter) {
        let mut first = true;
        for byte in self.data.into_iter().skip_while(|x| *x == 0) {
            if first {
                defmt::write!(fmt, "{=u8:x}", byte);
                first = false;
            }
            else {
                defmt::write!(fmt, "{=u8:02x}", byte);
            }
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum BcdError {
    Overflow,
    InvalidDigit(u8),
}

impl<const BYTES: usize> BcdNumber<BYTES> {
    /// Create a new BCD number from its value
    pub const fn try_new<T: ~const ValuePrimitive>(mut value: T) -> Result<Self, BcdError> {
        let mut data = [0; BYTES];
        let mut index = BYTES as isize - 1;

        while value > T::ZERO {
            if index < 0 {
                return Err(BcdError::Overflow);
            }

            let mut shifts = 0;
            while shifts < 8 {
                let next_value = value / T::TEN;
                let digit = value - next_value * T::TEN;
                let digit: u8 = digit.as_u8();

                data[index as usize] |= digit << shifts;

                value = next_value;
                shifts += 4;
            }
            index -= 1;
        }

        Ok(Self { data })
    }

    /// Get a BCD number from a series of bytes where each nibble represent a digit
    const fn try_from(bcd: [u8; BYTES]) -> Result<Self, BcdError> {
        let mut index = 0;
        while index < BYTES {
            get_nibbles(bcd[index])?;
            index += 1;
        }

        Ok(Self { data: bcd })
    }

    /// Get the number value
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

    /// Get the BCD encoded bytes
    pub const fn bcd_bytes(&self) -> [u8; BYTES] {
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
    if high > 9 {
        Err(BcdError::InvalidDigit(high))
    } else if low > 9 {
        Err(BcdError::InvalidDigit(low))
    } else {
        Ok((high, low))
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
        self
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

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;

    #[test]
    fn u8() {
        let bcd = BcdNumber::<1>::try_new(12u8).unwrap();
        assert_eq!(12u8, bcd.value());
        assert_eq!([0x12], bcd.bcd_bytes());
        assert_eq!(bcd, BcdNumber::try_from([0x12]).unwrap());
        assert_eq!("12", std::format!("{:?}", bcd));

        assert_eq!([0x99], BcdNumber::try_new(99u8).unwrap().bcd_bytes());
        assert_eq!(Err(BcdError::Overflow), BcdNumber::<1>::try_new(1_00u8));
    }

    #[test]
    fn u16() {
        let bcd = BcdNumber::<2>::try_new(1234u16).unwrap();
        assert_eq!(1234u16, bcd.value());
        assert_eq!([0x12, 0x34], bcd.bcd_bytes());
        assert_eq!(bcd, BcdNumber::try_from([0x12, 0x34]).unwrap());
        assert_eq!("1234", std::format!("{:?}", bcd));

        assert_eq!(
            [0x99, 0x99],
            BcdNumber::try_new(9999u16).unwrap().bcd_bytes()
        );
        assert_eq!(Err(BcdError::Overflow), BcdNumber::<2>::try_new(1_0000u16));
    }

    #[test]
    fn u32() {
        let bcd = BcdNumber::<4>::try_new(12345678u32).unwrap();
        assert_eq!(12345678u32, bcd.value());
        assert_eq!([0x12, 0x34, 0x56, 0x78], bcd.bcd_bytes());
        assert_eq!(bcd, BcdNumber::try_from([0x12, 0x34, 0x56, 0x78]).unwrap());
        assert_eq!("12345678", std::format!("{:?}", bcd));

        assert_eq!(
            [0x99, 0x99, 0x99, 0x99],
            BcdNumber::try_new(99999999u32).unwrap().bcd_bytes()
        );
        assert_eq!(
            Err(BcdError::Overflow),
            BcdNumber::<4>::try_new(1_00000000u32)
        );
    }

    #[test]
    fn u64() {
        let bcd = BcdNumber::<8>::try_new(1234567887654321u64).unwrap();
        assert_eq!(1234567887654321u64, bcd.value());
        assert_eq!(
            [0x12, 0x34, 0x56, 0x78, 0x87, 0x65, 0x43, 0x21],
            bcd.bcd_bytes()
        );
        assert_eq!(
            bcd,
            BcdNumber::try_from([0x12, 0x34, 0x56, 0x78, 0x87, 0x65, 0x43, 0x21]).unwrap()
        );
        assert_eq!("1234567887654321", std::format!("{:?}", bcd));

        assert_eq!(
            [0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99],
            BcdNumber::try_new(99999999_99999999u64)
                .unwrap()
                .bcd_bytes()
        );
        assert_eq!(
            Err(BcdError::Overflow),
            BcdNumber::<8>::try_new(1_00000000_00000000u64)
        );
    }

    #[test]
    fn fmt() {
        assert_eq!("1234", std::format!("{:?}", BcdNumber::<8>::try_new(1234u16).unwrap()));
        assert_eq!("1020304", std::format!("{:?}", BcdNumber::<8>::try_new(1020304u32).unwrap()));
        assert_eq!("10203040", std::format!("{:?}", BcdNumber::<8>::try_new(10203040u32).unwrap()));
    }

}
