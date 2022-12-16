#![cfg_attr(not(test), no_std)]

use funty::Integral;

#[derive(PartialEq, Clone, Copy)]
pub struct BcdNumber<const BYTES: usize> {
    data: [u8; BYTES],
}

#[derive(Debug)]
pub struct BcdError;

impl<const BYTES: usize> BcdNumber<BYTES> {
    pub const fn from_bcd(bcd: [u8; BYTES]) -> Result<Self, BcdError> {
        let mut index = 0;
        while index < BYTES {
            if get_nibbles(bcd[index]).is_err() {
                return Err(BcdError);
            }
            index += 1;
        }

        Ok(Self { data: bcd })
    }

    fn from_value<T: Integral + From<u8>>(mut value: T) -> Self {
        let ten: T = 10u8.into();
        let mut data = [0; BYTES];
        let mut index = BYTES - 1;

        while value > T::ZERO {
            let mut shifts = 0;
            while shifts < 8 {
                let next_value = value / ten;
                let digit = (value - next_value * ten).as_u8();

                data[index] |= digit << shifts;

                value = next_value;
                shifts += 4;
            }
            index = index.saturating_sub(1);
        }

        Self { data }
    }

    pub fn value<T: Integral + From<u8>>(&self) -> T {
        let ten: T = 10u8.into();
        let hundred: T = 100u8.into();
        let mut value = T::ZERO;
        for byte in self.data {
            let (high, low) = get_nibbles(byte).unwrap();
            let high: T = high.into();
            let low: T = low.into();
            value = (value * hundred) + high * ten + low;
        }
        value
    }

    pub const fn bcd_bytes(&self) -> &[u8; BYTES] {
        &self.data
    }
}

impl<const BYTES: usize> TryFrom<[u8; BYTES]> for BcdNumber<BYTES> {
    type Error = BcdError;

    fn try_from(value: [u8; BYTES]) -> Result<Self, Self::Error> {
        Self::from_bcd(value)
    }
}

impl BcdNumber<1> {
    pub fn from_u8(value: u8) -> Self {
        Self::from_value(value)
    }
}

impl BcdNumber<2> {
    pub fn from_u16(value: u16) -> Self {
        Self::from_value(value)
    }
}

impl BcdNumber<4> {
    pub fn from_u32(value: u32) -> Self {
        Self::from_value(value)
    }
}

impl BcdNumber<8> {
    pub fn from_u64(value: u64) -> Self {
        Self::from_value(value)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u8() {
        let bcd = BcdNumber::from_u8(12);
        assert_eq!(12, bcd.value());
        assert_eq!(&[0x12], bcd.bcd_bytes());
    }

    #[test]
    fn u16() {
        let bcd = BcdNumber::from_u16(1234);
        assert_eq!(1234, bcd.value());
        assert_eq!(&[0x12, 0x34], bcd.bcd_bytes());
    }

    #[test]
    fn u32() {
        let bcd = BcdNumber::from_u32(12345678);
        assert_eq!(12345678, bcd.value());
        assert_eq!(&[0x12, 0x34, 0x56, 0x78], bcd.bcd_bytes());
    }

    #[test]
    fn u64() {
        let bcd = BcdNumber::from_u64(1234567887654321);
        assert_eq!(1234567887654321u64, bcd.value());
        assert_eq!(
            &[0x12, 0x34, 0x56, 0x78, 0x87, 0x65, 0x43, 0x21],
            bcd.bcd_bytes()
        );
    }
}
