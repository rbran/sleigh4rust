#![no_std]

use core::fmt::Display;
pub use ethnum;

/*
naming based on the this example of a:
- unsigned_type = u16
- varnode_len = 3
- varnode_lsb = 14
- data_bits = 3
+----+------------------------+-----------------------+-----------------------+
|msb |            2           |           1           |           0           |
|lsb |            0           |           1           |           2           |
+----+------------------------+-----------------------+-----------------------+
|bit | 00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 22 23|
|read|                                           XX XX XX                     |
+----+------------------------------------------------------------------------+
- TYPE_BITS = 16
- TYPE_BYTES = 2
- data_lsb = 5
- read_bytes = 2
- data_addr_offset = if big { 0 } else { 1 }
- data_addr = data_addr_offset
- data_start = 0
- data_end = 2
*/
macro_rules! memory_read_bits {
    (
        $unsigned_type:ty,
        $signed_type:ty,
        $read_unsigned:ident,
        $read_signed:ident $(,)?
    ) => {
        fn $read_unsigned<const BIG_ENDIAN: bool>(
            &self,
            addr: Self::AddressType,
            varnode_lsb: usize,
            data_bits: usize,
        ) -> Result<$unsigned_type, MemoryReadError<Self::AddressType>> {
            const TYPE_BITS: usize = <$unsigned_type>::BITS as usize;
            const TYPE_BYTES: usize = TYPE_BITS / 8;
            assert!(data_bits > 0);
            let data_lsb = varnode_lsb % 8;
            let read_bytes = (data_bits + data_lsb + 7) / 8;
            assert!(read_bytes <= TYPE_BYTES);

            let data_start = if BIG_ENDIAN {
                TYPE_BYTES - read_bytes
            } else {
                0
            };
            let data_end = data_start + read_bytes;
            let mut data = [0u8; TYPE_BYTES];
            self.read(addr, &mut data[data_start..data_end])?;
            let data = if BIG_ENDIAN {
                <$unsigned_type>::from_be_bytes(data)
            } else {
                <$unsigned_type>::from_le_bytes(data)
            };
            let value_mask = <$unsigned_type>::MAX >> (TYPE_BITS - data_bits);
            Ok((data >> data_lsb) & value_mask)
        }
        fn $read_signed<const BIG_ENDIAN: bool>(
            &self,
            addr: Self::AddressType,
            start_bit: usize,
            len_bits: usize,
        ) -> Result<$signed_type, MemoryReadError<Self::AddressType>> {
            const TYPE_BITS: usize = <$signed_type>::BITS as usize;
            assert!(len_bits > 1);
            let data =
                self.$read_unsigned::<BIG_ENDIAN>(addr, start_bit, len_bits)?;
            let value_mask = <$unsigned_type>::try_from(<$signed_type>::MAX)
                .unwrap()
                >> (TYPE_BITS - len_bits);
            let sign_mask = !value_mask;
            let value_part = data & value_mask;
            let sign_part = data & sign_mask;
            //TODO: make better makeshift `as` that also works with u256
            if sign_part != 0 {
                //equivalent to `(value_part | sign_mask) as $signed type`
                let neg_value = (!value_part + 1) & value_mask;
                Ok(<$signed_type>::try_from(neg_value)
                    .unwrap()
                    .checked_neg()
                    .unwrap())
            } else {
                Ok(<$signed_type>::try_from(value_part).unwrap())
            }
        }
    };
}

macro_rules! memory_write_bits {
    (
        $unsigned_type:ty,
        $signed_type:ty,
        $write_unsigned:ident ,
        $write_signed:ident $(,)?
    ) => {
        fn $write_unsigned<const BIG_ENDIAN: bool>(
            &mut self,
            value: $unsigned_type,
            addr: Self::AddressType,
            varnode_lsb: usize,
            data_bits: usize,
        ) -> Result<(), MemoryWriteError<Self::AddressType>> {
            const TYPE_BITS: usize = <$unsigned_type>::BITS as usize;
            const TYPE_BYTES: usize = TYPE_BITS / 8;
            assert!(data_bits > 0);
            let data_lsb = varnode_lsb % 8;
            let read_bytes = (data_bits + data_lsb + 7) / 8;
            assert!(read_bytes <= TYPE_BYTES);
            let data_start = if BIG_ENDIAN {
                TYPE_BYTES - read_bytes
            } else {
                0
            };
            let data_end = data_start + read_bytes;
            let mut mem = [0u8; TYPE_BYTES];
            self.read(addr, &mut mem[data_start..data_end])?;
            let mut mem = if BIG_ENDIAN {
                <$unsigned_type>::from_be_bytes(mem)
            } else {
                <$unsigned_type>::from_le_bytes(mem)
            };
            let mask =
                (<$unsigned_type>::MAX >> (TYPE_BITS - data_bits)) << data_lsb;
            mem = mem & !mask;
            let value = (value << data_lsb) & mask;
            let final_mem = mem | value;
            let final_mem = if BIG_ENDIAN {
                final_mem.to_be_bytes()
            } else {
                final_mem.to_le_bytes()
            };
            self.write(addr, &final_mem[data_start..data_end])
        }
        fn $write_signed<const BIG_ENDIAN: bool>(
            &mut self,
            value: $signed_type,
            addr: Self::AddressType,
            start_bit: usize,
            len_bits: usize,
        ) -> Result<(), MemoryWriteError<Self::AddressType>> {
            const TYPE_BITS: usize = <$unsigned_type>::BITS as usize;
            assert!(len_bits > 1);
            assert!(len_bits + start_bit <= TYPE_BITS);
            //TODO: make better makeshift `as` that also works with u256
            let value: $unsigned_type = if value.is_negative() {
                <$unsigned_type>::MAX
                    - <$unsigned_type>::try_from(value.abs() - 1).unwrap()
            } else {
                <$unsigned_type>::try_from(value).unwrap()
            };
            let mask = <$unsigned_type>::MAX >> (TYPE_BITS - len_bits);
            let value = value & mask;
            self.$write_unsigned::<BIG_ENDIAN>(value, addr, start_bit, len_bits)
        }
    };
}

pub type FloatType = f64;
pub type NumberUnsigned = u64;
pub type NumberSigned = i64;
pub type NumberSuperSigned = i128;
pub type NumberSuperUnsigned = u128;
pub type NumberNonZeroUnsigned = core::num::NonZeroU64;
pub type NumberNonZeroSigned = core::num::NonZeroI64;
pub type NumberNonZeroSuperSigned = core::num::NonZeroI128;

//old naming convention
pub type IntTypeU = NumberUnsigned;
pub type IntTypeS = NumberSigned;
pub type NonZeroTypeU = NumberNonZeroUnsigned;
pub type NonZeroTypeS = NumberNonZeroSigned;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Endian {
    Little,
    Big,
}

impl Endian {
    pub fn is_little(&self) -> bool {
        matches!(self, Self::Little)
    }
    pub fn is_big(&self) -> bool {
        matches!(self, Self::Big)
    }
}

pub fn bytes_from_varnode<T>(
    big_endian: bool,
    varnode_addr: T,
    varnode_len: T,
    varnode_lsb: T,
    data_bits: T,
) -> (T, T)
where
    T: core::ops::Add<Output = T>
        + core::ops::Sub<Output = T>
        + core::ops::Div<Output = T>
        + core::ops::Rem<Output = T>
        + core::cmp::PartialOrd<T>
        + Copy
        + From<u8>,
{
    assert!(data_bits > 0.into());
    let data_lsb = varnode_lsb % 8.into();
    let read_bytes = (data_bits + data_lsb + 7.into()) / 8.into();
    let data_addr_offset = if big_endian {
        (varnode_len - read_bytes) - (varnode_lsb / 8.into())
    } else {
        varnode_lsb / 8.into()
    };
    let data_lsb = varnode_lsb % 8.into();
    (varnode_addr + data_addr_offset, data_lsb)
}

#[derive(Debug)]
pub enum MemoryReadError<T> {
    //InvalidLen(core::num::TryFromIntError),
    UnableToReadMemory(T, T),
    //TODO...
}
//impl<T> From<core::num::TryFromIntError> for MemoryReadError<T> {
//    fn from(value: core::num::TryFromIntError) -> Self {
//        Self::InvalidLen(value)
//    }
//}

pub trait MemoryRead
where
    usize: TryFrom<Self::AddressType>,
    <usize as TryFrom<Self::AddressType>>::Error: core::fmt::Debug,
    <Self::AddressType as TryFrom<usize>>::Error: core::fmt::Debug,
{
    type AddressType: Copy
        + core::fmt::Debug
        + core::ops::Sub<Output = Self::AddressType>
        + core::ops::Add<Output = Self::AddressType>
        + TryFrom<usize>;
    fn read(
        &self,
        addr: Self::AddressType,
        buf: &mut [u8],
    ) -> Result<(), MemoryReadError<Self::AddressType>>;
    memory_read_bits!(u8, i8, read_u8, read_i8);
    memory_read_bits!(u16, i16, read_u16, read_i16);
    memory_read_bits!(u32, i32, read_u32, read_i32);
    memory_read_bits!(u64, i64, read_u64, read_i64);
    memory_read_bits!(u128, i128, read_u128, read_i128);
    memory_read_bits!(ethnum::u256, ethnum::i256, read_u256, read_i256,);
}
#[derive(Debug)]
pub enum MemoryWriteError<T> {
    UnableToReadMemory(MemoryReadError<T>),
    //InvalidLen(core::num::TryFromIntError),
    UnableToWriteMemory(T, T),
    //TODO...
}
//impl<T> From<core::num::TryFromIntError> for MemoryWriteError<T> {
//    fn from(value: core::num::TryFromIntError) -> Self {
//        Self::InvalidLen(value)
//    }
//}
impl<T> From<MemoryReadError<T>> for MemoryWriteError<T> {
    fn from(value: MemoryReadError<T>) -> Self {
        Self::UnableToReadMemory(value)
    }
}
pub trait MemoryWrite: MemoryRead
where
    usize: TryFrom<Self::AddressType>,
    <usize as TryFrom<Self::AddressType>>::Error: core::fmt::Debug,
    <Self::AddressType as TryFrom<usize>>::Error: core::fmt::Debug,
{
    fn write(
        &mut self,
        addr: Self::AddressType,
        buf: &[u8],
    ) -> Result<(), MemoryWriteError<Self::AddressType>>;
    memory_write_bits!(u8, i8, write_u8, write_i8);
    memory_write_bits!(u16, i16, write_u16, write_i16);
    memory_write_bits!(u32, i32, write_u32, write_i32);
    memory_write_bits!(u64, i64, write_u64, write_i64);
    memory_write_bits!(u128, i128, write_u128, write_i128);
    memory_write_bits!(ethnum::u256, ethnum::i256, write_u256, write_i256,);
}

#[derive(Clone, Copy, Debug)]
pub enum DisplayElement<Reg: Display> {
    Literal(&'static str),
    Register(Reg),
    Number(bool, i64),
}
impl<Reg: Display> Display for DisplayElement<Reg> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Literal(lit) => lit.fmt(f),
            Self::Register(reg) => reg.fmt(f),
            Self::Number(hex, value) => match (*hex, value.is_negative()) {
                (true, true) => write!(f, "-0x{:x}", value.abs()),
                (true, false) => write!(f, "0x{:x}", value),
                (false, _) => value.fmt(f),
            },
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{bytes_from_varnode, MemoryRead, MemoryWrite};

    struct MyMemory<const LEN: usize>([u8; LEN]);
    impl<const LEN: usize> MemoryRead for MyMemory<LEN> {
        type AddressType = usize;
        fn read(
            &self,
            addr: Self::AddressType,
            buf: &mut [u8],
        ) -> Result<(), crate::MemoryReadError<Self::AddressType>> {
            let end = addr + buf.len();
            buf.copy_from_slice(&self.0.get(addr..end).unwrap());
            Ok(())
        }
    }
    impl<const LEN: usize> MemoryWrite for MyMemory<LEN> {
        fn write(
            &mut self,
            addr: Self::AddressType,
            buf: &[u8],
        ) -> Result<(), crate::MemoryWriteError<Self::AddressType>> {
            let end = addr + buf.len();
            self.0.get_mut(addr..end).unwrap().copy_from_slice(buf);
            Ok(())
        }
    }
    //I'm lazy
    trait Ligma: MemoryRead<AddressType = usize> + MemoryWrite {
        fn my_read_u8<const BIG: bool>(
            &self,
            varnode_addr: usize,
            varnode_len: usize,
            varnode_lsb: usize,
            data_bits: usize,
        ) -> u8 {
            assert!(data_bits <= u8::BITS as usize);
            let (data_addr, data_lsb) = bytes_from_varnode(
                BIG,
                varnode_addr,
                varnode_len,
                varnode_lsb,
                data_bits,
            );
            self.read_u8::<BIG>(data_addr, data_lsb, data_bits).unwrap()
        }
        fn my_read_u32<const BIG: bool>(
            &self,
            varnode_addr: usize,
            varnode_len: usize,
            varnode_lsb: usize,
            data_bits: usize,
        ) -> u32 {
            assert!(data_bits <= u32::BITS as usize);
            let (data_addr, data_lsb) = bytes_from_varnode(
                BIG,
                varnode_addr,
                varnode_len,
                varnode_lsb,
                data_bits,
            );
            self.read_u32::<BIG>(data_addr, data_lsb, data_bits)
                .unwrap()
        }
        fn my_write_u8<const BIG: bool>(
            &mut self,
            value: u8,
            varnode_addr: usize,
            varnode_len: usize,
            varnode_lsb: usize,
            data_bits: usize,
        ) {
            assert!(data_bits <= u8::BITS as usize);
            let (data_addr, data_lsb) = bytes_from_varnode(
                BIG,
                varnode_addr,
                varnode_len,
                varnode_lsb,
                data_bits,
            );
            self.write_u8::<BIG>(value, data_addr, data_lsb, data_bits)
                .unwrap()
        }
        fn my_write_u16<const BIG: bool>(
            &mut self,
            value: u16,
            varnode_addr: usize,
            varnode_len: usize,
            varnode_lsb: usize,
            data_bits: usize,
        ) {
            assert!(data_bits <= u16::BITS as usize);
            let (data_addr, data_lsb) = bytes_from_varnode(
                BIG,
                varnode_addr,
                varnode_len,
                varnode_lsb,
                data_bits,
            );
            self.write_u16::<BIG>(value, data_addr, data_lsb, data_bits)
                .unwrap()
        }
    }
    impl<const LEN: usize> Ligma for MyMemory<LEN> {}
    #[test]
    fn memory_read() {
        let value = 0x1FF9855u32;
        let le = MyMemory(value.to_le_bytes());
        let be = MyMemory(value.to_be_bytes());
        assert_eq!(be.my_read_u8::<true>(0, 4, 0, 8), 0x55);
        assert_eq!(le.my_read_u8::<false>(0, 4, 0, 8), 0x55);
        assert_eq!(be.my_read_u32::<true>(0, 4, 15, 10), 0x3FF);
        assert_eq!(le.my_read_u32::<false>(0, 4, 15, 10), 0x3FF);
        assert_eq!(be.my_read_u8::<true>(0, 4, 10, 4), 0b0110);
        assert_eq!(le.my_read_u8::<false>(0, 4, 10, 4), 0b0110);
        assert_eq!(be.my_read_u8::<true>(0, 4, 24, 3), 1);
        assert_eq!(le.my_read_u8::<false>(0, 4, 24, 3), 1);
    }
    #[test]
    fn memory_write() {
        let mut le = MyMemory([0u8; 4]);
        let mut be = MyMemory([0u8; 4]);
        le.my_write_u8::<false>(5, 0, 4, 0, 3);
        be.my_write_u8::<true>(5, 0, 4, 0, 3);
        assert_eq!(u32::from_be_bytes(be.0), 0x5);
        assert_eq!(u32::from_le_bytes(le.0), 0x5);
        le.my_write_u8::<false>(5, 0, 4, 4, 4);
        be.my_write_u8::<true>(5, 0, 4, 4, 4);
        assert_eq!(u32::from_be_bytes(be.0), 0x55);
        assert_eq!(u32::from_le_bytes(le.0), 0x55);
        le.my_write_u8::<false>(0x13, 0, 4, 11, 5);
        be.my_write_u8::<true>(0x13, 0, 4, 11, 5);
        assert_eq!(u32::from_be_bytes(be.0), 0x9855);
        assert_eq!(u32::from_le_bytes(le.0), 0x9855);
        le.my_write_u16::<false>(0xFF, 0, 4, 17, 9);
        be.my_write_u16::<true>(0xFF, 0, 4, 17, 9);
        assert_eq!(u32::from_be_bytes(be.0), 0x1FE9855);
        assert_eq!(u32::from_le_bytes(le.0), 0x1FE9855);
        le.my_write_u8::<false>(1, 0, 4, 16, 1);
        be.my_write_u8::<true>(1, 0, 4, 16, 1);
        assert_eq!(u32::from_be_bytes(be.0), 0x1FF9855);
        assert_eq!(u32::from_le_bytes(le.0), 0x1FF9855);
        le.my_write_u8::<false>(0, 0, 4, 16, 1);
        be.my_write_u8::<true>(0, 0, 4, 16, 1);
        assert_eq!(u32::from_be_bytes(be.0), 0x1FE9855);
        assert_eq!(u32::from_le_bytes(le.0), 0x1FE9855);
        le.my_write_u16::<false>(0, 0, 4, 17, 9);
        be.my_write_u16::<true>(0, 0, 4, 17, 9);
        assert_eq!(u32::from_be_bytes(be.0), 0x9855);
        assert_eq!(u32::from_le_bytes(le.0), 0x9855);
        le.my_write_u8::<false>(0, 0, 4, 11, 5);
        be.my_write_u8::<true>(0, 0, 4, 11, 5);
        assert_eq!(u32::from_be_bytes(be.0), 0x55);
        assert_eq!(u32::from_le_bytes(le.0), 0x55);
        le.my_write_u8::<false>(0, 0, 4, 4, 4);
        be.my_write_u8::<true>(0, 0, 4, 4, 4);
        assert_eq!(u32::from_be_bytes(be.0), 0x5);
        assert_eq!(u32::from_le_bytes(le.0), 0x5);
        le.my_write_u8::<false>(0, 0, 4, 0, 3);
        be.my_write_u8::<true>(0, 0, 4, 0, 3);
    }
}
