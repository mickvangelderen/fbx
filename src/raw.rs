use std::io;

pub trait ByteArray: AsRef<[u8]> + AsMut<[u8]> {
    fn default() -> Self;
}

impl<const N: usize> ByteArray for [u8; N] {
    fn default() -> Self {
        [0u8; N]
    }
}

pub trait FromBytes {
    type ByteArray: ByteArray;

    fn from_bytes(bytes: Self::ByteArray) -> Self;
}

impl FromBytes for u8 {
    type ByteArray = [u8; 1];

    fn from_bytes(bytes: Self::ByteArray) -> Self {
        bytes[0]
    }
}

impl<const N: usize> FromBytes for [u8; N] {
    type ByteArray = Self;

    fn from_bytes(bytes: Self::ByteArray) -> Self {
        bytes
    }
}

macro_rules! impl_from_bytes_for_newtype {
    ($T:ident($F:ty)) => {
        impl FromBytes for $T {
            type ByteArray = <$F as FromBytes>::ByteArray;

            fn from_bytes(bytes: Self::ByteArray) -> Self {
                Self(<$F as FromBytes>::from_bytes(bytes))
            }
        }
    };
}

pub trait ReadExt {
    fn read_value<T>(&mut self) -> io::Result<T>
    where
        T: FromBytes;

    fn read_bytes(&mut self, count: usize) -> io::Result<Vec<u8>>;
}

impl<R> ReadExt for R
where
    R: io::Read,
{
    fn read_value<T>(&mut self) -> io::Result<T>
    where
        T: FromBytes,
    {
        // NOTE(mickvangelderen): Could use
        // [`Read::read_buf_exact`](https://doc.rust-lang.org/std/io/trait.Read.html#method.read_buf_exact)
        // once stable in order not to have to initialize the value before writing to it.
        let mut bytes = T::ByteArray::default();
        self.read_exact(bytes.as_mut())?;
        Ok(T::from_bytes(bytes))
    }

    fn read_bytes(&mut self, count: usize) -> io::Result<Vec<u8>> {
        let mut bytes = vec![0u8; count];
        self.read_exact(&mut bytes)?;
        Ok(bytes)
    }
}

macro_rules! impl_integer {
    ($I:ty, le, $T:ident, [u8; $N:expr]) => {
        impl_integer!(@ $I, from_le_bytes, to_le_bytes, $T, [u8; $N]);
    };
    (@ $I:ty, $from_bytes:ident, $to_bytes:ident, $T:ident, [u8; $N:expr]) => {
        #[derive(Eq, PartialEq)]
        #[allow(non_camel_case_types)]
        #[repr(transparent)]
        pub struct $T(pub [u8; $N]);

        impl $T {
            pub const fn from_ne(value: $I) -> Self {
                Self(value.$to_bytes())
            }

            pub const fn into_ne(self) -> $I {
                <$I>::$from_bytes(self.0)
            }
        }

        impl From<$I> for $T {
            fn from(value: $I) -> Self {
                Self::from_ne(value)
            }
        }

        impl From<$T> for $I {
            fn from(value: $T) -> Self {
                value.into_ne()
            }
        }

        impl_from_bytes_for_newtype!($T([u8; $N]));
    };
}

impl_integer!(u32, le, u32le, [u8; 4]);
impl_integer!(u64, le, u64le, [u8; 8]);

#[repr(transparent)]
pub struct Version(pub u32le);

impl_from_bytes_for_newtype!(Version(u32le));

#[repr(transparent)]
pub struct Magic(pub [u8; 23]);

impl_from_bytes_for_newtype!(Magic([u8; 23]));

#[derive(Eq, PartialEq)]
#[repr(transparent)]
pub struct PropertyKind(pub u8);

impl_from_bytes_for_newtype!(PropertyKind(u8));

impl PropertyKind {
    pub const U8: Self = Self(b'C');
    pub const I16: Self = Self(b'Y');
    pub const I32: Self = Self(b'I');
    pub const I64: Self = Self(b'L');
    pub const F32: Self = Self(b'F');
    pub const F64: Self = Self(b'D');
    pub const U8_ARRAY: Self = Self(b'b');
    pub const I32_ARRAY: Self = Self(b'i');
    pub const I64_ARRAY: Self = Self(b'l');
    pub const F32_ARRAY: Self = Self(b'f');
    pub const F64_ARRAY: Self = Self(b'd');
    pub const STRING: Self = Self(b'S');
    pub const BYTES: Self = Self(b'R');
}

#[derive(Eq, PartialEq)]
#[repr(transparent)]
pub struct ArrayEncodingKind(pub u32le);

impl_from_bytes_for_newtype!(ArrayEncodingKind(u32le));

impl ArrayEncodingKind {
    pub const PLAIN: Self = Self(u32le::from_ne(0));
    pub const DEFLATE: Self = Self(u32le::from_ne(1));
}
