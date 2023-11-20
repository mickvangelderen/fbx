//! This crate lets you read FBX files.

#![warn(missing_docs)]
#![deny(unsafe_code)]

pub(crate) mod raw;

use crate::raw::ReadExt;
use core::fmt;
use std::{
    io::{self, Read, Seek},
    string::FromUtf8Error,
};
use thiserror::Error;

/// The `DeserializationError` enum represents an error that occurred during deserialization of an
/// FBX file.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum DeserializationError {
    /// See [`InvalidMagic`].
    #[error("invalid magic string")]
    InvalidMagic(InvalidMagic),

    /// See [`UnknownVersion`].
    #[error("unknown version {0}")]
    UnknownVersion(UnknownVersion),

    /// See [`UnknownPropertyKind`].
    #[error("unknown property kind {0}")]
    UnknownPropertyKind(UnknownPropertyKind),

    /// See [`UnknownArrayEncoding`].
    #[error("unknown array encoding kind {0}")]
    UnknownArrayEncoding(UnknownArrayEncoding),

    /// Returned when the node name is not a valid UTF-8 byte string.
    #[error("property name is not valid utf-8")]
    NodeNameIsNotValidUtf8(#[from] FromUtf8Error),
}

/// The `Error` enum wraps the io and deserialization errors.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum Error {
    /// See [`DeserializationError`].
    #[error("deserialization error")]
    Deserialization(#[from] DeserializationError),
    /// See [`std::io::Error`].
    #[error("io error")]
    Io(#[from] std::io::Error),
}

/// Convenient result alias.
pub type Result<T, E = Error> = ::core::result::Result<T, E>;

/// Zero sized type that represents the file header magic. Exists for symmetry.
struct Magic(());

/// The FBX file header should contain a particular sequence of bytes. This byte sequence is
/// often referred to as the "magic string". This error is returned when the magic is not what
/// it should be. This can happen when the input is not actually a valid binary FBX file.
#[derive(Debug)]
pub struct InvalidMagic(());

impl From<InvalidMagic> for DeserializationError {
    fn from(value: InvalidMagic) -> Self {
        DeserializationError::InvalidMagic(value)
    }
}

impl From<InvalidMagic> for Error {
    fn from(value: InvalidMagic) -> Self {
        Error::Deserialization(value.into())
    }
}

impl TryFrom<raw::Magic> for Magic {
    type Error = InvalidMagic;

    fn try_from(value: raw::Magic) -> std::result::Result<Self, Self::Error> {
        if value.0 == *b"Kaydara FBX Binary  \x00\x1A\x00" {
            Ok(Magic(()))
        } else {
            Err(InvalidMagic(()))
        }
    }
}

/// The FBX file header contains a version number. The number that was read is not a known or
/// supported version.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct UnknownVersion(pub u32);

impl std::fmt::Display for UnknownVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl From<UnknownVersion> for DeserializationError {
    fn from(value: UnknownVersion) -> Self {
        DeserializationError::UnknownVersion(value)
    }
}

impl From<UnknownVersion> for Error {
    fn from(value: UnknownVersion) -> Self {
        Error::Deserialization(value.into())
    }
}

/// An FBX file version. This does not cover all FBX file versions ever, just the ones that we
/// recognize.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Version {
    /// 2011
    V7100,
    /// 2012
    V7200,
    /// 2013
    V7300,
    /// 2014
    V7400,
    /// 2016.1.2
    V7500,
}

impl From<Version> for u32 {
    fn from(value: Version) -> Self {
        match value {
            Version::V7100 => 7100,
            Version::V7200 => 7200,
            Version::V7300 => 7300,
            Version::V7400 => 7400,
            Version::V7500 => 7500,
        }
    }
}

impl TryFrom<u32> for Version {
    type Error = UnknownVersion;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            7100 => Ok(Version::V7100),
            7200 => Ok(Version::V7200),
            7300 => Ok(Version::V7300),
            7400 => Ok(Version::V7400),
            7500 => Ok(Version::V7500),
            unknown => Err(UnknownVersion(unknown)),
        }
    }
}

impl From<Version> for raw::Version {
    fn from(value: Version) -> Self {
        raw::Version(u32::from(value).into())
    }
}

impl TryFrom<raw::Version> for Version {
    type Error = UnknownVersion;

    fn try_from(value: raw::Version) -> std::result::Result<Self, Self::Error> {
        u32::from(value.0).try_into()
    }
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        u32::from(*self).fmt(f)
    }
}

/// Represents an FBX file.
#[derive(Debug)]
pub struct File {
    ///
    pub version: Version,

    ///
    pub children: Vec<Node>,
}

impl File {
    /// Read an FBX file from the provided reader. Many small reads will be done from this reader so
    /// in certain cases it can be beneficial to wrap the reader in an [`std::io::BufReader`].
    pub fn read_from<R: Read + Seek>(mut reader: R) -> Result<Self> {
        let _: Magic = reader.read_value::<raw::Magic>()?.try_into()?;
        let version: Version = reader.read_value::<raw::Version>()?.try_into()?;

        let mut children = Vec::new();
        while let Some(node) = Node::read_from(&mut reader, version)? {
            children.push(node);
        }

        Ok(Self { version, children })
    }
}

///
#[derive(Debug)]
pub struct Node {
    ///
    pub name: String,
    ///
    pub properties: Vec<Property>,
    ///
    pub children: Vec<Node>,
}

impl Node {
    fn read_from<R: Read + Seek>(reader: &mut R, version: Version) -> Result<Option<Self>> {
        let end_byte_offset: u64;
        let property_count: u64;
        let property_list_len: u64;
        match version {
            Version::V7100 | Version::V7200 | Version::V7300 | Version::V7400 => {
                end_byte_offset = u32::from(reader.read_value::<raw::u32le>()?)
                    .try_into()
                    .unwrap();
                property_count = u32::from(reader.read_value::<raw::u32le>()?)
                    .try_into()
                    .unwrap();
                property_list_len = u32::from(reader.read_value::<raw::u32le>()?)
                    .try_into()
                    .unwrap();
            }
            Version::V7500 => {
                end_byte_offset = reader.read_value::<raw::u64le>()?.into();
                property_count = reader.read_value::<raw::u64le>()?.into();
                property_list_len = reader.read_value::<raw::u64le>()?.into();
            }
        }

        let name_len: u8 = reader.read_value::<u8>()?;

        // Check for a zeroed record. This check must occur after reading the entire header.
        if end_byte_offset == 0 {
            return Ok(None);
        }

        let name = Self::read_name(reader, name_len.try_into().unwrap())?;

        let properties_byte_start = reader.stream_position()?;

        let properties = Self::read_properties(reader, property_count.try_into().unwrap())?;

        let properties_byte_end = reader.stream_position()?;

        debug_assert_eq!(
            property_list_len,
            properties_byte_end - properties_byte_start
        );

        let children = Self::read_children(reader, version, end_byte_offset)?;

        debug_assert_eq!(end_byte_offset, reader.stream_position()?);

        Ok(Some(Node {
            name,
            properties,
            children,
        }))
    }

    fn read_name<R: Read + Seek>(reader: &mut R, byte_count: usize) -> Result<String> {
        let bytes = reader.read_bytes(byte_count)?;
        Ok(String::from_utf8(bytes).map_err(DeserializationError::NodeNameIsNotValidUtf8)?)
    }

    fn read_properties<R: Read + Seek>(reader: &mut R, count: usize) -> Result<Vec<Property>> {
        let mut properties = Vec::with_capacity(count);
        for _ in 0..count {
            properties.push(Property::read_from(reader)?);
        }
        Ok(properties)
    }

    fn read_children<R: Read + Seek>(
        reader: &mut R,
        version: Version,
        end_byte_offset: u64,
    ) -> Result<Vec<Node>> {
        let mut children = Vec::new();
        // NOTE(mickvangelderen): The child node list is not always terminated by a null record,
        // making this condition necessary.
        while reader.stream_position()? < end_byte_offset {
            match Node::read_from(reader, version)? {
                Some(node) => children.push(node),
                None => break,
            }
        }
        Ok(children)
    }
}

enum PropertyKind {
    U8,
    I16,
    I32,
    I64,
    F32,
    F64,
    U8Array,
    I32Array,
    I64Array,
    F32Array,
    F64Array,
    String,
    Bytes,
}

/// Returned when deserializing a property of which the kind (type) is not known.
#[derive(Debug)]
pub struct UnknownPropertyKind(u8);

impl From<UnknownPropertyKind> for DeserializationError {
    fn from(value: UnknownPropertyKind) -> Self {
        Self::UnknownPropertyKind(value)
    }
}

impl From<UnknownPropertyKind> for Error {
    fn from(value: UnknownPropertyKind) -> Self {
        Self::Deserialization(value.into())
    }
}

impl fmt::Display for UnknownPropertyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl TryFrom<raw::PropertyKind> for PropertyKind {
    type Error = UnknownPropertyKind;

    fn try_from(value: raw::PropertyKind) -> Result<Self, Self::Error> {
        match value {
            raw::PropertyKind::U8 => Ok(Self::U8),
            raw::PropertyKind::I16 => Ok(Self::I16),
            raw::PropertyKind::I32 => Ok(Self::I32),
            raw::PropertyKind::I64 => Ok(Self::I64),
            raw::PropertyKind::F32 => Ok(Self::F32),
            raw::PropertyKind::F64 => Ok(Self::F64),
            raw::PropertyKind::U8_ARRAY => Ok(Self::U8Array),
            raw::PropertyKind::I32_ARRAY => Ok(Self::I32Array),
            raw::PropertyKind::I64_ARRAY => Ok(Self::I64Array),
            raw::PropertyKind::F32_ARRAY => Ok(Self::F32Array),
            raw::PropertyKind::F64_ARRAY => Ok(Self::F64Array),
            raw::PropertyKind::STRING => Ok(Self::String),
            raw::PropertyKind::BYTES => Ok(Self::Bytes),
            unknown => Err(UnknownPropertyKind(unknown.0)),
        }
    }
}

enum ArrayEncodingKind {
    Plain,
    Deflate,
}

/// Returned when deserializing an array property of which the encoding is not known.
#[derive(Debug)]
pub struct UnknownArrayEncoding(u32);

impl From<UnknownArrayEncoding> for DeserializationError {
    fn from(value: UnknownArrayEncoding) -> Self {
        Self::UnknownArrayEncoding(value)
    }
}

impl From<UnknownArrayEncoding> for Error {
    fn from(value: UnknownArrayEncoding) -> Self {
        Self::Deserialization(value.into())
    }
}

impl fmt::Display for UnknownArrayEncoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl TryFrom<raw::ArrayEncodingKind> for ArrayEncodingKind {
    type Error = UnknownArrayEncoding;

    fn try_from(value: raw::ArrayEncodingKind) -> Result<Self, Self::Error> {
        match value {
            raw::ArrayEncodingKind::PLAIN => Ok(Self::Plain),
            raw::ArrayEncodingKind::DEFLATE => Ok(Self::Deflate),
            unknown => Err(UnknownArrayEncoding(unknown.0.into())),
        }
    }
}

/// A piece of data from an FBX file. Properties belong to a [`Node`].
#[derive(Debug)]
pub enum Property {
    ///
    Bool(bool),
    ///
    I16(i16),
    ///
    I32(i32),
    ///
    I64(i64),
    ///
    F32(f32),
    ///
    F64(f64),
    ///
    BoolArray(Vec<bool>),
    ///
    I32Array(Vec<i32>),
    ///
    I64Array(Vec<i64>),
    ///
    F32Array(Vec<f32>),
    ///
    F64Array(Vec<f64>),
    ///
    String(String),
    ///
    Bytes(Vec<u8>),
}

impl Property {
    fn read_from<R: Read + Seek>(reader: &mut R) -> Result<Self> {
        let property_kind: PropertyKind = reader.read_value::<raw::PropertyKind>()?.try_into()?;

        fn coerce_bool(value: u8) -> bool {
            value != 0
        }

        Ok(match property_kind {
            PropertyKind::U8 => Self::Bool(coerce_bool(reader.read_value()?)),
            PropertyKind::I16 => Self::I16(i16::from_le_bytes(reader.read_value()?)),
            PropertyKind::I32 => Self::I32(i32::from_le_bytes(reader.read_value()?)),
            PropertyKind::I64 => Self::I64(i64::from_le_bytes(reader.read_value()?)),
            PropertyKind::F32 => Self::F32(f32::from_le_bytes(reader.read_value()?)),
            PropertyKind::F64 => Self::F64(f64::from_le_bytes(reader.read_value()?)),
            PropertyKind::U8Array => Self::BoolArray(Self::read_array(reader, coerce_bool)?),
            PropertyKind::I32Array => Self::I32Array(Self::read_array(reader, i32::from_le_bytes)?),
            PropertyKind::I64Array => Self::I64Array(Self::read_array(reader, i64::from_le_bytes)?),
            PropertyKind::F32Array => Self::F32Array(Self::read_array(reader, f32::from_le_bytes)?),
            PropertyKind::F64Array => Self::F64Array(Self::read_array(reader, f64::from_le_bytes)?),
            PropertyKind::String => {
                let byte_count: u32 = reader.read_value::<raw::u32le>()?.into();
                let bytes = reader.read_bytes(byte_count.try_into().unwrap())?;
                Self::String(String::from_utf8(bytes).unwrap())
            }
            PropertyKind::Bytes => {
                let byte_count: u32 = reader.read_value::<raw::u32le>()?.into();
                let bytes = reader.read_bytes(byte_count.try_into().unwrap())?;
                Self::Bytes(bytes)
            }
        })
    }

    fn read_array<R, T, U, F>(mut reader: &mut R, deserialize: F) -> Result<Vec<U>>
    where
        R: Read + Seek,
        T: raw::FromBytes,
        F: Fn(T) -> U,
    {
        let element_count: usize = reader
            .read_value::<raw::u32le>()?
            .into_ne()
            .try_into()
            .unwrap();
        let array_encoding_kind: ArrayEncodingKind =
            reader.read_value::<raw::ArrayEncodingKind>()?.try_into()?;
        let byte_count: usize = reader
            .read_value::<raw::u32le>()?
            .into_ne()
            .try_into()
            .unwrap();
        Ok(match array_encoding_kind {
            ArrayEncodingKind::Plain => {
                debug_assert_eq!(
                    byte_count,
                    element_count * std::mem::size_of::<T::ByteArray>()
                );
                Self::read_array_items(reader, deserialize, element_count)?
            }
            ArrayEncodingKind::Deflate => {
                let start_byte = reader.stream_position()?;
                let array;
                reader = {
                    let mut deflate_reader =
                        flate2::read::ZlibDecoder::new(reader.take(byte_count.try_into().unwrap()));
                    array =
                        Self::read_array_items(&mut deflate_reader, deserialize, element_count)?;
                    deflate_reader.into_inner().into_inner()
                };
                let end_byte = reader.stream_position()?;
                debug_assert_eq!(end_byte - start_byte, byte_count.try_into().unwrap());
                array
            }
        })
    }

    fn read_array_items<R, T, U, F>(
        reader: &mut R,
        deserialize: F,
        count: usize,
    ) -> io::Result<Vec<U>>
    where
        R: Read,
        T: raw::FromBytes,
        F: Fn(T) -> U,
    {
        (0..count)
            .map(|_| Ok(deserialize(reader.read_value()?)))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_magic_works() {
        let mut reader = std::io::Cursor::new([0u8; 4]);
        assert!(reader.read_value::<raw::Magic>().is_err());
    }
}
