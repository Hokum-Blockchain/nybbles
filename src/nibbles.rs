use core::{
    borrow::Borrow,
    fmt,
    mem::MaybeUninit,
    ops::{Index, Range},
};
use smallvec::SmallVec;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

type Repr = SmallVec<[u64; 4]>;

macro_rules! unsafe_assume {
    ($e:expr $(,)?) => {
        if !$e {
            unsafe_unreachable!(stringify!($e));
        }
    };
}

macro_rules! unsafe_unreachable {
    ($($t:tt)*) => {
        if cfg!(debug_assertions) {
            unreachable!($($t)*);
        } else {
            unsafe { core::hint::unreachable_unchecked() };
        }
    };
}

/// Structure representing a sequence of nibbles.
///
/// A nibble is a 4-bit value, and this structure is used to store the nibble sequence representing
/// the keys in a Merkle Patricia Trie (MPT).
/// Using nibbles simplifies trie operations and enables consistent key representation in the MPT.
///
/// # Internal representation
///
/// The internal representation is currently a [`SmallVec`] that stores one nibble per byte. Nibbles
/// are stored inline (on the stack) up to a length of 64 nibbles, or 32 unpacked bytes. This means
/// that each byte has its upper 4 bits set to zero and the lower 4 bits representing the nibble
/// value.
///
/// This is enforced in the public API, but it is possible to create invalid [`Nibbles`] instances
/// using methods suffixed with `_unchecked`. These methods are not marked as `unsafe` as they
/// are not memory-unsafe, but creating invalid values will cause unexpected behavior in other
/// methods, and users should exercise caution when using them.
///
/// # Examples
///
/// ```
/// use nybbles::Nibbles;
///
/// let bytes = [0xAB, 0xCD];
/// let nibbles = Nibbles::unpack(&bytes);
/// assert_eq!(nibbles, Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C, 0x0D]));
/// assert_eq!(nibbles[..], [0x0A, 0x0B, 0x0C, 0x0D]);
///
/// let packed = nibbles.pack();
/// assert_eq!(&packed[..], &bytes[..]);
/// ```
#[derive(Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Nibbles(Repr, u8);

impl core::ops::Deref for Nibbles {
    type Target = [u64];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

// Override `SmallVec::from` in the default `Clone` implementation since it's not specialized for
// `Copy` types.
impl Clone for Nibbles {
    #[inline]
    fn clone(&self) -> Self {
        Self(SmallVec::from_slice(&self.0), self.1)
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.0.clone_from(&source.0);
    }
}

impl fmt::Debug for Nibbles {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Nibbles").field(&self.as_slice()).finish()
    }
}

impl From<Nibbles> for Vec<u64> {
    #[inline]
    fn from(value: Nibbles) -> Self {
        value.0.into_vec()
    }
}

impl PartialEq<[u64]> for Nibbles {
    #[inline]
    fn eq(&self, other: &[u64]) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<Nibbles> for [u64] {
    #[inline]
    fn eq(&self, other: &Nibbles) -> bool {
        self == other.as_slice()
    }
}

impl PartialOrd<[u64]> for Nibbles {
    #[inline]
    fn partial_cmp(&self, other: &[u64]) -> Option<core::cmp::Ordering> {
        self.as_slice().partial_cmp(other)
    }
}

impl PartialOrd<Nibbles> for [u64] {
    #[inline]
    fn partial_cmp(&self, other: &Nibbles) -> Option<core::cmp::Ordering> {
        self.partial_cmp(other.as_slice())
    }
}

impl Borrow<[u64]> for Nibbles {
    #[inline]
    fn borrow(&self) -> &[u64] {
        self.as_slice()
    }
}

impl<Idx> core::ops::Index<Idx> for Nibbles
where
    Repr: core::ops::Index<Idx>,
{
    type Output = <Repr as core::ops::Index<Idx>>::Output;

    #[inline]
    fn index(&self, index: Idx) -> &Self::Output {
        self.0.index(index)
    }
}

#[cfg(feature = "rlp")]
impl alloy_rlp::Encodable for Nibbles {
    #[inline]
    fn length(&self) -> usize {
        alloy_rlp::Encodable::length(self)
    }

    #[inline]
    fn encode(&self, out: &mut dyn alloy_rlp::BufMut) {
        alloy_rlp::Encodable::encode(self, out)
    }
}

#[cfg(feature = "arbitrary")]
impl proptest::arbitrary::Arbitrary for Nibbles {
    type Parameters = proptest::collection::SizeRange;
    type Strategy = proptest::strategy::Map<
        proptest::collection::VecStrategy<core::ops::RangeInclusive<u8>>,
        fn(Vec<u8>) -> Self,
    >;

    #[inline]
    fn arbitrary_with(size: proptest::collection::SizeRange) -> Self::Strategy {
        use proptest::prelude::*;
        proptest::collection::vec(0x0u8..=0xfu8, size).prop_map(Self::from_nibbles_unchecked)
    }
}

impl Nibbles {
    /// Creates a new empty [`Nibbles`] instance.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::new();
    /// assert_eq!(nibbles.len(), 0);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self(SmallVec::new_const(), 0)
    }

    /// Creates a new [`Nibbles`] instance with the given capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::with_capacity(10);
    /// assert_eq!(nibbles.len(), 0);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(SmallVec::with_capacity(capacity), 0)
    }

    /// Returns the total number of nibbles.
    ///
    /// # Examples
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C, 0x0D]);
    /// assert_eq!(nibbles.total_nibbles(), 4);
    /// ```
    #[inline]
    pub fn total_nibbles(&self) -> usize {
        self.1 as usize
    }

    /// Creates a new [`Nibbles`] instance by copying the given bytes.
    ///
    /// # Panics
    ///
    /// Panics if the any of the bytes is not a valid nibble (`0..=0x0f`).
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C, 0x0D]);
    /// assert_eq!(nibbles[..], [0x0A, 0x0B, 0x0C, 0x0D]);
    /// ```
    ///
    /// Invalid values will cause panics:
    ///
    /// ```should_panic
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_nibbles(&[0xFF]);
    /// ```
    #[inline]
    #[track_caller]
    pub fn from_nibbles<T: AsRef<[u8]>>(bytes: T) -> Self {
        let bytes = bytes.as_ref();
        if !bytes.iter().all(|&x| x <= 0x0F) {
            panic_invalid_nibbles();
        }
        Self::from_nibbles_unchecked(bytes)
    }

    /// Creates a new [`Nibbles`] instance by copying the given bytes, without checking their
    /// validity.
    ///
    /// This will not unpack the bytes into nibbles, and will instead store the bytes as-is.
    ///
    /// Note that it is possible to create a [`Nibbles`] instance with invalid nibble values (i.e.
    /// values greater than 0xf) using this method. See [the type docs](Self) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_nibbles_unchecked(&[0x0A, 0x0B, 0x0C, 0x0D]);
    /// assert_eq!(nibbles[..], [0x0A, 0x0B, 0x0C, 0x0D]);
    ///
    /// // Invalid value!
    /// let nibbles = Nibbles::from_nibbles_unchecked(&[0xFF]);
    /// assert_eq!(nibbles[..], [0xFF]);
    /// ```
    #[inline]
    pub fn from_nibbles_unchecked<T: AsRef<[u8]>>(nibbles: T) -> Self {
        let mut res = Self(SmallVec::<[u64; 4]>::new(), 0);

        for &byte in nibbles.as_ref().iter() {
            res.push_unchecked(byte);
        }

        res
    }

    /// Creates a new [`Nibbles`] instance from a byte vector, without checking its validity.
    ///
    /// This will not unpack the bytes into nibbles, and will instead store the bytes as-is.
    ///
    /// Note that it is possible to create a [`Nibbles`] instance with invalid nibble values (i.e.
    /// values greater than 0xf) using this method. See [the type docs](Self) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_vec_unchecked(vec![0x0A, 0x0B, 0x0C, 0x0D]);
    /// assert_eq!(nibbles[..], [0x0A, 0x0B, 0x0C, 0x0D]);
    /// ```
    ///
    /// Invalid values will cause panics:
    ///
    /// ```should_panic
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_vec(vec![0xFF]);
    /// ```
    #[inline]
    #[track_caller]
    pub fn from_vec(vec: Vec<u64>, nibbles: u8) -> Self {
        // if !vec.iter().all(|&x| x <= 0x0FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) {
        //     panic_invalid_nibbles();
        // }
        Self::from_vec_unchecked(vec, nibbles)
    }

    /// Creates a new [`Nibbles`] instance from a byte vector, without checking its validity.
    ///
    /// Note that it is possible to create a [`Nibbles`] instance with invalid nibble values (i.e.
    /// values greater than 0xf) using this method. See [the type docs](Self) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_vec_unchecked(vec![0x0A, 0x0B, 0x0C, 0x0D]);
    /// assert_eq!(nibbles[..], [0x0A, 0x0B, 0x0C, 0x0D]);
    ///
    /// // Invalid value!
    /// let nibbles = Nibbles::from_vec_unchecked(vec![0xFF]);
    /// assert_eq!(nibbles[..], [0xFF]);
    /// ```
    #[inline]
    pub fn from_vec_unchecked(vec: Vec<u64>, nibbles: u8) -> Self {
        Self(SmallVec::from_vec(vec), nibbles)
    }

    /// Converts a byte slice into a [`Nibbles`] instance containing the nibbles (half-bytes or 4
    /// bits) that make up the input byte data.
    ///
    /// # Panics
    ///
    /// Panics if the length of the input is greater than `usize::MAX / 2`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::unpack(&[0xAB, 0xCD]);
    /// assert_eq!(nibbles[..], [0x0A, 0x0B, 0x0C, 0x0D]);
    /// ```
    #[inline]
    pub fn unpack<T: AsRef<[u64]>>(data: T, nibbles: usize) -> Vec<u8> {
        // (0..nibbles as usize)
        //     .map(|l| ((data.as_ref()[l / 16] >> (60 - 4 * (l % 16))) & 0xf) as u8)
        //     .collect();

        let mut result = vec![0u8; nibbles];
        let data_ref = data.as_ref();
        let ptr = result.as_mut_ptr();

        unsafe {
            let ln = data_ref.len() - 1;

            for i in 0..ln {
                // hardcoded inlining
                let pptr = ptr.add(16 * i);
                pptr.write(((data_ref[i] >> 60) & 0xf) as u8);
                pptr.add(1).write(((data_ref[i] >> 56) & 0xf) as u8);
                pptr.add(2).write(((data_ref[i] >> 52) & 0xf) as u8);
                pptr.add(3).write(((data_ref[i] >> 48) & 0xf) as u8);
                pptr.add(4).write(((data_ref[i] >> 44) & 0xf) as u8);
                pptr.add(5).write(((data_ref[i] >> 40) & 0xf) as u8);
                pptr.add(6).write(((data_ref[i] >> 36) & 0xf) as u8);
                pptr.add(7).write(((data_ref[i] >> 32) & 0xf) as u8);
                pptr.add(8).write(((data_ref[i] >> 28) & 0xf) as u8);
                pptr.add(9).write(((data_ref[i] >> 24) & 0xf) as u8);
                pptr.add(10).write(((data_ref[i] >> 20) & 0xf) as u8);
                pptr.add(11).write(((data_ref[i] >> 16) & 0xf) as u8);
                pptr.add(12).write(((data_ref[i] >> 12) & 0xf) as u8);
                pptr.add(13).write(((data_ref[i] >> 8) & 0xf) as u8);
                pptr.add(14).write(((data_ref[i] >> 4) & 0xf) as u8);
                pptr.add(15).write((data_ref[i] & 0xf) as u8);
            }

            let end = if nibbles % 16 == 0 { 16 } else { nibbles % 16 };
            let pptr = ptr.add(16 * ln);

            for i in 0..end {
                pptr.add(i).write(((data_ref[ln] >> (60 - 4 * i)) & 0xf) as u8);
            }
        }

        result
    }

    /// Packs the nibbles into the given slice.
    ///
    /// This method combines each pair of consecutive nibbles into a single byte,
    /// effectively reducing the size of the data by a factor of two.
    /// If the number of nibbles is odd, the last nibble is shifted left by 4 bits and
    /// added to the packed byte vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C, 0x0D]);
    /// assert_eq!(nibbles.pack()[..], [0xAB, 0xCD]);
    /// ```
    #[inline]
    pub fn pack(&self) -> SmallVec<[u64; 4]> {
        self.0.clone()
    }

    /// Packs the nibbles into the given slice.
    ///
    /// See [`pack`](Self::pack) for more information.
    ///
    /// # Panics
    ///
    /// Panics if the slice is not at least `(self.len() + 1) / 2` bytes long.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C, 0x0D]);
    /// let mut packed = [0; 2];
    /// nibbles.pack_to(&mut packed);
    /// assert_eq!(packed[..], [0xAB, 0xCD]);
    /// ```
    #[inline]
    #[track_caller]
    pub fn pack_to(&self, ptr: &mut [u64]) {
        assert!(ptr.len() >= self.len());
        ptr[..self.len()].copy_from_slice(&self.0);
    }

    /// Gets the byte at the given index by combining two consecutive nibbles.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// let nibbles = Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C, 0x0D]);
    /// assert_eq!(nibbles.get_byte(0), Some(0xAB));
    /// assert_eq!(nibbles.get_byte(1), Some(0xBC));
    /// assert_eq!(nibbles.get_byte(2), Some(0xCD));
    /// assert_eq!(nibbles.get_byte(3), None);
    /// ```
    #[inline]
    pub fn get_byte(&self, i: usize) -> Option<u8> {
        if (i < usize::MAX) & (i < 8 * self.len()) {
            Some((self.0[i >> 3] >> (60 - 8 * (i % 8))) as u8)
        } else {
            None
        }
    }

    fn get_byte_unchecked(&self, i: usize) -> u8 {
        debug_assert!(i < usize::MAX);
        debug_assert!(i < 8 * self.len());
        (self.0[i >> 3] >> (60 - 8 * (i % 8))) as u8
    }

    /// Encodes a given path leaf as a compact array of bytes, where each byte represents two
    /// "nibbles" (half-bytes or 4 bits) of the original hex data, along with additional information
    /// about the leaf itself.
    ///
    /// The method takes the following input:
    /// `is_leaf`: A boolean value indicating whether the current node is a leaf node or not.
    ///
    /// The first byte of the encoded vector is set based on the `is_leaf` flag and the parity of
    /// the hex data length (even or odd number of nibbles).
    ///  - If the node is an extension with even length, the header byte is `0x00`.
    ///  - If the node is an extension with odd length, the header byte is `0x10 + <first nibble>`.
    ///  - If the node is a leaf with even length, the header byte is `0x20`.
    ///  - If the node is a leaf with odd length, the header byte is `0x30 + <first nibble>`.
    ///
    /// If there is an odd number of nibbles, store the first nibble in the lower 4 bits of the
    /// first byte of encoded.
    ///
    /// # Returns
    ///
    /// A vector containing the compact byte representation of the nibble sequence, including the
    /// header byte.
    ///
    /// This vector's length is `self.len() / 2 + 1`. For stack-allocated nibbles, this is at most
    /// 33 bytes, so 36 was chosen as the stack capacity to round up to the next usize-aligned
    /// size.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nybbles::Nibbles;
    /// // Extension node with an even path length:
    /// let nibbles = Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C, 0x0D]);
    /// assert_eq!(nibbles.encode_path_leaf(false)[..], [0x00, 0xAB, 0xCD]);
    ///
    /// // Extension node with an odd path length:
    /// let nibbles = Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C]);
    /// assert_eq!(nibbles.encode_path_leaf(false)[..], [0x1A, 0xBC]);
    ///
    /// // Leaf node with an even path length:
    /// let nibbles = Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C, 0x0D]);
    /// assert_eq!(nibbles.encode_path_leaf(true)[..], [0x20, 0xAB, 0xCD]);
    ///
    /// // Leaf node with an odd path length:
    /// let nibbles = Nibbles::from_nibbles(&[0x0A, 0x0B, 0x0C]);
    /// assert_eq!(nibbles.encode_path_leaf(true)[..], [0x3A, 0xBC]);
    /// ```
    #[inline]
    pub fn encode_path_leaf(&self, is_leaf: bool) -> SmallVec<[u8; 36]> {
        let encoded_len = (self.1 / 2 + 1) as usize;
        let mut encoded = SmallVec::with_capacity(encoded_len);
        // SAFETY: enough capacity.
        unsafe { self.encode_path_leaf_to(is_leaf, encoded.as_mut_ptr()) };
        // SAFETY: within capacity and `encode_path_leaf_to` initialized the memory.
        unsafe { encoded.set_len(encoded_len) };
        encoded
    }

    /// # Safety
    ///
    /// `ptr` must be valid for at least `self.len() / 2 + 1` bytes.
    #[inline]
    unsafe fn encode_path_leaf_to(&self, is_leaf: bool, ptr: *mut u8) {
        let sz = self.1 as usize;
        let odd_nibbles = sz % 2 != 0;
        *ptr = self.encode_path_leaf_first_byte(is_leaf, odd_nibbles);
        let pptr = unsafe { core::slice::from_raw_parts_mut(ptr, sz / 2 + 1) };
        let mut cnt = if odd_nibbles { 1 } else { 0 };

        while cnt < sz {
            let i = cnt / 16;
            let shift = 60 - (cnt % 16) * 4;
            let a = ((self.0[i] >> shift) & 0xf) as u8;

            if cnt < sz - 1 {
                pptr[cnt / 2 + 1] = 0;
            }

            match (odd_nibbles, cnt % 2 == 0) {
                (true, false) | (false, true) => {
                    pptr[cnt / 2 + 1] |= a << 4;
                }
                (true, true) | (false, false) => {
                    pptr[cnt / 2] |= a;
                }
            }

            cnt += 1;
        }
    }

    #[inline]
    fn encode_path_leaf_first_byte(&self, is_leaf: bool, odd_nibbles: bool) -> u8 {
        match (is_leaf, odd_nibbles) {
            (true, true) => 0x30 | ((self[0] >> 60) as u8),
            (true, false) => 0x20,
            (false, true) => 0x10 | ((self[0] >> 60) as u8),
            (false, false) => 0x00,
        }
    }

    /// Increments the nibble sequence by one.
    #[inline]
    pub fn increment(&self) -> Option<Self> {
        let mut incremented = self.clone();

        for nibble in incremented.0.iter_mut().rev() {
            debug_assert!(*nibble <= 0xf);
            if *nibble < 0xf {
                *nibble += 1;
                return Some(incremented);
            } else {
                *nibble = 0;
            }
        }

        None
    }

    /// The last element of the hex vector is used to determine whether the nibble sequence
    /// represents a leaf or an extension node. If the last element is 0x10 (16), then it's a leaf.
    #[inline]
    pub fn is_leaf(&self) -> bool {
        self.last() == Some(16)
    }

    /// Returns `true` if this nibble sequence starts with the given prefix.
    #[inline]
    pub fn has_prefix(&self, other: &[u64]) -> bool {
        self.starts_with(other)
    }

    /// Returns the nibble at the given index.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
    #[inline]
    #[track_caller]
    pub fn at(&self, i: usize) -> usize {
        self[i] as usize
    }

    /// Sets the nibble at the given index.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds, or if `value` is not a valid nibble (`0..=0x0f`).
    #[inline]
    #[track_caller]
    pub fn set_at(&mut self, i: usize, value: u64) {
        self.set_at_unchecked(i, value);
    }

    /// Sets the nibble at the given index, without checking its validity.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
    #[inline]
    #[track_caller]
    pub fn set_at_unchecked(&mut self, i: usize, value: u64) {
        self.0[i] = value;
    }

    /// Returns the first nibble of this nibble sequence.
    #[inline]
    pub fn first(&self) -> Option<u64> {
        self.0.first().copied().and_then(|seq| Some(seq & (0xf << 60))).or(None)
    }

    /// Returns the last nibble of this nibble sequence.
    #[inline]
    pub fn last(&self) -> Option<u64> {
        if self.1 == 0 {
            return None;
        }

        let last_idx = (self.1 / 16) as usize;
        let pos = 64 - (self.1 % 16) * 4;

        Some((self.0[last_idx] >> pos) & 0xf)
    }

    /// Returns the length of the common prefix between this nibble sequence and the given.
    #[inline]
    pub fn common_prefix_length(&self, other: &[u64]) -> usize {
        let len = core::cmp::min(self.len(), other.len());
        for i in 0..len {
            if self[i] != other[i] {
                return i;
            }
        }
        len
    }

    /// Returns a reference to the underlying byte slice.
    #[inline]
    pub fn as_slice(&self) -> &[u64] {
        &self.0
    }

    /// Returns a mutable reference to the underlying byte slice.
    ///
    /// Note that it is possible to create invalid [`Nibbles`] instances using this method. See
    /// [the type docs](Self) for more details.
    #[inline]
    pub fn as_mut_slice_unchecked(&mut self) -> &mut [u64] {
        &mut self.0
    }

    /// Returns a mutable reference to the underlying byte vector.
    ///
    /// Note that it is possible to create invalid [`Nibbles`] instances using this method. See
    /// [the type docs](Self) for more details.
    #[inline]
    pub fn as_mut_vec_unchecked(&mut self) -> &mut Repr {
        &mut self.0
    }

    /// Slice the current nibbles within the provided index range.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    #[inline]
    #[track_caller]
    pub fn slice<I>(&self, range: I) -> &[u64]
    where
        Self: Index<I, Output = [u64]>,
    {
        &self[range]
    }

    /// Join two nibbles together.
    #[inline]
    pub fn join(&self, b: &Self) -> Self {
        let mut nibbles = SmallVec::with_capacity(self.len() + b.len());
        nibbles.extend_from_slice(self);
        nibbles.extend_from_slice(b);
        Self(nibbles, self.1 + b.1)
    }

    /// Pushes a nibble to the end of the current nibbles.
    ///
    /// # Panics
    ///
    /// Panics if the nibble is not a valid nibble (`0..=0x0f`).
    #[inline]
    #[track_caller]
    pub fn push(&mut self, nibble: u8) {
        assert!(nibble <= 0xf);
        self.push_unchecked(nibble);
    }

    /// Pushes a nibble to the end of the current nibbles without checking its validity.
    ///
    /// Note that it is possible to create invalid [`Nibbles`] instances using this method. See
    /// [the type docs](Self) for more details.
    #[inline]
    pub fn push_unchecked(&mut self, nibble: u8) {
        if self.0.len() == 0 {
            self.0.push(0);
            self.0[0] |= (nibble as u64) << 60;
            self.1 += 1;
            return;
        }

        let last_idx = (self.1 / 16) as usize;
        let pos = 60 - (self.1 % 16) * 4;

        if pos == 60 && self.len() == last_idx {
            self.0.push(0);
            self.0[last_idx] = self.0[last_idx] | ((nibble as u64) << 60);
            self.1 += 1;
            return;
        }

        self.0[last_idx] = self.0[last_idx] | ((nibble as u64) << pos);
        self.1 += 1;
    }

    /// Pops a nibble from the end of the current nibbles.
    #[inline]
    pub fn pop(&mut self) -> Option<u8> {
        if self.0.len() == 0 {
            return None;
        }

        let last_idx = (self.1 / 16) as usize;
        let pos = 64 - (self.1 % 16) * 4;

        let nibble = ((self.0[last_idx] >> pos) & 0xf) as u8;

        self.0[last_idx] &= !(0xf << pos);
        self.1 -= 1;

        Some(nibble)
    }

    /// Extend the current nibbles with another nibbles.
    #[inline]
    pub fn extend_from_slice(&mut self, b: &Nibbles) {
        self.0.extend_from_slice(b.as_slice());
    }

    /// Extend the current nibbles with another byte slice.
    ///
    /// Note that it is possible to create invalid [`Nibbles`] instances using this method. See
    /// [the type docs](Self) for more details.
    #[inline]
    pub fn extend_from_slice_unchecked(&mut self, b: &[u64]) {
        self.0.extend_from_slice(b);
    }

    /// Truncates the current nibbles to the given length.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        self.0.truncate(new_len);
    }

    /// Clears the current nibbles.
    #[inline]
    pub fn clear(&mut self) {
        self.0.clear();
    }
}

#[cold]
#[track_caller]
const fn panic_invalid_nibbles() -> ! {
    panic!("attempted to create invalid nibbles");
}

#[cfg(test)]
mod tests {
    use super::*;
    use hex_literal::hex;

    #[test]
    fn hashed_regression() {
        let nibbles = Nibbles::from_nibbles(hex!("05010406040a040203030f010805020b050c04070003070e0909070f010b0a0805020301070c0a0902040b0f000f0006040a04050f020b090701000a0a040b"));
        let path = nibbles.encode_path_leaf(true);
        let expected = hex!("351464a4233f1852b5c47037e997f1ba852317ca924bf0f064a45f2b9710aa4b");
        assert_eq!(path[..], expected);
    }

    #[test]
    fn unpack_nibbles() {
        let tests: [(&[u64], usize, &[u8]); 2] = [
            (&[0xaaaaaaaaaaaaaaaa], 16, &[0xa; 16]),
            (
                &[0xbaaaaaaaaaaaaaaa, 0x0],
                17,
                &[
                    0xb, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa, 0xa,
                    0x0,
                ],
            ),
        ];

        for (input, size, expected) in tests {
            let nibbles = Nibbles::unpack(input, size);
            assert_eq!(nibbles, expected);
        }
    }

    #[test]
    fn pack_nibbles() {
        let tests = [
            (&[][..], &[][..]),
            (&[0xa], &[0xa << 60]),
            (&[0xa, 0x0], &[0xa0 << 56]),
            (&[0xa, 0xb], &[0xab << 56]),
            (&[0xa, 0xb, 0x2], &[0xab20 << 48]),
            (&[0xa, 0xb, 0x2, 0x0], &[0xab20 << 48]),
            (&[0xa, 0xb, 0x2, 0x7], &[0xab27 << 48]),
        ];
        for (input, expected) in tests {
            assert!(input.iter().all(|&x| x <= 0xf));
            let nibbles = Nibbles::from_nibbles(input);
            let encoded = nibbles.pack();
            assert_eq!(&encoded[..], expected);
        }
    }

    #[test]
    fn slice() {
        const RAW: &[u8] = &hex!("05010406040a040203030f010805020b050c04070003070e0909070f010b0a0805020301070c0a0902040b0f000f0006040a04050f020b090701000a0a040b");

        #[track_caller]
        fn test_slice<I>(range: I, expected: &[u8])
        where
            Nibbles: Index<I, Output = [u64]>,
        {
            let nibbles = Nibbles::from_nibbles_unchecked(RAW);
            let sliced = nibbles.slice(range);
            assert_eq!(sliced, Nibbles::from_nibbles(expected).pack().as_slice());
        }

        test_slice(0..0, &[]);
        test_slice(0..1, &hex!("05010406040a040203030f010805020b"));
        test_slice(1..1, &[]);
        test_slice(1..=1, &hex!("050c04070003070e0909070f010b0a08"));
        test_slice(
            0..=1,
            &hex!("05010406040a040203030f010805020b050c04070003070e0909070f010b0a08"),
        );
        test_slice(0..2, &hex!("05010406040a040203030f010805020b050c04070003070e0909070f010b0a08"));
        test_slice(..0, &[]);
        test_slice(..1, &hex!("05010406040a040203030f010805020b"));
        test_slice(..=1, &hex!("05010406040a040203030f010805020b050c04070003070e0909070f010b0a08"));
        test_slice(..2, &hex!("05010406040a040203030f010805020b050c04070003070e0909070f010b0a08"));
        test_slice(.., RAW);
        test_slice(..4, RAW);
        test_slice(0.., RAW);
        test_slice(0..4, RAW);
    }

    #[test]
    fn indexing() {
        let mut nibbles = Nibbles::from_nibbles([0x0A]);
        assert_eq!(nibbles.at(0), 0xA << 60);
        nibbles.set_at(0, 0xB << 60);
        assert_eq!(nibbles.at(0), 0xB << 60);
    }

    #[test]
    fn push_pop() {
        let mut nibbles = Nibbles::new();
        nibbles.push(0xA);
        assert_eq!(nibbles[0], 0xA << 60);
        assert_eq!(nibbles.len(), 1);

        assert_eq!(nibbles.pop(), Some(0xA));
        assert_eq!(nibbles.total_nibbles(), 0);

        nibbles.push(0xB);
        assert_eq!(nibbles[0], 0xB << 60);
        assert_eq!(nibbles.len(), 1);

        assert_eq!(nibbles.pop(), Some(0xB));
        assert_eq!(nibbles.total_nibbles(), 0);
    }

    #[test]
    fn get_byte_max() {
        let nibbles = Nibbles::from_nibbles([0x0A, 0x0B, 0x0C, 0x0D]);
        assert_eq!(nibbles.get_byte(usize::MAX), None);
    }

    #[cfg(feature = "arbitrary")]
    mod arbitrary {
        use super::*;
        use proptest::{collection::vec, prelude::*, strategy::ValueTree};

        proptest::proptest! {
            #[test]
            fn pack_unpack_roundtrip(input in vec(0..=0xfu8, 0..64)) {
                let _nibbles = Nibbles::from_nibbles(&input);
                // prop_assert!(nibbles.iter().all(|&nibble| nibble <= 0xf));
                // let packed = nibbles.pack();
                // prop_assert_eq!(&packed[..], input);
            }

            #[test]
            fn encode_path_first_byte(input in vec(0..=0xfu8, 1..64)) {
                prop_assume!(!input.is_empty());
                let input = Nibbles::from_nibbles(input);
                let input_is_odd = input.total_nibbles() % 2 == 1;

                let compact_leaf = input.encode_path_leaf(true);
                let leaf_flag = compact_leaf[0];
                // Check flag
                assert_ne!(leaf_flag & 0x20, 0);
                assert_eq!(input_is_odd, (leaf_flag & 0x10) != 0);
                if input_is_odd {
                    assert_eq!((leaf_flag & 0x0f) as u8, (input.first().unwrap() >> 60 & 0xf) as u8);
                }


                let compact_extension = input.encode_path_leaf(false);
                let extension_flag = compact_extension[0];
                // Check first byte
                assert_eq!(extension_flag & 0x20, 0);
                assert_eq!(input_is_odd, (extension_flag & 0x10) != 0);
                if input_is_odd {
                    assert_eq!((extension_flag & 0x0f) as u8, (input.first().unwrap() >> 60 & 0xf) as u8);
                }
            }
        }

        fn get_bytes(len: usize) -> Vec<u64> {
            proptest::collection::vec(proptest::arbitrary::any::<u64>(), len as usize)
                .new_tree(&mut Default::default())
                .unwrap()
                .current()
        }

        fn unpack_naive(bytes: &[u64], len: usize) -> Vec<u8> {
            (0..len)
                .map(|l| ((bytes.as_ref()[l / 16] >> (60 - 4 * (l % 16))) & 0xf) as u8)
                .collect()
        }

        #[test]
        fn naive_equivalency() {
            for len in [1usize, 2, 4, 32, 128] {
                let bytes = get_bytes(len);
                let nibbles = Nibbles::unpack(&bytes, 16 * (len as usize));
                assert_eq!(unpack_naive(&bytes, 16 * len)[..], nibbles[..]);
                // assert_eq!(
                //     pack_naive(&nibbles[..])[..],
                //     Nibbles::pack(&Nibbles::from_nibbles(&nibbles))[..]
                // );
                println!("OK");
            }
        }
    }
}
