use core::{convert::TryInto, fmt};
use digest::{
    block_buffer::Eager,
    consts::U64,
    core_api::{
        AlgorithmName, Block as GenBlock, BlockSizeUser, Buffer, BufferKindUser, OutputSizeUser,
        TruncSide, UpdateCore, VariableOutputCore,
    },
    HashMarker, InvalidOutputSize, Output,
};

use crate::consts::{BLOCK_SIZE, C};
use crate::table::SHUFFLED_LIN_TABLE;

type Block = [u8; 64];

/// Core block-level Streebog hasher with variable output size.
///
/// Supports initialization only for 32 and 64 byte output sizes,
/// i.e. 256 and 512 bits respectively.
#[derive(Clone)]
pub struct StreebogVarCore {
    h: Block,
    n: [u64; 8],
    sigma: [u64; 8],
}

#[inline(always)]
fn lps(h: &mut Block, n: &Block) {
    for i in 0..64 {
        h[i] ^= n[i];
    }

    let mut buf = [0u64; 8];

    for i in 0..4 {
        for j in 0..8 {
            let b = h[2 * i + 8 * j] as usize;
            buf[2 * i] ^= SHUFFLED_LIN_TABLE[j][b];
            let b = h[2 * i + 1 + 8 * j] as usize;
            buf[2 * i + 1] ^= SHUFFLED_LIN_TABLE[j][b];
        }
    }

    *h = to_bytes(&buf);
}

impl StreebogVarCore {
    fn g(&mut self, n: &Block, m: &Block) {
        let mut key = [0u8; 64];
        let mut block = [0u8; 64];

        key.copy_from_slice(&self.h);
        block.copy_from_slice(m);

        lps(&mut key, n);

        #[allow(clippy::needless_range_loop)]
        for i in 0..12 {
            lps(&mut block, &key);
            lps(&mut key, &C[i]);
        }

        for i in 0..64 {
            self.h[i] ^= block[i] ^ key[i] ^ m[i];
        }
    }

    fn update_sigma(&mut self, m: &Block) {
        let t = from_bytes(m);
        let mut carry = 0;
        adc(&mut self.sigma[0], t[0], &mut carry);
        adc(&mut self.sigma[1], t[1], &mut carry);
        adc(&mut self.sigma[2], t[2], &mut carry);
        adc(&mut self.sigma[3], t[3], &mut carry);
        adc(&mut self.sigma[4], t[4], &mut carry);
        adc(&mut self.sigma[5], t[5], &mut carry);
        adc(&mut self.sigma[6], t[6], &mut carry);
        adc(&mut self.sigma[7], t[7], &mut carry);
    }

    fn update_n(&mut self, len: u64) {
        let mut carry = 0;
        // note: `len` can not be bigger than block size,
        // so `8*len` will never overflow
        adc(&mut self.n[0], 8 * len, &mut carry);
        adc(&mut self.n[1], 0, &mut carry);
        adc(&mut self.n[2], 0, &mut carry);
        adc(&mut self.n[3], 0, &mut carry);
        adc(&mut self.n[4], 0, &mut carry);
        adc(&mut self.n[5], 0, &mut carry);
        adc(&mut self.n[6], 0, &mut carry);
        adc(&mut self.n[7], 0, &mut carry);
    }

    fn compress(&mut self, block: &[u8; 64], msg_len: u64) {
        self.g(&to_bytes(&self.n), block);
        self.update_n(msg_len);
        self.update_sigma(block);
    }
}

impl HashMarker for StreebogVarCore {}

impl BlockSizeUser for StreebogVarCore {
    type BlockSize = U64;
}

impl BufferKindUser for StreebogVarCore {
    type BufferKind = Eager;
}

impl UpdateCore for StreebogVarCore {
    #[inline]
    fn update_blocks(&mut self, blocks: &[GenBlock<Self>]) {
        for block in blocks {
            self.compress(block.as_ref(), BLOCK_SIZE as u64);
        }
    }
}

impl OutputSizeUser for StreebogVarCore {
    type OutputSize = U64;
}

impl VariableOutputCore for StreebogVarCore {
    const TRUNC_SIDE: TruncSide = TruncSide::Right;

    #[inline]
    fn new(output_size: usize) -> Result<Self, InvalidOutputSize> {
        let h = match output_size {
            32 => [1; 64],
            64 => [0; 64],
            _ => return Err(InvalidOutputSize),
        };
        let (n, sigma) = Default::default();
        Ok(Self { h, n, sigma })
    }

    #[inline]
    fn finalize_variable_core(&mut self, buffer: &mut Buffer<Self>, out: &mut Output<Self>) {
        let pos = buffer.get_pos();
        let block = buffer.pad_with_zeros();
        block[pos] = 1;
        self.compress(block.as_ref(), pos as u64);
        self.g(&[0u8; 64], &to_bytes(&self.n));
        self.g(&[0u8; 64], &to_bytes(&self.sigma));
        out.copy_from_slice(&self.h);
    }
}

impl AlgorithmName for StreebogVarCore {
    #[inline]
    fn write_alg_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Streebog")
    }
}

impl fmt::Debug for StreebogVarCore {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("StreebogVarCore { ... }")
    }
}

#[inline(always)]
fn adc(a: &mut u64, b: u64, carry: &mut u64) {
    let ret = (*a as u128) + (b as u128) + (*carry as u128);
    *a = ret as u64;
    *carry = (ret >> 64) as u64;
}

#[inline(always)]
fn to_bytes(b: &[u64; 8]) -> Block {
    let mut t = [0; 64];
    for (chunk, v) in t.chunks_exact_mut(8).zip(b.iter()) {
        chunk.copy_from_slice(&v.to_le_bytes());
    }
    t
}

#[inline(always)]
fn from_bytes(b: &Block) -> [u64; 8] {
    let mut t = [0u64; 8];
    for (v, chunk) in t.iter_mut().zip(b.chunks_exact(8)) {
        *v = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    t
}
#[cfg(test)]
mod tests_rug_399 {
    use super::*;
    
    #[test]
    fn test_lps() {
        let mut h: [u8; 64] = [
            0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0,
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
            0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
            0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5, 0x96, 0x87,
            0x78, 0x69, 0x5a, 0x4b, 0x3c, 0x2d, 0x1e, 0x0f,
            0xf1, 0xe0, 0xd3, 0xc2, 0xb5, 0xa4, 0x97, 0x86,
        ];
        let n: [u8; 64] = [
            0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88,
            0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x00,
            0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5, 0x96, 0x87,
            0x78, 0x69, 0x5a, 0x4b, 0x3c, 0x2d, 0x1e, 0x0f,
            0xf1, 0xe0, 0xd3, 0xc2, 0xb5, 0xa4, 0x97, 0x86,
            0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88,
            0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x00,
            0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5, 0x96, 0x87,
        ];

        crate::core_api::lps(&mut h, &n);
    }
}#[cfg(test)]
mod tests_rug_400 {
    use super::*;

    #[test]
    fn test_adc() {
        let mut a: u64 = 0x123456789abcdef0;
        let b: u64 = 0xfedcba9876543210;
        let mut carry: u64 = 1;

        crate::core_api::adc(&mut a, b, &mut carry);

        // Optional: Add assertions to verify the results
        assert_eq!(a, 0x1111111111111110);
        assert_eq!(carry, 0x1);
    }
}#[cfg(test)]
mod tests_rug_401 {
    use super::*;

    #[test]
    fn test_rug() {
        let mut p0: [u64; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

        crate::core_api::to_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_402 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 64] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,
            0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
            0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F,
            0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
            0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F,
        ];

        let _result = crate::core_api::from_bytes(&p0);

    }
}#[cfg(test)]
mod tests_rug_403 {
    use super::*;
    use crate::core_api::{StreebogVarCore, Block};
    use crate::digest::generic_array::{ArrayLength, GenericArray};
    use crate::digest::typenum::U64;
    
    #[test]
    fn test_rug() {
        let mut p0 = StreebogVarCore::new(64).unwrap();
        let p1: &Block = &[0u8; 64];
        let p2: &Block = &[1u8; 64];

        p0.g(p1, p2);
    }
}