#![allow(clippy::many_single_char_names)]
use core::{convert::TryInto, fmt};
use digest::{
    block_buffer::Eager,
    core_api::{
        AlgorithmName, Block as TBlock, BlockSizeUser, Buffer, BufferKindUser, FixedOutputCore,
        OutputSizeUser, Reset, UpdateCore,
    },
    typenum::{Unsigned, U32},
    HashMarker, Output,
};

use crate::params::{Block, Gost94Params, SBox};

const C: Block = [
    0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00,
    0x00, 0xff, 0xff, 0x00, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0x00, 0xff, 0xff, 0x00, 0xff,
];

fn sbox(a: u32, s: &SBox) -> u32 {
    let mut v = 0;

    #[allow(clippy::needless_range_loop)]
    for i in 0..8 {
        let shft = 4 * i;
        let k = ((a & (0b1111u32 << shft)) >> shft) as usize;
        v += u32::from(s[i][k]) << shft;
    }

    v
}

fn g(a: u32, k: u32, s: &SBox) -> u32 {
    sbox(a.wrapping_add(k), s).rotate_left(11)
}

#[allow(clippy::needless_range_loop)]
fn encrypt(msg: &mut [u8], key: Block, sbox: &SBox) {
    let mut k = [0u32; 8];
    let mut a = u32::from_le_bytes(msg[0..4].try_into().unwrap());
    let mut b = u32::from_le_bytes(msg[4..8].try_into().unwrap());
    for (o, chunk) in k.iter_mut().zip(key.chunks_exact(4)) {
        *o = u32::from_le_bytes(chunk.try_into().unwrap());
    }

    for _ in 0..3 {
        for i in 0..8 {
            let t = b ^ g(a, k[i], sbox);
            b = a;
            a = t;
        }
    }
    for i in (0..8).rev() {
        let t = b ^ g(a, k[i], sbox);
        b = a;
        a = t;
    }

    msg[0..4].copy_from_slice(&b.to_le_bytes());
    msg[4..8].copy_from_slice(&a.to_le_bytes());
}

fn x(a: &Block, b: &Block) -> Block {
    let mut out = Block::default();
    for i in 0..32 {
        out[i] = a[i] ^ b[i];
    }
    out
}

fn x_mut(a: &mut Block, b: &Block) {
    for i in 0..32 {
        a[i] ^= b[i];
    }
}

fn a(x: Block) -> Block {
    let mut out = Block::default();
    out[..24].clone_from_slice(&x[8..]);
    for i in 0..8 {
        out[24 + i] = x[i] ^ x[i + 8];
    }
    out
}

fn p(y: Block) -> Block {
    let mut out = Block::default();

    for i in 0..4 {
        for k in 0..8 {
            out[i + 4 * k] = y[8 * i + k];
        }
    }
    out
}

fn psi(block: &mut Block) {
    let mut out = Block::default();
    out[..30].copy_from_slice(&block[2..]);
    out[30..].copy_from_slice(&block[..2]);

    out[30] ^= block[2];
    out[31] ^= block[3];

    out[30] ^= block[4];
    out[31] ^= block[5];

    out[30] ^= block[6];
    out[31] ^= block[7];

    out[30] ^= block[24];
    out[31] ^= block[25];

    out[30] ^= block[30];
    out[31] ^= block[31];

    block.copy_from_slice(&out);
}

#[inline(always)]
fn adc(a: &mut u64, b: u64, carry: &mut u64) {
    let ret = (*a as u128) + (b as u128) + (*carry as u128);
    *a = ret as u64;
    *carry = (ret >> 64) as u64;
}

/// Core GOST94 algorithm generic over parameters.
#[derive(Clone)]
pub struct Gost94Core<P: Gost94Params> {
    h: Block,
    n: [u64; 4],
    sigma: [u64; 4],
    _m: core::marker::PhantomData<P>,
}

impl<P: Gost94Params> Gost94Core<P> {
    fn shuffle(&mut self, m: &Block, s: &Block) {
        let mut res = Block::default();
        res.copy_from_slice(s);
        for _ in 0..12 {
            psi(&mut res);
        }
        x_mut(&mut res, m);
        psi(&mut res);
        x_mut(&mut self.h, &res);
        for _ in 0..61 {
            psi(&mut self.h);
        }
    }

    fn f(&mut self, m: &Block) {
        let mut s = Block::default();
        s.copy_from_slice(&self.h);
        let k = p(x(&self.h, m));
        encrypt(&mut s[0..8], k, &P::S_BOX);

        let u = a(self.h);
        let v = a(a(*m));
        let k = p(x(&u, &v));
        encrypt(&mut s[8..16], k, &P::S_BOX);

        let mut u = a(u);
        x_mut(&mut u, &C);
        let v = a(a(v));
        let k = p(x(&u, &v));
        encrypt(&mut s[16..24], k, &P::S_BOX);

        let u = a(u);
        let v = a(a(v));
        let k = p(x(&u, &v));
        encrypt(&mut s[24..32], k, &P::S_BOX);

        self.shuffle(m, &s);
    }

    fn update_sigma(&mut self, m: &Block) {
        let mut carry = 0;
        for (a, chunk) in self.sigma.iter_mut().zip(m.chunks_exact(8)) {
            let b = u64::from_le_bytes(chunk.try_into().unwrap());
            adc(a, b, &mut carry);
        }
    }

    fn update_n(&mut self, len: usize) {
        let mut carry = 0;
        adc(&mut self.n[0], (len as u64) << 3, &mut carry);
        adc(&mut self.n[1], (len as u64) >> 61, &mut carry);
        adc(&mut self.n[2], 0, &mut carry);
        adc(&mut self.n[3], 0, &mut carry);
    }

    #[inline(always)]
    fn compress(&mut self, block: &[u8; 32]) {
        self.f(block);
        self.update_sigma(block);
    }
}

impl<P: Gost94Params> HashMarker for Gost94Core<P> {}

impl<P: Gost94Params> BlockSizeUser for Gost94Core<P> {
    type BlockSize = U32;
}

impl<P: Gost94Params> BufferKindUser for Gost94Core<P> {
    type BufferKind = Eager;
}

impl<P: Gost94Params> OutputSizeUser for Gost94Core<P> {
    type OutputSize = U32;
}

impl<P: Gost94Params> UpdateCore for Gost94Core<P> {
    #[inline]
    fn update_blocks(&mut self, blocks: &[TBlock<Self>]) {
        let len = Self::BlockSize::USIZE * blocks.len();
        self.update_n(len);
        blocks.iter().for_each(|b| self.compress(b.as_ref()));
    }
}

impl<P: Gost94Params> FixedOutputCore for Gost94Core<P> {
    #[inline]
    fn finalize_fixed_core(&mut self, buffer: &mut Buffer<Self>, out: &mut Output<Self>) {
        if buffer.get_pos() != 0 {
            self.update_n(buffer.get_pos());
            self.compress(buffer.pad_with_zeros().as_ref());
        }

        let mut buf = Block::default();
        for (o, v) in buf.chunks_exact_mut(8).zip(self.n.iter()) {
            o.copy_from_slice(&v.to_le_bytes());
        }
        self.f(&buf);

        for (o, v) in buf.chunks_exact_mut(8).zip(self.sigma.iter()) {
            o.copy_from_slice(&v.to_le_bytes());
        }
        self.f(&buf);

        out.copy_from_slice(&self.h);
    }
}

impl<P: Gost94Params> Default for Gost94Core<P> {
    #[inline]
    fn default() -> Self {
        Self {
            h: P::H0,
            n: Default::default(),
            sigma: Default::default(),
            _m: Default::default(),
        }
    }
}

impl<P: Gost94Params> Reset for Gost94Core<P> {
    #[inline]
    fn reset(&mut self) {
        *self = Default::default();
    }
}

impl<P: Gost94Params> AlgorithmName for Gost94Core<P> {
    fn write_alg_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(P::NAME)
    }
}

impl<P: Gost94Params> fmt::Debug for Gost94Core<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(P::NAME)?;
        f.write_str("Core { .. }")
    }
}
#[cfg(test)]
mod tests_rug_119 {
    use super::*;
    
    #[test]
    fn test_sbox() {
        let mut p0: u32 = 0x12345678;
        let mut p1: [[u8; 16]; 8] = [
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
        ];

        crate::gost94_core::sbox(p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_121 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 8] = [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF];
        let mut p1: [u8; 32] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F
        ];
        let mut p2: [[u8; 16]; 8] = [
            [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F],
            [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F],
            [0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F],
            [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F],
            [0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F],
            [0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F],
            [0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F],
            [0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F]
        ];

        crate::gost94_core::encrypt(&mut p0, Block::from(p1), &p2);
    }
}#[cfg(test)]
mod tests_rug_122 {
    use super::*;
    use crate::gost94_core::{x, Block};

    #[test]
    fn test_rug() {
        let p0: [u8; 32] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 
                            17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32];
        let p1: [u8; 32] = [32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17,
                            16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1];

        let result = x(&Block::from(p0), &Block::from(p1));

        // Example assertion (you can modify this based on your expected output)
        assert_ne!(result, Block::default());
    }
}#[cfg(test)]
mod tests_rug_123 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 32] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 
                                0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,
                                0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
                                0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20];
        let p1: [u8; 32] =     [0xFF, 0xFE, 0xFD, 0xFC, 0xFB, 0xFA, 0xF9, 0xF8,
                                0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1, 0xF0,
                                0xEF, 0xEE, 0xED, 0xEC, 0xEB, 0xEA, 0xE9, 0xE8,
                                0xE7, 0xE6, 0xE5, 0xE4, 0xE3, 0xE2, 0xE1, 0xE0];
        
        crate::gost94_core::x_mut(&mut p0, &p1);

        let expected: [u8; 32] = [0xFE, 0xFC, 0xFA, 0xF8, 0xF4, 0xF0, 0xED, 0xF0,
                                  0xF6, 0xF4, 0xF2, 0xF0, 0xEE, 0xEC, 0xEA, 0xE0,
                                  0xF4, 0xFA, 0xFC, 0xFE, 0xF0, 0xEF, 0xF8, 0xF8,
                                  0xF2, 0xF6, 0xF5, 0xFA, 0xE3, 0xE1, 0xE1, 0x20];
        
        assert_eq!(p0, expected);
    }
}#[cfg(test)]
mod tests_rug_124 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 32] = [
            0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF,
            0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54, 0x32, 0x10,
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF
        ];

        let result = crate::gost94_core::a(p0);
        
        // Example assertion (you can modify it based on expected output)
        assert_eq!(result, [0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54, 0x32, 0x10,
                            0x01, 0x00, 0x21, 0x21, 0x45, 0x55, 0x67, 0x77,
                            0x89, 0x89, 0xAB, 0xAB, 0xCD, 0xCD, 0xEF, 0xEF,
                            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77]);
    }
}#[cfg(test)]
mod tests_rug_125 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 32] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,
        ];

        crate::gost94_core::p(p0);
    }
}#[cfg(test)]
mod tests_rug_126 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 32] = [
            0x1f, 0xa6, 0x8b, 0xc2, 0x3d, 0x7b, 0x9a, 0xf4,
            0x3d, 0x5e, 0xad, 0x03, 0x13, 0xef, 0xea, 0x67,
            0xb8, 0xd5, 0x7f, 0x2a, 0x0d, 0x4b, 0xa9, 0xc5,
            0xf3, 0x14, 0xcd, 0xe2, 0x6c, 0x8e, 0x9f, 0x7a
        ];

        crate::gost94_core::psi(&mut p0);

        // Add assertions to verify the result if necessary
    }
}#[cfg(test)]
mod tests_rug_127 {
    use super::*;
    
    #[test]
    fn test_adc() {
        let mut p0: u64 = 123456789;
        let p1: u64 = 987654321;
        let mut p2: u64 = 1;

        crate::gost94_core::adc(&mut p0, p1, &mut p2);
    }
}