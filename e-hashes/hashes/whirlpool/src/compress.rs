use crate::BLOCK_SIZE;
use core::convert::TryInto;

#[path = "consts.rs"]
mod consts;
use consts::*;

fn compress_block(state: &mut [u64; 8], b: &[u8; BLOCK_SIZE]) {
    let mut k = [0u64; 8];
    let mut block = [0u64; 8];
    let mut s = [0u64; 8];
    let mut l = [0u64; 8];

    for (o, chunk) in block.iter_mut().zip(b.chunks_exact(8)) {
        *o = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    k.copy_from_slice(state);

    for i in 0..8 {
        s[i] = block[i] ^ k[i];
    }

    #[allow(clippy::needless_range_loop)]
    for r in 0..R {
        for i in 0..8 {
            l[i] = C0[(k[(i) % 8] & 0xff) as usize]
                ^ C1[((k[(7 + i) % 8] >> 8) & 0xff) as usize]
                ^ C2[((k[(6 + i) % 8] >> 16) & 0xff) as usize]
                ^ C3[((k[(5 + i) % 8] >> 24) & 0xff) as usize]
                ^ C4[((k[(4 + i) % 8] >> 32) & 0xff) as usize]
                ^ C5[((k[(3 + i) % 8] >> 40) & 0xff) as usize]
                ^ C6[((k[(2 + i) % 8] >> 48) & 0xff) as usize]
                ^ C7[((k[(1 + i) % 8] >> 56) & 0xff) as usize]
                ^ if i == 0 { RC[r] } else { 0 };
        }
        k = l;
        for i in 0..8 {
            l[i] = C0[(s[(i) % 8] & 0xff) as usize]
                ^ C1[((s[(7 + i) % 8] >> 8) & 0xff) as usize]
                ^ C2[((s[(6 + i) % 8] >> 16) & 0xff) as usize]
                ^ C3[((s[(5 + i) % 8] >> 24) & 0xff) as usize]
                ^ C4[((s[(4 + i) % 8] >> 32) & 0xff) as usize]
                ^ C5[((s[(3 + i) % 8] >> 40) & 0xff) as usize]
                ^ C6[((s[(2 + i) % 8] >> 48) & 0xff) as usize]
                ^ C7[((s[(1 + i) % 8] >> 56) & 0xff) as usize]
                ^ k[i];
        }
        s = l;
    }

    for i in 0..8 {
        state[i] ^= s[i] ^ block[i];
    }
}

pub(crate) fn compress(state: &mut [u64; 8], blocks: &[[u8; BLOCK_SIZE]]) {
    for block in blocks {
        compress_block(state, block);
    }
}
#[cfg(test)]
mod tests_rug_425 {
    use super::*;
    use crate::compress::{compress_block, BLOCK_SIZE, R, C0, C1, C2, C3, C4, C5, C6, C7, RC};

    #[test]
    fn test_rug() {
        let mut p0: [u64; 8] = [0x123456789abcdef0, 0xfedcba9876543210, 0x0123456789abcdef, 0xefcdab8967452301, 0x1a2b3c4d5e6f7080, 0x80706f5e4d3c2b1a, 0xa1b2c3d4e5f60798, 0x9807f6e5d4c3b2a1];
        let p1: [u8; BLOCK_SIZE] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
            0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
            0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
            0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
            0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
        ];

        crate::compress::compress_block(&mut p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_426 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: [u64; 8] = [0x123456789ABCDEF0, 0xFEDCBA9876543210, 0x1122334455667788, 0x8877665544332211, 0xAABBCCDDEEFF0011, 0x1100EEFFDDCCBBAA, 0x2233445566778899, 0x9988776655443322];
        let p1: [[u8; BLOCK_SIZE]; 2] = [
            [0u8; BLOCK_SIZE],
            [1u8; BLOCK_SIZE],
        ];

        crate::compress::compress(&mut p0, &p1);
    }
}