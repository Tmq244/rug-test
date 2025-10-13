use super::tables::{T1, T2, T3, T4};
use super::State;
use core::convert::TryInto;

#[inline(always)]
fn round(a: &mut u64, b: &mut u64, c: &mut u64, x: &u64, mul: u8) {
    *c ^= *x;
    let c2: [u8; 8] = c.to_le_bytes();
    let a2 = T1[usize::from(c2[0])]
        ^ T2[usize::from(c2[2])]
        ^ T3[usize::from(c2[4])]
        ^ T4[usize::from(c2[6])];
    let b2 = T4[usize::from(c2[1])]
        ^ T3[usize::from(c2[3])]
        ^ T2[usize::from(c2[5])]
        ^ T1[usize::from(c2[7])];
    *a = a.wrapping_sub(a2);
    *b = b.wrapping_add(b2).wrapping_mul(u64::from(mul));
}

#[inline(always)]
fn pass(a: &mut u64, b: &mut u64, c: &mut u64, x: &[u64; 8], mul: u8) {
    round(a, b, c, &x[0], mul);
    round(b, c, a, &x[1], mul);
    round(c, a, b, &x[2], mul);
    round(a, b, c, &x[3], mul);
    round(b, c, a, &x[4], mul);
    round(c, a, b, &x[5], mul);
    round(a, b, c, &x[6], mul);
    round(b, c, a, &x[7], mul);
}

#[inline(always)]
fn key_schedule(x: &mut [u64; 8]) {
    x[0] = x[0].wrapping_sub(x[7] ^ 0xA5A5_A5A5_A5A5_A5A5);
    x[1] ^= x[0];
    x[2] = x[2].wrapping_add(x[1]);
    x[3] = x[3].wrapping_sub(x[2] ^ ((!x[1]) << 19));
    x[4] ^= x[3];
    x[5] = x[5].wrapping_add(x[4]);
    x[6] = x[6].wrapping_sub(x[5] ^ ((!x[4]) >> 23));
    x[7] ^= x[6];
    x[0] = x[0].wrapping_add(x[7]);
    x[1] = x[1].wrapping_sub(x[0] ^ ((!x[7]) << 19));
    x[2] ^= x[1];
    x[3] = x[3].wrapping_add(x[2]);
    x[4] = x[4].wrapping_sub(x[3] ^ ((!x[2]) >> 23));
    x[5] ^= x[4];
    x[6] = x[6].wrapping_add(x[5]);
    x[7] = x[7].wrapping_sub(x[6] ^ 0x0123_4567_89AB_CDEF);
}

pub(crate) fn compress(state: &mut State, raw_block: &[u8; 64]) {
    let mut block: [u64; 8] = Default::default();
    for (o, chunk) in block.iter_mut().zip(raw_block.chunks_exact(8)) {
        *o = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    let [mut a, mut b, mut c] = *state;

    pass(&mut a, &mut b, &mut c, &block, 5);
    key_schedule(&mut block);
    pass(&mut c, &mut a, &mut b, &block, 7);
    key_schedule(&mut block);
    pass(&mut b, &mut c, &mut a, &block, 9);

    state[0] ^= a;
    state[1] = b.wrapping_sub(state[1]);
    state[2] = c.wrapping_add(state[2]);
}
#[cfg(test)]
mod tests_rug_411 {
    use super::*;

    #[test]
    fn test_round() {
        let mut p0: u64 = 123456789;
        let mut p1: u64 = 987654321;
        let mut p2: u64 = 1122334455;
        let p3: &u64 = &0xdeadbeefcafebabe;
        let p4: u8 = 42;

        crate::compress::round(&mut p0, &mut p1, &mut p2, p3, p4);
    }
}#[cfg(test)]
mod tests_rug_412 {
    use super::*;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789;
        let mut p1: u64 = 987654321;
        let mut p2: u64 = 1122334455;
        let mut p3: [u64; 8] = [0x0001020304050607, 0x08090A0B0C0D0E0F, 0x1011121314151617, 0x18191A1B1C1D1E1F, 0x2021222324252627, 0x28292A2B2C2D2E2F, 0x3031323334353637, 0x38393A3B3C3D3E3F];
        let mut p4: u8 = 3;

        crate::compress::pass(&mut p0, &mut p1, &mut p2, &p3, p4);
    }
}#[cfg(test)]
mod tests_rug_413 {
    use super::*;

    #[test]
    fn test_key_schedule() {
        let mut p0: [u64; 8] = [0x123456789abcdef0, 0xfedcba0987654321, 0x1122334455667788, 0x8877665544332211, 
                                0xaabbccddeeff0011, 0x0011223344556677, 0x99aabbccddeeff00, 0xffeeddccbbaa9988];

        crate::compress::key_schedule(&mut p0);

        // Add assertions here to verify the output if needed
    }
}#[cfg(test)]
mod tests_rug_414 {
    use super::*;

    #[test]
    fn test_compress() {
        let mut p0: [u64; 3] = [123456789, 987654321, 112233445];
        let mut p1: [u8; 64] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,
            0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
            0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F,
            0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
            0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F,
        ];

        compress(&mut p0, &p1);
    }
}