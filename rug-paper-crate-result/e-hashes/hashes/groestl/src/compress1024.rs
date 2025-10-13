#![allow(clippy::needless_range_loop)]
use crate::table::TABLE;
use core::{convert::TryInto, u64};

pub(crate) const COLS: usize = 16;
const ROUNDS: u64 = 14;

#[inline(always)]
fn column(x: &[u64; COLS], c: [usize; 8]) -> u64 {
    let mut t = 0;
    for i in 0..8 {
        let sl = 8 * (7 - i);
        let idx = ((x[c[i]] >> sl) & 0xFF) as usize;
        t ^= TABLE[i][idx];
    }
    t
}

#[inline(always)]
fn rndq(mut x: [u64; COLS], r: u64) -> [u64; COLS] {
    for i in 0..COLS {
        x[i] ^= u64::MAX.wrapping_sub((i as u64) << 4) ^ r;
    }
    [
        column(&x, [1, 3, 5, 11, 0, 2, 4, 6]),
        column(&x, [2, 4, 6, 12, 1, 3, 5, 7]),
        column(&x, [3, 5, 7, 13, 2, 4, 6, 8]),
        column(&x, [4, 6, 8, 14, 3, 5, 7, 9]),
        column(&x, [5, 7, 9, 15, 4, 6, 8, 10]),
        column(&x, [6, 8, 10, 0, 5, 7, 9, 11]),
        column(&x, [7, 9, 11, 1, 6, 8, 10, 12]),
        column(&x, [8, 10, 12, 2, 7, 9, 11, 13]),
        column(&x, [9, 11, 13, 3, 8, 10, 12, 14]),
        column(&x, [10, 12, 14, 4, 9, 11, 13, 15]),
        column(&x, [11, 13, 15, 5, 10, 12, 14, 0]),
        column(&x, [12, 14, 0, 6, 11, 13, 15, 1]),
        column(&x, [13, 15, 1, 7, 12, 14, 0, 2]),
        column(&x, [14, 0, 2, 8, 13, 15, 1, 3]),
        column(&x, [15, 1, 3, 9, 14, 0, 2, 4]),
        column(&x, [0, 2, 4, 10, 15, 1, 3, 5]),
    ]
}

#[inline(always)]
fn rndp(mut x: [u64; COLS], r: u64) -> [u64; COLS] {
    for i in 0..COLS {
        x[i] ^= ((i as u64) << 60) ^ r;
    }
    [
        column(&x, [0, 1, 2, 3, 4, 5, 6, 11]),
        column(&x, [1, 2, 3, 4, 5, 6, 7, 12]),
        column(&x, [2, 3, 4, 5, 6, 7, 8, 13]),
        column(&x, [3, 4, 5, 6, 7, 8, 9, 14]),
        column(&x, [4, 5, 6, 7, 8, 9, 10, 15]),
        column(&x, [5, 6, 7, 8, 9, 10, 11, 0]),
        column(&x, [6, 7, 8, 9, 10, 11, 12, 1]),
        column(&x, [7, 8, 9, 10, 11, 12, 13, 2]),
        column(&x, [8, 9, 10, 11, 12, 13, 14, 3]),
        column(&x, [9, 10, 11, 12, 13, 14, 15, 4]),
        column(&x, [10, 11, 12, 13, 14, 15, 0, 5]),
        column(&x, [11, 12, 13, 14, 15, 0, 1, 6]),
        column(&x, [12, 13, 14, 15, 0, 1, 2, 7]),
        column(&x, [13, 14, 15, 0, 1, 2, 3, 8]),
        column(&x, [14, 15, 0, 1, 2, 3, 4, 9]),
        column(&x, [15, 0, 1, 2, 3, 4, 5, 10]),
    ]
}

pub(crate) fn compress(h: &mut [u64; COLS], block: &[u8; 128]) {
    let mut q = [0u64; COLS];
    for (chunk, v) in block.chunks_exact(8).zip(q.iter_mut()) {
        *v = u64::from_be_bytes(chunk.try_into().unwrap());
    }
    let mut p = [0u64; COLS];
    for i in 0..COLS {
        p[i] = h[i] ^ q[i];
    }
    for i in 0..ROUNDS {
        q = rndq(q, i);
    }
    for i in 0..ROUNDS {
        p = rndp(p, i << 56);
    }
    for i in 0..COLS {
        h[i] ^= q[i] ^ p[i];
    }
}

pub(crate) fn p(h: &[u64; COLS]) -> [u64; COLS] {
    let mut p = *h;
    for i in 0..ROUNDS {
        p = rndp(p, i << 56);
    }
    for i in 0..COLS {
        p[i] ^= h[i];
    }
    p
}
#[cfg(test)]
mod tests_rug_139 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: [u64; 16] = [
            0x037b29e9, 0x5a88fc0d, 0xa2ee4c5f, 0xfce722a9,
            0x0701c39d, 0x5306cc1f, 0xa8293cd1, 0xf1b6e8dd,
            0x0eb542a7, 0x56ae0983, 0xad825bfa, 0xf4d4bcce,
            0x10c9f95b, 0x65930cd5, 0xbde64e37, 0x023a598f
        ];
        let mut p1: u64 = 0x123456789abcdef0;

        crate::compress1024::rndq(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_140 {
    use super::*;
    use crate::compress1024;

    #[test]
    fn test_rug() {
        let mut p0: [u64; 16] = [0x1111111111111111, 0x2222222222222222, 0x3333333333333333, 0x4444444444444444,
                                  0x5555555555555555, 0x6666666666666666, 0x7777777777777777, 0x8888888888888888,
                                  0x9999999999999999, 0xaaaaaaaaaaaaaaaa, 0xbbbbbbbbbbbbbbbb, 0xcccccccccccccccc,
                                  0xdddddddddddddddd, 0xeeeeeeeeeeeeeeee, 0xffffffffffffffff, 0x0000000000000000];
        let mut p1: u64 = 0xdeadbeef;

        compress1024::rndp(p0, p1);
    }
}