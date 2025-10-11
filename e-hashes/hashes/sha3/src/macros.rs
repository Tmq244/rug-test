macro_rules! impl_sha3 {
    (
        $name:ident, $full_name:ident, $output_size:ident,
        $rate:ident, $pad:expr, $alg_name:expr $(,)?
    ) => {
        #[doc = "Core "]
        #[doc = $alg_name]
        #[doc = " hasher state."]
        #[derive(Clone)]
        #[allow(non_camel_case_types)]
        pub struct $name {
            state: Sha3State,
        }

        impl HashMarker for $name {}

        impl BlockSizeUser for $name {
            type BlockSize = $rate;
        }

        impl BufferKindUser for $name {
            type BufferKind = Eager;
        }

        impl OutputSizeUser for $name {
            type OutputSize = $output_size;
        }

        impl UpdateCore for $name {
            #[inline]
            fn update_blocks(&mut self, blocks: &[Block<Self>]) {
                for block in blocks {
                    self.state.absorb_block(block)
                }
            }
        }

        impl FixedOutputCore for $name {
            #[inline]
            fn finalize_fixed_core(&mut self, buffer: &mut Buffer<Self>, out: &mut Output<Self>) {
                let pos = buffer.get_pos();
                let block = buffer.pad_with_zeros();
                block[pos] = $pad;
                let n = block.len();
                block[n - 1] |= 0x80;

                self.state.absorb_block(block);

                self.state.as_bytes(out);
            }
        }

        impl Default for $name {
            #[inline]
            fn default() -> Self {
                Self {
                    state: Default::default(),
                }
            }
        }

        impl Reset for $name {
            #[inline]
            fn reset(&mut self) {
                *self = Default::default();
            }
        }

        impl AlgorithmName for $name {
            fn write_alg_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(stringify!($full_name))
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(concat!(stringify!($name), " { ... }"))
            }
        }

        #[doc = $alg_name]
        #[doc = " hasher state."]
        pub type $full_name = CoreWrapper<$name>;
    };
    (
        $name:ident, $full_name:ident, $output_size:ident,
        $rate:ident, $pad:expr, $alg_name:expr, $oid:literal $(,)?
    ) => {
        impl_sha3!($name, $full_name, $output_size, $rate, $pad, $alg_name);

        #[cfg(feature = "oid")]
        #[cfg_attr(docsrs, doc(cfg(feature = "oid")))]
        impl AssociatedOid for $name {
            const OID: ObjectIdentifier = ObjectIdentifier::new_unwrap($oid);
        }
    };
}

macro_rules! impl_shake {
    (
        $name:ident, $full_name:ident, $reader:ident, $reader_full:ident,
        $rate:ident, $pad:expr, $alg_name:expr $(,)?
    ) => {
        #[doc = "Core "]
        #[doc = $alg_name]
        #[doc = " hasher state."]
        #[derive(Clone)]
        #[allow(non_camel_case_types)]
        pub struct $name {
            state: Sha3State,
        }

        impl HashMarker for $name {}

        impl BlockSizeUser for $name {
            type BlockSize = $rate;
        }

        impl BufferKindUser for $name {
            type BufferKind = Eager;
        }

        impl UpdateCore for $name {
            #[inline]
            fn update_blocks(&mut self, blocks: &[Block<Self>]) {
                for block in blocks {
                    self.state.absorb_block(block)
                }
            }
        }

        impl ExtendableOutputCore for $name {
            type ReaderCore = $reader;

            #[inline]
            fn finalize_xof_core(&mut self, buffer: &mut Buffer<Self>) -> Self::ReaderCore {
                let pos = buffer.get_pos();
                let block = buffer.pad_with_zeros();
                block[pos] = $pad;
                let n = block.len();
                block[n - 1] |= 0x80;

                self.state.absorb_block(block);
                $reader {
                    state: self.state.clone(),
                }
            }
        }

        impl Default for $name {
            #[inline]
            fn default() -> Self {
                Self {
                    state: Default::default(),
                }
            }
        }

        impl Reset for $name {
            #[inline]
            fn reset(&mut self) {
                *self = Default::default();
            }
        }

        impl AlgorithmName for $name {
            fn write_alg_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(stringify!($full_name))
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(concat!(stringify!($name), " { ... }"))
            }
        }

        #[doc = "Core "]
        #[doc = $alg_name]
        #[doc = " reader state."]
        #[derive(Clone)]
        #[allow(non_camel_case_types)]
        pub struct $reader {
            state: Sha3State,
        }

        impl BlockSizeUser for $reader {
            type BlockSize = $rate;
        }

        impl XofReaderCore for $reader {
            #[inline]
            fn read_block(&mut self) -> Block<Self> {
                let mut block = Block::<Self>::default();
                self.state.as_bytes(&mut block);
                self.state.permute();
                block
            }
        }

        #[doc = $alg_name]
        #[doc = " hasher state."]
        pub type $full_name = CoreWrapper<$name>;

        #[doc = $alg_name]
        #[doc = " reader state."]
        pub type $reader_full = XofReaderCoreWrapper<$reader>;
    };
    (
        $name:ident, $full_name:ident, $reader:ident, $reader_full:ident,
        $rate:ident, $pad:expr, $alg_name:expr, $oid:literal $(,)?
    ) => {
        impl_shake!(
            $name,
            $full_name,
            $reader,
            $reader_full,
            $rate,
            $pad,
            $alg_name
        );

        #[cfg(feature = "oid")]
        #[cfg_attr(docsrs, doc(cfg(feature = "oid")))]
        impl AssociatedOid for $name {
            const OID: ObjectIdentifier = ObjectIdentifier::new_unwrap($oid);
        }
    };
}

macro_rules! impl_turbo_shake {
    (
        $name:ident, $full_name:ident, $reader:ident, $reader_full:ident,
        $rate:ident, $alg_name:expr $(,)?
    ) => {
        #[doc = "Core "]
        #[doc = $alg_name]
        #[doc = " hasher state."]
        #[derive(Clone)]
        #[allow(non_camel_case_types)]
        pub struct $name {
            domain_separation: u8,
            state: Sha3State,
        }

        impl $name {
            /// Creates a new TurboSHAKE instance with the given domain separation.
            /// Note that the domain separation needs to be a byte with a value in
            /// the range [0x01, . . . , 0x7F]
            pub fn new(domain_separation: u8) -> Self {
                assert!((0x01..=0x7F).contains(&domain_separation));
                Self {
                    domain_separation,
                    state: Sha3State::new(TURBO_SHAKE_ROUND_COUNT),
                }
            }
        }

        impl HashMarker for $name {}

        impl BlockSizeUser for $name {
            type BlockSize = $rate;
        }

        impl BufferKindUser for $name {
            type BufferKind = Eager;
        }

        impl UpdateCore for $name {
            #[inline]
            fn update_blocks(&mut self, blocks: &[Block<Self>]) {
                for block in blocks {
                    self.state.absorb_block(block)
                }
            }
        }

        impl ExtendableOutputCore for $name {
            type ReaderCore = $reader;

            #[inline]
            fn finalize_xof_core(&mut self, buffer: &mut Buffer<Self>) -> Self::ReaderCore {
                let pos = buffer.get_pos();
                let block = buffer.pad_with_zeros();
                block[pos] = self.domain_separation;
                let n = block.len();
                block[n - 1] |= 0x80;

                self.state.absorb_block(block);
                $reader {
                    state: self.state.clone(),
                }
            }
        }

        impl Reset for $name {
            #[inline]
            fn reset(&mut self) {
                *self = Self::new(self.domain_separation);
            }
        }

        impl AlgorithmName for $name {
            fn write_alg_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(stringify!($full_name))
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(concat!(stringify!($name), " { ... }"))
            }
        }

        #[doc = "Core "]
        #[doc = $alg_name]
        #[doc = " reader state."]
        #[derive(Clone)]
        #[allow(non_camel_case_types)]
        pub struct $reader {
            state: Sha3State,
        }

        impl BlockSizeUser for $reader {
            type BlockSize = $rate;
        }

        impl XofReaderCore for $reader {
            #[inline]
            fn read_block(&mut self) -> Block<Self> {
                let mut block = Block::<Self>::default();
                self.state.as_bytes(&mut block);
                self.state.permute();
                block
            }
        }

        #[doc = $alg_name]
        #[doc = " hasher state."]
        pub type $full_name = CoreWrapper<$name>;

        #[doc = $alg_name]
        #[doc = " reader state."]
        pub type $reader_full = XofReaderCoreWrapper<$reader>;
    };
    (
        $name:ident, $full_name:ident, $reader:ident, $reader_full:ident,
        $rate:ident, $alg_name:expr, $oid:literal $(,)?
    ) => {
        impl_turbo_shake!($name, $full_name, $reader, $reader_full, $rate, $alg_name);

        #[cfg(feature = "oid")]
        #[cfg_attr(docsrs, doc(cfg(feature = "oid")))]
        impl AssociatedOid for $name {
            const OID: ObjectIdentifier = ObjectIdentifier::new_unwrap($oid);
        }
    };
}

macro_rules! impl_cshake {
    (
        $name:ident, $full_name:ident, $reader:ident, $reader_full:ident,
        $rate:ident, $shake_pad:expr, $cshake_pad:expr, $alg_name:expr,
    ) => {
        #[doc = "Core "]
        #[doc = $alg_name]
        #[doc = " hasher state."]
        #[derive(Clone)]
        #[allow(non_camel_case_types)]
        pub struct $name {
            padding: u8,
            state: Sha3State,
            #[cfg(feature = "reset")]
            initial_state: Sha3State,
        }

        impl $name {
            /// Creates a new CSHAKE instance with the given customization.
            pub fn new(customization: &[u8]) -> Self {
                Self::new_with_function_name(&[], customization)
            }

            /// Creates a new CSHAKE instance with the given function name and customization.
            /// Note that the function name is intended for use by NIST and should only be set to
            /// values defined by NIST. You probably don't need to use this function.
            pub fn new_with_function_name(function_name: &[u8], customization: &[u8]) -> Self {
                let mut state = Sha3State::default();
                if function_name.is_empty() && customization.is_empty() {
                    return Self {
                        padding: $shake_pad,
                        state: state.clone(),
                        #[cfg(feature = "reset")]
                        initial_state: state,
                    };
                }

                let mut buffer = Buffer::<Self>::default();
                let mut b = [0u8; 9];
                buffer.digest_blocks(left_encode($rate::to_u64(), &mut b), |blocks| {
                    for block in blocks {
                        state.absorb_block(block);
                    }
                });
                buffer.digest_blocks(
                    left_encode((function_name.len() * 8) as u64, &mut b),
                    |blocks| {
                        for block in blocks {
                            state.absorb_block(block);
                        }
                    },
                );
                buffer.digest_blocks(function_name, |blocks| {
                    for block in blocks {
                        state.absorb_block(block);
                    }
                });
                buffer.digest_blocks(
                    left_encode((customization.len() * 8) as u64, &mut b),
                    |blocks| {
                        for block in blocks {
                            state.absorb_block(block);
                        }
                    },
                );
                buffer.digest_blocks(customization, |blocks| {
                    for block in blocks {
                        state.absorb_block(block);
                    }
                });
                state.absorb_block(buffer.pad_with_zeros());

                Self {
                    padding: $cshake_pad,
                    state: state.clone(),
                    #[cfg(feature = "reset")]
                    initial_state: state,
                }
            }
        }

        impl HashMarker for $name {}

        impl BlockSizeUser for $name {
            type BlockSize = $rate;
        }

        impl BufferKindUser for $name {
            type BufferKind = Eager;
        }

        impl UpdateCore for $name {
            #[inline]
            fn update_blocks(&mut self, blocks: &[Block<Self>]) {
                for block in blocks {
                    self.state.absorb_block(block)
                }
            }
        }

        impl ExtendableOutputCore for $name {
            type ReaderCore = $reader;

            #[inline]
            fn finalize_xof_core(&mut self, buffer: &mut Buffer<Self>) -> Self::ReaderCore {
                let pos = buffer.get_pos();
                let block = buffer.pad_with_zeros();
                block[pos] = self.padding;
                let n = block.len();
                block[n - 1] |= 0x80;

                self.state.absorb_block(block);
                $reader {
                    state: self.state.clone(),
                }
            }
        }

        #[cfg(feature = "reset")]
        impl Reset for $name {
            #[inline]
            fn reset(&mut self) {
                self.state = self.initial_state.clone();
            }
        }

        impl AlgorithmName for $name {
            fn write_alg_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(stringify!($full_name))
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(concat!(stringify!($name), " { ... }"))
            }
        }

        #[doc = "Core "]
        #[doc = $alg_name]
        #[doc = " reader state."]
        #[derive(Clone)]
        #[allow(non_camel_case_types)]
        pub struct $reader {
            state: Sha3State,
        }

        impl BlockSizeUser for $reader {
            type BlockSize = $rate;
        }

        impl XofReaderCore for $reader {
            #[inline]
            fn read_block(&mut self) -> Block<Self> {
                let mut block = Block::<Self>::default();
                self.state.as_bytes(&mut block);
                self.state.permute();
                block
            }
        }

        #[doc = $alg_name]
        #[doc = " hasher state."]
        pub type $full_name = CoreWrapper<$name>;

        #[doc = $alg_name]
        #[doc = " reader state."]
        pub type $reader_full = XofReaderCoreWrapper<$reader>;
    };
}
#[cfg(test)]
mod tests_rug_288 {
    use super::*;
    use crate::digest::core_api::{UpdateCore, BlockSizeUser};
    use digest::generic_array::GenericArray;
    use crate::Keccak224Core;

    #[test]
    fn test_rug() {
        let mut p0: Keccak224Core = Default::default();
        let mut block_data = [0u8; 1152 / 8]; // BlockSize for Keccak224 is 1152 bits, which is 144 bytes
        let p1: &[GenericArray<u8, <Keccak224Core as BlockSizeUser>::BlockSize>] = 
            core::slice::from_ref(&GenericArray::from_slice(&block_data));

        p0.update_blocks(p1);
    }
}#[cfg(test)]
mod tests_rug_290 {
    use super::*;
    use crate::{Keccak224, Keccak224Core};
    use core::default::Default;

    #[test]
    fn test_rug() {
        let keccak224_core: Keccak224Core = <Keccak224Core as Default>::default();
        
        // You can add assertions here if needed
    }
}#[cfg(test)]
mod tests_rug_291 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Keccak224Core, digest::core_api::UpdateCore};

    #[test]
    fn test_rug() {
        let mut p0: Keccak224Core = Default::default();

        <Keccak224Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_293 {
    use super::*;
    use crate::digest::core_api::{UpdateCore, BlockSizeUser};
    use digest::generic_array::GenericArray;
    use crate::{Keccak256Core, Digest};

    #[test]
    fn test_rug() {
        let mut p0 = Keccak256Core::default();
        let mut block1 = GenericArray::<u8, <Keccak256Core as BlockSizeUser>::BlockSize>::default();
        block1[0] = 0x31;
        block1[1] = 0x32;
        block1[2] = 0x33;

        let mut block2 = GenericArray::<u8, <Keccak256Core as BlockSizeUser>::BlockSize>::default();
        block2[0] = 0x41;
        block2[1] = 0x42;
        block2[2] = 0x43;

        let p1 = &[block1, block2];

        <Keccak256Core as UpdateCore>::update_blocks(&mut p0, p1);
    }
}#[cfg(test)]
mod tests_rug_294 {
    use super::*;
    use crate::digest::core_api::{FixedOutputCore, UpdateCore};
    use crate::Keccak256Core;
    use digest::block_buffer::BlockBuffer;
    use digest::generic_array::GenericArray;

    #[test]
    fn test_rug() {
        let mut p0 = Keccak256Core::default();
        let mut p1 = BlockBuffer::<
            <Keccak256Core as digest::core_api::BlockSizeUser>::BlockSize,
            <Keccak256Core as digest::core_api::BufferKindUser>::BufferKind,
        >::default();
        let mut p2 = GenericArray::<u8, <Keccak256Core as digest::OutputSizeUser>::OutputSize>::default();

        <Keccak256Core>::finalize_fixed_core(&mut p0, &mut p1, &mut p2);
    }
}#[cfg(test)]
mod tests_rug_295 {
    use super::*;
    use crate::{Keccak256, Keccak256Core};

    #[test]
    fn test_rug() {
        let keccak: Keccak256Core = <Keccak256Core as Default>::default();

    }
}#[cfg(test)]
mod tests_rug_296 {
    use super::*;
    use crate::digest::Reset;
    use crate::Keccak256Core;

    #[test]
    fn test_rug() {
        let mut p0: Keccak256Core = Default::default();

        <Keccak256Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_299 {
    use super::*;
    use crate::digest::core_api::{FixedOutputCore, UpdateCore};
    use crate::digest::block_buffer::BlockBuffer;
    use crate::digest::generic_array::GenericArray;
    use crate::digest::OutputSizeUser;
    use crate::Keccak384Core;

    #[test]
    fn test_rug() {
        let mut p0 = Keccak384Core::default();
        let mut p1 = BlockBuffer::<
            <Keccak384Core as digest::core_api::BlockSizeUser>::BlockSize,
            <Keccak384Core as digest::core_api::BufferKindUser>::BufferKind,
        >::default();
        let mut p2 = GenericArray::<u8, <Keccak384Core as OutputSizeUser>::OutputSize>::default();

        <Keccak384Core>::finalize_fixed_core(&mut p0, &mut p1, &mut p2);
    }
}#[cfg(test)]
mod tests_rug_300 {
    use super::*;
    use crate::{Keccak384Core};
    use core::default::Default;

    #[test]
    fn test_rug() {
        let keccak: Keccak384Core = <Keccak384Core>::default();
    }
}#[cfg(test)]
mod tests_rug_301 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Keccak384, Keccak384Core};

    #[test]
    fn test_reset() {
        let mut p0: Keccak384Core = Default::default();

        <Keccak384Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_303 {
    use super::*;
    use crate::digest::core_api::{BlockSizeUser, UpdateCore};
    use digest::generic_array::GenericArray;
    use crate::Keccak512Core;

    #[test]
    fn test_rug() {
        let mut p0 = Keccak512Core::default();
        let mut block = GenericArray::<u8, <Keccak512Core as BlockSizeUser>::BlockSize>::default();
        
        // Fill the block with some sample data
        for (i, byte) in block.iter_mut().enumerate() {
            *byte = i as u8;
        }

        let p1 = &[block];

        <Keccak512Core as UpdateCore>::update_blocks(&mut p0, p1);
    }
}#[cfg(test)]
mod tests_rug_304 {
    use super::*;
    use crate::digest::core_api::{BlockSizeUser, BufferKindUser, FixedOutputCore, OutputSizeUser};
    use crate::Keccak512Core;
    use digest::block_buffer::BlockBuffer;
    use digest::generic_array::GenericArray;

    #[test]
    fn test_rug() {
        let mut p0 = Keccak512Core::default();
        let mut p1 = BlockBuffer::<
            <Keccak512Core as BlockSizeUser>::BlockSize,
            <Keccak512Core as BufferKindUser>::BufferKind,
        >::default();
        let mut p2 = GenericArray::<u8, <Keccak512Core as OutputSizeUser>::OutputSize>::default();

        <Keccak512Core>::finalize_fixed_core(&mut p0, &mut p1, &mut p2);
    }
}#[cfg(test)]
mod tests_rug_306 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Keccak512Core, digest::core_api::UpdateCore};

    #[test]
    fn test_rug() {
        let mut p0: Keccak512Core = Default::default();

        <Keccak512Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_309 {
    use super::*;
    use crate::digest::core_api::{BufferKindUser, BlockSizeUser, FixedOutputCore, OutputSizeUser};
    use crate::Keccak256FullCore;
    use digest::block_buffer::BlockBuffer;
    use digest::generic_array::GenericArray;

    #[test]
    fn test_rug() {
        let mut p0 = Keccak256FullCore::default();
        let mut p1 = BlockBuffer::<
            <Keccak256FullCore as BlockSizeUser>::BlockSize,
            <Keccak256FullCore as BufferKindUser>::BufferKind,
        >::default();
        let mut p2 = GenericArray::<u8, <Keccak256FullCore as OutputSizeUser>::OutputSize>::default();

        <Keccak256FullCore>::finalize_fixed_core(&mut p0, &mut p1, &mut p2);
    }
}#[cfg(test)]
mod tests_rug_310 {
    use super::*;
    use crate::{Keccak256, Keccak256FullCore};
    use core::default::Default;

    #[test]
    fn test_rug() {
        let keccak: Keccak256FullCore = <Keccak256FullCore>::default();
    }
}#[cfg(test)]
mod tests_rug_311 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Keccak256, Keccak256FullCore};

    #[test]
    fn test_reset() {
        let mut p0: Keccak256FullCore = Default::default();

        <Keccak256FullCore as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_315 {
    use super::*;
    use crate::Sha3_224Core;

    #[test]
    fn test_default() {
        let _sha3_224_core: Sha3_224Core = <Sha3_224Core>::default();
    }
}#[cfg(test)]
mod tests_rug_316 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Sha3_224Core, digest::core_api::UpdateCore};

    #[test]
    fn test_rug() {
        let mut p0: Sha3_224Core = Default::default();

        <Sha3_224Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_318 {
    use super::*;
    use crate::digest::core_api::{UpdateCore, BlockSizeUser};
    use digest::generic_array::GenericArray;
    use crate::{Sha3_256Core, Sha3State};

    #[test]
    fn test_rug() {
        let mut p0: Sha3_256Core = Default::default();
        let mut block1: GenericArray<u8, <Sha3_256Core as BlockSizeUser>::BlockSize> = GenericArray::default();
        let mut block2: GenericArray<u8, <Sha3_256Core as BlockSizeUser>::BlockSize> = GenericArray::default();

        // Example modification of blocks for testing
        block1[0] = 0x01;
        block2[0] = 0x02;

        let p1: &[GenericArray<u8, <Sha3_256Core as BlockSizeUser>::BlockSize>] = &[block1, block2];

        p0.update_blocks(p1);
    }
}#[cfg(test)]
mod tests_rug_320 {
    use super::*;
    use crate::{Sha3_256Core};

    #[test]
    fn test_default() {
        let default_core: Sha3_256Core = <Sha3_256Core>::default();
    }
}#[cfg(test)]
mod tests_rug_321 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Sha3_256Core, digest::core_api::UpdateCore};

    #[test]
    fn test_rug() {
        let mut p0: Sha3_256Core = Default::default();

        <Sha3_256Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_325 {
    use super::*;
    use crate::{Sha3_384Core};
    use core::default::Default;

    #[test]
    fn test_rug() {
        let _core: Sha3_384Core = <Sha3_384Core as Default>::default();
    }
}#[cfg(test)]
mod tests_rug_326 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Sha3_384, Sha3_384Core};

    #[test]
    fn test_rug() {
        let mut p0: Sha3_384Core = Default::default();

        <Sha3_384Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_329 {
    use super::*;
    use crate::digest::core_api::FixedOutputCore;
    use crate::digest::block_buffer::BlockBuffer;
    use crate::digest::generic_array::GenericArray;
    use crate::Sha3_512Core;

    #[test]
    fn test_finalize_fixed_core() {
        let mut p0 = Sha3_512Core::default();
        let mut p1 = BlockBuffer::<
            <Sha3_512Core as digest::core_api::BlockSizeUser>::BlockSize,
            <Sha3_512Core as digest::core_api::BufferKindUser>::BufferKind
        >::default();
        let mut p2 = GenericArray::<u8, <Sha3_512Core as digest::OutputSizeUser>::OutputSize>::default();

        <Sha3_512Core>::finalize_fixed_core(&mut p0, &mut p1, &mut p2);
    }
}#[cfg(test)]
mod tests_rug_330 {
    use super::*;
    use crate::{Sha3_512Core};

    #[test]
    fn test_default() {
        let sha3_core: Sha3_512Core = <Sha3_512Core>::default();
    }
}#[cfg(test)]
mod tests_rug_331 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Sha3_512, Sha3_512Core};

    #[test]
    fn test_reset() {
        let mut p0: Sha3_512Core = Default::default();

        <Sha3_512Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_335 {
    use super::*;
    use core::default::Default;
    use crate::{Shake128Core};

    #[test]
    fn test_rug() {
        let shake128_core: Shake128Core = <Shake128Core as Default>::default();

        // Additional assertions can be added here if needed
    }
}#[cfg(test)]
mod tests_rug_336 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Shake128Core, digest::core_api::UpdateCore};

    #[test]
    fn test_rug() {
        let mut p0: Shake128Core = Default::default();

        <Shake128Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_338 {
    use super::*;
    use crate::digest::core_api::XofReaderCore;
    use crate::Shake128ReaderCore;
    use crate::Sha3State;

    #[test]
    fn test_rug() {
        let mut p0 = Shake128ReaderCore { state: Sha3State::default() };

        <Shake128ReaderCore>::read_block(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_339 {
    use super::*;
    use crate::digest::core_api::{UpdateCore, BlockSizeUser};
    use digest::generic_array::GenericArray;
    use crate::{Shake256Core, Sha3State};

    #[test]
    fn test_rug() {
        let mut p0: Shake256Core = Shake256Core::default();
        let mut block1 = GenericArray::<u8, <Shake256Core as BlockSizeUser>::BlockSize>::default();
        let mut block2 = GenericArray::<u8, <Shake256Core as BlockSizeUser>::BlockSize>::default();

        // Example data for blocks
        block1[0] = 0x31;
        block1[1] = 0x32;
        block2[0] = 0x33;
        block2[1] = 0x34;

        let p1: &[GenericArray<u8, <Shake256Core as BlockSizeUser>::BlockSize>] = &[block1, block2];

        <Shake256Core as UpdateCore>::update_blocks(&mut p0, p1);
    }
}#[cfg(test)]
mod tests_rug_341 {
    use super::*;
    use core::default::Default;
    use crate::Shake256Core;

    #[test]
    fn test_rug() {
        let _shake256_core: Shake256Core = <Shake256Core>::default();
    }
}#[cfg(test)]
mod tests_rug_342 {
    use super::*;
    use crate::digest::Reset;
    use crate::{Shake256Core, digest::core_api::UpdateCore};

    #[test]
    fn test_rug() {
        let mut p0: Shake256Core = Default::default();

        <Shake256Core as Reset>::reset(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_344 {
    use super::*;
    use crate::digest::core_api::{XofReaderCore, Block};
    use crate::state::Sha3State;
    use crate::Shake256ReaderCore;

    #[test]
    fn test_read_block() {
        let mut p0 = Shake256ReaderCore {
            state: Sha3State::default(),
        };

        <Shake256ReaderCore as XofReaderCore>::read_block(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_345 {
    use super::*;
    use crate::TurboShake128Core;
    
    #[test]
    fn test_rug() {
        let mut p0: u8 = 0x57;

        <TurboShake128Core>::new(p0);
    }
}#[cfg(test)]
mod tests_rug_346 {
    use super::*;
    use crate::digest::core_api::{UpdateCore, BlockSizeUser};
    use digest::generic_array::GenericArray;
    use crate::TurboShake128Core;

    #[test]
    fn test_rug() {
        let mut p0 = TurboShake128Core::new(0x01);
        let mut block = GenericArray::<u8, <TurboShake128Core as BlockSizeUser>::BlockSize>::default();
        
        // Fill the block with some sample data
        for (i, elem) in block.iter_mut().enumerate() {
            *elem = i as u8;
        }

        let p1 = &[block];

        <TurboShake128Core as UpdateCore>::update_blocks(&mut p0, p1);
    }
}#[cfg(test)]
mod tests_rug_350 {
    use super::*;
    use crate::digest::core_api::XofReaderCore;
    use crate::TurboShake128ReaderCore;
    use crate::Sha3State;
    use core::convert::Infallible;

    #[test]
    fn test_rug() {
        let mut p0 = TurboShake128ReaderCore { state: Sha3State::default() };

        p0.read_block();
    }
}#[cfg(test)]
mod tests_rug_351 {
    use super::*;
    use crate::{TurboShake256Core, Sha3State, TURBO_SHAKE_ROUND_COUNT};

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0x01;

        TurboShake256Core::new(p0);
    }
}#[cfg(test)]
mod tests_rug_357 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"custom";

        crate::CShake128Core::new(p0);
    }
}#[cfg(test)]
mod tests_rug_358 {
    use super::*;
    use crate::{CShake128Core, Sha3State, Buffer};

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"function_name";
        let mut p1: &[u8] = b"customization";

        <CShake128Core>::new_with_function_name(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_359 {
    use super::*;
    use crate::digest::core_api::{UpdateCore, BlockSizeUser};
    use digest::generic_array::GenericArray;
    use crate::{CShake128Core, Sha3State};

    #[test]
    fn test_rug() {
        let mut p0 = CShake128Core::new_with_function_name(b"function", b"customization");
        let mut block = GenericArray::<u8, <CShake128Core as BlockSizeUser>::BlockSize>::default();
        for i in 0..block.len() {
            block[i] = i as u8;
        }
        let p1 = &[block];

        <CShake128Core as UpdateCore>::update_blocks(&mut p0, p1);
    }
}#[cfg(test)]
mod tests_rug_362 {
    use super::*;
    use crate::digest::core_api::XofReaderCore;
    use crate::CShake128ReaderCore;
    use crate::Sha3State;

    #[test]
    fn test_rug() {
        let mut p0: CShake128ReaderCore = CShake128ReaderCore { state: Sha3State::default() };

        p0.read_block();
    }
}#[cfg(test)]
mod tests_rug_363 {
    use super::*;
    use crate::CShake256Core;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"customization";

        <CShake256Core>::new(p0);
    }
}#[cfg(test)]
mod tests_rug_364 {
    use super::*;
    use crate::{CShake256Core, Sha3State};
    
    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"function_name";
        let mut p1: &[u8] = b"customization";

        CShake256Core::new_with_function_name(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_365 {
    use super::*;
    use crate::digest::core_api::{UpdateCore, BlockSizeUser};
    use digest::generic_array::GenericArray;
    use crate::{CShake256Core, Sha3State};

    #[test]
    fn test_rug() {
        let mut p0 = CShake256Core::new_with_function_name(b"function", b"custom");
        let mut block = GenericArray::<u8, <CShake256Core as BlockSizeUser>::BlockSize>::default();
        // Fill the block with some data for testing
        for i in 0..block.len() {
            block[i] = i as u8;
        }
        let p1 = &[block];

        p0.update_blocks(p1);
    }
}