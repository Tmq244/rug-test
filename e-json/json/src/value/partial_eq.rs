use super::Value;
use alloc::string::String;

fn eq_i64(value: &Value, other: i64) -> bool {
    value.as_i64().map_or(false, |i| i == other)
}

fn eq_u64(value: &Value, other: u64) -> bool {
    value.as_u64().map_or(false, |i| i == other)
}

fn eq_f32(value: &Value, other: f32) -> bool {
    match value {
        Value::Number(n) => n.as_f32().map_or(false, |i| i == other),
        _ => false,
    }
}

fn eq_f64(value: &Value, other: f64) -> bool {
    value.as_f64().map_or(false, |i| i == other)
}

fn eq_bool(value: &Value, other: bool) -> bool {
    value.as_bool().map_or(false, |i| i == other)
}

fn eq_str(value: &Value, other: &str) -> bool {
    value.as_str().map_or(false, |i| i == other)
}

impl PartialEq<str> for Value {
    fn eq(&self, other: &str) -> bool {
        eq_str(self, other)
    }
}

impl<'a> PartialEq<&'a str> for Value {
    fn eq(&self, other: &&str) -> bool {
        eq_str(self, *other)
    }
}

impl PartialEq<Value> for str {
    fn eq(&self, other: &Value) -> bool {
        eq_str(other, self)
    }
}

impl<'a> PartialEq<Value> for &'a str {
    fn eq(&self, other: &Value) -> bool {
        eq_str(other, *self)
    }
}

impl PartialEq<String> for Value {
    fn eq(&self, other: &String) -> bool {
        eq_str(self, other.as_str())
    }
}

impl PartialEq<Value> for String {
    fn eq(&self, other: &Value) -> bool {
        eq_str(other, self.as_str())
    }
}

macro_rules! partialeq_numeric {
    ($($eq:ident [$($ty:ty)*])*) => {
        $($(
            impl PartialEq<$ty> for Value {
                fn eq(&self, other: &$ty) -> bool {
                    $eq(self, *other as _)
                }
            }

            impl PartialEq<Value> for $ty {
                fn eq(&self, other: &Value) -> bool {
                    $eq(other, *self as _)
                }
            }

            impl<'a> PartialEq<$ty> for &'a Value {
                fn eq(&self, other: &$ty) -> bool {
                    $eq(*self, *other as _)
                }
            }

            impl<'a> PartialEq<$ty> for &'a mut Value {
                fn eq(&self, other: &$ty) -> bool {
                    $eq(*self, *other as _)
                }
            }
        )*)*
    }
}

partialeq_numeric! {
    eq_i64[i8 i16 i32 i64 isize]
    eq_u64[u8 u16 u32 u64 usize]
    eq_f32[f32]
    eq_f64[f64]
    eq_bool[bool]
}
#[cfg(test)]
mod tests_rug_429 {
    use super::*;
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: i64 = 42;

        assert!(crate::value::partial_eq::eq_i64(&p0, p1));

        // Test case where the value does not match
        let p0_mismatch: Value = Value::Object(vec![("key1".to_string(), Value::from(43)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        assert!(!crate::value::partial_eq::eq_i64(&p0_mismatch, p1));

        // Test case where the value is not an integer
        let p0_not_int: Value = Value::Object(vec![("key1".to_string(), Value::from("not an int")), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        assert!(!crate::value::partial_eq::eq_i64(&p0_not_int, p1));
    }
}#[cfg(test)]
mod tests_rug_430 {
    use super::*;
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u64 = 42;

        assert_eq!(crate::value::partial_eq::eq_u64(&p0, p1), false);

        p0 = Value::Number(42.into());
        assert_eq!(crate::value::partial_eq::eq_u64(&p0, p1), true);
    }
}#[cfg(test)]
mod tests_rug_431 {
    use super::*;
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: f32 = 42.0;

        assert_eq!(crate::value::partial_eq::eq_f32(&p0, p1), false);
    }
}#[cfg(test)]
mod tests_rug_432 {
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: f64 = 42.0;

        assert_eq!(crate::value::partial_eq::eq_f64(&p0, p1), false);
    }
}#[cfg(test)]
mod tests_rug_433 {
    use super::*;
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: bool = true;

        assert_eq!(crate::value::partial_eq::eq_bool(&p0, p1), false);
    }
}#[cfg(test)]
mod tests_rug_434 {
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: &str = "value";

        assert_eq!(crate::value::partial_eq::eq_str(&p0, p1), true);

        // Additional test cases
        p0 = Value::String("another_value".to_string());
        p1 = "another_value";
        assert_eq!(crate::value::partial_eq::eq_str(&p0, p1), true);

        p0 = Value::String("mismatched_value".to_string());
        p1 = "another_value";
        assert_eq!(crate::value::partial_eq::eq_str(&p0, p1), false);

        p0 = Value::Bool(true);
        p1 = "true";
        assert_eq!(crate::value::partial_eq::eq_str(&p0, p1), false);

        p0 = Value::Null;
        p1 = "null";
        assert_eq!(crate::value::partial_eq::eq_str(&p0, p1), false);
    }
}#[cfg(test)]
mod tests_rug_435 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: &str = "some string";

        <Value as PartialEq<str>>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_436 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: &&str = &"some_string";

        <Value>::eq(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_437 {
    use super::*;
    use crate::{Value, Map};
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &str = "key1";
        let mut p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <str>::eq(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_438 {
    use super::*;
    use crate::{Value, Map};

    #[test]
    fn test_rug() {
        let p0: &str = "key1";
        let mut map = Map::new();
        map.insert("key1".to_string(), Value::from(42));
        map.insert("key2".to_string(), Value::from("value"));
        let p1: &Value = &Value::Object(map);

        assert!(!p0.eq(p1));
    }
}#[cfg(test)]
mod tests_rug_439 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: String = "some_string".to_string();

        <Value as PartialEq<String>>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_440 {
    use super::*;
    use crate::{Value, Map};

    #[test]
    fn test_rug() {
        let mut p0: std::string::String = "value".to_string();
        let mut p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <std::string::String as PartialEq<Value>>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_441 {
    use super::*;
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: i8 = 42;

        assert!(!<Value as PartialEq<i8>>::eq(&p0, &p1));
    }
}#[cfg(test)]
mod tests_rug_442 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let p0: i8 = 42;
        let p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        assert!(!<i8 as PartialEq<Value>>::eq(&p0, p1));
    }
}#[cfg(test)]
mod tests_rug_444 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: i8 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_445 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: i16 = 42;

        <Value as PartialEq<i16>>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_446 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let p0: i16 = 42;
        let p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        assert_eq!(<i16 as PartialEq<Value>>::eq(&p0, p1), false);
    }
}#[cfg(test)]
mod tests_rug_447 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: i16 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_448 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: i16 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_449 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: i32 = 42;

        <Value>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_450 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let p0: i32 = 42;
        let p1 = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <i32 as PartialEq<Value>>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_451 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: i32 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_452 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: i32 = 42;

        assert_eq!(p0.eq(&p1), false);
    }
}#[cfg(test)]
mod tests_rug_453 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: i64 = 42;

        <Value as PartialEq<i64>>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_454 {
    use super::*;
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 42;
        let mut p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        assert!(!<i64 as PartialEq<Value>>::eq(&p0, p1));
    }
}#[cfg(test)]
mod tests_rug_455 {
    use super::*;
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: i64 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_456 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: i64 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_457 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: isize = 42;

        <Value>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_458 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let p0: isize = 42;
        let p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <isize as PartialEq<Value>>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_459 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: isize = 42;

        p0.eq(&p1);
    }
}#[cfg(test)]
mod tests_rug_460 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: isize = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_461 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u8 = 42;

        <Value>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_462 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;
        let p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        assert!(!<u8 as PartialEq<Value>>::eq(&p0, p1));
    }
}#[cfg(test)]
mod tests_rug_463 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u8 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_464 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: u8 = 42;

        p0.eq(&p1);
    }
}#[cfg(test)]
mod tests_rug_465 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u16 = 42;

        <Value as PartialEq<u16>>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_466 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;
        let mut p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        assert_eq!(<u16 as PartialEq<Value>>::eq(&p0, p1), false);
    }
}#[cfg(test)]
mod tests_rug_467 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u16 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_468 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u16 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_469 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u32 = 42;

        <Value as PartialEq<u32>>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_470 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;
        let mut p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <u32 as PartialEq<Value>>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_471 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: u32 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_472 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u32 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_473 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u64 = 42;

        assert!(!<Value as PartialEq<u64>>::eq(&p0, &p1));
    }
}#[cfg(test)]
mod tests_rug_474 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let p0: u64 = 42;
        let p1 = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <u64 as PartialEq<Value>>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_475 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u64 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_476 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: u64 = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_477 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: usize = 42;

        <Value as PartialEq<usize>>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_478 {
    use super::*;
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;
        let mut p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <usize>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_479 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: usize = 42;

        p0.eq(&p1);
    }
}#[cfg(test)]
mod tests_rug_480 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: usize = 42;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_481 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: f32 = 42.0;

        <Value as PartialEq<f32>>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_482 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 42.0;
        let mut p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <f32 as PartialEq<Value>>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_483 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: f32 = 42.0;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_484 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: &mut f32 = &mut 42.0;

        p0.eq(p1);
    }
}#[cfg(test)]
mod tests_rug_485 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: f64 = 42.0;

        <Value as PartialEq<f64>>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_486 {
    use super::*;
    use crate::Value;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 42.0;
        let mut p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <f64 as PartialEq<Value>>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_487 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: f64 = 42.0;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_488 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: f64 = 42.0;

        assert!(!p0.eq(&p1));
    }
}#[cfg(test)]
mod tests_rug_489 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: bool = false;

        <Value>::eq(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_490 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: bool = true;
        let mut p1: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());

        <bool>::eq(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_491 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: &Value = &Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let mut p1: bool = true;

        p0.eq(&p1);
    }
}#[cfg(test)]
mod tests_rug_492 {
    use super::*;
    use crate::Value;
    use std::cmp::PartialEq;

    #[test]
    fn test_rug() {
        let mut p0: Value = Value::Object(vec![("key1".to_string(), Value::from(42)), ("key2".to_string(), Value::from("value"))].into_iter().collect());
        let p1: bool = true;

        p0.eq(&p1);
    }
}