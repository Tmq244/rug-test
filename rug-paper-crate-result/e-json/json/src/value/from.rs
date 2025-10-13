use super::Value;
use crate::map::Map;
use crate::number::Number;
use alloc::borrow::Cow;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::iter::FromIterator;

macro_rules! from_integer {
    ($($ty:ident)*) => {
        $(
            impl From<$ty> for Value {
                fn from(n: $ty) -> Self {
                    Value::Number(n.into())
                }
            }
        )*
    };
}

from_integer! {
    i8 i16 i32 i64 isize
    u8 u16 u32 u64 usize
}

#[cfg(feature = "arbitrary_precision")]
from_integer! {
    i128 u128
}

impl From<f32> for Value {
    /// Convert 32-bit floating point number to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let f: f32 = 13.37;
    /// let x: Value = f.into();
    /// ```
    fn from(f: f32) -> Self {
        Number::from_f32(f).map_or(Value::Null, Value::Number)
    }
}

impl From<f64> for Value {
    /// Convert 64-bit floating point number to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let f: f64 = 13.37;
    /// let x: Value = f.into();
    /// ```
    fn from(f: f64) -> Self {
        Number::from_f64(f).map_or(Value::Null, Value::Number)
    }
}

impl From<bool> for Value {
    /// Convert boolean to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let b = false;
    /// let x: Value = b.into();
    /// ```
    fn from(f: bool) -> Self {
        Value::Bool(f)
    }
}

impl From<String> for Value {
    /// Convert `String` to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let s: String = "lorem".to_string();
    /// let x: Value = s.into();
    /// ```
    fn from(f: String) -> Self {
        Value::String(f)
    }
}

impl<'a> From<&'a str> for Value {
    /// Convert string slice to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let s: &str = "lorem";
    /// let x: Value = s.into();
    /// ```
    fn from(f: &str) -> Self {
        Value::String(f.to_string())
    }
}

impl<'a> From<Cow<'a, str>> for Value {
    /// Convert copy-on-write string to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    /// use std::borrow::Cow;
    ///
    /// let s: Cow<str> = Cow::Borrowed("lorem");
    /// let x: Value = s.into();
    /// ```
    ///
    /// ```
    /// use serde_json::Value;
    /// use std::borrow::Cow;
    ///
    /// let s: Cow<str> = Cow::Owned("lorem".to_string());
    /// let x: Value = s.into();
    /// ```
    fn from(f: Cow<'a, str>) -> Self {
        Value::String(f.into_owned())
    }
}

impl From<Number> for Value {
    /// Convert `Number` to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::{Number, Value};
    ///
    /// let n = Number::from(7);
    /// let x: Value = n.into();
    /// ```
    fn from(f: Number) -> Self {
        Value::Number(f)
    }
}

impl From<Map<String, Value>> for Value {
    /// Convert map (with string keys) to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::{Map, Value};
    ///
    /// let mut m = Map::new();
    /// m.insert("Lorem".to_string(), "ipsum".into());
    /// let x: Value = m.into();
    /// ```
    fn from(f: Map<String, Value>) -> Self {
        Value::Object(f)
    }
}

impl<T: Into<Value>> From<Vec<T>> for Value {
    /// Convert a `Vec` to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let v = vec!["lorem", "ipsum", "dolor"];
    /// let x: Value = v.into();
    /// ```
    fn from(f: Vec<T>) -> Self {
        Value::Array(f.into_iter().map(Into::into).collect())
    }
}

impl<'a, T: Clone + Into<Value>> From<&'a [T]> for Value {
    /// Convert a slice to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let v: &[&str] = &["lorem", "ipsum", "dolor"];
    /// let x: Value = v.into();
    /// ```
    fn from(f: &'a [T]) -> Self {
        Value::Array(f.iter().cloned().map(Into::into).collect())
    }
}

impl<T: Into<Value>> FromIterator<T> for Value {
    /// Convert an iteratable type to a `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let v = std::iter::repeat(42).take(5);
    /// let x: Value = v.collect();
    /// ```
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let v: Vec<_> = vec!["lorem", "ipsum", "dolor"];
    /// let x: Value = v.into_iter().collect();
    /// ```
    ///
    /// ```
    /// use std::iter::FromIterator;
    /// use serde_json::Value;
    ///
    /// let x: Value = Value::from_iter(vec!["lorem", "ipsum", "dolor"]);
    /// ```
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Value::Array(iter.into_iter().map(Into::into).collect())
    }
}

impl<K: Into<String>, V: Into<Value>> FromIterator<(K, V)> for Value {
    /// Convert an iteratable type to a `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let v: Vec<_> = vec![("lorem", 40), ("ipsum", 2)];
    /// let x: Value = v.into_iter().collect();
    /// ```
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Value::Object(
            iter.into_iter()
                .map(|(k, v)| (k.into(), v.into()))
                .collect(),
        )
    }
}

impl From<()> for Value {
    /// Convert `()` to `Value`
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    ///
    /// let u = ();
    /// let x: Value = u.into();
    /// ```
    fn from((): ()) -> Self {
        Value::Null
    }
}

impl<T> From<Option<T>> for Value
where
    T: Into<Value>,
{
    fn from(opt: Option<T>) -> Self {
        match opt {
            None => Value::Null,
            Some(value) => Into::into(value),
        }
    }
}
#[cfg(test)]
mod tests_rug_715 {
    use super::*;
    use crate::value::Value;
    use std::convert::From;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        let _result: Value = Value::from(p0);
    }
}#[cfg(test)]
mod tests_rug_716 {
    use super::*;
    use crate::value::Value;
    use std::convert::From;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;

        let result = Value::from(p0);
        assert_eq!(result, Value::Number(42.into()));
    }
}#[cfg(test)]
mod tests_rug_717 {
    use super::*;
    use crate::value::Value;
    use std::convert::From;

    #[test]
    fn test_rug() {
        let p0: i32 = 42;

        let result: Value = Value::from(p0);
        
        assert_eq!(result, Value::Number(42.into()));
    }
}#[cfg(test)]
mod tests_rug_719 {
    use super::*;
    use crate::value::Value;
    use std::convert::From;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        let value: Value = Value::from(p0);

        assert_eq!(value, Value::Number(42.into()));
    }
}#[cfg(test)]
mod tests_rug_720 {
    use super::*;
    use crate::value::Value;
    use std::convert::From;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        <Value>::from(p0);
    }
}#[cfg(test)]
mod tests_rug_723 {
    use super::*;
    use crate::value::Value;
    use std::convert::From;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789;

        let result: Value = <Value>::from(p0);
        assert_eq!(result, Value::Number(123456789.into()));
    }
}#[cfg(test)]
mod tests_rug_725 {
    use super::*;
    use crate::value::{self, Value};

    #[test]
    fn test_rug() {
        let mut p0: f32 = 13.37;

        <Value>::from(p0);
    }
}#[cfg(test)]
mod tests_rug_727 {
    use super::*;
    use crate::Value;
    use std::convert::From;

    #[test]
    fn test_rug() {
        let mut p0: bool = false;

        let _value: Value = <Value>::from(p0);
    }
}#[cfg(test)]
mod tests_rug_728 {
    use super::*;
    use crate::Value;
    use std::convert::From;

    #[test]
    fn test_rug() {
        let mut p0: String = "lorem".to_string();

        <Value>::from(p0);
    }
}#[cfg(test)]
mod tests_rug_730 {
    use super::*;
    use crate::Value;
    use std::borrow::Cow;

    #[test]
    fn test_rug() {
        let p0: Cow<str> = Cow::Borrowed("sample data");

        let _value: Value = <Value>::from(p0);
    }
}#[cfg(test)]
mod tests_rug_733 {
    use super::*;
    use crate::value::Value;
    use crate::value::Value as JsonValue;

    #[test]
    fn test_rug() {
        let mut p0: Vec<&str> = vec!["lorem", "ipsum", "dolor"];

        let result: Value = <JsonValue>::from(p0);

        assert_eq!(result, JsonValue::Array(vec![
            JsonValue::String("lorem".to_string()),
            JsonValue::String("ipsum".to_string()),
            JsonValue::String("dolor".to_string())
        ]));
    }
}#[cfg(test)]
mod tests_rug_734 {
    use super::*;
    use crate::Value;
    
    #[test]
    fn test_rug() {
        let mut p0: &[i32] = &[1, 2, 3];

        let value: Value = <Value>::from(p0);
    }
}#[cfg(test)]
mod tests_rug_735 {
    use super::*;
    use crate::value::{Map, Value};
    use std::iter::FromIterator;

    #[test]
    fn test_rug() {
        let mut p0: Vec<(String, Value)> = vec![
            ("key1".to_string(), Value::from("value1")),
            ("key2".to_string(), Value::from(42)),
            ("key3".to_string(), Value::from(true)),
        ];

        let _result: Value = <Value>::from_iter(p0);
    }
}#[cfg(test)]
mod tests_rug_738 {
    use super::*;
    use crate::value::Value;
    use std::convert::From;

    #[test]
    fn test_rug() {
        let mut p0: Option<i32> = Some(42);

        let result = <Value>::from(p0);
        assert_eq!(result, Value::Number(42.into()));

        p0 = None;
        let result = <Value>::from(p0);
        assert_eq!(result, Value::Null);
    }
}