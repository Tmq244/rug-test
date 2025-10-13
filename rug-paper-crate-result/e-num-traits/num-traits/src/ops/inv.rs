/// Unary operator for retrieving the multiplicative inverse, or reciprocal, of a value.
pub trait Inv {
    /// The result after applying the operator.
    type Output;

    /// Returns the multiplicative inverse of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::f64::INFINITY;
    /// use num_traits::Inv;
    ///
    /// assert_eq!(7.0.inv() * 7.0, 1.0);
    /// assert_eq!((-0.0).inv(), -INFINITY);
    /// ```
    fn inv(self) -> Self::Output;
}

impl Inv for f32 {
    type Output = f32;
    #[inline]
    fn inv(self) -> f32 {
        1.0 / self
    }
}
impl Inv for f64 {
    type Output = f64;
    #[inline]
    fn inv(self) -> f64 {
        1.0 / self
    }
}
impl<'a> Inv for &'a f32 {
    type Output = f32;
    #[inline]
    fn inv(self) -> f32 {
        1.0 / *self
    }
}
impl<'a> Inv for &'a f64 {
    type Output = f64;
    #[inline]
    fn inv(self) -> f64 {
        1.0 / *self
    }
}
#[cfg(test)]
mod tests_rug_1651 {
    use super::*;
    use crate::Inv;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.5;

        <f32 as Inv>::inv(p0);
    }
}#[cfg(test)]
mod tests_rug_1652 {
    use super::*;
    use crate::Inv;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;

        <f64 as Inv>::inv(p0);
    }
}#[cfg(test)]
mod tests_rug_1653 {
    use super::*;
    use crate::Inv;

    #[test]
    fn test_rug() {
        let p0: f32 = 4.0;
        let p0_ref: &f32 = &p0;

        <&f32 as Inv>::inv(p0_ref);
    }
}#[cfg(test)]
mod tests_rug_1654 {
    use super::*;
    use crate::Inv;

    #[test]
    fn test_rug() {
        let p0: f64 = 2.5;
        
        <&f64 as Inv>::inv(&p0);
    }
}