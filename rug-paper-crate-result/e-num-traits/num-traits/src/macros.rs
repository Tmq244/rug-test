// not all are used in all features configurations
#![allow(unused)]

/// Forward a method to an inherent method or a base trait method.
macro_rules! forward {
    ($( Self :: $method:ident ( self $( , $arg:ident : $ty:ty )* ) -> $ret:ty ; )*)
        => {$(
            #[inline]
            fn $method(self $( , $arg : $ty )* ) -> $ret {
                Self::$method(self $( , $arg )* )
            }
        )*};
    ($( $base:ident :: $method:ident ( self $( , $arg:ident : $ty:ty )* ) -> $ret:ty ; )*)
        => {$(
            #[inline]
            fn $method(self $( , $arg : $ty )* ) -> $ret {
                <Self as $base>::$method(self $( , $arg )* )
            }
        )*};
    ($( $base:ident :: $method:ident ( $( $arg:ident : $ty:ty ),* ) -> $ret:ty ; )*)
        => {$(
            #[inline]
            fn $method( $( $arg : $ty ),* ) -> $ret {
                <Self as $base>::$method( $( $arg ),* )
            }
        )*};
    ($( $imp:path as $method:ident ( self $( , $arg:ident : $ty:ty )* ) -> $ret:ty ; )*)
        => {$(
            #[inline]
            fn $method(self $( , $arg : $ty )* ) -> $ret {
                $imp(self $( , $arg )* )
            }
        )*};
}

macro_rules! constant {
    ($( $method:ident () -> $ret:expr ; )*)
        => {$(
            #[inline]
            fn $method() -> Self {
                $ret
            }
        )*};
}
#[cfg(test)]
mod tests_rug_1857 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_infinity() {
        let inf_f32: f32 = <f32 as FloatCore>::infinity();
        
        assert_eq!(inf_f32, std::f32::INFINITY);
    }
}#[cfg(test)]
mod tests_rug_1858 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_neg_infinity() {
        let result: f32 = <f32 as FloatCore>::neg_infinity();

        assert_eq!(result, std::f32::NEG_INFINITY);
    }
}#[cfg(test)]
mod tests_rug_1859 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_nan() {
        let result: f32 = <f32 as FloatCore>::nan();
        
        assert!(result.is_nan());
    }
}#[cfg(test)]
mod tests_rug_1860 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_neg_zero() {
        let neg_zero_value: f32 = <f32 as FloatCore>::neg_zero();

        assert_eq!(neg_zero_value, -0.0);
    }
}#[cfg(test)]
mod tests_rug_1861 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_min_value() {
        let result: f32 = <f32 as FloatCore>::min_value();
        assert_eq!(result, 1.1754943508222875e-38);
    }
}#[cfg(test)]
mod tests_rug_1862 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_min_positive_value() {
        let result: f32 = <f32 as FloatCore>::min_positive_value();
        assert_eq!(result, 1.1754943508222875e-38);
    }
}#[cfg(test)]
mod tests_rug_1863 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_epsilon() {
        let result: f32 = <f32 as FloatCore>::epsilon();
        assert_eq!(result, 1.1920929e-7);
    }
}#[cfg(test)]
mod tests_rug_1864 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_max_value() {
        let value: f32 = <f32 as FloatCore>::max_value();
        
        assert_eq!(value, std::f32::MAX);
    }
}#[cfg(test)]
mod tests_rug_1865 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 0.0 / 0.0; // NaN

        <f32 as FloatCore>::is_nan(p0);
    }
}#[cfg(test)]
mod tests_rug_1866 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.0 / 0.0; // Sample data for infinity

        assert_eq!(<f32 as FloatCore>::is_infinite(p0), true);
    }
}#[cfg(test)]
mod tests_rug_1867 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let p0: f32 = 3.14;

        assert!(<f32 as FloatCore>::is_finite(p0));
    }
}#[cfg(test)]
mod tests_rug_1868 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.23; 

        assert!((<f32 as FloatCore>::is_normal)(p0));
    }
}#[cfg(test)]
mod tests_rug_1869 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as FloatCore>::classify(p0);
    }
}#[cfg(test)]
mod tests_rug_1870 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 3.7;

        <f32 as FloatCore>::floor(p0);
    }
}#[cfg(test)]
mod tests_rug_1871 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 4.3;

        assert_eq!(p0.ceil(), 5.0);
    }
}#[cfg(test)]
mod tests_rug_1872 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.5;

        <f32 as FloatCore>::round(p0);
    }
}#[cfg(test)]
mod tests_rug_1873 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_trunc() {
        let p0: f32 = 12.75;

        assert_eq!(<f32 as FloatCore>::trunc(p0), 12.0);
    }
}#[cfg(test)]
mod tests_rug_1874 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as FloatCore>::fract(p0);
    }
}#[cfg(test)]
mod tests_rug_1875 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let p0: f32 = -3.14;

        assert_eq!(<f32 as FloatCore>::abs(p0), 3.14);
    }
}#[cfg(test)]
mod tests_rug_1876 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = -1.5;

        <f32 as FloatCore>::signum(p0);
    }
}#[cfg(test)]
mod tests_rug_1877 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let p0: f32 = 42.0;

        assert!(<f32 as FloatCore>::is_sign_positive(p0));
    }
}#[cfg(test)]
mod tests_rug_1878 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = -42.5;

        assert!(<f32 as FloatCore>::is_sign_negative(p0));
    }
}#[cfg(test)]
mod tests_rug_1879 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 3.14;
        let mut p1: f32 = 2.71;

        <f32 as FloatCore>::min(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1880 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 3.14;
        let mut p1: f32 = 2.71;

        assert_eq!(<f32 as FloatCore>::max(p0, p1), 3.14);
    }
}#[cfg(test)]
mod tests_rug_1881 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 42.0;

        <f32 as FloatCore>::recip(p0);
    }
}#[cfg(test)]
mod tests_rug_1882 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.0;
        let mut p1: i32 = 3;

        <f32 as FloatCore>::powi(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1883 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let p0: f32 = 1.5708; // This is a sample value for f32, which is π/2 radians

        <f32 as FloatCore>::to_degrees(p0);
    }
}#[cfg(test)]
mod tests_rug_1884 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 180.0;

        <f32 as FloatCore>::to_radians(p0);
    }
}#[cfg(test)]
mod tests_rug_1885 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_infinity() {
        let inf: f64 = <f64 as FloatCore>::infinity();

        assert_eq!(inf, f64::INFINITY);
    }
}#[cfg(test)]
mod tests_rug_1886 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_neg_infinity() {
        let result: f64 = <f64 as FloatCore>::neg_infinity();
        
        assert_eq!(result, f64::NEG_INFINITY);
    }
}#[cfg(test)]
mod tests_rug_1887 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_nan() {
        let result: f64 = <f64 as FloatCore>::nan();
        
        assert!(result.is_nan());
    }
}#[cfg(test)]
mod tests_rug_1888 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_neg_zero() {
        let neg_zero_value: f64 = <f64 as FloatCore>::neg_zero();

        assert_eq!(neg_zero_value, -0.0);
    }
}#[cfg(test)]
mod tests_rug_1889 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_min_value() {
        let result: f64 = <f64 as FloatCore>::min_value();
        assert_eq!(result, f64::MIN);
    }
}#[cfg(test)]
mod tests_rug_1890 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_min_positive_value() {
        let min_pos_val: f64 = <f64 as FloatCore>::min_positive_value();
        
        assert_eq!(min_pos_val, 5.0e-324);
    }
}#[cfg(test)]
mod tests_rug_1891 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let epsilon_value: f64 = <f64 as FloatCore>::epsilon();

        assert_eq!(epsilon_value, 2.2204460492503131e-16);
    }
}#[cfg(test)]
mod tests_rug_1892 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_max_value() {
        let max_val: f64 = <f64 as FloatCore>::max_value();

        assert_eq!(max_val, std::f64::MAX);
    }
}#[cfg(test)]
mod tests_rug_1893 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = std::f64::NAN; // Using sample data to initialize it

        assert!((<f64 as FloatCore>::is_nan)(p0));
    }
}#[cfg(test)]
mod tests_rug_1894 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.0 / 0.0; // This is a sample to initialize an infinite f64 value

        assert!(<f64 as FloatCore>::is_infinite(p0));

        let p1: f64 = 0.0;
        assert!(!<f64 as FloatCore>::is_infinite(p1));

        let p2: f64 = -1.0 / 0.0; // This is another sample to initialize a negative infinite f64 value
        assert!(<f64 as FloatCore>::is_infinite(p2));
    }
}#[cfg(test)]
mod tests_rug_1895 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        assert!(<f64 as FloatCore>::is_finite(p0));
        
        p0 = f64::INFINITY;
        assert!(!<f64 as FloatCore>::is_finite(p0));
        
        p0 = f64::NEG_INFINITY;
        assert!(!<f64 as FloatCore>::is_finite(p0));
        
        p0 = f64::NAN;
        assert!(!<f64 as FloatCore>::is_finite(p0));
    }
}#[cfg(test)]
mod tests_rug_1896 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14; // Sample data for f64

        assert_eq!(<f64 as FloatCore>::is_normal(p0), true);

        // Additional test cases
        let p1: f64 = 0.0;
        let p2: f64 = f64::INFINITY;
        let p3: f64 = f64::NEG_INFINITY;
        let p4: f64 = f64::NAN;
        let p5: f64 = -0.0;

        assert_eq!(<f64 as FloatCore>::is_normal(p1), false);
        assert_eq!(<f64 as FloatCore>::is_normal(p2), false);
        assert_eq!(<f64 as FloatCore>::is_normal(p3), false);
        assert_eq!(<f64 as FloatCore>::is_normal(p4), false);
        assert_eq!(<f64 as FloatCore>::is_normal(p5), false);

        let p6: f64 = 1.0e-308; // Subnormal number
        assert_eq!(<f64 as FloatCore>::is_normal(p6), false);

        let p7: f64 = 1.0;
        assert_eq!(<f64 as FloatCore>::is_normal(p7), true);
    }
}#[cfg(test)]
mod tests_rug_1897 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as FloatCore>::classify(p0);
    }
}#[cfg(test)]
mod tests_rug_1898 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        assert_eq!(<f64 as FloatCore>::floor(p0), 3.0);
    }
}#[cfg(test)]
mod tests_rug_1899 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        assert_eq!(<f64 as FloatCore>::ceil(p0), 4.0);
    }
}#[cfg(test)]
mod tests_rug_1900 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        <f64 as FloatCore>::round(p0);
    }
}#[cfg(test)]
mod tests_rug_1901 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.456;

        <f64 as FloatCore>::trunc(p0);
    }
}#[cfg(test)]
mod tests_rug_1902 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        <f64 as FloatCore>::fract(p0);
    }
}#[cfg(test)]
mod tests_rug_1903 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = -123.45;

        let result = <f64 as FloatCore>::abs(p0);
        assert_eq!(result, 123.45);
    }
}#[cfg(test)]
mod tests_rug_1904 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = -3.14;

        assert_eq!(<f64 as FloatCore>::signum(p0), -1.0);
        
        p0 = 2.71;
        assert_eq!(<f64 as FloatCore>::signum(p0), 1.0);

        p0 = 0.0;
        assert_eq!(<f64 as FloatCore>::signum(p0), 0.0);
    }
}#[cfg(test)]
mod tests_rug_1905 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        assert!(<f64 as FloatCore>::is_sign_positive(p0));
    }
}#[cfg(test)]
mod tests_rug_1906 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let p0: f64 = -3.14;

        assert_eq!(<f64 as FloatCore>::is_sign_negative(p0), true);
    }
}#[cfg(test)]
mod tests_rug_1907 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;
        let mut p1: f64 = 2.71;

        assert_eq!((<f64 as FloatCore>::min)(p0, p1), 2.71);
    }
}#[cfg(test)]
mod tests_rug_1908 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;
        let mut p1: f64 = 2.71;

        assert_eq!(<f64 as FloatCore>::max(p0, p1), 3.14);
    }
}#[cfg(test)]
mod tests_rug_1909 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;

        let result = <f64 as FloatCore>::recip(p0);
        assert_eq!(result, 0.4);
    }
}#[cfg(test)]
mod tests_rug_1910 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: i32 = 3;

        <f64 as FloatCore>::powi(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1911 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.5708; // Sample value for f64, which is π/2 radians

        let result = <f64 as FloatCore>::to_degrees(p0);
        
        assert_eq!(result, 90.0); // π/2 radians is 90 degrees
    }
}#[cfg(test)]
mod tests_rug_1912 {
    use super::*;
    use crate::float::FloatCore;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 180.0;

        <f64 as FloatCore>::to_radians(p0);
    }
}#[cfg(test)]
mod tests_rug_1913 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_nan() {
        let nan_value: f32 = <f32 as Float>::nan();
        
        assert!(nan_value.is_nan());
    }
}#[cfg(test)]
mod tests_rug_1914 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_infinity() {
        let inf: f32 = <f32 as Float>::infinity();

        assert_eq!(inf, std::f32::INFINITY);
    }
}#[cfg(test)]
mod tests_rug_1915 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_neg_infinity() {
        let result: f32 = <f32 as Float>::neg_infinity();

        assert_eq!(result, std::f32::NEG_INFINITY);
    }
}#[cfg(test)]
mod tests_rug_1916 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_neg_zero() {
        let result: f32 = <f32 as Float>::neg_zero();
        
        assert_eq!(result, -0.0);
    }
}#[cfg(test)]
mod tests_rug_1917 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_min_value() {
        let min_f32: f32 = <f32 as Float>::min_value();

        assert_eq!(min_f32, std::f32::MIN);
    }
}#[cfg(test)]
mod tests_rug_1918 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_min_positive_value() {
        let result: f32 = <f32 as Float>::min_positive_value();
        assert_eq!(result, 1.1754944e-38);
    }
}#[cfg(test)]
mod tests_rug_1919 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_epsilon() {
        let result: f32 = <f32 as Float>::epsilon();
        assert_eq!(result, 1.1920929e-7);
    }
}#[cfg(test)]
mod tests_rug_1920 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_max_value() {
        let max_f32: f32 = <f32 as Float>::max_value();

        assert_eq!(max_f32, std::f32::MAX);
    }
}#[cfg(test)]
mod tests_rug_1921 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 0.0 / 0.0; // This will create a NaN value

        assert!(<f32 as Float>::is_nan(p0));
    }
}#[cfg(test)]
mod tests_rug_1922 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_rug() {
        let p0: f32 = 1.0 / 0.0; // This is a sample to initialize an infinite value

        assert!(<f32 as Float>::is_infinite(p0));
    }
}#[cfg(test)]
mod tests_rug_1923 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 42.0;

        <f32 as Float>::is_finite(p0);
    }
}#[cfg(test)]
mod tests_rug_1924 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.234; // Sample data for f32

        <f32 as Float>::is_normal(p0);
    }
}#[cfg(test)]
mod tests_rug_1925 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as Float>::classify(p0);
    }
}#[cfg(test)]
mod tests_rug_1926 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456;

        <f32 as Float>::floor(p0);
    }
}#[cfg(test)]
mod tests_rug_1927 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 3.14;

        <f32 as Float>::ceil(p0);
    }
}#[cfg(test)]
mod tests_rug_1928 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_round() {
        let mut p0: f32 = 1.5;

        assert_eq!(<f32 as Float>::round(p0), 2.0);
    }
}#[cfg(test)]
mod tests_rug_1929 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 3.14;

        <f32 as Float>::trunc(p0);
    }
}#[cfg(test)]
mod tests_rug_1930 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 3.14;

        <f32 as Float>::fract(p0);
    }
}#[cfg(test)]
mod tests_rug_1931 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = -10.5;

        <f32 as Float>::abs(p0);
    }
}#[cfg(test)]
mod tests_rug_1932 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = -1.5; // Sample data for f32

        <f32 as Float>::signum(p0);
    }
}#[cfg(test)]
mod tests_rug_1933 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 42.0;

        <f32 as Float>::is_sign_positive(p0);
    }
}#[cfg(test)]
mod tests_rug_1934 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = -42.42;

        <f32 as Float>::is_sign_negative(p0);
    }
}#[cfg(test)]
mod tests_rug_1935 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.5;
        let mut p1: f32 = 2.5;
        let mut p2: f32 = 3.5;

        <f32 as Float>::mul_add(p0, p1, p2);
    }
}#[cfg(test)]
mod tests_rug_1936 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.5;

        <f32 as Float>::recip(p0);
    }
}#[cfg(test)]
mod tests_rug_1937 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_powi() {
        let mut p0: f32 = 2.0;
        let mut p1: i32 = 3;

        <f32 as Float>::powi(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1938 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_powf() {
        let mut p0: f32 = 2.0;
        let mut p1: f32 = 3.0;

        <f32 as Float>::powf(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1939 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 4.0; // Sample data for f32

        <f32 as Float>::sqrt(p0);
    }
}#[cfg(test)]
mod tests_rug_1940 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.0; // Sample data for f32

        <f32 as Float>::exp(p0);
    }
}#[cfg(test)]
mod tests_rug_1941 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 3.0; // Sample data for f32

        <f32 as Float>::exp2(p0);
    }
}#[cfg(test)]
mod tests_rug_1942 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.0; // Sample data for initialization

        <f32 as Float>::ln(p0);
    }
}#[cfg(test)]
mod tests_rug_1943 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 10.0;
        let mut p1: f32 = 2.0;

        <f32 as Float>::log(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1944 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 8.0; // Sample data for f32

        <f32 as Float>::log2(p0);
    }
}#[cfg(test)]
mod tests_rug_1945 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f32 = 100.0;

        <f32 as Float>::log10(p0);
    }
}#[cfg(test)]
mod tests_rug_1946 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.5708; // Sample data for f32, which is π/2 radians

        <f32 as Float>::to_degrees(p0);
    }
}#[cfg(test)]
mod tests_rug_1947 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f32 = 180.0;

        <f32 as Float>::to_radians(p0);
    }
}#[cfg(test)]
mod tests_rug_1948 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 3.14;
        let mut p1: f32 = 2.71;

        assert_eq!(<f32 as Float>::max(p0, p1), 3.14);
    }
}#[cfg(test)]
mod tests_rug_1949 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 5.6;
        let mut p1: f32 = 3.4;

        <f32 as Float>::min(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1950 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_cbrt() {
        let mut p0: f32 = 27.0;

        <f32 as Float>::cbrt(p0);
    }
}#[cfg(test)]
mod tests_rug_1951 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_hypot() {
        let mut p0: f32 = 3.0;
        let mut p1: f32 = 4.0;

        <f32 as Float>::hypot(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1952 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f32 = 1.234; // Sample data for f32

        <f32 as Float>::sin(p0);
    }
}#[cfg(test)]
mod tests_rug_1953 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.0; // Sample data for f32

        <f32 as Float>::cos(p0);
    }
}#[cfg(test)]
mod tests_rug_1954 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.5708; // This is approximately π/2 radians

        <f32 as Float>::tan(p0);
    }
}#[cfg(test)]
mod tests_rug_1955 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f32 = 0.5;

        <f32 as Float>::asin(p0);
    }
}#[cfg(test)]
mod tests_rug_1956 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 0.5;

        <f32 as Float>::acos(p0);
    }
}#[cfg(test)]
mod tests_rug_1957 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.0; // Sample data for f32

        <f32 as Float>::atan(p0);
    }
}#[cfg(test)]
mod tests_rug_1958 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.0;
        let mut p1: f32 = 2.0;

        <f32 as Float>::atan2(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1959 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f32 = 1.0;

        <f32 as Float>::sin_cos(p0);
    }
}#[cfg(test)]
mod tests_rug_1960 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.0;

        <f32 as Float>::exp_m1(p0);
    }
}#[cfg(test)]
mod tests_rug_1961 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.5_f32;

        <f32 as Float>::ln_1p(p0);
    }
}#[cfg(test)]
mod tests_rug_1962 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.5_f32;

        <f32 as Float>::sinh(p0);
    }
}#[cfg(test)]
mod tests_rug_1963 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.5; // Sample data for f32

        <f32 as Float>::cosh(p0);
    }
}#[cfg(test)]
mod tests_rug_1964 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.0;

        <f32 as Float>::tanh(p0);
    }
}#[cfg(test)]
mod tests_rug_1965 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.5; // Sample data for initialization

        <f32 as Float>::asinh(p0);
    }
}#[cfg(test)]
mod tests_rug_1966 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.5; // Sample data for f32

        <f32 as Float>::acosh(p0);
    }
}#[cfg(test)]
mod tests_rug_1967 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_atanh() {
        let mut p0: f32 = 0.5;

        <f32 as Float>::atanh(p0);
    }
}#[cfg(test)]
mod tests_rug_1968 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_nan() {
        let nan_value: f64 = <f64 as Float>::nan();
        
        assert!(nan_value.is_nan());
    }
}#[cfg(test)]
mod tests_rug_1969 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_infinity() {
        let result: f64 = <f64 as Float>::infinity();
        
        assert_eq!(result, std::f64::INFINITY);
    }
}#[cfg(test)]
mod tests_rug_1970 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_neg_infinity() {
        let result: f64 = <f64 as Float>::neg_infinity();

        assert_eq!(result, std::f64::NEG_INFINITY);
    }
}#[cfg(test)]
mod tests_rug_1971 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_neg_zero() {
        let result: f64 = <f64 as Float>::neg_zero();

        assert_eq!(result, -0.0);
    }
}#[cfg(test)]
mod tests_rug_1972 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_min_value() {
        let value: f64 = <f64 as Float>::min_value();
        
        assert_eq!(value, f64::MIN);
    }
}#[cfg(test)]
mod tests_rug_1973 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_min_positive_value() {
        let min_pos: f64 = <f64 as Float>::min_positive_value();

        assert_eq!(min_pos, 2.2250738585072014e-308);
    }
}#[cfg(test)]
mod tests_rug_1974 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_rug() {
        let epsilon_value: f64 = <f64 as Float>::epsilon();

        assert_eq!(epsilon_value, 2.2204460492503131e-16);
    }
}#[cfg(test)]
mod tests_rug_1975 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_max_value() {
        let max_val: f64 = <f64 as Float>::max_value();

        assert_eq!(max_val, std::f64::MAX);
    }
}#[cfg(test)]
mod tests_rug_1976 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = std::f64::NAN;

        assert!((<f64 as Float>::is_nan)(p0));
    }
}#[cfg(test)]
mod tests_rug_1977 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.0 / 0.0; // This represents positive infinity

        assert!(<f64 as Float>::is_infinite(p0));

        let p1: f64 = -1.0 / 0.0; // This represents negative infinity
        assert!(<f64 as Float>::is_infinite(p1));

        let p2: f64 = 0.0;
        assert!(!<f64 as Float>::is_infinite(p2));

        let p3: f64 = 123.456;
        assert!(!<f64 as Float>::is_infinite(p3));
    }
}#[cfg(test)]
mod tests_rug_1978 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14; // Sample data for f64

        assert!(<f64 as Float>::is_finite(p0));
    }
}#[cfg(test)]
mod tests_rug_1979 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 3.14; // Sample data for a normal floating point number

        assert!(<f64 as Float>::is_normal(p0));
    }
}#[cfg(test)]
mod tests_rug_1980 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 3.14; // Sample value for f64

        <f64 as Float>::classify(p0);
    }
}#[cfg(test)]
mod tests_rug_1981 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        <f64 as Float>::floor(p0);
    }
}#[cfg(test)]
mod tests_rug_1982 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 3.14;

        <f64 as Float>::ceil(p0);
    }
}#[cfg(test)]
mod tests_rug_1983 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        <f64 as Float>::round(p0);
    }
}#[cfg(test)]
mod tests_rug_1984 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 3.14159;

        <f64 as Float>::trunc(p0);
    }
}#[cfg(test)]
mod tests_rug_1985 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as Float>::fract(p0);
    }
}#[cfg(test)]
mod tests_rug_1986 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = -3.14;

        <f64 as Float>::abs(p0);
    }
}#[cfg(test)]
mod tests_rug_1987 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_signum() {
        let mut p0: f64 = -3.14;

        assert_eq!(p0.signum(), -1.0);
        p0 = 0.0;
        assert_eq!(p0.signum(), 0.0);
        p0 = 2.71;
        assert_eq!(p0.signum(), 1.0);
    }
}#[cfg(test)]
mod tests_rug_1988 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        assert!(<f64 as Float>::is_sign_positive(p0));
        
        // Additional test cases
        p0 = -2.71;
        assert!(!<f64 as Float>::is_sign_positive(p0));

        p0 = 0.0;
        assert!(<f64 as Float>::is_sign_positive(p0));

        p0 = -0.0;
        assert!(!<f64 as Float>::is_sign_positive(p0));
    }
}#[cfg(test)]
mod tests_rug_1989 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = -3.14;

        assert_eq!(<f64 as Float>::is_sign_negative(p0), true);
        
        p0 = 2.71;
        assert_eq!(<f64 as Float>::is_sign_negative(p0), false);

        p0 = -0.0;
        assert_eq!(<f64 as Float>::is_sign_negative(p0), true);

        p0 = 0.0;
        assert_eq!(<f64 as Float>::is_sign_negative(p0), false);
    }
}#[cfg(test)]
mod tests_rug_1990 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: f64 = 3.1;
        let mut p2: f64 = 4.7;

        <f64 as Float>::mul_add(p0, p1, p2);
    }
}#[cfg(test)]
mod tests_rug_1991 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 2.5;

        <f64 as Float>::recip(p0);
    }
}#[cfg(test)]
mod tests_rug_1992 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.0;
        let mut p1: i32 = 3;

        <f64 as Float>::powi(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1993 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_powf() {
        let mut p0: f64 = 2.0;
        let mut p1: f64 = 3.0;

        <f64 as Float>::powf(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1994 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 16.0; // Sample data for a positive float

        <f64 as Float>::sqrt(p0);
    }
}#[cfg(test)]
mod tests_rug_1995 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.0;

        <f64 as Float>::exp(p0);
    }
}#[cfg(test)]
mod tests_rug_1996 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.0;

        <f64 as Float>::exp2(p0);
    }
}#[cfg(test)]
mod tests_rug_1997 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 1.5; // Sample data for initialization

        <f64 as Float>::ln(p0);
    }
}#[cfg(test)]
mod tests_rug_1998 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 10.0;
        let mut p1: f64 = 2.0;

        <f64 as Float>::log(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1999 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 16.0; // Sample data for f64

        <f64 as Float>::log2(p0);
    }
}#[cfg(test)]
mod tests_rug_2000 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 100.0;

        <f64 as Float>::log10(p0);
    }
}#[cfg(test)]
mod tests_rug_2001 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_to_degrees() {
        let mut p0: f64 = 1.5708; // This is equivalent to π/2 radians

        let result = <f64 as Float>::to_degrees(p0);
        assert_eq!(result, 90.0);
    }
}#[cfg(test)]
mod tests_rug_2002 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 180.0;

        let result = <f64 as Float>::to_radians(p0);
        assert_eq!(result, std::f64::consts::PI);
    }
}#[cfg(test)]
mod tests_rug_2003 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;
        let mut p1: f64 = 2.71;

        assert_eq!(<f64 as Float>::max(p0, p1), 3.14);
    }
}#[cfg(test)]
mod tests_rug_2004 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;
        let mut p1: f64 = 2.71;

        <f64 as Float>::min(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_2005 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 27.0;

        <f64 as Float>::cbrt(p0);
    }
}#[cfg(test)]
mod tests_rug_2006 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_hypot() {
        let mut p0: f64 = 3.0;
        let mut p1: f64 = 4.0;

        let result = <f64 as Float>::hypot(p0, p1);
        assert_eq!(result, 5.0);
    }
}#[cfg(test)]
mod tests_rug_2007 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.23;

        <f64 as Float>::sin(p0);
    }
}#[cfg(test)]
mod tests_rug_2008 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 1.23; // Sample data for f64 type

        <f64 as Float>::cos(p0);
    }
}#[cfg(test)]
mod tests_rug_2009 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.23;

        <f64 as Float>::tan(p0);
    }
}#[cfg(test)]
mod tests_rug_2010 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 0.5;

        <f64 as Float>::asin(p0);
    }
}#[cfg(test)]
mod tests_rug_2011 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 0.5;

        <f64 as Float>::acos(p0);
    }
}#[cfg(test)]
mod tests_rug_2012 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.0;

        <f64 as Float>::atan(p0);
    }
}#[cfg(test)]
mod tests_rug_2013 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;
        let mut p1: f64 = 2.71;

        <f64 as Float>::atan2(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_2014 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.23; // Sample data for initialization

        <f64 as Float>::sin_cos(p0);
    }
}#[cfg(test)]
mod tests_rug_2015 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.0; // Sample data for initialization

        <f64 as Float>::exp_m1(p0);
    }
}#[cfg(test)]
mod tests_rug_2016 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let p0: f64 = 1.0; // Sample data for the first argument

        <f64 as Float>::ln_1p(p0);
    }
}#[cfg(test)]
mod tests_rug_2017 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.0; // Sample data for f64 type

        <f64 as Float>::sinh(p0);
    }
}#[cfg(test)]
mod tests_rug_2018 {
    use super::*;
    use crate::float::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.234;

        <f64 as Float>::cosh(p0);
    }
}#[cfg(test)]
mod tests_rug_2019 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.0;

        <f64 as Float>::tanh(p0);
    }
}#[cfg(test)]
mod tests_rug_2020 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.0; // Sample data for f64

        <f64 as Float>::asinh(p0);
    }
}#[cfg(test)]
mod tests_rug_2021 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.5; // Sample data for f64

        <f64 as Float>::acosh(p0);
    }
}#[cfg(test)]
mod tests_rug_2022 {
    use super::*;
    use crate::Float;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 0.5; // Sample data for a valid input to atanh

        <f64 as Float>::atanh(p0);
    }
}#[cfg(test)]
mod tests_rug_2023 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_e_constant() {
        let e: f32 = <f32 as FloatConst>::E();
        
        assert_eq!(e, std::f32::consts::E);
    }
}#[cfg(test)]
mod tests_rug_2024 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let result: f32 = <f32 as FloatConst>::FRAC_1_PI();
        
        // Example assertion, you might want to adjust the expected value based on your precision needs
        assert!((result - 0.31830987).abs() < 1e-6);
    }
}#[cfg(test)]
mod tests_rug_2025 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let result: f32 = <f32 as FloatConst>::FRAC_1_SQRT_2();

        assert_eq!(result, 0.70710678);
    }
}#[cfg(test)]
mod tests_rug_2026 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_fract_2_pi() {
        let expected: f32 = 0.6366197723675814; // This is the value of FRAC_2_PI for f32

        let result = <f32 as FloatConst>::FRAC_2_PI();

        assert_eq!(result, expected);
    }
}#[cfg(test)]
mod tests_rug_2027 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let result: f32 = <f32 as FloatConst>::FRAC_2_SQRT_PI();
        
        // Example assertion, you can adjust this based on your needs
        assert!((result - 1.128379167095512573896158903121545171688).abs() < 1e-6);
    }
}#[cfg(test)]
mod tests_rug_2028 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let pi_over_two: f32 = <f32 as FloatConst>::FRAC_PI_2();

        assert_eq!(pi_over_two, std::f32::consts::FRAC_PI_2);
    }
}#[cfg(test)]
mod tests_rug_2029 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_frac_pi_3() {
        let result: f32 = <f32 as FloatConst>::FRAC_PI_3();
        assert_eq!(result, std::f32::consts::PI / 3.0);
    }
}#[cfg(test)]
mod tests_rug_2030 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let pi_over_four: f32 = <f32 as FloatConst>::FRAC_PI_4();
        
        assert_eq!(pi_over_four, std::f32::consts::FRAC_PI_4);
    }
}#[cfg(test)]
mod tests_rug_2031 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_frac_pi_6() {
        let frac_pi_6: f32 = <f32 as FloatConst>::FRAC_PI_6();

        assert_eq!(frac_pi_6, std::f32::consts::PI / 6.0);
    }
}#[cfg(test)]
mod tests_rug_2032 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let frac_pi_8: f32 = <f32 as FloatConst>::FRAC_PI_8();

        assert_eq!(frac_pi_8, std::f32::consts::PI / 8.0);
    }
}#[cfg(test)]
mod tests_rug_2033 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_ln_10() {
        let ln_10_f32: f32 = <f32 as FloatConst>::LN_10();
        
        assert_eq!(ln_10_f32, 2.3025851f32);
    }
}#[cfg(test)]
mod tests_rug_2034 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_ln_2() {
        let ln_2: f32 = <f32 as FloatConst>::LN_2();
        
        assert_eq!(ln_2, 0.6931472);
    }
}#[cfg(test)]
mod tests_rug_2035 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_log10_e() {
        let log10_e: f32 = <f32 as FloatConst>::LOG10_E();
        
        // You can add assertions here to verify the value if needed
        assert_eq!(log10_e, 0.4342945);
    }
}#[cfg(test)]
mod tests_rug_2036 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_log2_e() {
        let log2_e: f32 = <f32 as FloatConst>::LOG2_E();
        
        // Example assertion, you can adjust based on your needs
        assert!((log2_e - 1.4426950408889634).abs() < 1e-7);
    }
}#[cfg(test)]
mod tests_rug_2037 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_pi() {
        let pi_value: f32 = <f32 as FloatConst>::PI();
        
        assert_eq!(pi_value, std::f32::consts::PI);
    }
}#[cfg(test)]
mod tests_rug_2038 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_sqrt_2() {
        let sqrt_two: f32 = <f32 as FloatConst>::SQRT_2();
        
        assert_eq!(sqrt_two, 1.4142135);
    }
}#[cfg(test)]
mod tests_rug_2039 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_tau() {
        let tau: f32 = <f32 as FloatConst>::TAU();
        
        assert_eq!(tau, std::f32::consts::PI * 2.0);
    }
}#[cfg(test)]
mod tests_rug_2040 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_log10_2() {
        let log10_2: f32 = <f32 as FloatConst>::LOG10_2();
        assert_eq!(log10_2, 0.3010299956639812);
    }
}#[cfg(test)]
mod tests_rug_2041 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_log2_10() {
        let log2_10: f32 = <f32 as FloatConst>::LOG2_10();
        
        // You can add assertions here to verify the value if needed
        assert_eq!(log2_10, 3.3219281);
    }
}#[cfg(test)]
mod tests_rug_2042 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_e() {
        let e: f64 = <f64 as FloatConst>::E();
        assert_eq!(e, std::f64::consts::E);
    }
}#[cfg(test)]
mod tests_rug_2043 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let result: f64 = <f64 as FloatConst>::FRAC_1_PI();
        
        // Example assertion, you might want to adjust the expected value based on precision requirements
        assert_eq!(result, 0.3183098861837907);
    }
}#[cfg(test)]
mod tests_rug_2044 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let result: f64 = <f64 as FloatConst>::FRAC_1_SQRT_2();
        
        assert_eq!(result, 0.7071067811865476);
    }
}#[cfg(test)]
mod tests_rug_2045 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let expected: f64 = 0.6366197723675814; // This is the value of 2/π

        let result: f64 = <f64 as FloatConst>::FRAC_2_PI();

        assert_eq!(result, expected);
    }
}#[cfg(test)]
mod tests_rug_2046 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_fract_2_sqrt_pi() {
        let expected: f64 = 1.1283791670955126; // This is the value of 2/sqrt(pi)

        assert_eq!(<f64 as FloatConst>::FRAC_2_SQRT_PI(), expected);
    }
}#[cfg(test)]
mod tests_rug_2047 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_frfrac_pi_2() {
        let result: f64 = <f64 as FloatConst>::FRAC_PI_2();

        assert_eq!(result, std::f64::consts::FRAC_PI_2);
    }
}#[cfg(test)]
mod tests_rug_2048 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_fracion_pi_3() {
        let pi_over_3: f64 = <f64 as FloatConst>::FRAC_PI_3();

        assert_eq!(pi_over_3, std::f64::consts::PI / 3.0);
    }
}#[cfg(test)]
mod tests_rug_2049 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_rug() {
        let result: f64 = <f64 as FloatConst>::FRAC_PI_4();
        assert_eq!(result, std::f64::consts::FRAC_PI_4);
    }
}#[cfg(test)]
mod tests_rug_2050 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_frac_pi_6() {
        let expected_value: f64 = std::f64::consts::PI / 6.0;
        let actual_value: f64 = <f64 as FloatConst>::FRAC_PI_6();

        assert_eq!(actual_value, expected_value);
    }
}#[cfg(test)]
mod tests_rug_2051 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_fract_pi_8() {
        let result: f64 = <f64 as FloatConst>::FRAC_PI_8();

        // Example assertion, you can replace it with a more precise check if needed
        assert_eq!(result, std::f64::consts::PI / 8.0);
    }
}#[cfg(test)]
mod tests_rug_2052 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_ln_10() {
        let expected: f64 = 2.302585092994046;
        let result: f64 = <f64 as FloatConst>::LN_10();

        assert_eq!(result, expected);
    }
}#[cfg(test)]
mod tests_rug_2053 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_ln_2() {
        let expected: f64 = 0.6931471805599453;
        let result: f64 = <f64 as FloatConst>::LN_2();

        assert_eq!(result, expected);
    }
}#[cfg(test)]
mod tests_rug_2054 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_log10_e() {
        let expected: f64 = 0.4342944819032518;
        let result: f64 = <f64 as FloatConst>::LOG10_E();

        assert_eq!(result, expected);
    }
}#[cfg(test)]
mod tests_rug_2055 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_log2_e() {
        let log2_e: f64 = <f64 as FloatConst>::LOG2_E();

        assert_eq!(log2_e, 1.4426950408889634);
    }
}#[cfg(test)]
mod tests_rug_2056 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_pi() {
        let pi: f64 = <f64 as FloatConst>::PI();

        assert_eq!(pi, std::f64::consts::PI);
    }
}#[cfg(test)]
mod tests_rug_2057 {
    use crate::float::FloatConst;

    #[test]
    fn test_sqrt_2() {
        let sqrt_2: f64 = <f64 as FloatConst>::SQRT_2();
        assert_eq!(sqrt_2, std::f64::consts::SQRT_2);
    }
}#[cfg(test)]
mod tests_rug_2058 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_tau() {
        let tau: f64 = <f64 as FloatConst>::TAU();

        assert_eq!(tau, std::f64::consts::PI * 2.0);
    }
}#[cfg(test)]
mod tests_rug_2059 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_log10_2() {
        let result: f64 = <f64 as FloatConst>::LOG10_2();
        assert_eq!(result, 0.3010299956639812);
    }
}#[cfg(test)]
mod tests_rug_2060 {
    use super::*;
    use crate::float::FloatConst;

    #[test]
    fn test_log2_10() {
        let log2_10: f64 = <f64 as FloatConst>::LOG2_10();
        assert_eq!(log2_10, 3.321928094887362);
    }
}#[cfg(test)]
mod tests_rug_2061 {
    use super::*;
    use crate::real::Real;

    #[test]
    fn test_min_value() {
        let value: f64 = 0.0;
        
        let min_val = <f64 as Real>::min_value();
        
        assert_eq!(min_val, std::f64::MIN);
    }
}#[cfg(test)]
mod tests_rug_2062 {
    use super::*;
    use crate::real::Real;

    #[test]
    fn test_min_positive_value_f32() {
        let result: f32 = <f32 as Real>::min_positive_value();
        assert_eq!(result, f32::MIN_POSITIVE);
    }

    #[test]
    fn test_min_positive_value_f64() {
        let result: f64 = <f64 as Real>::min_positive_value();
        assert_eq!(result, f64::MIN_POSITIVE);
    }
}#[cfg(test)]
mod tests_rug_2063 {
    use super::*;
    use crate::real::Real;

    #[test]
    fn test_epsilon() {
        let x: f64 = 1.0;
        
        let epsilon_value: f64 = <f64 as Real>::epsilon();
        
        assert!(epsilon_value > 0.0);
        assert!(epsilon_value <= x);
    }
}#[cfg(test)]
mod tests_rug_2064 {
    use super::*;
    use crate::real::Real;

    #[test]
    fn test_rug() {
        let x: f64 = 3.14;
        let y: f64 = 2.71;

        // Since `max_value` is a static method that returns the maximum value for the type,
        // it does not take any arguments.
        let max_f64: f64 = <f64 as Real>::max_value();

        assert_eq!(max_f64, std::f64::MAX);
    }
}use crate::Float;fn calculate<T: Float>(value: T) -> T {
    // Perform some calculations using the trait's methods
    value.exp() + value.sqrt()
}fn compute_something<F: Float>(value: F) -> F {
    value.sqrt() + value.ln_1p()
}