use super::Configurable;

use crate::config_file::Config;

use clap::ArgMatches;

/// The flag showing how to display symbolic arrow.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymlinkArrow(String);

impl Configurable<Self> for SymlinkArrow {
    /// `SymlinkArrow` can not be configured by [ArgMatches]
    ///
    /// Return `None`
    fn from_arg_matches(_: &ArgMatches) -> Option<Self> {
        None
    }
    /// Get a potential `SymlinkArrow` value from a [Config].
    ///
    /// If the `Config::symlink-arrow` has value,
    /// returns its value as the value of the `SymlinkArrow`, in a [Some].
    /// Otherwise this returns [None].
    fn from_config(config: &Config) -> Option<Self> {
        config
            .symlink_arrow
            .as_ref()
            .map(|arrow| SymlinkArrow(arrow.to_string()))
    }
}

/// The default value for the `SymlinkArrow` is `\u{21d2}(⇒)`
impl Default for SymlinkArrow {
    fn default() -> Self {
        Self(String::from("\u{21d2}")) // ⇒
    }
}

use std::fmt;
impl fmt::Display for SymlinkArrow {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod test {
    use crate::config_file::Config;
    use crate::flags::Configurable;

    use super::SymlinkArrow;
    #[test]
    fn test_symlink_arrow_from_config_utf8() {
        let mut c = Config::with_none();
        c.symlink_arrow = Some("↹".into());
        assert_eq!(
            Some(SymlinkArrow(String::from("\u{21B9}"))),
            SymlinkArrow::from_config(&c)
        );
    }

    #[test]
    fn test_symlink_arrow_from_args_none() {
        use clap::App;
        assert_eq!(
            None,
            SymlinkArrow::from_arg_matches(&App::new("lsd").get_matches())
        );
    }

    #[test]
    fn test_symlink_arrow_default() {
        assert_eq!(
            SymlinkArrow(String::from("\u{21d2}")),
            SymlinkArrow::default()
        );
    }

    #[test]
    fn test_symlink_display() {
        assert_eq!("⇒", format!("{}", SymlinkArrow::default()));
    }
}
#[cfg(test)]
mod tests_rug_143 {
    use super::*;
    use crate::flags::{Configurable, symlink_arrow::SymlinkArrow};
    use clap::ArgMatches;

    #[test]
    fn test_rug() {
        let mut p0: ArgMatches<'_> = ArgMatches::default();

        <SymlinkArrow as Configurable<SymlinkArrow>>::from_arg_matches(&p0);

    }
}#[cfg(test)]
mod tests_rug_144 {
    use super::*;
    use crate::flags::{self, Configurable};
    use crate::config_file::Config;

    #[test]
    fn test_from_config_with_symlink_arrow() {
        let mut config = Config::default();
        config.symlink_arrow = Some(String::from("->"));

        let result = <flags::symlink_arrow::SymlinkArrow as flags::Configurable<flags::symlink_arrow::SymlinkArrow>>::from_config(&config);

        assert_eq!(result, Some(flags::symlink_arrow::SymlinkArrow(String::from("->"))));
    }

    #[test]
    fn test_from_config_without_symlink_arrow() {
        let config = Config::default();

        let result = <flags::symlink_arrow::SymlinkArrow as flags::Configurable<flags::symlink_arrow::SymlinkArrow>>::from_config(&config);

        assert_eq!(result, None);
    }
}#[cfg(test)]
mod tests_rug_145 {
    use super::*;
    use crate::flags::symlink_arrow::SymlinkArrow;
    use std::default::Default;

    #[test]
    fn test_symlink_arrow_default() {
        let default_arrow: SymlinkArrow = <SymlinkArrow as Default>::default();
        
        assert_eq!(default_arrow.0, "\u{21d2}");
    }
}