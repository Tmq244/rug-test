//! This module defines the [NoSymlink] flag. To set it up from [ArgMatches], a [Config] and its
//! [Default] value, use the [configure_from](Configurable::configure_from) method.

use super::Configurable;

use crate::config_file::Config;

use clap::ArgMatches;

/// The flag showing whether to follow symbolic links.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Default)]
pub struct NoSymlink(pub bool);

impl Configurable<Self> for NoSymlink {
    /// Get a potential `NoSymlink` value from [ArgMatches].
    ///
    /// If the "no-symlink" argument is passed, this returns a `NoSymlink` with value `true` in a
    /// [Some]. Otherwise this returns [None].
    fn from_arg_matches(matches: &ArgMatches) -> Option<Self> {
        if matches.is_present("no-symlink") {
            Some(Self(true))
        } else {
            None
        }
    }

    /// Get a potential `NoSymlink` value from a [Config].
    ///
    /// If the `Config::no-symlink` has value,
    /// this returns it as the value of the `NoSymlink`, in a [Some].
    /// Otherwise this returns [None].
    fn from_config(config: &Config) -> Option<Self> {
        config.no_symlink.map(Self)
    }
}

#[cfg(test)]
mod test {
    use super::NoSymlink;

    use crate::app;
    use crate::config_file::Config;
    use crate::flags::Configurable;

    #[test]
    fn test_from_arg_matches_none() {
        let argv = vec!["lsd"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(None, NoSymlink::from_arg_matches(&matches));
    }

    #[test]
    fn test_from_arg_matches_true() {
        let argv = vec!["lsd", "--no-symlink"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(Some(NoSymlink(true)), NoSymlink::from_arg_matches(&matches));
    }

    #[test]
    fn test_from_config_none() {
        assert_eq!(None, NoSymlink::from_config(&Config::with_none()));
    }

    #[test]
    fn test_from_config_true() {
        let mut c = Config::with_none();
        c.no_symlink = Some(true);
        assert_eq!(Some(NoSymlink(true)), NoSymlink::from_config(&c));
    }

    #[test]
    fn test_from_config_false() {
        let mut c = Config::with_none();
        c.no_symlink = Some(false);
        assert_eq!(Some(NoSymlink(false)), NoSymlink::from_config(&c));
    }
}
#[cfg(test)]
mod tests_rug_146 {
    use super::*;
    use crate::flags::{self, Configurable};
    use clap::{App, Arg};

    #[test]
    fn test_rug() {
        let mut app = App::new("test")
            .arg(Arg::with_name("no-symlink").long("no-symlink"));
        
        let matches_with_no_symlink = app.clone().get_matches_from(vec!["test", "--no-symlink"]);
        let matches_without_no_symlink = app.get_matches_from(vec!["test"]);

        assert_eq!(
            <flags::symlinks::NoSymlink as Configurable<flags::symlinks::NoSymlink>>::from_arg_matches(&matches_with_no_symlink),
            Some(flags::symlinks::NoSymlink(true))
        );

        assert_eq!(
            <flags::symlinks::NoSymlink as Configurable<flags::symlinks::NoSymlink>>::from_arg_matches(&matches_without_no_symlink),
            None
        );
    }
}#[cfg(test)]
mod tests_rug_147 {
    use super::*;
    use crate::flags::{symlinks::NoSymlink, Configurable};
    use crate::config_file::Config;

    #[test]
    fn test_rug() {
        let mut p0: &Config = &Config::default();

        <NoSymlink>::from_config(p0);
    }
}