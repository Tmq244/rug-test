//! This module defines the [Dereference] flag. To set it up from [ArgMatches], a [Config] and its
//! [Default] value, use the [configure_from](Configurable::configure_from) method.

use super::Configurable;

use crate::config_file::Config;

use clap::ArgMatches;

/// The flag showing whether to dereference symbolic links.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Default)]
pub struct Dereference(pub bool);

impl Configurable<Self> for Dereference {
    /// Get a potential `Dereference` value from [ArgMatches].
    ///
    /// If the "dereference" argument is passed, this returns a `Dereference` with value `true` in
    /// a [Some]. Otherwise this returns [None].
    fn from_arg_matches(matches: &ArgMatches) -> Option<Self> {
        if matches.is_present("dereference") {
            Some(Self(true))
        } else {
            None
        }
    }

    /// Get a potential `Dereference` value from a [Config].
    ///
    /// If the `Config::dereference` has value, this returns its value
    /// as the value of the `Dereference`, in a [Some], Otherwise this returns [None].
    fn from_config(config: &Config) -> Option<Self> {
        config.dereference.as_ref().map(|deref| Self(*deref))
    }
}

#[cfg(test)]
mod test {
    use super::Dereference;

    use crate::app;
    use crate::config_file::Config;
    use crate::flags::Configurable;

    #[test]
    fn test_from_arg_matches_none() {
        let argv = vec!["lsd"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(None, Dereference::from_arg_matches(&matches));
    }

    #[test]
    fn test_from_arg_matches_true() {
        let argv = vec!["lsd", "--dereference"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(Dereference(true)),
            Dereference::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_config_none() {
        assert_eq!(None, Dereference::from_config(&Config::with_none()));
    }

    #[test]
    fn test_from_config_true() {
        let mut c = Config::with_none();
        c.dereference = Some(true);
        assert_eq!(Some(Dereference(true)), Dereference::from_config(&c));
    }

    #[test]
    fn test_from_config_false() {
        let mut c = Config::with_none();
        c.dereference = Some(false);
        assert_eq!(Some(Dereference(false)), Dereference::from_config(&c));
    }
}
#[cfg(test)]
mod tests_rug_89 {
    use super::*;
    use crate::flags::{Configurable, dereference::Dereference};
    use clap::{App, Arg, ArgMatches};

    #[test]
    fn test_rug() {
        let mut app = App::new("myapp")
            .arg(Arg::with_name("dereference").long("dereference"));
        
        let p0: ArgMatches = app.get_matches_from(vec!["myapp", "--dereference"]);

        assert_eq!(<Dereference as Configurable<Dereference>>::from_arg_matches(&p0), Some(Dereference(true)));
    }

    #[test]
    fn test_no_deref() {
        let mut app = App::new("myapp")
            .arg(Arg::with_name("dereference").long("dereference"));
        
        let p0: ArgMatches = app.get_matches_from(vec!["myapp"]);

        assert_eq!(<Dereference as Configurable<Dereference>>::from_arg_matches(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_90 {
    use super::*;
    use crate::flags::{self, Configurable};
    use crate::config_file::Config;

    #[test]
    fn test_rug() {
        let mut config = Config::default();

        <flags::dereference::Dereference as Configurable<flags::dereference::Dereference>>::from_config(&config);
    }
}