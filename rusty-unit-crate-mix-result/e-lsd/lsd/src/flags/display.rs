//! This module defines the [Display] flag. To set it up from [ArgMatches], a [Config] and its
//! [Default] value, use its [configure_from](Configurable::configure_from) method.

use super::Configurable;

use crate::config_file::Config;

use clap::ArgMatches;
use serde::Deserialize;

/// The flag showing which file system nodes to display.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Display {
    All,
    AlmostAll,
    DirectoryOnly,
    VisibleOnly,
}

impl Configurable<Self> for Display {
    /// Get a potential `Display` variant from [ArgMatches].
    ///
    /// If any of the "all", "almost-all" or "directory-only" arguments is passed, this returns the
    /// corresponding `Display` variant in a [Some]. If neither of them is passed, this returns
    /// [None].
    fn from_arg_matches(matches: &ArgMatches) -> Option<Self> {
        if matches.is_present("directory-only") {
            Some(Self::DirectoryOnly)
        } else if matches.is_present("almost-all") {
            Some(Self::AlmostAll)
        } else if matches.is_present("all") {
            Some(Self::All)
        } else {
            None
        }
    }

    /// Get a potential `Display` variant from a [Config].
    ///
    /// If the `Config::display` has value and is one of
    /// "all", "almost-all", "directory-only" or `visible-only`,
    /// this returns the corresponding `Display` variant in a [Some].
    /// Otherwise this returns [None].
    fn from_config(config: &Config) -> Option<Self> {
        config.display
    }
}

/// The default value for `Display` is [Display::VisibleOnly].
impl Default for Display {
    fn default() -> Self {
        Display::VisibleOnly
    }
}

#[cfg(test)]
mod test {
    use super::Display;

    use crate::app;
    use crate::config_file::Config;
    use crate::flags::Configurable;

    #[test]
    fn test_from_arg_matches_none() {
        let argv = vec!["lsd"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(None, Display::from_arg_matches(&matches));
    }

    #[test]
    fn test_from_arg_matches_all() {
        let argv = vec!["lsd", "--all"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(Some(Display::All), Display::from_arg_matches(&matches));
    }

    #[test]
    fn test_from_arg_matches_almost_all() {
        let argv = vec!["lsd", "--almost-all"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(Display::AlmostAll),
            Display::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_arg_matches_directory_only() {
        let argv = vec!["lsd", "--directory-only"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(Display::DirectoryOnly),
            Display::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_config_none() {
        assert_eq!(None, Display::from_config(&Config::with_none()));
    }

    #[test]
    fn test_from_config_all() {
        let mut c = Config::with_none();
        c.display = Some(Display::All);
        assert_eq!(Some(Display::All), Display::from_config(&c));
    }

    #[test]
    fn test_from_config_almost_all() {
        let mut c = Config::with_none();
        c.display = Some(Display::AlmostAll);
        assert_eq!(Some(Display::AlmostAll), Display::from_config(&c));
    }

    #[test]
    fn test_from_config_directory_only() {
        let mut c = Config::with_none();
        c.display = Some(Display::DirectoryOnly);
        assert_eq!(Some(Display::DirectoryOnly), Display::from_config(&c));
    }

    #[test]
    fn test_from_config_visible_only() {
        let mut c = Config::with_none();
        c.display = Some(Display::VisibleOnly);
        assert_eq!(Some(Display::VisibleOnly), Display::from_config(&c));
    }
}
#[cfg(test)]
mod tests_rug_91 {
    use super::*;
    use crate::flags::{Configurable, display::Display};
    use clap::{App, Arg, ArgMatches};

    #[test]
    fn test_rug() {
        let app = App::new("lsd")
            .arg(Arg::with_name("directory-only").long("directory-only"))
            .arg(Arg::with_name("almost-all").long("almost-all"))
            .arg(Arg::with_name("all").long("all"));

        // Test with "directory-only"
        let mut p0: ArgMatches = app.clone().get_matches_from(vec!["lsd", "--directory-only"]);
        assert_eq!(Display::from_arg_matches(&p0), Some(Display::DirectoryOnly));

        // Test with "almost-all"
        let mut p1: ArgMatches = app.clone().get_matches_from(vec!["lsd", "--almost-all"]);
        assert_eq!(Display::from_arg_matches(&p1), Some(Display::AlmostAll));

        // Test with "all"
        let mut p2: ArgMatches = app.clone().get_matches_from(vec!["lsd", "--all"]);
        assert_eq!(Display::from_arg_matches(&p2), Some(Display::All));

        // Test without any flags
        let mut p3: ArgMatches = app.get_matches_from(vec!["lsd"]);
        assert_eq!(Display::from_arg_matches(&p3), None);
    }
}#[cfg(test)]
mod tests_rug_92 {
    use super::*;
    use crate::flags::{Configurable, display::Display};
    use crate::config_file::Config;

    #[test]
    fn test_rug() {
        let mut config = Config::default();

        <Display as Configurable<Display>>::from_config(&config);
    }
}#[cfg(test)]
mod tests_rug_93 {
    use super::*;
    use crate::flags::display::Display;

    #[test]
    fn test_default_display() {
        let display: Display = <Display as Default>::default();
        
        assert_eq!(display, Display::VisibleOnly);
    }
}