//! This module defines the [IconOption]. To set it up from [ArgMatches], a [Config] and its
//! [Default] value, use its [configure_from](Configurable::configure_from) method.

use super::Configurable;

use crate::config_file::Config;

use clap::ArgMatches;
use serde::Deserialize;

/// A collection of flags on how to use icons.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Icons {
    /// When to use icons.
    pub when: IconOption,
    /// Which icon theme to use.
    pub theme: IconTheme,
    /// String between icon and name.
    pub separator: IconSeparator,
}

impl Icons {
    /// Get an `Icons` struct from [ArgMatches], a [Config] or the [Default] values.
    ///
    /// The [IconOption] and [IconTheme] are configured with their respective [Configurable]
    /// implementation.
    pub fn configure_from(matches: &ArgMatches, config: &Config) -> Self {
        let when = IconOption::configure_from(matches, config);
        let theme = IconTheme::configure_from(matches, config);
        let separator = IconSeparator::configure_from(matches, config);
        Self {
            when,
            theme,
            separator,
        }
    }
}

/// The flag showing when to use icons in the output.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum IconOption {
    Always,
    Auto,
    Never,
}

impl Configurable<Self> for IconOption {
    /// Get a potential `IconOption` variant from [ArgMatches].
    ///
    /// If the "classic" argument is passed, then this returns the [IconOption::Never] variant in
    /// a [Some]. Otherwise if the argument is passed, this returns the variant corresponding to
    /// its parameter in a [Some]. Otherwise this returns [None].
    fn from_arg_matches(matches: &ArgMatches) -> Option<Self> {
        if matches.is_present("classic") {
            Some(Self::Never)
        } else if matches.occurrences_of("icon") > 0 {
            match matches.values_of("icon")?.last() {
                Some("always") => Some(Self::Always),
                Some("auto") => Some(Self::Auto),
                Some("never") => Some(Self::Never),
                _ => panic!("This should not be reachable!"),
            }
        } else {
            None
        }
    }

    /// Get a potential `IconOption` variant from a [Config].
    ///
    /// If the `Configs::classic` has value and is "true" then this returns Some(IconOption::Never).
    /// Otherwise if the `Config::icon::when` has value and is one of "always", "auto" or "never",
    /// this returns its corresponding variant in a [Some].
    /// Otherwise this returns [None].
    fn from_config(config: &Config) -> Option<Self> {
        if let Some(true) = &config.classic {
            return Some(Self::Never);
        }

        if let Some(icon) = &config.icons {
            icon.when
        } else {
            None
        }
    }
}

/// The default value for the `IconOption` is [IconOption::Auto].
impl Default for IconOption {
    fn default() -> Self {
        Self::Auto
    }
}

/// The flag showing which icon theme to use.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum IconTheme {
    Unicode,
    Fancy,
}

impl Configurable<Self> for IconTheme {
    /// Get a potential `IconTheme` variant from [ArgMatches].
    ///
    /// If the argument is passed, this returns the variant corresponding to its parameter in a
    /// [Some]. Otherwise this returns [None].
    fn from_arg_matches(matches: &ArgMatches) -> Option<Self> {
        if matches.occurrences_of("icon-theme") > 0 {
            match matches.values_of("icon-theme")?.last() {
                Some("fancy") => Some(Self::Fancy),
                Some("unicode") => Some(Self::Unicode),
                _ => panic!("This should not be reachable!"),
            }
        } else {
            None
        }
    }

    /// Get a potential `IconTheme` variant from a [Config].
    ///
    /// If the `Config::icons::theme` has value and is one of "fancy" or "unicode",
    /// this returns its corresponding variant in a [Some].
    /// Otherwise this returns [None].
    fn from_config(config: &Config) -> Option<Self> {
        if let Some(icon) = &config.icons {
            if let Some(theme) = icon.theme {
                return Some(theme);
            }
        }
        None
    }
}

/// The default value for `IconTheme` is [IconTheme::Fancy].
impl Default for IconTheme {
    fn default() -> Self {
        Self::Fancy
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct IconSeparator(pub String);

impl Configurable<Self> for IconSeparator {
    /// Get a potential `IconSeparator` variant from [ArgMatches].
    ///
    /// If the argument is passed, this returns the variant corresponding to its parameter in a
    /// [Some]. Otherwise this returns [None].
    fn from_arg_matches(_matches: &ArgMatches) -> Option<Self> {
        None
    }

    /// Get a potential `IconSeparator` variant from a [Config].
    ///
    /// This returns its corresponding variant in a [Some].
    /// Otherwise this returns [None].
    fn from_config(config: &Config) -> Option<Self> {
        if let Some(icon) = &config.icons {
            if let Some(separator) = icon.separator.clone() {
                return Some(IconSeparator(separator));
            }
        }
        None
    }
}

/// The default value for `IconSeparator` is [" "].
impl Default for IconSeparator {
    fn default() -> Self {
        IconSeparator(" ".to_string())
    }
}

#[cfg(test)]
mod test_icon_option {
    use super::IconOption;

    use crate::app;
    use crate::config_file::{Config, Icons};
    use crate::flags::Configurable;

    #[test]
    fn test_from_arg_matches_none() {
        let argv = vec!["lsd"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(None, IconOption::from_arg_matches(&matches));
    }

    #[test]
    fn test_from_arg_matches_always() {
        let argv = vec!["lsd", "--icon", "always"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(IconOption::Always),
            IconOption::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_arg_matches_autp() {
        let argv = vec!["lsd", "--icon", "auto"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(IconOption::Auto),
            IconOption::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_arg_matches_never() {
        let argv = vec!["lsd", "--icon", "never"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(IconOption::Never),
            IconOption::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_arg_matches_classic_mode() {
        let argv = vec!["lsd", "--icon", "always", "--classic"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(IconOption::Never),
            IconOption::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_arg_matches_icon_when_multi() {
        let argv = vec!["lsd", "--icon", "always", "--icon", "never"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(IconOption::Never),
            IconOption::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_config_none() {
        assert_eq!(None, IconOption::from_config(&Config::with_none()));
    }

    #[test]
    fn test_from_config_always() {
        let mut c = Config::with_none();
        c.icons = Some(Icons {
            when: Some(IconOption::Always),
            theme: None,
            separator: None,
        });
        assert_eq!(Some(IconOption::Always), IconOption::from_config(&c));
    }

    #[test]
    fn test_from_config_auto() {
        let mut c = Config::with_none();
        c.icons = Some(Icons {
            when: Some(IconOption::Auto),
            theme: None,
            separator: None,
        });
        assert_eq!(Some(IconOption::Auto), IconOption::from_config(&c));
    }

    #[test]
    fn test_from_config_never() {
        let mut c = Config::with_none();
        c.icons = Some(Icons {
            when: Some(IconOption::Never),
            theme: None,
            separator: None,
        });
        assert_eq!(Some(IconOption::Never), IconOption::from_config(&c));
    }

    #[test]
    fn test_from_config_classic_mode() {
        let mut c = Config::with_none();
        c.classic = Some(true);
        c.icons = Some(Icons {
            when: Some(IconOption::Always),
            theme: None,
            separator: None,
        });
        assert_eq!(Some(IconOption::Never), IconOption::from_config(&c));
    }
}

#[cfg(test)]
mod test_icon_theme {
    use super::IconTheme;

    use crate::app;
    use crate::config_file::{Config, Icons};
    use crate::flags::Configurable;

    #[test]
    fn test_from_arg_matches_none() {
        let argv = vec!["lsd"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(None, IconTheme::from_arg_matches(&matches));
    }

    #[test]
    fn test_from_arg_matches_fancy() {
        let argv = vec!["lsd", "--icon-theme", "fancy"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(IconTheme::Fancy),
            IconTheme::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_arg_matches_unicode() {
        let argv = vec!["lsd", "--icon-theme", "unicode"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(IconTheme::Unicode),
            IconTheme::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_arg_matches_icon_multi() {
        let argv = vec!["lsd", "--icon-theme", "fancy", "--icon-theme", "unicode"];
        let matches = app::build().get_matches_from_safe(argv).unwrap();
        assert_eq!(
            Some(IconTheme::Unicode),
            IconTheme::from_arg_matches(&matches)
        );
    }

    #[test]
    fn test_from_config_none() {
        assert_eq!(None, IconTheme::from_config(&Config::with_none()));
    }

    #[test]
    fn test_from_config_fancy() {
        let mut c = Config::with_none();
        c.icons = Some(Icons {
            when: None,
            theme: Some(IconTheme::Fancy),
            separator: None,
        });
        assert_eq!(Some(IconTheme::Fancy), IconTheme::from_config(&c));
    }

    #[test]
    fn test_from_config_unicode() {
        let mut c = Config::with_none();
        c.icons = Some(Icons {
            when: None,
            theme: Some(IconTheme::Unicode),
            separator: None,
        });
        assert_eq!(Some(IconTheme::Unicode), IconTheme::from_config(&c));
    }
}

#[cfg(test)]
mod test_icon_separator {
    use super::IconSeparator;

    use crate::config_file::{Config, Icons};
    use crate::flags::Configurable;

    #[test]
    fn test_from_config_default() {
        let mut c = Config::with_none();
        c.icons = Some(Icons {
            when: None,
            theme: None,
            separator: Some(" ".to_string()),
        });
        let expected = Some(IconSeparator(" ".to_string()));
        assert_eq!(expected, IconSeparator::from_config(&c));
    }

    #[test]
    fn test_from_config_custom() {
        let mut c = Config::with_none();
        c.icons = Some(Icons {
            when: None,
            theme: None,
            separator: Some(" |".to_string()),
        });
        let expected = Some(IconSeparator(" |".to_string()));
        assert_eq!(expected, IconSeparator::from_config(&c));
    }
}
#[cfg(test)]
mod tests_rug_97 {
    use super::*;
    use clap::ArgMatches;
    use crate::config_file::Config;
    
    #[test]
    fn test_rug() {
        let p0: ArgMatches = ArgMatches::default(); // Using default for simplicity, as no specific sample is provided
        let mut p1: Config = Config::default();

        crate::flags::icons::Icons::configure_from(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_98 {
    use super::*;
    use crate::flags::{Configurable, icons::IconOption};
    use clap::{App, Arg};

    #[test]
    fn test_rug() {
        let mut app = App::new("test")
            .arg(Arg::with_name("classic").long("classic"))
            .arg(Arg::with_name("icon").long("icon").takes_value(true));

        let matches: clap::ArgMatches<'_> = app.get_matches_from(vec!["test", "--icon", "always"]);
        
        <IconOption as Configurable<IconOption>>::from_arg_matches(&matches);
    }

    #[test]
    fn test_classic() {
        let mut app = App::new("test")
            .arg(Arg::with_name("classic").long("classic"))
            .arg(Arg::with_name("icon").long("icon").takes_value(true));

        let matches: clap::ArgMatches<'_> = app.get_matches_from(vec!["test", "--classic"]);
        
        <IconOption as Configurable<IconOption>>::from_arg_matches(&matches);
    }

    #[test]
    fn test_auto() {
        let mut app = App::new("test")
            .arg(Arg::with_name("classic").long("classic"))
            .arg(Arg::with_name("icon").long("icon").takes_value(true));

        let matches: clap::ArgMatches<'_> = app.get_matches_from(vec!["test", "--icon", "auto"]);
        
        <IconOption as Configurable<IconOption>>::from_arg_matches(&matches);
    }

    #[test]
    fn test_never() {
        let mut app = App::new("test")
            .arg(Arg::with_name("classic").long("classic"))
            .arg(Arg::with_name("icon").long("icon").takes_value(true));

        let matches: clap::ArgMatches<'_> = app.get_matches_from(vec!["test", "--icon", "never"]);
        
        <IconOption as Configurable<IconOption>>::from_arg_matches(&matches);
    }

    #[test]
    fn test_no_args() {
        let mut app = App::new("test")
            .arg(Arg::with_name("classic").long("classic"))
            .arg(Arg::with_name("icon").long("icon").takes_value(true));

        let matches: clap::ArgMatches<'_> = app.get_matches_from(vec!["test"]);
        
        <IconOption as Configurable<IconOption>>::from_arg_matches(&matches);
    }
}#[cfg(test)]
mod tests_rug_100 {
    use super::*;
    use crate::flags::icons::IconOption;
    use std::default::Default;

    #[test]
    fn test_rug() {
        let icon_option: IconOption = <IconOption as Default>::default();

        assert_eq!(icon_option, IconOption::Auto);
    }
}#[cfg(test)]
mod tests_rug_101 {
    use super::*;
    use crate::flags::{self, Configurable};
    use clap::{App, Arg};

    #[test]
    fn test_rug() {
        let mut app = App::new("myapp");
        app = app.arg(
            Arg::with_name("icon-theme")
                .long("icon-theme")
                .takes_value(true)
                .multiple(true),
        );

        let matches: clap::ArgMatches = app.get_matches_from(vec!["myapp", "--icon-theme=fancy"]);

        let p0: &clap::ArgMatches<'_> = &matches;

        assert_eq!(
            <flags::icons::IconTheme as Configurable<flags::icons::IconTheme>>::from_arg_matches(p0),
            Some(flags::icons::IconTheme::Fancy)
        );
    }

    #[test]
    fn test_unicode() {
        let mut app = App::new("myapp");
        app = app.arg(
            Arg::with_name("icon-theme")
                .long("icon-theme")
                .takes_value(true)
                .multiple(true),
        );

        let matches: clap::ArgMatches = app.get_matches_from(vec!["myapp", "--icon-theme=unicode"]);

        let p0: &clap::ArgMatches<'_> = &matches;

        assert_eq!(
            <flags::icons::IconTheme as Configurable<flags::icons::IconTheme>>::from_arg_matches(p0),
            Some(flags::icons::IconTheme::Unicode)
        );
    }

    #[test]
    fn test_no_icon_theme() {
        let mut app = App::new("myapp");
        app = app.arg(
            Arg::with_name("icon-theme")
                .long("icon-theme")
                .takes_value(true)
                .multiple(true),
        );

        let matches: clap::ArgMatches = app.get_matches_from(vec!["myapp"]);

        let p0: &clap::ArgMatches<'_> = &matches;

        assert_eq!(
            <flags::icons::IconTheme as Configurable<flags::icons::IconTheme>>::from_arg_matches(p0),
            None
        );
    }
}#[cfg(test)]
mod tests_rug_103 {
    use super::*;
    use crate::flags::icons::IconTheme;
    use std::default::Default;

    #[test]
    fn test_rug() {
        let icon_theme: IconTheme = <IconTheme>::default();
        
        assert_eq!(icon_theme, IconTheme::Fancy);
    }
}#[cfg(test)]
mod tests_rug_104 {
    use super::*;
    use crate::flags::{Configurable, icons::IconSeparator};
    use clap::ArgMatches;

    #[test]
    fn test_rug() {
        let mut p0: ArgMatches<'_> = ArgMatches::default();

        <IconSeparator as Configurable<IconSeparator>>::from_arg_matches(&p0);
    }
}