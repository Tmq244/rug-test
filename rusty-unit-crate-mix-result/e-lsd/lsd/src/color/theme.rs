///! This module provides methods to create theme from files and operations related to
///! this.
use crate::config_file;
use crate::print_error;

use crossterm::style::Color;
use serde::Deserialize;
use std::fs;
use std::path::Path;

/// A struct holding the theme configuration
/// Color table: https://upload.wikimedia.org/wikipedia/commons/1/15/Xterm_256color_chart.avg
#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct Theme {
    pub user: Color,
    pub group: Color,
    pub permission: Permission,
    pub date: Date,
    pub size: Size,
    pub inode: INode,
    pub tree_edge: Color,
    pub links: Links,

    #[serde(skip)]
    pub file_type: FileType,
}

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct Permission {
    pub read: Color,
    pub write: Color,
    pub exec: Color,
    pub exec_sticky: Color,
    pub no_access: Color,
    pub octal: Color,
    pub acl: Color,
    pub context: Color,
}

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct FileType {
    pub file: File,
    pub dir: Dir,
    pub pipe: Color,
    pub symlink: Symlink,
    pub block_device: Color,
    pub char_device: Color,
    pub socket: Color,
    pub special: Color,
}

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct File {
    pub exec_uid: Color,
    pub uid_no_exec: Color,
    pub exec_no_uid: Color,
    pub no_exec_no_uid: Color,
}

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct Dir {
    pub uid: Color,
    pub no_uid: Color,
}

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct Symlink {
    pub default: Color,
    pub broken: Color,
    pub missing_target: Color,
}

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct Date {
    pub hour_old: Color,
    pub day_old: Color,
    pub older: Color,
}

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct Size {
    pub none: Color,
    pub small: Color,
    pub medium: Color,
    pub large: Color,
}

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct INode {
    pub valid: Color,
    pub invalid: Color,
}

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
#[serde(default)]
pub struct Links {
    pub valid: Color,
    pub invalid: Color,
}

impl Default for Permission {
    fn default() -> Self {
        Permission {
            read: Color::DarkGreen,
            write: Color::DarkYellow,
            exec: Color::DarkRed,
            exec_sticky: Color::AnsiValue(5),
            no_access: Color::AnsiValue(245), // Grey
            octal: Color::AnsiValue(6),
            acl: Color::DarkCyan,
            context: Color::Cyan,
        }
    }
}
impl Default for FileType {
    fn default() -> Self {
        FileType {
            file: File::default(),
            dir: Dir::default(),
            symlink: Symlink::default(),
            pipe: Color::AnsiValue(44),         // DarkTurquoise
            block_device: Color::AnsiValue(44), // DarkTurquoise
            char_device: Color::AnsiValue(172), // Orange3
            socket: Color::AnsiValue(44),       // DarkTurquoise
            special: Color::AnsiValue(44),      // DarkTurquoise
        }
    }
}
impl Default for File {
    fn default() -> Self {
        File {
            exec_uid: Color::AnsiValue(40),        // Green3
            uid_no_exec: Color::AnsiValue(184),    // Yellow3
            exec_no_uid: Color::AnsiValue(40),     // Green3
            no_exec_no_uid: Color::AnsiValue(184), // Yellow3
        }
    }
}
impl Default for Dir {
    fn default() -> Self {
        Dir {
            uid: Color::AnsiValue(33),    // DodgerBlue1
            no_uid: Color::AnsiValue(33), // DodgerBlue1
        }
    }
}
impl Default for Symlink {
    fn default() -> Self {
        Symlink {
            default: Color::AnsiValue(44),         // DarkTurquoise
            broken: Color::AnsiValue(124),         // Red3
            missing_target: Color::AnsiValue(124), // Red3
        }
    }
}
impl Default for Date {
    fn default() -> Self {
        Date {
            hour_old: Color::AnsiValue(40), // Green3
            day_old: Color::AnsiValue(42),  // SpringGreen2
            older: Color::AnsiValue(36),    // DarkCyan
        }
    }
}
impl Default for Size {
    fn default() -> Self {
        Size {
            none: Color::AnsiValue(245),   // Grey
            small: Color::AnsiValue(229),  // Wheat1
            medium: Color::AnsiValue(216), // LightSalmon1
            large: Color::AnsiValue(172),  // Orange3
        }
    }
}
impl Default for INode {
    fn default() -> Self {
        INode {
            valid: Color::AnsiValue(13),    // Pink
            invalid: Color::AnsiValue(245), // Grey
        }
    }
}
impl Default for Links {
    fn default() -> Self {
        Links {
            valid: Color::AnsiValue(13),    // Pink
            invalid: Color::AnsiValue(245), // Grey
        }
    }
}

impl Default for Theme {
    fn default() -> Self {
        // TODO(zwpaper): check terminal color and return light or dark
        Self::default_dark()
    }
}

impl Theme {
    /// This read theme from file,
    /// use the file path if it is absolute
    /// prefix the config_file dir to it if it is not
    pub fn from_path(file: &str) -> Option<Self> {
        let real = if let Some(path) = config_file::Config::expand_home(file) {
            path
        } else {
            print_error!("Not a valid theme file path: {}.", &file);
            return None;
        };
        let path = if Path::new(&real).is_absolute() {
            real
        } else {
            config_file::Config::config_file_path()?
                .join("themes")
                .join(real)
        };
        match fs::read(&path.with_extension("yaml")) {
            Ok(f) => match Self::with_yaml(&String::from_utf8_lossy(&f)) {
                Ok(t) => Some(t),
                Err(e) => {
                    print_error!("Theme file {} format error: {}.", &file, e);
                    None
                }
            },
            Err(_) => {
                // try `yml` if `yaml` extension file not found
                match fs::read(&path.with_extension("yml")) {
                    Ok(f) => match Self::with_yaml(&String::from_utf8_lossy(&f)) {
                        Ok(t) => Some(t),
                        Err(e) => {
                            print_error!("Theme file {} format error: {}.", &file, e);
                            None
                        }
                    },
                    Err(e) => {
                        print_error!("Not a valid theme: {}, {}.", path.to_string_lossy(), e);
                        None
                    }
                }
            }
        }
    }

    /// This constructs a Theme struct with a passed [Yaml] str.
    fn with_yaml(yaml: &str) -> Result<Self, serde_yaml::Error> {
        serde_yaml::from_str::<Self>(yaml)
    }

    pub fn default_dark() -> Self {
        Theme {
            user: Color::AnsiValue(230),  // Cornsilk1
            group: Color::AnsiValue(187), // LightYellow3
            permission: Permission::default(),
            file_type: FileType::default(),
            date: Date::default(),
            size: Size::default(),
            inode: INode::default(),
            links: Links::default(),
            tree_edge: Color::AnsiValue(245), // Grey
        }
    }

    #[cfg(test)]
    pub fn default_yaml() -> &'static str {
        r#"---
user: 230
group: 187
permission:
  read: dark_green
  write: dark_yellow
  exec: dark_red
  exec-sticky: 5
  no-access: 245
date:
  hour-old: 40
  day-old: 42
  older: 36
size:
  none: 245
  small: 229
  medium: 216
  large: 172
inode:
  valid: 13
  invalid: 245
links:
  valid: 13
  invalid: 245
tree-edge: 245
"#
    }
}

#[cfg(test)]
mod tests {
    use super::Theme;

    #[test]
    fn test_default_theme() {
        assert_eq!(
            Theme::default_dark(),
            Theme::with_yaml(Theme::default_yaml()).unwrap()
        );
    }

    #[test]
    fn test_default_theme_file() {
        use std::fs::File;
        use std::io::Write;
        let dir = assert_fs::TempDir::new().unwrap();
        let theme = dir.path().join("theme.yaml");
        let mut file = File::create(&theme).unwrap();
        writeln!(file, "{}", Theme::default_yaml()).unwrap();

        assert_eq!(
            Theme::default_dark(),
            Theme::from_path(theme.to_str().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_empty_theme_return_default() {
        // Must contain one field at least
        // ref https://github.com/dtolnay/serde-yaml/issues/86
        let empty_theme = Theme::with_yaml("user: 230".into()).unwrap(); // 230 is the default value
        let default_theme = Theme::default_dark();
        assert_eq!(empty_theme, default_theme);
    }

    #[test]
    fn test_first_level_theme_return_default_but_changed() {
        // Must contain one field at least
        // ref https://github.com/dtolnay/serde-yaml/issues/86
        let empty_theme = Theme::with_yaml("user: 130".into()).unwrap();
        let mut theme = Theme::default_dark();
        use crossterm::style::Color;
        theme.user = Color::AnsiValue(130);
        assert_eq!(empty_theme, theme);
    }

    #[test]
    fn test_second_level_theme_return_default_but_changed() {
        // Must contain one field at least
        // ref https://github.com/dtolnay/serde-yaml/issues/86
        let empty_theme = Theme::with_yaml(
            r#"---
permission:
  read: 130"#
                .into(),
        )
        .unwrap();
        let mut theme = Theme::default_dark();
        use crossterm::style::Color;
        theme.permission.read = Color::AnsiValue(130);
        assert_eq!(empty_theme, theme);
    }
}
#[cfg(test)]
mod tests_rug_37 {
    use super::*;
    use crate::color::{Color, theme::Permission};

    #[test]
    fn test_default_permission() {
        let default_permission: Permission = <Permission as Default>::default();

        assert_eq!(default_permission.read, Color::DarkGreen);
        assert_eq!(default_permission.write, Color::DarkYellow);
        assert_eq!(default_permission.exec, Color::DarkRed);
        assert_eq!(default_permission.exec_sticky, Color::AnsiValue(5));
        assert_eq!(default_permission.no_access, Color::AnsiValue(245));
        assert_eq!(default_permission.octal, Color::AnsiValue(6));
        assert_eq!(default_permission.acl, Color::DarkCyan);
        assert_eq!(default_permission.context, Color::Cyan);
    }
}#[cfg(test)]
mod tests_rug_38 {
    use super::*;
    use crate::color::theme::{Color, FileType};
    use std::default::Default;

    #[test]
    fn test_rug() {
        let file_type_default: FileType = <FileType as Default>::default();

        assert_eq!(file_type_default.pipe, Color::AnsiValue(44));         // DarkTurquoise
        assert_eq!(file_type_default.block_device, Color::AnsiValue(44)); // DarkTurquoise
        assert_eq!(file_type_default.char_device, Color::AnsiValue(172)); // Orange3
        assert_eq!(file_type_default.socket, Color::AnsiValue(44));       // DarkTurquoise
        assert_eq!(file_type_default.special, Color::AnsiValue(44));      // DarkTurquoise
    }
}#[cfg(test)]
mod tests_rug_39 {
    use super::*;
    use crate::color::{Color, theme::File};
    use std::default::Default;

    #[test]
    fn test_default_file_theme() {
        let default_file: File = <File>::default();

        assert_eq!(default_file.exec_uid, Color::AnsiValue(40));
        assert_eq!(default_file.uid_no_exec, Color::AnsiValue(184));
        assert_eq!(default_file.exec_no_uid, Color::AnsiValue(40));
        assert_eq!(default_file.no_exec_no_uid, Color::AnsiValue(184));
    }
}#[cfg(test)]
mod tests_rug_40 {
    use super::*;
    use crate::color::Color; // Added based on the usage in the default function

    #[test]
    fn test_default_dir() {
        let expected_uid: Color = Color::AnsiValue(33);
        let expected_no_uid: Color = Color::AnsiValue(33);

        let dir = <crate::color::theme::Dir>::default();

        assert_eq!(dir.uid, expected_uid);
        assert_eq!(dir.no_uid, expected_no_uid);
    }
}#[cfg(test)]
mod tests_rug_41 {
    use super::*;
    use crate::color::{self, theme};
    use std::default::Default;

    #[test]
    fn test_symlink_default() {
        let symlink: color::theme::Symlink = <color::theme::Symlink as Default>::default();
        
        assert_eq!(symlink.default, color::Color::AnsiValue(44));
        assert_eq!(symlink.broken, color::Color::AnsiValue(124));
        assert_eq!(symlink.missing_target, color::Color::AnsiValue(124));
    }
}#[cfg(test)]
mod tests_rug_42 {
    use super::*;
    use crate::color::theme::Date;
    use crate::color::Color;

    #[test]
    fn test_default_date() {
        let default_date: Date = <Date as Default>::default();

        assert_eq!(default_date.hour_old, Color::AnsiValue(40));
        assert_eq!(default_date.day_old, Color::AnsiValue(42));
        assert_eq!(default_date.older, Color::AnsiValue(36));
    }
}#[cfg(test)]
mod tests_rug_43 {
    use super::*;
    use crate::color::theme::Size;
    use std::default::Default;

    #[test]
    fn test_rug() {
        let size: Size = <Size>::default();
        
        assert_eq!(size.none, Color::AnsiValue(245));
        assert_eq!(size.small, Color::AnsiValue(229));
        assert_eq!(size.medium, Color::AnsiValue(216));
        assert_eq!(size.large, Color::AnsiValue(172));
    }
}#[cfg(test)]
mod tests_rug_44 {
    use super::*;
    use crate::color::{Color, theme::INode};
    
    #[test]
    fn test_rug() {
        let inode: INode = <INode as Default>::default();
        
        assert_eq!(inode.valid, Color::AnsiValue(13));
        assert_eq!(inode.invalid, Color::AnsiValue(245));
    }
}#[cfg(test)]
mod tests_rug_45 {
    use super::*;
    use crate::color::theme::Links;
    use crate::color::Color;
    
    #[test]
    fn test_default_links() {
        let links: Links = <Links as Default>::default();
        
        assert_eq!(links.valid, Color::AnsiValue(13));
        assert_eq!(links.invalid, Color::AnsiValue(245));
    }
}#[cfg(test)]
mod tests_rug_46 {
    use super::*;
    use crate::color::theme::Theme;
    use std::default::Default;

    #[test]
    fn test_default_theme() {
        let default_theme: Theme = <Theme as Default>::default();

        // You can add assertions here to verify the properties of the default theme
    }
}#[cfg(test)]
mod tests_rug_47 {
    use super::*;
    use std::path::Path;
    use crate::config_file;
    use crate::color::theme::Theme;

    #[test]
    fn test_rug() {
        let mut p0: &str = "example_theme";

        Theme::from_path(p0);
    }
}#[cfg(test)]
mod tests_rug_48 {
    use super::*;
    use crate::color::theme::Theme;
    use serde_yaml;

    #[test]
    fn test_rug() {
        let mut p0: &str = "colors:
  directory: 38;5;69
  executable: 38;5;148";

        Theme::with_yaml(p0).unwrap();
    }
}