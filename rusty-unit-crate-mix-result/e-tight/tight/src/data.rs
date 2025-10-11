use crate::date::*;
use crate::expense::*;

use std::collections::HashSet;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::prelude::*;
use std::path::Path;

use serde::{Serialize, Deserialize};

#[derive(Debug)]
struct DataError(String);

impl fmt::Display for DataError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Error for DataError {}

#[derive(Serialize, Deserialize)]
pub struct Datafile {
    pub version: u64,
    pub tags: HashSet<String>,
    pub entries: Vec<Expense>,
}

impl Datafile {
    fn new() -> Datafile {
        Datafile {
            version: 1,
            tags: HashSet::new(),
            entries: vec!(),
        }
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Datafile, Box<dyn Error>> {
        let file = File::open(path)?;
        let reader = std::io::BufReader::new(file);

        let d: Datafile = serde_json::from_reader(reader)?;

        if d.version != 1 {
            return Err(Box::new(DataError("unknown version in datafile!".into())));
        }

        Ok(d)
    }

    pub fn add_tag(&mut self, tag: String) {
        self.tags.insert(tag);
    }

    pub fn insert(&mut self, expense: Expense) {
        let mut insert_idx = 0;
        for (idx, saved) in self.entries.iter().enumerate() {
            match saved.compare_dates(&expense) {
                std::cmp::Ordering::Greater => { insert_idx = idx; break; },
                std::cmp::Ordering::Less    => { insert_idx = idx + 1; },
                std::cmp::Ordering::Equal   => { insert_idx = idx + 1; },
            }
        }

        if insert_idx > self.entries.len() {
            self.entries.push(expense);
        } else {
            self.entries.insert(insert_idx, expense);
        }
    }

    pub fn remove(&mut self, id: u64) -> Result<(), Box<dyn Error>> {
        let mut rm_idx = 0;
        for (idx, saved) in self.entries.iter().enumerate() {
            if saved.compare_id(id) {
                rm_idx = idx;
                break;
            }
        }

        if rm_idx > self.entries.len() {
            return Err(Box::new(DataError("couldn't find item".into())));
        }

        self.entries.remove(rm_idx);
        Ok(())
    }

    pub fn find(&self, id: u64) -> Option<&Expense> {
        for expense in &self.entries {
            if expense.compare_id(id) {
                return Some(expense);
            }
        }

        None
    }

    pub fn save<P: AsRef<Path>>(&self, path: P) -> Result<(), Box<dyn Error>> {
        let file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .open(path)?;
        let writer = std::io::BufWriter::new(file);

        serde_json::to_writer(writer, &self)?;

        Ok(())
    }

    // TODO make this faster
    pub fn expenses_between(&self, start: &SimpleDate, end: &SimpleDate) -> &[Expense] {
        let mut start_idx = 0;
        for (idx, expense) in self.entries.iter().enumerate() {
            if let Some(end_date) = expense.get_end_date() {
                if end_date > start {
                    start_idx = idx;
                    break;
                }
            } else {
                start_idx = idx;
                break;
            }
        }

        let mut end_idx = self.entries.len();
        for (idx, expense) in self.entries[start_idx..].iter().enumerate() {
            if expense.get_start_date() > end {
                end_idx = idx + start_idx;
                break;
            }
        }

        &self.entries[start_idx..end_idx]
    }
}

pub fn initialise<P: AsRef<Path>>(path: P) -> std::io::Result<()> {
    let mut file = OpenOptions::new().write(true)
        .create_new(true)
        .open(path)?;
    let contents = serde_json::to_string(&Datafile::new())?;
    file.write_all(contents.as_bytes())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_single() {
        let mut datafile = Datafile::new();
        let expense = Expense::new(0, "test".into(), 100, SimpleDate::from_ymd(2020, 10, 14), None, None, vec!());

        datafile.insert(expense);

        assert_eq!(datafile.entries.len(), 1);
    }

    #[test]
    fn insert_sorted() {
        let mut datafile = Datafile::new();
        let expense1 = Expense::new(0, "test".into(), 100, SimpleDate::from_ymd(2020, 10, 14), None, None, vec!());
        let expense2 = Expense::new(1, "test".into(), 101, SimpleDate::from_ymd(2020, 10, 15), None, None, vec!());

        datafile.insert(expense2);
        datafile.insert(expense1);

        assert_eq!(datafile.entries.len(), 2);
        assert_eq!(datafile.entries[0].amount(), 100);
        assert_eq!(datafile.entries[1].amount(), 101);
    }

    #[test]
    fn remove() {
        let mut datafile = Datafile::new();
        let expense1 = Expense::new(0, "test".into(), 100, SimpleDate::from_ymd(2020, 10, 14), None, None, vec!());
        let expense2 = Expense::new(1, "test".into(), 101, SimpleDate::from_ymd(2020, 10, 15), None, None, vec!());

        datafile.insert(expense2);
        datafile.insert(expense1);

        assert_eq!(datafile.entries.len(), 2);

        assert!(datafile.remove(1).is_ok());

        assert_eq!(datafile.entries.len(), 1);
        assert_eq!(datafile.entries[0].amount(), 100);
    }

    #[test]
    fn find() {
        let mut datafile = Datafile::new();
        let expense1 = Expense::new(0, "test".into(), 100, SimpleDate::from_ymd(2020, 10, 14), None, None, vec!());
        let expense2 = Expense::new(1, "test".into(), 101, SimpleDate::from_ymd(2020, 10, 15), None, None, vec!());

        datafile.insert(expense2);
        datafile.insert(expense1);

        assert!(datafile.find(9999).is_none());

        assert!(datafile.find(1).is_some());
        assert_eq!(datafile.find(1).unwrap().amount(), 101);
    }
}
#[cfg(test)]
mod tests_rug_3 {
    use super::*;
    use std::fs::File;
    use std::io::{BufReader, Write};
    use std::path::Path;

    #[test]
    fn test_from_file() {
        let mut data = vec![1, 2, 3];
        let mut v3 = data.iter_mut();
        
        // Create a temporary file with sample JSON content
        let temp_file_path = "temp_datafile.json";
        let mut temp_file = File::create(temp_file_path).unwrap();
        let sample_json = r#"{"version":1,"data":[1,2,3]}"#;
        write!(temp_file, "{}", sample_json).unwrap();

        // Use the path of the temporary file as the input
        let p0: &Path = Path::new(temp_file_path);

        match crate::data::Datafile::from_file(p0) {
            Ok(datafile) => assert_eq!(datafile.version, 1),
            Err(e) => panic!("Failed to read datafile: {}", e),
        }

        // Clean up the temporary file
        std::fs::remove_file(temp_file_path).unwrap();
    }
}#[cfg(test)]
mod tests_rug_4 {
    use super::*;
    use std::collections::HashSet;
    use crate::data::Datafile;

    #[test]
    fn test_rug() {
        let mut p0: Datafile = Datafile {
            version: 1,
            tags: HashSet::from(["sample_tag".to_string()]),
            entries: vec![],
        };
        let mut p1: String = "new_tag".to_string();

        <Datafile>::add_tag(&mut p0, p1);

        assert!(p0.tags.contains("new_tag"));
    }
}#[cfg(test)]
mod tests_rug_6 {
    use super::*;
    use std::collections::HashSet;
    use crate::data::Datafile;

    #[test]
    fn test_rug() {
        let mut p0: Datafile = Datafile {
            version: 1,
            tags: HashSet::from(["sample_tag".to_string()]),
            entries: vec![],
        };

        let p1: u64 = 123;

        <Datafile>::remove(&mut p0, p1).unwrap_or_else(|e| panic!("Test failed: {}", e));
    }
}#[cfg(test)]
mod tests_rug_8 {
    use super::*;
    use std::collections::HashSet;
    use crate::data::Datafile; // Ensure this path is correct based on your project structure
    use std::path::PathBuf;

    #[test]
    fn test_rug() {
        let mut p0 = Datafile {
            version: 1,
            tags: HashSet::from(["sample_tag".to_string()]),
            entries: vec![],
        };

        let data = vec!["/tmp/test_datafile.json"];
        let mut v6 = data.iter();
        let p1 = PathBuf::from(v6.next().unwrap());

        <Datafile>::save(&p0, &p1).expect("Failed to save Datafile");
    }
}#[cfg(test)]
mod tests_rug_9 {
    use super::*;
    use std::collections::HashSet;
    use crate::data::Datafile;
    use crate::date::SimpleDate;

    #[test]
    fn test_rug() {
        let mut data_file = Datafile {
            version: 1,
            tags: HashSet::from(["sample_tag".to_string()]),
            entries: vec![],
        };

        let start_date = SimpleDate::from_ymd(2023, 10, 5);
        let end_date = SimpleDate::from_ymd(2023, 10, 10);

        data_file.expenses_between(&start_date, &end_date);
    }
}