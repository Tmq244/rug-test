//! Minesweeper
//!
//! Check struct [`Minesweeper`](https://docs.rs/gamie/*/gamie/minesweeper/struct.Minesweeper.html) for more information
//!
//! # Examples
//!
//! ```rust
//! # fn minesweeper() {
//! use gamie::minesweeper::Minesweeper;
//! use rand::rngs::ThreadRng;
//!
//! let mut game = Minesweeper::new(8, 8, 9, &mut ThreadRng::default()).unwrap();
//!
//! game.toggle_flag(3, 2).unwrap();
//! // ...
//! game.click(7, 7, true).unwrap();
//! // ...
//! # }
//! ```

use crate::std_lib::{iter, Vec, VecDeque};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use rand::{
    distributions::{Distribution, Uniform},
    Rng,
};
use snafu::Snafu;

/// Minesweeper
///
/// To avoid unessecary memory allocation, the game board is stored in a single `Vec` rather than a nested one.
///
/// Passing an invalid position to a method will cause panic. Check the target position validity first when dealing with user input
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Minesweeper {
    board: Vec<Cell>,
    height: usize,
    width: usize,
    status: GameState,
}

/// The cell in the board.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Cell {
    pub is_mine: bool,
    pub mine_adjacent: usize,
    pub is_revealed: bool,
    pub is_flagged: bool,
}

impl Cell {
    fn new(is_mine: bool) -> Self {
        Self {
            is_mine,
            mine_adjacent: 0,
            is_revealed: false,
            is_flagged: false,
        }
    }
}

/// Game status
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum GameState {
    Win,
    Exploded(Vec<(usize, usize)>),
    InProgress,
}

impl Minesweeper {
    /// Create a new Minesweeper game
    ///
    /// A mutable reference of a random number generator is required for randomizing mine positions
    ///
    /// Return `Err(MinesweeperError::TooManyMines)` if `height * width < mines`
    ///
    /// # Examples
    /// ```rust
    /// # fn minesweeper() {
    /// use gamie::minesweeper::Minesweeper;
    /// use rand::rngs::ThreadRng;
    ///
    /// let mut game = Minesweeper::new(8, 8, 9, &mut ThreadRng::default()).unwrap();
    /// # }
    /// ```
    pub fn new<R: Rng + ?Sized>(
        height: usize,
        width: usize,
        mines: usize,
        rng: &mut R,
    ) -> Result<Self, MinesweeperError> {
        if height * width < mines {
            return Err(MinesweeperError::TooManyMines);
        }

        let board = iter::repeat(Cell::new(true))
            .take(mines)
            .chain(iter::repeat(Cell::new(false)).take(height * width - mines))
            .collect();

        let mut minesweeper = Self {
            board,
            height,
            width,
            status: GameState::InProgress,
        };
        minesweeper.randomize(rng).unwrap();

        Ok(minesweeper)
    }

    /// Randomize the board
    ///
    /// A mutable reference of a random number generator is required for randomizing mine positions
    pub fn randomize<R: Rng + ?Sized>(&mut self, rng: &mut R) -> Result<(), MinesweeperError> {
        if self.is_ended() {
            return Err(MinesweeperError::GameEnded);
        }

        let range = Uniform::from(0..self.height * self.width);

        for idx in 0..self.height * self.width {
            self.board.swap(idx, range.sample(rng));
        }

        self.update_around_mine_count();

        Ok(())
    }

    /// Get a cell reference from the game board
    /// Panic when target position out of bounds
    pub fn get(&self, row: usize, col: usize) -> &Cell {
        if row >= self.height || col >= self.width {
            panic!("Invalid position: ({}, {})", row, col);
        }

        &self.board[row * self.width + col]
    }

    /// Check if the game was end
    pub fn is_ended(&self) -> bool {
        self.status != GameState::InProgress
    }

    /// Get the game status
    pub fn status(&self) -> &GameState {
        &self.status
    }

    /// Click a cell on the game board
    ///
    /// Clicking an already revealed cell will unreveal its adjacent cells if the flagged cell count around it equals to its adjacent mine count
    /// When `auto_flag` is `true`, clicking an already revealed cell will flag its adjacent unflagged-unrevealed cells if the unflagged-revealed cell count around it equals to its adjacent mine count
    ///
    /// The return value indicates if the game board is changed from the click
    ///
    /// Panic when target position out of bounds
    pub fn click(
        &mut self,
        row: usize,
        col: usize,
        auto_flag: bool,
    ) -> Result<bool, MinesweeperError> {
        if row >= self.height || col >= self.width {
            panic!("Invalid position: ({}, {})", row, col);
        }

        if self.is_ended() {
            return Err(MinesweeperError::GameEnded);
        }

        if !self.board[row * self.width + col].is_revealed {
            self.click_unrevealed(row, col)?;
            Ok(true)
        } else {
            Ok(self.click_revealed(row, col, auto_flag)?)
        }
    }

    /// Flag or unflag a cell on the board
    /// Return Err(MinesweeperError::AlreadyRevealed) if the target cell is already revealed
    ///
    /// Panic when target position out of bounds
    pub fn toggle_flag(&mut self, row: usize, col: usize) -> Result<(), MinesweeperError> {
        if row >= self.height || col >= self.width {
            panic!("Invalid position: ({}, {})", row, col);
        }

        if self.is_ended() {
            return Err(MinesweeperError::GameEnded);
        }

        if self.board[row * self.width + col].is_revealed {
            return Err(MinesweeperError::AlreadyRevealed);
        }

        self.board[row * self.width + col].is_flagged =
            !self.board[row * self.width + col].is_flagged;

        self.check_state();

        Ok(())
    }

    fn click_unrevealed(&mut self, row: usize, col: usize) -> Result<(), MinesweeperError> {
        if self.board[row * self.width + col].is_flagged {
            return Err(MinesweeperError::AlreadyFlagged);
        }

        if self.board[row * self.width + col].is_mine {
            self.status = GameState::Exploded(vec![(row, col)]);
            return Ok(());
        }

        self.reveal_from(row * self.width + col);
        self.check_state();

        Ok(())
    }

    fn click_revealed(
        &mut self,
        row: usize,
        col: usize,
        auto_flag: bool,
    ) -> Result<bool, MinesweeperError> {
        let mut is_changed = false;

        if self.board[row * self.width + col].mine_adjacent > 0 {
            let mut adjacent_all = 0;
            let mut adjacent_revealed = 0;
            let mut adjacent_flagged = 0;

            self.get_adjacent_cells(row, col)
                .map(|idx| self.board[idx])
                .for_each(|cell| {
                    adjacent_all += 1;

                    if cell.is_revealed {
                        adjacent_revealed += 1;
                    } else if cell.is_flagged {
                        adjacent_flagged += 1;
                    }
                });

            let adjacent_unrevealed = adjacent_all - adjacent_revealed - adjacent_flagged;

            if adjacent_unrevealed > 0 {
                if adjacent_flagged == self.board[row * self.width + col].mine_adjacent {
                    let mut exploded = None;

                    self.get_adjacent_cells(row, col).for_each(|idx| {
                        if !self.board[idx].is_flagged && !self.board[idx].is_revealed {
                            if self.board[idx].is_mine {
                                self.board[idx].is_revealed = true;

                                match exploded {
                                    None => exploded = Some(vec![(row, col)]),
                                    Some(ref mut exploded) => {
                                        exploded.push((row, col));
                                    }
                                }
                            } else {
                                self.reveal_from(idx);
                                is_changed = true;
                            }
                        }
                    });

                    if let Some(exploded) = exploded {
                        self.status = GameState::Exploded(exploded);
                        return Ok(true);
                    }
                }

                if auto_flag
                    && adjacent_unrevealed + adjacent_flagged
                        == self.board[row * self.width + col].mine_adjacent
                {
                    self.get_adjacent_cells(row, col).for_each(|idx| {
                        if !self.board[idx].is_flagged && !self.board[idx].is_revealed {
                            self.board[idx].is_flagged = true;
                            is_changed = true;
                        }
                    });
                }
            }

            self.check_state();
        }

        Ok(is_changed)
    }

    fn reveal_from(&mut self, idx: usize) {
        if self.board[idx].mine_adjacent != 0 {
            self.board[idx].is_revealed = true;
        } else {
            let mut cell_idxs_to_reveal = VecDeque::new();
            cell_idxs_to_reveal.push_back(idx);

            while let Some(cell_idx) = cell_idxs_to_reveal.pop_front() {
                self.board[cell_idx].is_revealed = true;

                for neighbor_idx in
                    self.get_adjacent_cells(cell_idx / self.width, cell_idx % self.width)
                {
                    if !self.board[neighbor_idx].is_flagged && !self.board[neighbor_idx].is_revealed
                    {
                        if self.board[neighbor_idx].mine_adjacent == 0 {
                            cell_idxs_to_reveal.push_back(neighbor_idx);
                        } else {
                            self.board[neighbor_idx].is_revealed = true;
                        }
                    }
                }
            }
        }
    }

    fn check_state(&mut self) {
        self.status = if self
            .board
            .iter()
            .filter(|cell| !cell.is_mine)
            .all(|cell| cell.is_revealed)
        {
            GameState::Win
        } else {
            GameState::InProgress
        };
    }

    fn update_around_mine_count(&mut self) {
        for idx in 0..self.height * self.width {
            let count = self
                .get_adjacent_cells(idx / self.width, idx % self.width)
                .filter(|idx| self.board[*idx].is_mine)
                .count();

            self.board[idx].mine_adjacent = count;
        }
    }

    fn get_adjacent_cells(&self, row: usize, col: usize) -> AdjacentCells {
        AdjacentCells::new(row, col, self.height, self.width)
    }
}

#[derive(Clone)]
struct AdjacentCells {
    around: [(isize, isize); 8],
    board_height: isize,
    board_width: isize,
    offset: usize,
}

impl Iterator for AdjacentCells {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        self.around[self.offset..]
            .iter()
            .enumerate()
            .filter(|(_, (row, col))| {
                *row >= 0 && *col >= 0 && *row < self.board_height && *col < self.board_width
            })
            .next()
            .map(|(idx, (row, col))| {
                self.offset += idx + 1;
                (row * self.board_width + col) as usize
            })
    }
}

impl AdjacentCells {
    fn new(row: usize, col: usize, board_height: usize, board_width: usize) -> Self {
        let (row, col, board_height, board_width) = (
            row as isize,
            col as isize,
            board_height as isize,
            board_width as isize,
        );

        AdjacentCells {
            around: [
                (row - 1, col - 1),
                (row - 1, col),
                (row - 1, col + 1),
                (row, col - 1),
                (row, col + 1),
                (row + 1, col - 1),
                (row + 1, col),
                (row + 1, col + 1),
            ],
            board_height,
            board_width,
            offset: 0,
        }
    }
}

/// Errors that can occur.
#[derive(Debug, Eq, PartialEq, Snafu)]
pub enum MinesweeperError {
    #[snafu(display("Too many mines"))]
    TooManyMines,
    #[snafu(display("Clicked an already flagged cell"))]
    AlreadyFlagged,
    #[snafu(display("Clicked an already revealed cell"))]
    AlreadyRevealed,
    #[snafu(display("The game was already end"))]
    GameEnded,
}
#[cfg(test)]
mod tests_rug_26 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: bool = true;

        crate::minesweeper::Cell::new(p0);
    }
}#[cfg(test)]
mod tests_rug_27 {
    use super::*;
    use rand::rngs::ThreadRng;
    use std::boxed::Box;

    #[test]
    fn test_rug() {
        let p0: usize = 8; // height
        let p1: usize = 8; // width
        let p2: usize = 9; // mines
        let mut p3: Box<ThreadRng> = Box::new(ThreadRng::default());

        crate::minesweeper::Minesweeper::new(p0, p1, p2, &mut *p3).unwrap();
    }
}#[cfg(test)]
mod tests_rug_28 {
    use super::*;
    use crate::minesweeper::Minesweeper;
    use rand::rngs::ThreadRng;

    #[test]
    fn test_randomize() {
        let mut rng = ThreadRng::default();
        let mut p0: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();
        let mut p1: Box<ThreadRng> = Box::new(rng);

        crate::minesweeper::Minesweeper::randomize(&mut p0, &mut *p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_29 {
    use crate::minesweeper::{Minesweeper, Cell};
    use rand::rngs::ThreadRng;

    #[test]
    fn test_get() {
        let mut rng = ThreadRng::default();
        let p0: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();
        let p1: usize = 3;
        let p2: usize = 4;

        let cell: &Cell = <Minesweeper>::get(&p0, p1, p2);
    }
}#[cfg(test)]
mod tests_rug_30 {
    use crate::minesweeper::{Minesweeper, GameState};
    use rand::rngs::ThreadRng;

    #[test]
    fn test_rug() {
        let mut rng = ThreadRng::default();
        let mut p0: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();

        assert!(!p0.is_ended());

        // Simulate ending the game
        p0.status = GameState::Win;
        assert!(p0.is_ended());
    }
}#[cfg(test)]
mod tests_rug_32 {
    use crate::minesweeper::{Minesweeper, MinesweeperError};
    use rand::rngs::ThreadRng;
    
    #[test]
    fn test_click() {
        let mut rng = ThreadRng::default();
        let mut game: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();
        let row: usize = 0;
        let col: usize = 0;
        let auto_flag: bool = false;

        match game.click(row, col, auto_flag) {
            Ok(changed) => assert!(changed),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }
}#[cfg(test)]
mod tests_rug_33 {
    use crate::minesweeper::{Minesweeper, MinesweeperError};
    use rand::rngs::ThreadRng;

    #[test]
    fn test_toggle_flag() {
        let mut rng = ThreadRng::default();
        let mut p0: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();
        let p1: usize = 3;
        let p2: usize = 4;

        assert!(p0.toggle_flag(p1, p2).is_ok());
        assert!(p0.board[p1 * p0.width + p2].is_flagged);

        // Test toggling the flag off
        assert!(p0.toggle_flag(p1, p2).is_ok());
        assert!(!p0.board[p1 * p0.width + p2].is_flagged);

        // Test already revealed cell
        p0.board[p1 * p0.width + p2].is_revealed = true;
        assert_eq!(p0.toggle_flag(p1, p2), Err(MinesweeperError::AlreadyRevealed));
    }
}#[cfg(test)]
mod tests_rug_34 {
    use super::*;
    use crate::minesweeper::{Minesweeper, MinesweeperError};
    use rand::rngs::ThreadRng;

    #[test]
    fn test_rug() {
        let mut rng = ThreadRng::default();
        let mut p0: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();
        let p1: usize = 3;
        let p2: usize = 4;

        assert!(p0.click_unrevealed(p1, p2).is_ok());
    }
}#[cfg(test)]
mod tests_rug_35 {
    use crate::minesweeper::{Minesweeper, MinesweeperError, GameState};
    use rand::rngs::ThreadRng;

    #[test]
    fn test_click_revealed() {
        let mut rng = ThreadRng::default();
        let mut p0: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();
        let p1: usize = 3;
        let p2: usize = 4;
        let p3: bool = false;

        let result = p0.click_revealed(p1, p2, p3);
        assert!(result.is_ok());
    }
}#[cfg(test)]
mod tests_rug_36 {
    use crate::minesweeper::{Minesweeper, Cell};
    use rand::rngs::ThreadRng;
    use std::collections::VecDeque;

    #[test]
    fn test_rug() {
        let mut rng = ThreadRng::default();
        let mut v9 = Minesweeper::new(8, 8, 9, &mut rng).unwrap();

        let idx: usize = 0; // Sample data for the second argument

        <Minesweeper>::reveal_from(&mut v9, idx);
    }
}#[cfg(test)]
mod tests_rug_37 {
    use super::*;
    use crate::minesweeper::{Minesweeper, GameState};
    use rand::rngs::ThreadRng;

    #[test]
    fn test_rug() {
        let mut rng = ThreadRng::default();
        let mut p0: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();

        p0.check_state();
        
        // Example assertions to verify the state
        assert_eq!(p0.status, GameState::InProgress); // Adjust based on expected behavior
    }
}#[cfg(test)]
mod tests_rug_38 {
    use crate::minesweeper::{Minesweeper, Cell};
    use rand::rngs::ThreadRng;

    #[test]
    fn test_update_around_mine_count() {
        let mut rng = ThreadRng::default();
        let mut p0: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();

        p0.update_around_mine_count();
    }
}#[cfg(test)]
mod tests_rug_39 {
    use super::*;
    use crate::minesweeper::{Minesweeper, AdjacentCells};
    use rand::rngs::ThreadRng;

    #[test]
    fn test_rug() {
        let mut rng = ThreadRng::default();
        let p0: Minesweeper = Minesweeper::new(8, 8, 9, &mut rng).unwrap();
        let p1: usize = 3; // Sample data
        let p2: usize = 4; // Sample data

        let _result = p0.get_adjacent_cells(p1, p2);

    }
}#[cfg(test)]
mod tests_rug_40 {
    use super::*;
    use crate::minesweeper::AdjacentCells;
    use std::iter::Iterator;

    #[test]
    fn test_rug() {
        let mut p0: AdjacentCells = AdjacentCells::new(2, 3, 5, 6);

        assert_eq!(p0.next(), Some(18));
        assert_eq!(p0.next(), Some(19));
        assert_eq!(p0.next(), Some(24));
        assert_eq!(p0.next(), Some(25));
        assert_eq!(p0.next(), Some(26));
        assert_eq!(p0.next(), None);
    }
}#[cfg(test)]
mod tests_rug_41 {
    use super::*;

    #[test]
    fn test_rug() {
        let mut p0: usize = 2;
        let mut p1: usize = 3;
        let mut p2: usize = 5;
        let mut p3: usize = 6;

        crate::minesweeper::AdjacentCells::new(p0, p1, p2, p3);
    }
}