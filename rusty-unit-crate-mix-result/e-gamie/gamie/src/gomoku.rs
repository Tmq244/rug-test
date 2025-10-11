//! Gomoku game
//!
//! Check struct [`Gomoku`](https://docs.rs/gamie/*/gamie/gomoku/struct.Gomoku.html) for more information
//!
//! # Examples
//!
//! ```rust
//! # fn gomoku() {
//! use gamie::gomoku::{Gomoku, Player as GomokuPlayer};
//!
//! let mut game = Gomoku::new().unwrap();
//! game.place(GomokuPlayer::Player0, 7, 8).unwrap();
//! game.place(GomokuPlayer::Player1, 8, 7).unwrap();
//! // ...
//! # }
//! ```

use crate::std_lib::{iter, Box, Infallible};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use snafu::Snafu;

/// Gomoku
///
/// Passing an invalid position to a method will cause panic. Check the target position validity first when dealing with user input
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Gomoku {
    board: [[Option<Player>; 15]; 15],
    next: Player,
    status: GameState,
}

/// Players
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Player {
    Player0,
    Player1,
}

impl Player {
    /// Get the opposite player
    pub fn other(self) -> Self {
        match self {
            Player::Player0 => Player::Player1,
            Player::Player1 => Player::Player0,
        }
    }
}

/// Game status
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum GameState {
    Win(Player),
    Tie,
    InProgress,
}

impl Gomoku {
    /// Create a new Gomoku game.
    pub fn new() -> Result<Self, Infallible> {
        Ok(Self {
            board: [[None; 15]; 15],
            next: Player::Player0,
            status: GameState::InProgress,
        })
    }

    /// Get a cell reference from the game board
    /// Panic when target position out of bounds
    pub fn get(&self, row: usize, col: usize) -> &Option<Player> {
        &self.board[row][col]
    }

    /// Check if the game was end
    pub fn is_ended(&self) -> bool {
        self.status != GameState::InProgress
    }

    /// Get the winner of the game. Return `None` when the game is tied or not end yet
    pub fn winner(&self) -> Option<Player> {
        if let GameState::Win(player) = self.status {
            Some(player)
        } else {
            None
        }
    }

    /// Get the game status
    pub fn status(&self) -> &GameState {
        &self.status
    }

    /// Get the next player
    pub fn get_next_player(&self) -> Player {
        self.next
    }

    /// Place a piece on the board
    /// Panic when target position out of bounds
    pub fn place(&mut self, player: Player, row: usize, col: usize) -> Result<(), GomokuError> {
        if self.is_ended() {
            return Err(GomokuError::GameEnded);
        }

        if player != self.next {
            return Err(GomokuError::WrongPlayer);
        }

        if self.board[row][col].is_some() {
            return Err(GomokuError::OccupiedPosition);
        }

        self.board[row][col] = Some(player);
        self.next = self.next.other();

        self.check_state();

        Ok(())
    }

    fn check_state(&mut self) {
        for connectable in Self::get_connectable() {
            let mut last = None;
            let mut count = 0u8;

            for cell in connectable.map(|(row, col)| self.board[col][row]) {
                if cell != last {
                    last = cell;
                    count = 1;
                } else {
                    count += 1;
                    if count == 5 && cell.is_some() {
                        self.status = GameState::Win(cell.unwrap());
                        return;
                    }
                }
            }
        }

        if self.board.iter().flatten().all(|cell| cell.is_some()) {
            self.status = GameState::Tie;
        }
    }

    fn get_connectable() -> impl Iterator<Item = Box<dyn Iterator<Item = (usize, usize)>>> {
        let horizontal = (0usize..15).map(move |row| {
            Box::new((0usize..15).map(move |col| (row, col)))
                as Box<dyn Iterator<Item = (usize, usize)>>
        });

        let vertical = (0usize..15).map(move |col| {
            Box::new((0usize..15).map(move |row| (row, col)))
                as Box<dyn Iterator<Item = (usize, usize)>>
        });

        let horizontal_upper_left_to_lower_right = (0usize..15).map(move |col| {
            Box::new(
                iter::successors(Some((0usize, col)), |(row, col)| Some((row + 1, col + 1)))
                    .take(15 - col),
            ) as Box<dyn Iterator<Item = (usize, usize)>>
        });

        let vertical_upper_left_to_lower_right = (0usize..15).map(move |row| {
            Box::new(
                iter::successors(Some((row, 0usize)), |(row, col)| Some((row + 1, col + 1)))
                    .take(15 - row),
            ) as Box<dyn Iterator<Item = (usize, usize)>>
        });

        let horizontal_upper_right_to_lower_left = (0usize..15).map(move |col| {
            Box::new(
                iter::successors(Some((0usize, col)), |(row, col)| {
                    col.checked_sub(1).map(|new_col| (row + 1, new_col))
                })
                .take(1 + col),
            ) as Box<dyn Iterator<Item = (usize, usize)>>
        });

        let vertical_upper_right_to_lower_left = (0usize..15).map(move |row| {
            Box::new(
                iter::successors(Some((row, 14usize)), |(row, col)| Some((row + 1, col - 1)))
                    .take(15 - row),
            ) as Box<dyn Iterator<Item = (usize, usize)>>
        });

        horizontal
            .chain(vertical)
            .chain(horizontal_upper_left_to_lower_right)
            .chain(vertical_upper_left_to_lower_right)
            .chain(horizontal_upper_right_to_lower_left)
            .chain(vertical_upper_right_to_lower_left)
    }
}

/// Errors that can occur when placing a piece on the board
#[derive(Debug, Eq, PartialEq, Snafu)]
pub enum GomokuError {
    #[snafu(display("Wrong player"))]
    WrongPlayer,
    #[snafu(display("Occupied position"))]
    OccupiedPosition,
    #[snafu(display("The game was already end"))]
    GameEnded,
}
#[cfg(test)]
mod tests_rug_18 {
    use crate::gomoku::Gomoku;

    #[test]
    fn test_rug() {
        let mut p0: Gomoku = Gomoku::new().unwrap();
        let p1: usize = 0;
        let p2: usize = 0;

        assert_eq!(p0.get(p1, p2), &None);
    }
}#[cfg(test)]
mod tests_rug_21 {
    use super::*;
    use crate::gomoku::Gomoku;

    #[test]
    fn test_rug() {
        let mut game: Gomoku = Gomoku::new().unwrap();

        let status = crate::gomoku::Gomoku::status(&game);
        
        // You might want to add assertions here based on what you expect from the status
        // For example:
        // assert_eq!(*status, GameState::YourExpectedState);
    }
}#[cfg(test)]
mod tests_rug_22 {
    use super::*;
    use crate::gomoku::{Gomoku, Player};

    #[test]
    fn test_get_next_player() {
        let mut gomoku: Gomoku = Gomoku::new().unwrap();

        // Assuming the initial player is set correctly in the new method
        let next_player: Player = gomoku.get_next_player();
        
        // You can add assertions based on expected behavior, for example:
        // assert_eq!(next_player, Player::Black); // or whatever the initial player is supposed to be
    }
}#[cfg(test)]
mod tests_rug_23 {
    use crate::gomoku::{Gomoku, Player, GomokuError};

    #[test]
    fn test_place() {
        let mut game: Gomoku = Gomoku::new().unwrap();
        let player1: Player = game.get_next_player();
        let row: usize = 0;
        let col: usize = 0;

        assert_eq!(game.place(player1, row, col), Ok(()));
    }

    #[test]
    fn test_place_out_of_bounds() {
        let mut game: Gomoku = Gomoku::new().unwrap();
        let player1: Player = game.get_next_player();
        let row: usize = 20; // Assuming board size is less than 20
        let col: usize = 20;

        assert!(game.place(player1, row, col).is_err());
    }

    #[test]
    fn test_place_wrong_player() {
        let mut game: Gomoku = Gomoku::new().unwrap();
        let player1: Player = game.get_next_player();
        let player2: Player = player1.other();
        let row: usize = 0;
        let col: usize = 0;

        assert_eq!(game.place(player2, row, col), Err(GomokuError::WrongPlayer));
    }

    #[test]
    fn test_place_occupied_position() {
        let mut game: Gomoku = Gomoku::new().unwrap();
        let player1: Player = game.get_next_player();
        let row: usize = 0;
        let col: usize = 0;

        assert_eq!(game.place(player1, row, col), Ok(()));
        assert_eq!(game.place(player1, row, col), Err(GomokuError::OccupiedPosition));
    }

    #[test]
    fn test_place_game_ended() {
        let mut game: Gomoku = Gomoku::new().unwrap();
        let player1: Player = game.get_next_player();
        let row: usize = 0;
        let col: usize = 0;

        // Simulate a win to end the game
        for i in 0..5 {
            assert_eq!(game.place(player1, i, 0), Ok(()));
        }

        assert_eq!(game.place(player1, 6, 0), Err(GomokuError::GameEnded));
    }
}#[cfg(test)]
mod tests_rug_24 {
    use super::*;
    use crate::gomoku::{Gomoku, GameState};

    #[test]
    fn test_rug() {
        let mut p0: Gomoku = Gomoku::new().unwrap();

        p0.check_state();
    }
}#[cfg(test)]
mod tests_rug_25 {
    use super::*;
    use std::iter;

    #[test]
    fn test_get_connectable() {
        let connectable_iter = crate::gomoku::Gomoku::get_connectable();
        
        // Example of how to iterate over the result and collect some values for testing
        let mut all_positions: Vec<(usize, usize)> = connectable_iter
            .flat_map(|it| it)
            .collect();

        // Asserting that we have the correct number of positions (15 * 15 * 6 directions)
        assert_eq!(all_positions.len(), 15 * 15 * 6);

        // Example: checking some specific points in the first few iterators
        let mut horizontal_iter = all_positions.drain(..225).collect::<Vec<_>>();
        assert_eq!(horizontal_iter[0], (0, 0));
        assert_eq!(horizontal_iter[14], (0, 14));
        assert_eq!(horizontal_iter[15], (1, 0));

        let mut vertical_iter = all_positions.drain(..225).collect::<Vec<_>>();
        assert_eq!(vertical_iter[0], (0, 0));
        assert_eq!(vertical_iter[14], (14, 0));
        assert_eq!(vertical_iter[15], (0, 1));

        let mut diag_ul_lr_iter = all_positions.drain(..225).collect::<Vec<_>>();
        assert_eq!(diag_ul_lr_iter[0], (0, 0));
        assert_eq!(diag_ul_lr_iter[14], (14, 14));
        assert_eq!(diag_ul_lr_iter[15], (0, 1));

        let mut diag_vul_lr_iter = all_positions.drain(..225).collect::<Vec<_>>();
        assert_eq!(diag_vul_lr_iter[0], (0, 0));
        assert_eq!(diag_vul_lr_iter[14], (14, 14));
        assert_eq!(diag_vul_lr_iter[15], (1, 0));

        let mut diag_ur_ll_iter = all_positions.drain(..225).collect::<Vec<_>>();
        assert_eq!(diag_ur_ll_iter[0], (0, 14));
        assert_eq!(diag_ur_ll_iter[14], (14, 0));
        assert_eq!(diag_ur_ll_iter[15], (0, 13));

        let diag_vur_ll_iter = all_positions;
        assert_eq!(diag_vur_ll_iter[0], (0, 14));
        assert_eq!(diag_vur_ll_iter[14], (14, 0));
        assert_eq!(diag_vur_ll_iter[15], (1, 13));
    }
}