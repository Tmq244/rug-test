//! Reversi
//!
//! Check struct [`Reversi`](https://docs.rs/gamie/*/gamie/reversi/struct.Reversi.html) for more information
//!
//! # Examples
//!
//! ```rust
//! # fn reversi() {
//! use gamie::reversi::{Reversi, Player as ReversiPlayer};
//!
//! let mut game = Reversi::new().unwrap();
//!
//! game.place(ReversiPlayer::Player0, 2, 4).unwrap();
//!
//! // The next player may not be able to place the piece in any position, so check the output of `get_next_player()`
//! assert_eq!(game.get_next_player(), ReversiPlayer::Player1);
//!
//! game.place(ReversiPlayer::Player1, 2, 3).unwrap();
//!
//! // ...
//! # }
//! ```

use crate::std_lib::{iter, Infallible, Ordering};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use snafu::Snafu;

/// Reversi
///
/// Passing an invalid position to a method will cause panic. Check the target position validity first when dealing with user input
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Reversi {
    board: [[Option<Player>; 8]; 8],
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

impl Reversi {
    /// Create a new Reversi game
    pub fn new() -> Result<Self, Infallible> {
        let mut board = [[None; 8]; 8];
        board[3][3] = Some(Player::Player0);
        board[4][4] = Some(Player::Player0);
        board[3][4] = Some(Player::Player1);
        board[4][3] = Some(Player::Player1);

        Ok(Self {
            board,
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
    pub fn place(&mut self, player: Player, row: usize, col: usize) -> Result<(), ReversiError> {
        self.simple_check_position_validity(row, col, player)?;

        let mut flipped = false;

        for dir in Direction::iter() {
            if let Some((to_row, to_col)) =
                self.check_occupied_line_in_direction(row, col, dir, player)
            {
                self.flip(row, col, to_row, to_col, dir, player);
                flipped = true;
            }
        }

        if flipped {
            self.next = player.other();

            if !self.can_player_move(player.other()) {
                self.next = player;

                if !self.can_player_move(player) {
                    self.check_state();
                }
            }

            Ok(())
        } else {
            Err(ReversiError::InvalidPosition)
        }
    }

    /// Check if a position is valid for placing piece
    /// Panic when target position out of bounds
    pub fn check_position_validity(
        &self,
        row: usize,
        col: usize,
        player: Player,
    ) -> Result<(), ReversiError> {
        self.simple_check_position_validity(row, col, player)?;

        if Direction::iter()
            .map(|dir| self.check_occupied_line_in_direction(row, col, dir, player))
            .any(|o| o.is_some())
        {
            Ok(())
        } else {
            Err(ReversiError::InvalidPosition)
        }
    }

    fn simple_check_position_validity(
        &self,
        row: usize,
        col: usize,
        player: Player,
    ) -> Result<(), ReversiError> {
        if self.is_ended() {
            return Err(ReversiError::GameEnded);
        }

        if player != self.next {
            return Err(ReversiError::WrongPlayer);
        }

        if self.board[row][col].is_some() {
            return Err(ReversiError::OccupiedPosition);
        }

        Ok(())
    }

    fn can_player_move(&self, player: Player) -> bool {
        for row in 0..8 {
            for col in 0..8 {
                if self.board[row][col].is_none()
                    && self.check_position_validity(row, col, player).is_ok()
                {
                    return true;
                }
            }
        }

        false
    }

    fn check_state(&mut self) {
        let mut black_count = 0;
        let mut white_count = 0;

        for cell in self.board.iter().flatten().flatten() {
            match cell {
                Player::Player0 => black_count += 1,
                Player::Player1 => white_count += 1,
            }
        }

        self.status = match black_count.cmp(&white_count) {
            Ordering::Less => GameState::Win(Player::Player1),
            Ordering::Equal => GameState::Tie,
            Ordering::Greater => GameState::Win(Player::Player0),
        };
    }

    fn flip(
        &mut self,
        from_row: usize,
        from_col: usize,
        to_row: usize,
        to_col: usize,
        dir: Direction,
        player: Player,
    ) {
        self.iter_positions_in_direction_from(from_row, from_col, dir)
            .take_while(|(row, col)| *row != to_row || *col != to_col)
            .for_each(|(row, col)| {
                self.board[row][col] = Some(player);
            });
    }

    fn check_occupied_line_in_direction(
        &self,
        row: usize,
        col: usize,
        dir: Direction,
        player: Player,
    ) -> Option<(usize, usize)> {
        let mut pos = self.iter_positions_in_direction_from(row, col, dir);

        pos.next();

        let first = if let Some(pos) = pos.next() {
            pos
        } else {
            return None;
        };

        if self.board[first.0][first.1] != Some(player.other()) {
            return None;
        }

        for (row, col) in pos {
            match self.board[row][col] {
                Some(piece) if piece == player.other() => continue,
                Some(_) => return Some((row, col)),
                None => return None,
            }
        }

        None
    }

    fn iter_positions_in_direction_from(
        &self,
        row: usize,
        col: usize,
        dir: Direction,
    ) -> impl Iterator<Item = (usize, usize)> {
        iter::successors(Some((row, col)), move |(row, col)| {
            let (offset_row, offset_col) = dir.as_offset();
            Some((
                (*row as i8 + offset_row) as usize,
                (*col as i8 + offset_col) as usize,
            ))
        })
        .take_while(|(row, col)| *row < 8 && *col < 8)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Direction {
    Upper,
    UpperRight,
    Right,
    LowerRight,
    Lower,
    LowerLeft,
    Left,
    UpperLeft,
}

impl Direction {
    fn as_offset(&self) -> (i8, i8) {
        match self {
            Direction::Upper => (-1, 0),
            Direction::UpperRight => (-1, 1),
            Direction::Right => (0, 1),
            Direction::LowerRight => (1, 1),
            Direction::Lower => (1, 0),
            Direction::LowerLeft => (1, -1),
            Direction::Left => (0, -1),
            Direction::UpperLeft => (-1, -1),
        }
    }

    fn iter() -> impl Iterator<Item = Self> {
        [
            Direction::Upper,
            Direction::UpperRight,
            Direction::Right,
            Direction::LowerRight,
            Direction::Lower,
            Direction::LowerLeft,
            Direction::Left,
            Direction::UpperLeft,
        ]
        .into_iter()
    }
}

/// Errors that can occur when placing a piece on the board
#[derive(Debug, Eq, PartialEq, Snafu)]
pub enum ReversiError {
    #[snafu(display("Wrong player"))]
    WrongPlayer,
    #[snafu(display("Position already occupied"))]
    OccupiedPosition,
    #[snafu(display("Invalid position"))]
    InvalidPosition,
    #[snafu(display("The game was already end"))]
    GameEnded,
}

#[cfg(test)]
mod tests {
    use crate::reversi::*;

    #[test]
    fn test() {
        let mut game = Reversi::new().unwrap();

        assert_eq!(game.place(Player::Player0, 2, 4), Ok(()));

        assert_eq!(game.place(Player::Player1, 2, 3), Ok(()));

        assert_eq!(
            game.place(Player::Player1, 2, 6),
            Err(ReversiError::WrongPlayer)
        );

        assert_eq!(
            game.place(Player::Player0, 2, 6),
            Err(ReversiError::InvalidPosition)
        );
    }
}
#[cfg(test)]
mod tests_rug_42 {
    use super::*;
    use crate::reversi::Player;

    #[test]
    fn test_rug() {
        let mut p0: Player = Player::Player0;

        assert_eq!(p0.other(), Player::Player1);

        p0 = Player::Player1;
        assert_eq!(p0.other(), Player::Player0);
    }
}#[cfg(test)]
mod tests_rug_43 {
    use super::*;
    use std::convert::Infallible;
    use crate::reversi::{Reversi, Player, GameState};

    #[test]
    fn test_new() {
        let result: Result<Reversi, Infallible> = crate::reversi::Reversi::new();
        
        assert!(result.is_ok());
        let game = result.unwrap();

        let mut expected_board = [[None; 8]; 8];
        expected_board[3][3] = Some(Player::Player0);
        expected_board[4][4] = Some(Player::Player0);
        expected_board[3][4] = Some(Player::Player1);
        expected_board[4][3] = Some(Player::Player1);

        assert_eq!(game.board, expected_board);
        assert_eq!(game.next, Player::Player0);
        assert_eq!(game.status, GameState::InProgress);
    }
}#[cfg(test)]
mod tests_rug_44 {
    use crate::reversi::{self, Reversi};

    #[test]
    fn test_rug() {
        let mut p0: Reversi = Reversi::new().unwrap();
        let p1: usize = 3;
        let p2: usize = 4;

        let _cell = p0.get(p1, p2);
    }
}#[cfg(test)]
mod tests_rug_45 {
    use super::*;
    use crate::reversi::{self, Reversi};
    
    #[test]
    fn test_rug() {
        let mut p0: Reversi = Reversi::new().unwrap();

        assert_eq!(p0.is_ended(), false);
    }
}#[cfg(test)]
mod tests_rug_46 {
    use crate::reversi::{self, Reversi};
    use super::*;

    #[test]
    fn test_rug() {
        let mut p0: Reversi = Reversi::new().unwrap();

        assert_eq!(p0.winner(), None);
    }
}#[cfg(test)]
mod tests_rug_47 {
    use super::*;
    use crate::reversi::{self, Reversi};

    #[test]
    fn test_rug() {
        let mut p0: Reversi = Reversi::new().unwrap();

        <reversi::Reversi>::status(&p0);
    }
}#[cfg(test)]
mod tests_rug_48 {
    use crate::reversi::{self, Reversi};
    
    #[test]
    fn test_get_next_player() {
        let mut p0: Reversi = Reversi::new().unwrap();

        let _next_player = p0.get_next_player();
    }
}#[cfg(test)]
mod tests_rug_49 {
    use crate::reversi::{self, Reversi, Player};

    #[test]
    fn test_place() {
        let mut game: Reversi = Reversi::new().unwrap();
        let player: Player = Player::Player0;
        let row: usize = 2;
        let col: usize = 3;

        assert_eq!(game.place(player, row, col), Ok(()));
    }
}#[cfg(test)]
mod tests_rug_50 {
    use crate::reversi::{self, Reversi, Player, ReversiError};

    #[test]
    fn test_rug() {
        let mut p0: Reversi = Reversi::new().unwrap();
        let mut p1: usize = 3; // sample data
        let mut p2: usize = 3; // sample data
        let mut p3: Player = Player::Player0;

        assert_eq!(p0.check_position_validity(p1, p2, p3), Ok(()));
    }
}#[cfg(test)]
mod tests_rug_51 {
    use crate::reversi::{self, Reversi, Player};
    use super::*;

    #[test]
    fn test_rug() {
        let mut p0: Reversi = Reversi::new().unwrap();
        let mut p1: usize = 3;
        let mut p2: usize = 4;
        let mut p3: Player = Player::Player0;

        assert!(p0.simple_check_position_validity(p1, p2, p3).is_ok());
    }
}#[cfg(test)]
mod tests_rug_52 {
    use crate::reversi::{self, Reversi, Player};

    #[test]
    fn test_can_player_move() {
        let mut p0: Reversi = Reversi::new().unwrap();
        let mut p1: Player = Player::Player0;

        assert!(p0.can_player_move(p1));
    }
}#[cfg(test)]
mod tests_rug_53 {
    use super::*;
    use crate::reversi::{self, Reversi, Player, GameState};
    use std::cmp::Ordering;

    #[test]
    fn test_check_state() {
        let mut p0: Reversi = Reversi::new().unwrap();

        // Optionally, you can modify the board state for more comprehensive testing
        // For example:
        // p0.board[3][3] = Player::Player0;
        // p0.board[4][4] = Player::Player1;

        p0.check_state();

        // Example assertions based on the initial state of Reversi::new()
        assert_eq!(p0.status, GameState::Tie);
    }
}#[cfg(test)]
mod tests_rug_54 {
    use crate::reversi::{self, Reversi, Direction, Player};

    #[test]
    fn test_rug() {
        let mut p0: Reversi = Reversi::new().unwrap();
        let p1: usize = 3;
        let p2: usize = 3;
        let p3: usize = 4;
        let p4: usize = 4;
        let p5: Direction = Direction::Right;
        let p6: Player = Player::Player0;

        <reversi::Reversi>::flip(&mut p0, p1, p2, p3, p4, p5, p6);
    }
}#[cfg(test)]
mod tests_rug_55 {
    use crate::reversi::{self, Reversi, Direction, Player};

    #[test]
    fn test_rug() {
        let mut p0: Reversi = Reversi::new().unwrap();
        let p1: usize = 3; // sample data for row
        let p2: usize = 3; // sample data for col
        let p3: Direction = Direction::Right; // example direction, you can choose any valid direction
        let p4: Player = Player::Player0;

        p0.check_occupied_line_in_direction(p1, p2, p3, p4);
    }
}#[cfg(test)]
mod tests_rug_57 {
    use super::*;
    use crate::reversi::{Direction, Reversi};

    #[test]
    fn test_rug() {
        let mut p0: Direction = Direction::Upper;

        let _offset = <Direction>::as_offset(&p0);
    }
}#[cfg(test)]
mod tests_rug_58 {
    use super::*;
    use crate::reversi::Direction;

    #[test]
    fn test_iter() {
        let directions: Vec<Direction> = Direction::iter().collect();
        
        assert_eq!(
            directions,
            vec![
                Direction::Upper,
                Direction::UpperRight,
                Direction::Right,
                Direction::LowerRight,
                Direction::Lower,
                Direction::LowerLeft,
                Direction::Left,
                Direction::UpperLeft,
            ]
        );
    }
}