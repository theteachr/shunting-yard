use std::fmt;

use crate::{
	errors::UnbalancedParen,
	stack::{OpStack, Stack},
};

use super::{OpStackToken, OutToken};

#[derive(Debug, Eq, PartialEq)]
pub enum Paren {
	Left,
	Right,
}

impl Paren {
	pub fn handle_parsing(
		self,
		output: &mut Vec<OutToken>,
		ops: &mut Stack<OpStackToken>,
	) -> Result<(), UnbalancedParen> {
		match self {
			p @ Paren::Left => ops.push(p.into()),
			Paren::Right => ops.pop_until_left_paren(output)?,
		};

		Ok(())
	}
}

impl From<Paren> for OpStackToken {
	fn from(_: Paren) -> Self {
		Self::LeftParen
	}
}

impl fmt::Display for Paren {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let c = match self {
			Self::Left => "(",
			Self::Right => ")",
		};

		c.fmt(f)
	}
}
