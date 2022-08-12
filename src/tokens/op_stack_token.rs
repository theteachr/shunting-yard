use super::{Operator, OutToken, Paren};
use crate::errors::UnbalancedParen;

#[derive(Debug, Eq, PartialEq)]
pub enum OpStackToken {
	Op(Operator),
	LeftParen,
}

impl OpStackToken {
	pub fn precedes(&self, rhs: Operator) -> bool {
		match self {
			Self::LeftParen => false,
			Self::Op(op) => op.precedes(rhs),
		}
	}
}

impl TryFrom<OpStackToken> for OutToken {
	type Error = UnbalancedParen;

	fn try_from(token: OpStackToken) -> Result<Self, Self::Error> {
		match token {
			OpStackToken::Op(op) => Ok(Self::Op(op)),
			OpStackToken::LeftParen => Err(UnbalancedParen(Paren::Left)),
		}
	}
}
