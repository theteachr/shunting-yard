use crate::tokens::*;

#[derive(Debug, Eq, PartialEq)]
pub enum ParseError {
	InvalidToken(char),
	UnbalancedParen(Paren),
	NotEnoughOperands,
	NoValue,
	LonerNumber(i32),
}

#[derive(Debug, Eq, PartialEq)]
pub struct InvalidToken(pub char);

#[derive(Debug, Eq, PartialEq)]
pub struct UnbalancedParen(pub Paren);

#[derive(Debug, Eq, PartialEq)]
pub struct NotEnoughOperands;

impl From<NotEnoughOperands> for ParseError {
	fn from(_: NotEnoughOperands) -> Self {
		Self::NotEnoughOperands
	}
}

impl From<UnbalancedParen> for ParseError {
	fn from(unbalanced_paren: UnbalancedParen) -> Self {
		Self::UnbalancedParen(unbalanced_paren.0)
	}
}

impl From<InvalidToken> for ParseError {
	fn from(invalid_token: InvalidToken) -> Self {
		Self::InvalidToken(invalid_token.0)
	}
}

impl From<Operator> for InToken {
	fn from(op: Operator) -> Self {
		Self::Op(op)
	}
}

impl From<Operator> for OpStackToken {
	fn from(op: Operator) -> Self {
		Self::Op(op)
	}
}

impl From<Paren> for InToken {
	fn from(paren: Paren) -> Self {
		Self::Paren(paren)
	}
}
