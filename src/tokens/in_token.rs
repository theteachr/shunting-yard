use super::{Operator, Paren};
use crate::errors::InvalidToken;
use std::fmt;

#[derive(Debug, Eq, PartialEq)]
pub enum InToken {
	Num(i32),
	Op(Operator),
	Paren(Paren),
}

impl fmt::Display for InToken {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::Num(n) => n.fmt(f),
			Self::Op(op) => op.fmt(f),
			Self::Paren(paren) => paren.fmt(f),
		}
	}
}

impl TryFrom<String> for InToken {
	type Error = InvalidToken;

	fn try_from(text: String) -> Result<Self, Self::Error> {
		Ok(match text.as_str() {
			"+" => Operator::Add.into(),
			"-" => Operator::Sub.into(),
			"*" => Operator::Mul.into(),
			"/" => Operator::Div.into(),
			"(" => Paren::Left.into(),
			")" => Paren::Right.into(),
			s => s
				.parse::<i32>()
				.map(InToken::Num)
				.map_err(|_| InvalidToken(s.chars().next().unwrap()))?,
		})
	}
}
