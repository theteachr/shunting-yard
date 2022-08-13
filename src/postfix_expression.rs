use crate::convert_to_postfix;
use crate::errors::*;
use crate::tokens::*;
use std::str::FromStr;

#[derive(Debug, Eq, PartialEq)]
pub struct PostfixExpression(Vec<OutToken>);

impl From<Vec<OutToken>> for PostfixExpression {
	fn from(tokens: Vec<OutToken>) -> Self {
		Self(tokens)
	}
}

impl IntoIterator for PostfixExpression {
	type Item = OutToken;

	type IntoIter = std::vec::IntoIter<Self::Item>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl FromStr for PostfixExpression {
	type Err = ParseError;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		convert_to_postfix(s)
	}
}

impl From<PostfixExpression> for Vec<OutToken> {
	fn from(expr: PostfixExpression) -> Self {
		expr.0
	}
}
