use crate::errors::*;
use crate::tokens::*;
use crate::Enter;
use crate::Stack;
use std::collections::VecDeque;
use std::str::FromStr;

#[derive(Debug, Eq, PartialEq)]
pub struct PostfixExpression(Vec<OutToken>);

impl PostfixExpression {
	pub fn eval(self) -> Result<i32, ParseError> {
		let mut numbers: VecDeque<i32> = VecDeque::new();

		for token in self {
			match token {
				OutToken::Num(n) => numbers.push_front(n),
				OutToken::Op(op) => op.evaluate(&mut numbers)?.enter(&mut numbers),
			}
		}

		// There has to be only one element in `numbers`.
		match numbers.pop_front() {
			Some(val) if numbers.is_empty() => Ok(val),
			Some(_) => Err(ParseError::LonerNumber(numbers.pop_front().unwrap())),
			None => Err(ParseError::NoValue),
		}
	}
}

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
		let mut output = Vec::new();
		let mut ops = Stack::default();

		for token in group_numbers(s)
			.into_iter()
			.map(InToken::try_from)
			.collect::<Result<Vec<InToken>, InvalidToken>>()?
		{
			match token {
				InToken::Num(n) => output.push(OutToken::Num(n)),
				InToken::Op(op) => op.handle_parsing(&mut output, &mut ops),
				InToken::Paren(paren) => paren.handle_parsing(&mut output, &mut ops)?,
			}
		}

		// Collect the operators on the operator stack. If the stack contains a paren,
		// return with error.
		let popped_operators = ops
			.into_iter()
			.map(OutToken::try_from)
			.collect::<Result<Vec<OutToken>, UnbalancedParen>>()?;

		// Push all the operators into the output queue.
		output.extend(popped_operators);

		Ok(output.into())
	}
}

impl From<PostfixExpression> for Vec<OutToken> {
	fn from(expr: PostfixExpression) -> Self {
		expr.0
	}
}

//////// THE WORST ////////
// TODO: Tokenize in one pass (just store the spans?)
fn group_numbers(expr: &str) -> Vec<String> {
	let mut current_num = Vec::new();
	let mut new_tokens = Vec::new();

	for c in expr.chars() {
		if c.is_ascii_digit() {
			current_num.push(c);
			continue;
		}

		if !current_num.is_empty() {
			new_tokens.push(current_num.iter().collect::<String>());
			current_num.clear();
		}

		if c.is_whitespace() {
			continue;
		}

		new_tokens.push(c.to_string());
	}

	if !current_num.is_empty() {
		new_tokens.push(current_num.iter().collect::<String>());
	}

	new_tokens
}
