#![feature(assert_matches)]

use std::collections::VecDeque;
use std::convert::TryFrom;
use std::fmt::Display;
use std::iter::Iterator;

// TODO Add 'em comments.
// TODO Handle negative numbers and all the other jazz with a unary minus.

#[derive(Debug, PartialEq, Eq)]
struct Stack<T>(Vec<T>);

impl<T> Stack<T> {
	fn new() -> Self {
		Self(Vec::new())
	}

	fn pop(&mut self) -> Option<T> {
		self.0.pop()
	}

	fn last(&mut self) -> Option<&T> {
		self.0.last()
	}

	fn push(&mut self, item: T) {
		self.0.push(item);
	}
}

impl<T> From<Stack<T>> for Vec<T> {
	fn from(stack: Stack<T>) -> Self {
		stack.0
	}
}

trait OpStack {
	fn pop_op_when<P>(&mut self, p: P) -> Option<Operator>
	where
		P: FnOnce(&OpStackToken) -> bool;
}

impl<T> Iterator for Stack<T> {
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		self.0.pop()
	}
}

impl OpStack for Stack<OpStackToken> {
	fn pop_op_when<P>(&mut self, p: P) -> Option<Operator>
	where
		P: FnOnce(&OpStackToken) -> bool,
	{
		if self.last().filter(|&top| p(top)).is_some() {
			if let Some(OpStackToken::Op(op)) = self.pop() {
				return Some(op);
			}
		}

		None
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Operator {
	Add = 0b00,
	Sub = 0b01,
	Mul = 0b10,
	Div = 0b11,
}

impl Display for Operator {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let text = match self {
			Self::Add => "+",
			Self::Sub => "-",
			Self::Mul => "*",
			Self::Div => "/",
		};

		text.fmt(f)
	}
}

impl Operator {
	fn precedes(self, rhs: Self) -> bool {
		(self as u8 >> 1) >= (rhs as u8 >> 1)
	}

	fn perform(&self, a: i32, b: i32) -> i32 {
		match self {
			Self::Add => a + b,
			Self::Sub => a - b,
			Self::Mul => a * b,
			Self::Div => a / b,
		}
	}
}

#[derive(Debug, Eq, PartialEq)]
pub enum Paren {
	Left,
	Right,
}

impl Display for Paren {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let c = match self {
			Self::Left => "(",
			Self::Right => ")",
		};

		c.fmt(f)
	}
}

#[derive(Debug, Eq, PartialEq)]
pub enum InToken {
	Num(i32),
	Op(Operator),
	Paren(Paren),
}

#[derive(Debug, Eq, PartialEq)]
pub enum OpStackToken {
	Op(Operator),
	LeftParen,
}

#[derive(Debug, Eq, PartialEq)]
pub enum OutToken {
	Num(i32),
	Op(Operator),
}

impl OpStackToken {
	fn precedes(&self, rhs: Operator) -> bool {
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

impl From<OutToken> for String {
	fn from(token: OutToken) -> Self {
		match token {
			OutToken::Num(n) => n.to_string(),
			OutToken::Op(op) => op.to_string(),
		}
	}
}

impl Display for InToken {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Num(n) => n.fmt(f),
			Self::Op(op) => op.fmt(f),
			Self::Paren(paren) => paren.fmt(f),
		}
	}
}

#[derive(Debug, Eq, PartialEq)]
pub enum ResolveError {
	InvalidToken(char),
	UnbalancedParen(Paren),
	NotEnoughOperands,
	NoValue,
	LonerNumber(i32),
}

#[derive(Debug, Eq, PartialEq)]
pub struct InvalidToken(char);

#[derive(Debug, Eq, PartialEq)]
pub struct UnbalancedParen(Paren);

#[derive(Debug, Eq, PartialEq)]
pub struct NotEnoughOperands;

impl From<NotEnoughOperands> for ResolveError {
	fn from(_: NotEnoughOperands) -> Self {
		Self::NotEnoughOperands
	}
}

impl From<UnbalancedParen> for ResolveError {
	fn from(unbalanced_paren: UnbalancedParen) -> Self {
		Self::UnbalancedParen(unbalanced_paren.0)
	}
}

impl From<InvalidToken> for ResolveError {
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

fn pop_until_left_paren(
	output: &mut Vec<OutToken>,
	ops: &mut Stack<OpStackToken>,
) -> Result<(), UnbalancedParen> {
	while let Some(op) = ops.pop() {
		match op {
			OpStackToken::LeftParen => return Ok(()),
			OpStackToken::Op(o) => output.push(OutToken::Op(o)),
		}
	}

	Err(UnbalancedParen(Paren::Right))
}

fn handle_operation_parsing(
	op: Operator,
	output: &mut Vec<OutToken>,
	ops: &mut Stack<OpStackToken>,
) {
	// While the top of the operator stack has a higher precedence than `op`,
	// pop it off and push it to the output queue.
	while let Some(top) = ops.pop_op_when(|top| top.precedes(op)) {
		output.push(OutToken::Op(top));
	}

	ops.push(op.into())
}

fn handle_operation_evaluation(
	op: Operator,
	numbers: &mut VecDeque<i32>,
) -> Result<i32, NotEnoughOperands> {
	numbers
		.pop_front()
		.zip(numbers.pop_front())
		.map(|(rop, lop)| op.perform(lop, rop))
		.ok_or(NotEnoughOperands)
}

// Worst fn in this code base
// TODO Tokenize in one pass (just store the spans?)
fn group_numbers(expr: String) -> Vec<String> {
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

	dbg!(&new_tokens);

	new_tokens
}

/// Converts the infix expression into a stream of tokens in the postfix notation.
///
/// This can return a stream that is not valid. Currently, the error is caught at `eval`uation.
fn parse_into_tokens(expr: String) -> Result<Vec<OutToken>, ResolveError> {
	let mut output = Vec::new();
	let mut ops = Stack::new();

	// 23  + 5 => ["23", "+", "5"]
	// 23+58546 => ["23", "+", "58546"]

	let tokens = group_numbers(expr)
		.into_iter()
		.map(InToken::try_from)
		.collect::<Result<Vec<InToken>, _>>()?;

	for token in tokens {
		match token {
			InToken::Num(n) => output.push(OutToken::Num(n)),
			InToken::Op(op) => handle_operation_parsing(op, &mut output, &mut ops),
			InToken::Paren(paren) => match paren {
				Paren::Left => ops.push(OpStackToken::LeftParen),
				Paren::Right => pop_until_left_paren(&mut output, &mut ops)?,
			},
		}
	}

	// While there are operators on the operator stack, pop them off and push them into the output
	// queue.
	output.extend(
		ops.into_iter()
			.map(OutToken::try_from)
			.collect::<Result<Vec<OutToken>, _>>()?,
	);

	Ok(output)
}

pub fn parse(expr: String) -> Result<String, ResolveError> {
	Ok(parse_into_tokens(expr)?
		.into_iter()
		.map(String::from)
		.collect::<Vec<String>>()
		.join(" "))
}

pub fn eval(expr: String) -> Result<i32, ResolveError> {
	let tokens = parse_into_tokens(expr)?;
	let mut numbers: VecDeque<i32> = VecDeque::new();

	dbg!(&tokens);

	for token in tokens {
		match token {
			OutToken::Num(n) => numbers.push_front(n),
			OutToken::Op(op) => {
				let val = handle_operation_evaluation(op, &mut numbers)?;
				dbg!(val);
				numbers.push_front(val);
			}
		}
	}

	// There has to be only one element in `numbers`.
	let result = numbers.pop_front().ok_or(ResolveError::NoValue);

	numbers
		.pop_front()
		.map_or(result, |n| Err(ResolveError::LonerNumber(n)))
}

// 1+2-(2+1)*2
//
// 12+21+2*-
// ______________________           __________________
//       output                         input
//
//  op_stack:
//
//
//
//
//
//
//
// ______________________           __________________
//       input                          output
//
//  working_stack:
//  num_queue: 36
//

#[cfg(test)]
mod tests {
	use super::*;
	use std::assert_matches::assert_matches;
	use Operator::*;

	#[test]
	fn add_precedes_sub() {
		assert!(Add.precedes(Sub))
	}

	#[test]
	fn sub_precedes_add() {
		assert!(Sub.precedes(Add))
	}

	#[test]
	fn mul_precedes_div() {
		assert!(Mul.precedes(Div))
	}

	#[test]
	fn div_precedes_mul() {
		assert!(Div.precedes(Mul))
	}

	#[test]
	fn mul_precedes_add() {
		assert!(Mul.precedes(Add))
	}

	#[test]
	fn div_precedes_add() {
		assert!(Div.precedes(Add))
	}

	#[test]
	fn mul_precedes_sub() {
		assert!(Mul.precedes(Sub))
	}

	#[test]
	fn add_does_not_precede_mul() {
		assert!(!Add.precedes(Mul))
	}

	#[test]
	fn sub_does_not_precede_mul() {
		assert!(!Sub.precedes(Mul))
	}

	#[test]
	fn sub_does_not_precede_div() {
		assert!(!Sub.precedes(Div))
	}

	#[test]
	fn add_does_not_precede_div() {
		assert!(!Add.precedes(Div))
	}

	// TODO Break tests
	// TODO Test multi digit number parsing

	#[test]
	fn parsing_invalid_expressions() {
		use Paren::*;
		use ResolveError::*;

		macro_rules! gen_tests {
			($($input:literal => $expected:pat,)+) => {
				$(assert_matches!(
					parse_into_tokens(String::from($input)),
					Err($expected),
					"input = `{}`", $input
				);)+
			};
		}

		gen_tests! {
			"1+s" => InvalidToken('s'),
			"1+2-8)" => UnbalancedParen(Right),
			"1 +2- 8)" => UnbalancedParen(Right),
			")))" => UnbalancedParen(Right),
		}
	}

	#[test]
	fn parsing_valid_expressions() {
		use Operator::*;
		use OutToken::*;

		macro_rules! gen_token {
			(-) => {
				Op(Sub)
			};
			(+) => {
				Op(Add)
			};
			(*) => {
				Op(Mul)
			};
			(/) => {
				Op(Div)
			};
			($number:literal) => {
				Num($number)
			};
		}

		macro_rules! gen_tests {
			($($input:literal => [$($variant:tt)*],)+) => {
				$(
					assert_eq!(
						parse_into_tokens(String::from($input)).map(Vec::from),
						Ok(vec![$(gen_token!($variant)),*]),
						"input = `{}`", $input
					);
				)+
			}
		}

		gen_tests! {
			"12-(2+1)*2" => [12 2 1 + 2 * -],
			"(0)" => [0],
			"" => [],
			"(())" => [],
			"1 + 1" => [1 1 +],
		}
	}

	#[test]
	fn eval_works() {
		assert_eq!(eval(String::from("1+2-(2+1)*2")).unwrap(), -3);
		assert_eq!(eval(String::from("2+(3*(8-4))")).unwrap(), 14);
		assert_eq!(eval(String::from("0")).unwrap(), 0);
		assert_eq!(eval(String::from("(0)")).unwrap(), 0);
		assert_eq!(eval(String::from("(((0-1)))")).unwrap(), -1);

		assert_matches!(
			eval(String::from("expr")),
			Err(ResolveError::InvalidToken('e'))
		);
		assert_matches!(
			eval(String::from("))")),
			Err(ResolveError::UnbalancedParen(Paren::Right))
		);
		assert_matches!(eval(String::from("(())")), Err(ResolveError::NoValue));
		assert_matches!(eval(String::from("")), Err(ResolveError::NoValue));
		assert_matches!(
			eval(String::from("(")),
			Err(ResolveError::UnbalancedParen(Paren::Left))
		);
	}

	#[test]
	fn spaced_single_digit_numbers() {
		assert!(eval(String::from("112+(1 9)")).is_err());
	}

	#[test]
	fn no_operator() {
		assert_matches!(
			eval(String::from("112(1+9)")),
			Err(ResolveError::LonerNumber(112))
		);
	}
}
