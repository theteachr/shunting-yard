use std::collections::VecDeque;
use std::convert::TryFrom;
use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Operation {
	Add = 1,
	Sub = 7,
	Mul = 2,
	Div = 8,
	LeftParen = 0,
	RightParen = 9,
}

impl Display for Operation {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let text = match self {
			Self::Add => "+",
			Self::Sub => "-",
			Self::Mul => "*",
			Self::Div => "/",
			Self::LeftParen => "(",
			Self::RightParen => ")",
		};

		text.fmt(f)
	}
}

impl Operation {
	fn precedes(self, other: Self) -> bool {
		((self as u8) % 6) >= ((other as u8) % 6)
	}

	fn perform(&self, a: i32, b: i32) -> i32 {
		match self {
			Operation::Add => a + b,
			Operation::Sub => a - b,
			Operation::Mul => a * b,
			Operation::Div => a / b,
			_ => unreachable!(),
		}
	}
}

#[derive(Debug)]
pub enum Token {
	Num(i32),
	Op(Operation),
}

impl Display for Token {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Num(n) => n.fmt(f),
			Self::Op(op) => op.fmt(f),
		}
	}
}

#[derive(Debug)]
pub enum ResolveError {
	Token(char),
	LeftParenNotFound,
	NotEnoughOperands,
	NoValue,
}

#[derive(Debug)]
pub struct InvalidToken(char);

#[derive(Debug)]
struct LeftParenNotFound;

#[derive(Debug)]
struct NotEnoughOperands;

impl From<NotEnoughOperands> for ResolveError {
	fn from(_: NotEnoughOperands) -> Self {
		Self::NotEnoughOperands
	}
}

impl From<LeftParenNotFound> for ResolveError {
	fn from(_: LeftParenNotFound) -> Self {
		Self::LeftParenNotFound
	}
}

impl From<InvalidToken> for ResolveError {
	fn from(invalid_token: InvalidToken) -> Self {
		Self::Token(invalid_token.0)
	}
}

impl From<Operation> for Token {
	fn from(op: Operation) -> Self {
		Self::Op(op)
	}
}

impl TryFrom<char> for Token {
	type Error = InvalidToken;

	fn try_from(string: char) -> Result<Self, Self::Error> {
		let op = match string {
			'+' => Operation::Add,
			'-' => Operation::Sub,
			'*' => Operation::Mul,
			'/' => Operation::Div,
			'(' => Operation::LeftParen,
			')' => Operation::RightParen,
			s => {
				return s
					.to_digit(10)
					.map(|digit| Self::Num(digit as i32))
					.ok_or(InvalidToken(s));
			}
		};

		Ok(op.into())
	}
}

fn pop_until_left_paren(
	output: &mut Vec<Token>,
	ops: &mut Vec<Operation>,
) -> Result<(), LeftParenNotFound> {
	while let Some(op) = ops.pop() {
		if matches!(op, Operation::LeftParen) {
			return Ok(());
		}

		output.push(Token::Op(op));
	}

	Err(LeftParenNotFound)
}

fn handle_operation_parsing(op: Operation, output: &mut Vec<Token>, ops: &mut Vec<Operation>) {
	while ops.last().map(|&top| top.precedes(op)).unwrap_or(false) {
		output.push(Token::Op(ops.pop().unwrap()));
	}

	ops.push(op)
}

fn handle_operation_evaluation(
	op: Operation,
	numbers: &mut VecDeque<i32>,
) -> Result<(), NotEnoughOperands> {
	let result = numbers
		.pop_front()
		.zip(numbers.pop_front())
		.map(|(rop, lop)| op.perform(lop, rop))
		.ok_or(NotEnoughOperands)?;

	Ok(numbers.push_front(result))
}

// TODO Make this work for multi digit numbers.
fn parse_into_tokens(expr: &str) -> Result<Vec<Token>, ResolveError> {
	let mut output: Vec<Token> = Vec::new();
	let mut ops: Vec<Operation> = Vec::new();
	let tokens = expr.chars().map(Token::try_from).collect::<Result<Vec<Token>, _>>()?;

	for token in tokens.into_iter() {
		match token {
			Token::Num(_) => output.push(token),
			Token::Op(op @ Operation::LeftParen) => ops.push(op),
			Token::Op(Operation::RightParen) => pop_until_left_paren(&mut output, &mut ops)?,
			Token::Op(op) => handle_operation_parsing(op, &mut output, &mut ops),
		}
	}

	while let Some(op) = ops.pop() {
		output.push(op.into())
	}

	Ok(output)
}

pub fn parse(expr: &str) -> Result<String, ResolveError> {
	Ok(parse_into_tokens(expr)?
		.iter()
		.map(Token::to_string)
		.collect())
}

pub fn eval(expr: &str) -> Result<i32, ResolveError> {
	let tokens = parse_into_tokens(expr)?;
	let mut numbers: VecDeque<i32> = VecDeque::new();

	for token in tokens.into_iter() {
		match token {
			Token::Num(n) => numbers.push_front(n),
			Token::Op(op) => handle_operation_evaluation(op, &mut numbers)?,
		}
	}

	numbers.pop_front().ok_or(ResolveError::NoValue)
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
	use Operation::*;

	#[test]
	fn add_precedes_sub() {
		assert!(Add.precedes(Sub))
	}

	#[test]
	fn sub_precedes_add() {
		assert!(Sub.precedes(Add))
	}

	// TODO Use macros to write the tests.
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
	fn parsing_works() {
		assert!(matches!(parse("1+s"), Err(_)));
		assert!(matches!(parse("1+2-8)"), Err(_)));
		assert!(matches!(parse(")))"), Err(_)));
		assert_eq!(parse("1+2-(2+1)*2").unwrap(), "12+21+2*-");
		assert_eq!(parse("2+(3*(8-4))").unwrap(), "2384-*+");
		assert_eq!(parse("(0)").unwrap(), "0");
	}

	#[test]
	fn eval_works() {
		assert_eq!(eval("1+2-(2+1)*2").unwrap(), -3);
		assert_eq!(eval("2+(3*(8-4))").unwrap(), 14);
		assert_eq!(eval("0").unwrap(), 0);
		assert_eq!(eval("(0)").unwrap(), 0);
		assert_eq!(eval("(((0-1)))").unwrap(), -1);
		assert!(matches!(eval("expr"), Err(_)));
		assert!(matches!(eval("))"), Err(_)));
	}
}
