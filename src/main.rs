use std::collections::VecDeque;
use std::convert::TryFrom;
use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Operation {
	Add = 2,
	Sub = 1,
	Mul = 4,
	Div = 3,
	LeftParen = 0,
	RightParen = 6,
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
	fn precedes(self, other: &Self) -> bool {
		self.cmp(other).is_ge()
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
enum Token {
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

// FIXME Add a type for each kind of error.
#[derive(Debug)]
struct InvalidToken(char);

impl TryFrom<char> for Token {
	type Error = InvalidToken;

	fn try_from(string: char) -> Result<Self, Self::Error> {
		let op = match string {
			'+' => Self::Op(Operation::Add),
			'-' => Self::Op(Operation::Sub),
			'*' => Self::Op(Operation::Mul),
			'/' => Self::Op(Operation::Div),
			'(' => Self::Op(Operation::LeftParen),
			')' => Self::Op(Operation::RightParen),
			s => {
				return s
					.to_digit(10)
					.map(|digit| Self::Num(digit as i32))
					.ok_or(InvalidToken(s));
			}
		};

		Ok(op)
	}
}

fn pop_until_left_paren(
	output: &mut Vec<Token>,
	ops: &mut Vec<Operation>,
) -> Result<(), InvalidToken> {
	while let Some(op) = ops.pop() {
		if matches!(op, Operation::LeftParen) {
			println!("Removed paren.");
			return Ok(());
		}
		output.push(Token::Op(op));
	}

	Err(InvalidToken(')'))
}

fn handle_operation_parsing(op: Operation, output: &mut Vec<Token>, ops: &mut Vec<Operation>) {
	while ops.last().map(|&top| top.precedes(&op)).unwrap_or(false) {
		output.push(Token::Op(ops.pop().unwrap()));
	}

	ops.push(op)
}

fn handle_operation_evaluation(op: Operation, numbers: &mut VecDeque<i32>) -> Result<(), InvalidToken> {
	let result = numbers
		.pop_front()
		.zip(numbers.pop_front())
		.map(|(rop, lop)| op.perform(lop, rop))
		.ok_or(InvalidToken('x'))?;

	Ok(numbers.push_front(result))
}

// TODO Make this work for multi digit numbers.
fn parse_into_tokens(expr: &str) -> Result<Vec<Token>, InvalidToken> {
	let mut output: Vec<Token> = Vec::new();
	let mut ops: Vec<Operation> = Vec::new();
	let tokens: Result<Vec<Token>, InvalidToken> = expr.chars().map(Token::try_from).collect();

	for token in tokens?.into_iter() {
		match token {
			Token::Num(_) => output.push(token),
			Token::Op(op @ Operation::LeftParen) => ops.push(op),
			Token::Op(Operation::RightParen) => pop_until_left_paren(&mut output, &mut ops)?,
			Token::Op(op) => handle_operation_parsing(op, &mut output, &mut ops),
		}
	}

	output.extend(ops.drain(..).rev().map(Token::Op));

	Ok(output)
}

fn parse(expr: &str) -> Result<String, InvalidToken> {
	Ok(parse_into_tokens(expr)?
		.iter()
		.map(Token::to_string)
		.collect())
}

fn eval(expr: &str) -> Result<i32, InvalidToken> {
	let tokens = parse_into_tokens(expr)?.into_iter();
	let mut numbers: VecDeque<i32> = VecDeque::new();

	for token in tokens {
		match token {
			Token::Num(n) => numbers.push_front(n),
			Token::Op(op) => handle_operation_evaluation(op, &mut numbers)?,
		}
	}

	Ok(numbers.pop_front().unwrap())
}

fn main() {
	let input: String = std::env::args().skip(1).take(1).collect();

	println!(
		"{}",
		parse(input.as_str()).unwrap_or("Unparsable input".to_string())
	);

	println!("{} = {}", input, eval(input.as_str()).unwrap_or(0));
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
		assert!(Add.precedes(&Sub))
	}

	#[test]
	fn sub_does_not_precede_add() {
		assert!(!Sub.precedes(&Add))
	}

	#[test]
	fn mul_precedes_div() {
		assert!(Mul.precedes(&Div))
	}

	#[test]
	fn div_does_not_precede_mul() {
		assert!(!Div.precedes(&Mul))
	}

	#[test]
	fn mul_precedes_add() {
		assert!(Mul.precedes(&Add))
	}

	#[test]
	fn div_precedes_add() {
		assert!(Div.precedes(&Add))
	}

	#[test]
	fn mul_precedes_sub() {
		assert!(Mul.precedes(&Sub))
	}

	#[test]
	fn parsing_works() {
		assert!(matches!(parse("1+s"), Err(_)));
		assert!(matches!(parse("1+2-8)"), Err(_)));
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
	}
}
