mod errors;
mod postfix_expression;
mod stack;
mod tokens;

use std::collections::VecDeque;
use std::fmt;
use std::iter::Iterator;
use std::str::FromStr;

use errors::*;
use postfix_expression::PostfixExpression;
use stack::*;
use tokens::*;

// TODO Add 'em comments.
// TODO Handle negative numbers and all the other jazz with a unary minus.

/// Converts the stream of input tokens into a stream of tokens in the postfix notation.
///
/// This can return a stream that is not valid. Currently, the error is caught at `eval`uation.
fn convert_to_postfix(expr: &str) -> Result<PostfixExpression, ParseError> {
	let mut output = Vec::new();
	let mut ops = Stack::new();

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

	Ok(output.into())
}

// Worst fn in this code base
// TODO Tokenize in one pass (just store the spans?)
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

pub fn handle_operation_evaluation(
	op: Operator,
	numbers: &mut VecDeque<i32>,
) -> Result<i32, NotEnoughOperands> {
	numbers
		.pop_front()
		.zip(numbers.pop_front())
		.map(|(rop, lop)| op.perform(lop, rop))
		.ok_or(NotEnoughOperands)
}

pub struct PostfixString(String);

impl From<String> for PostfixString {
	fn from(s: String) -> Self {
		Self(s)
	}
}

impl FromStr for PostfixString {
	type Err = ParseError;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(s.parse::<PostfixExpression>()?
			.into_iter()
			.map(String::from)
			.collect::<Vec<String>>()
			.join(" ")
			.into())
	}
}

impl fmt::Display for PostfixString {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.0.fmt(f)
	}
}

/// Evaluates the the infix expression contained in `expr`.
///
/// # Usage
///
/// ```
/// use shunting_yard::eval;
///
/// let valid_expr = "1+2-(2+1)*2";
/// let invalid_expr = "x";
///
/// assert_eq!(eval(valid_expr), Ok(-3));
/// assert!(eval(invalid_expr).is_err())
/// ```
pub fn eval(expr: &str) -> Result<i32, ParseError> {
	let tokens = expr.parse::<PostfixExpression>()?;
	let mut numbers: VecDeque<i32> = VecDeque::new();

	for token in tokens {
		match token {
			OutToken::Num(n) => numbers.push_front(n),
			OutToken::Op(op) => {
				let val = handle_operation_evaluation(op, &mut numbers)?;
				numbers.push_front(val);
			}
		}
	}

	// There has to be only one element in `numbers`.
	let result = numbers.pop_front().ok_or(ParseError::NoValue);

	numbers
		.pop_front()
		.map_or(result, |n| Err(ParseError::LonerNumber(n)))
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
		use ParseError::*;

		macro_rules! gen_tests {
			($($input:literal => $expected:expr,)+) => {
				$(assert_eq!(
					$input.parse::<PostfixExpression>(),
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
						$input.parse::<PostfixExpression>().map(Vec::from),
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
		assert_eq!(eval("1+2-(2+1)*2").unwrap(), -3);
		assert_eq!(eval("2+(3*(8-4))").unwrap(), 14);
		assert_eq!(eval("0").unwrap(), 0);
		assert_eq!(eval("(0)").unwrap(), 0);
		assert_eq!(eval("(((0-1)))").unwrap(), -1);

		assert_eq!(eval("expr"), Err(ParseError::InvalidToken('e')));
		assert_eq!(eval("))"), Err(ParseError::UnbalancedParen(Paren::Right)));
		assert_eq!(eval("(())"), Err(ParseError::NoValue));
		assert_eq!(eval(""), Err(ParseError::NoValue));
		assert_eq!(eval("("), Err(ParseError::UnbalancedParen(Paren::Left)));
	}

	#[test]
	fn spaced_single_digit_numbers() {
		assert!(eval("112+(1 9)").is_err());
	}

	#[test]
	fn no_operator() {
		assert_eq!(eval("112(1+9)"), Err(ParseError::LonerNumber(112)));
	}
}
