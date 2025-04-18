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

// TODO: Handle negative numbers and all the other jazz with a unary minus.

pub struct PostfixString(String);

impl From<String> for PostfixString {
	fn from(s: String) -> Self {
		Self(s)
	}
}

impl FromStr for PostfixString {
	type Err = ParseError;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		if s.is_empty() {
			return Err(ParseError::NoValue);
		}

		let result = s
			.parse::<PostfixExpression>()?
			.into_iter()
			.map(String::from)
			.collect::<Vec<String>>()
			.join("|");

		Ok(format!("|{result}|").into())
	}
}

impl fmt::Display for PostfixString {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.0.fmt(f)
	}
}

trait Enter: Sized {
	fn enter(self, queue: &mut VecDeque<Self>) {
		queue.push_front(self);
	}
}

impl Enter for i32 {}

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
	expr.parse::<PostfixExpression>()?.eval()
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
	use tokens::*;
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
