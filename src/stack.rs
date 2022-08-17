use crate::{errors::UnbalancedParen, tokens::*};

#[derive(Debug, PartialEq, Eq)]
pub struct Stack<T>(Vec<T>);

impl<T> Default for Stack<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Stack<T> {
	pub fn new() -> Self {
		Self(Vec::new())
	}

	pub fn pop(&mut self) -> Option<T> {
		self.0.pop()
	}

	pub fn last(&mut self) -> Option<&T> {
		self.0.last()
	}

	pub fn push(&mut self, item: T) {
		self.0.push(item);
	}
}

impl<T> From<Stack<T>> for Vec<T> {
	fn from(stack: Stack<T>) -> Self {
		stack.0
	}
}

pub(crate) trait OpStack {
	fn pop_op_when<F>(&mut self, predicate: F) -> Option<Operator>
	where
		F: FnOnce(&OpStackToken) -> bool;
	fn pop_until_left_paren(&mut self, output: &mut Vec<OutToken>) -> Result<(), UnbalancedParen>;
}

impl<T> Iterator for Stack<T> {
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		self.0.pop()
	}
}

impl OpStack for Stack<OpStackToken> {
	fn pop_op_when<F>(&mut self, predicate: F) -> Option<Operator>
	where
		F: FnOnce(&OpStackToken) -> bool,
	{
		if self.last().filter(|&top| predicate(top)).is_some() {
			if let Some(OpStackToken::Op(op)) = self.pop() {
				return Some(op);
			}
		}

		None
	}

	fn pop_until_left_paren(&mut self, output: &mut Vec<OutToken>) -> Result<(), UnbalancedParen> {
		while let Some(op) = self.pop() {
			match op {
				OpStackToken::LeftParen => return Ok(()),
				OpStackToken::Op(o) => output.push(OutToken::Op(o)),
			}
		}

		Err(UnbalancedParen(Paren::Right))
	}
}
