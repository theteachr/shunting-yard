use std::collections::VecDeque;

use crate::{
	errors::NotEnoughOperands,
	stack::{OpStack, Stack},
};

use super::{OpStackToken, OutToken};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Operator {
	Add = 0b00,
	Sub = 0b01,
	Mul = 0b10,
	Div = 0b11,
}

impl std::fmt::Display for Operator {
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
	pub fn precedes(self, rhs: Self) -> bool {
		(self as u8 >> 1) >= (rhs as u8 >> 1)
	}

	pub fn perform(&self, a: i32, b: i32) -> i32 {
		match self {
			Self::Add => a + b,
			Self::Sub => a - b,
			Self::Mul => a * b,
			Self::Div => a / b,
		}
	}

	pub fn handle_parsing(self, output: &mut Vec<OutToken>, ops: &mut Stack<OpStackToken>) {
		// While the top of the operator stack has a higher precedence than `self`,
		// pop it off and push it to the output queue.
		while let Some(top) = ops.pop_op_when(|top| top.precedes(self)) {
			output.push(top.into());
		}

		// Push `self` into the operator stack.
		ops.push(self.into())
	}

	pub fn evaluate(self, numbers: &mut VecDeque<i32>) -> Result<i32, NotEnoughOperands> {
		numbers
			.pop_front()
			.zip(numbers.pop_front())
			.map(|(rop, lop)| self.perform(lop, rop))
			.ok_or(NotEnoughOperands)
	}
}

impl From<Operator> for OutToken {
	fn from(op: Operator) -> Self {
		Self::Op(op)
	}
}
