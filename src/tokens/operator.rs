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
}
