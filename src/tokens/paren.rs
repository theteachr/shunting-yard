use std::fmt;

#[derive(Debug, Eq, PartialEq)]
pub enum Paren {
	Left,
	Right,
}

impl fmt::Display for Paren {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let c = match self {
			Self::Left => "(",
			Self::Right => ")",
		};

		c.fmt(f)
	}
}
