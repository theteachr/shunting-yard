use super::Operator;

#[derive(Debug, Eq, PartialEq)]
pub enum OutToken {
	Num(i32),
	Op(Operator),
}

impl From<OutToken> for String {
	fn from(token: OutToken) -> Self {
		match token {
			OutToken::Num(n) => n.to_string(),
			OutToken::Op(op) => op.to_string(),
		}
	}
}
