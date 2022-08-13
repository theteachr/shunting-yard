use shunting_yard::{eval, PostfixString};

fn main() {
	let input_expr: String = std::env::args().skip(1).take(1).collect();

	match &input_expr.parse::<PostfixString>() {
		Ok(postfix_expr) => println!("{} => {}", input_expr, postfix_expr),
		Err(e) => eprintln!("{:?}", e),
	}

	match eval(&input_expr) {
		Ok(v) => println!("{} = {}", input_expr, v),
		Err(e) => eprintln!("{:?}", e),
	}
}
