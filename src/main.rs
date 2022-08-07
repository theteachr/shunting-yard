use shunting_yard::{eval, parse};

fn main() {
	let input_expr: String = std::env::args().skip(1).take(1).collect();

	match parse(input_expr.clone()) {
		Ok(postfix_expr) => println!("{} => {}", input_expr, postfix_expr),
		Err(e) => eprintln!("{:?}", e),
	}

	match eval(input_expr.clone()) {
		Ok(v) => println!("{} = {}", input_expr, v),
		Err(e) => eprintln!("{:?}", e),
	}
}
