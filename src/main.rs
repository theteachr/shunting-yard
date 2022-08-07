use shunting_yard::{eval, parse_into_tokens};

fn main() {
	let input: String = std::env::args().skip(1).take(1).collect();

	match parse_into_tokens(input.clone()).and_then(eval) {
		Ok(result) => println!("{} = {}", input, result),
		Err(e) => eprintln!("{:?}", e),
	}
}
