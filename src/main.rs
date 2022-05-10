use shunting_yard::eval;

fn main() {
	let input: String = std::env::args().skip(1).take(1).collect();

	match eval(input.as_str()) {
		Ok(result) => println!("{} = {}", input, result),
		Err(e) => println!("{:?}", e),
	}
}
