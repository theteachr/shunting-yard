use shunting_yard::eval;

fn main() {
	let input: String = std::env::args().skip(1).take(1).collect();

	print!("{} = ", input);

	match eval(input) {
		Ok(result) => println!("{}", result),
		Err(e) => println!("{:?}", e),
	}
}
