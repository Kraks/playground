use std::io;

fn main() {
	let mut count: i32 = 0;

	fn hanoi(from:String, to:String, tmp:String, n:u8) {
		//fn mov(s1:&String, s2:&String){ }
    let mut mov = |s1: &String, s2: &String| {
      //count += 1;
      //println!("{}: {} --> {}", count, s1, s2);
      println!("{}: {} --> {}", count, s1, s2);
    };

		if n==1 {
			mov(&from,&to);
		} else {
			hanoi(from.clone(),tmp.clone(),to.clone(),n-1);
			mov(&from,&to);
			hanoi(tmp,to,from,n-1)
		}
	}

	loop {
		let mut buffer = String::new();
		let stdin = io::stdin();
		match stdin.read_line(&mut buffer) {
			Ok(_) => {
				hanoi(
					"A".to_string(),
					"B".to_string(),
					"C".to_string(),
					buffer.trim().parse::<u8>().unwrap());
			},
			Err(error) => println!("error: {error}"),
		}
		count=0;
	}
}
