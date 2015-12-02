extern crate regex;

use regex::regex::SatisfiesRegex;

fn main() {
    let args : Vec<String> = ::std::env::args().collect();
    if args.len() != 3 {
        println!("Usage: <regex> <string>");
        return;
    }

    if args[1].clone().is_satisfied_by(args[2].clone()) {
        println!("Match!");
    } else {
        println!("No match!");
    }
}
