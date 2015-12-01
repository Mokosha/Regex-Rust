// Regex matcher
//
// Supported expressions
// a      - character
// .      - wildcard
// *      - match none or more
// +      - match one or more
// ?      - match none or one
// \      - escape
// 0-9    - numeral
// a-z    - lowercase
// A-Z    - uppercase
// [...]  - any of
// [^...] - none of
// (...)  - subexpression

mod expr;
mod tokenizer;
pub mod regex;

#[test]
fn it_works() {
}
