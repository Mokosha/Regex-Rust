// Regex matcher
//
// Supported expressions
// a      - character
// .      - wildcard
// *      - match none or more
// +      - match one or more
// ?      - match none or one
// \      - escape
// [0-9]  - numeral
// [a-z]  - lowercase
// [A-Z]  - uppercase
// [...]  - any of
// [^...] - none of
// (...)  - subexpression

mod expr;
mod tokenizer;
pub mod regex;

#[test]
fn it_can_recognize_phone_numbers() {
    use regex::SatisfiesRegex;
    let phone_regex = "(1[-.]?)?\\(?([0-9][0-9][0-9])\\)?[-. ]?([0-9][0-9][0-9])[-. ]?([0-9][0-9][0-9][0-9])";

    assert!(phone_regex.is_satisfied_by("(623) 456-8293".to_string()));
    assert!(phone_regex.is_satisfied_by("623.456.8293".to_string()));
    assert!(phone_regex.is_satisfied_by("(623).456.8293".to_string()));
    assert!(phone_regex.is_satisfied_by("623-456-8293".to_string()));

    assert!(phone_regex.is_satisfied_by("1-623-456-8293".to_string()));
    assert!(phone_regex.is_satisfied_by("1.623.456.8293".to_string()));
    assert!(phone_regex.is_satisfied_by("16234568293".to_string()));
    assert!(phone_regex.is_satisfied_by("6234568293".to_string()));

    assert!(phone_regex.is_not_satisfied_by("116234568293".to_string()));
}
