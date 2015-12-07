mod expr;
mod tokenizer;
mod nfa;
pub mod regex;

#[test]
fn it_can_recognize_phone_numbers() {
    use regex::IsRegex;
    let phone_regex = "(1[-.]?)?\\(?([0-9][0-9][0-9])\\)?[-. ]?([0-9][0-9][0-9])[-. ]?([0-9][0-9][0-9][0-9])";

    assert!(phone_regex.is_matched_by("(623) 456-8293".to_string()));
    assert!(phone_regex.is_matched_by("623.456.8293".to_string()));
    assert!(phone_regex.is_matched_by("(623).456.8293".to_string()));
    assert!(phone_regex.is_matched_by("623-456-8293".to_string()));

    assert!(phone_regex.is_matched_by("1-623-456-8293".to_string()));
    assert!(phone_regex.is_matched_by("1.623.456.8293".to_string()));
    assert!(phone_regex.is_matched_by("16234568293".to_string()));
    assert!(phone_regex.is_matched_by("6234568293".to_string()));

    assert!(phone_regex.is_not_matched_by("116234568293".to_string()));
    assert!(phone_regex.is_not_matched_by("1-6-23-456-8293".to_string()));
    assert!(phone_regex.is_not_matched_by("16-23-456-8293".to_string()));
    assert!(phone_regex.is_not_matched_by("1-800-GEICO".to_string()));

    // These are supported, but probably shouldn't be:
    assert!(phone_regex.is_matched_by("1-(800-2222222".to_string()));
    assert!(phone_regex.is_matched_by("1-800)-222 2222".to_string()));
}

#[test]
fn it_handles_exponential_time() {
    use regex::IsRegex;
    assert!("a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*"
            .is_not_matched_by("aaaaaaaaaaaaaaaaaaaaaaaab"));

    for i in 0..50 {
        let mut regex = ::std::iter::repeat("a?").take(i).collect::<String>();
        for _ in 0..i {
            regex.push('a');
        }

        let s = ::std::iter::repeat("a").take(i).collect::<String>();
        assert!(regex.is_matched_by(s));
    }
}
