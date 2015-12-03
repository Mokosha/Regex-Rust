//! A crate for using regular expressions.
//!
//! ---
//!
//! Although many of the features common to regular expressions are excluded,
//! this crate does present an initial system of matching against regular
//! expressions.
//!
//! ## Supported expressions:
//!
//! String literals:
//!
//! ```
//!   use regex::regex::SatisfiesRegex;
//!   assert!("hello".is_satisfied_by("hello".to_string()));
//! ```
//!
//! ---
//! Wildcards
//!
//! ```
//!   use regex::regex::SatisfiesRegex;
//!   assert!("h.ll.".is_satisfied_by("hello".to_string()));
//!   assert!("h.ll.".is_satisfied_by("hilly".to_string()));
//! ```
//!
//! ---
//! None or more
//!
//! ```
//!   use regex::regex::SatisfiesRegex;
//!   assert!("hello*".is_satisfied_by("hello".to_string()));
//!   assert!("hello*".is_satisfied_by("hell".to_string()));
//!   assert!("hello*".is_satisfied_by("helloooooooooooooooooooo".to_string()));
//!   assert!("h.l*y".is_satisfied_by("hilllllllllly".to_string()));
//!   assert!("h.l*y".is_satisfied_by("hiy".to_string()));
//! ```
//!
//! ---
//! One or more
//!
//! ```
//!   use regex::regex::SatisfiesRegex;
//!   assert!("hel+o".is_satisfied_by("hello".to_string()));
//!   assert!("hel+o".is_satisfied_by("helo".to_string()));
//!   assert!("hel+o".is_satisfied_by("hellllllllo".to_string()));
//!   assert!("hel+o".is_not_satisfied_by("heo".to_string()));
//! ```
//!
//! ---
//! None or one
//!
//! ```
//!   use regex::regex::SatisfiesRegex;
//!   assert!("hello? world".is_satisfied_by("hello world".to_string()));
//!   assert!("hello? world".is_satisfied_by("hell world".to_string()));
//!   assert!("hello ?world".is_satisfied_by("helloworld".to_string()));
//!   assert!("hello ?world".is_satisfied_by("hello world".to_string()));
//!   assert!("hello ?world".is_not_satisfied_by("hell world".to_string()));
//! ```
//!
//! ---
//! Escaped characters
//!
//! ```
//!   use regex::regex::SatisfiesRegex;
//!   assert!("hello\\? world".is_satisfied_by("hello? world".to_string()));
//!   assert!("hello\\? world".is_not_satisfied_by("hell world".to_string()));
//!   assert!("h.l+.\\? world".is_satisfied_by("hilly? world".to_string()));
//! ```
//!
//! ---
//! Character sets
//!
//! ```
//!   use regex::regex::SatisfiesRegex;
//!   assert!("[a-z ]*".is_satisfied_by("hello world".to_string()));
//!   assert!("[a-z ]*".is_not_satisfied_by("Hello World".to_string()));
//!   assert!("[a-z ]*".is_not_satisfied_by("hell0 world".to_string()));
//!   assert!("[0-9a-z ]*".is_satisfied_by("hell0 world".to_string()));
//!   assert!("[A-Za-z ]*".is_satisfied_by("Hello World".to_string()));
//!   assert!("[WHerdlo ]+".is_satisfied_by("Hello World".to_string()));
//!   assert!("[Hello] [World]".is_satisfied_by("H W".to_string()));
//!   assert!("[Hello] [World]".is_not_satisfied_by("Hello World".to_string()));
//!
//!   // To match none of a character set
//!   assert!("[^A-Za-z ]*".is_satisfied_by("867-5309".to_string()));
//!   assert!("[^A-Z]+".is_satisfied_by("hello world".to_string()));
//!   assert!("[^aeiou]+".is_satisfied_by("hll wrld".to_string()));
//! ```
//!
//! ---
//! Subexpressions
//!
//! ```
//!   use regex::regex::SatisfiesRegex;
//!   assert!("(lu)+-lemon".is_satisfied_by("lulu-lemon".to_string()));
//!   assert!("(na )+batman!".is_satisfied_by(
//!     "na na na na na na na na batman!".to_string()));
//!   assert!("ba([a-z]i[0-9])?tman!".is_satisfied_by("batman!".to_string()));
//!   assert!("ba([a-z]i[0-9])?tman!".is_satisfied_by("baai9tman!".to_string()));
//!   assert!("ba([a-z]i[0-9])?tman!".is_not_satisfied_by("baaitman!".to_string()));
//! ```

use expr::Expression;
use expr::Character;
use tokenizer::parse_string;

fn drop_n<T: Clone>(v: Vec<T>, n: usize) -> Vec<T> {
    v.iter().skip(n).map(|x| x.clone()).collect()
}

fn match_char(c: Character, s: char) -> bool {
    match c {
        Character::Char(c) => s == c,
        Character::Numeral => "0123456789".contains(s),
        Character::Lowercase => "abcdefghijklmnopqrstuvwxyz".contains(s),
        Character::Uppercase => "ABCDEFGHIJKLMNOPQRSTUVWXYZ".contains(s),
    }
}

fn match_expr(e: Expression, _s: Vec<char>) -> bool {
    let mut expr_stack = vec![e];
    let mut s = _s.clone();

    loop {
//        println!("{:?}", (expr_stack.clone(), s.clone()));
//        ::std::thread::sleep(::std::time::Duration::new(1, 0));

        let e = expr_stack.pop().unwrap();

        match e {
            Expression::Char(c) => {
                if s.len() == 0 || !match_char(c, s[0]) {
                    return false
                }
                s = drop_n(s.clone(), 1);
            },

            Expression::Wildcard => {
                if s.len() == 0 {
                    return false;
                }
                s = drop_n(s.clone(), 1);
            },
            
            Expression::None(chars) => {
                // If there are no chars to match, then we can ignore this
                if !chars.is_empty() {
                    // If there are chars to match, then
                    // we have to match at least some character...
                    if s.is_empty() {
                        return false;
                    } else {
                        if chars.iter().any(|c| { match_char(*c, s[0]) }) {
                            return false;
                        }
                        s = drop_n(s.clone(), 1);
                    }
                } 
            },

            Expression::Any(chars) => {
                if !chars.is_empty() {
                    if s.is_empty() {
                        return false;
                    } else {
                        if chars.iter().all(|c| { !match_char(*c, s[0]) }) {
                            return false;
                        }
                        s = drop_n(s.clone(), 1);
                    }
                }
            },

            Expression::All(exprs) => {
                let mut exprs_rev = exprs.clone();
                exprs_rev.reverse();
                for expr in exprs_rev {
                    expr_stack.push(expr.clone());
                }
            },

            Expression::NoneOrMore(expr_box) => {
                if !(s.is_empty()) {
                    // More?
                    let more = {
                        let mut stack = expr_stack.clone();
                        stack.push(Expression::NoneOrMore(expr_box.clone()));
                        stack.push((*expr_box).clone());
                        stack.reverse();
                        match_expr(Expression::All(stack), s.clone())
                    };

                    if more { return true; }

                    let mut stack = expr_stack.clone();
                    stack.reverse();
                    return match_expr(Expression::All(stack), s.clone());
                }
            },

            Expression::OneOrMore(expr_box) => {
                let mut stack = expr_stack.clone();
                stack.push(Expression::NoneOrMore(expr_box.clone()));
                stack.push((*expr_box).clone());
                stack.reverse();
                return match_expr(Expression::All(stack), s.clone());
            },

            Expression::NoneOrOne(expr_box) => {
                // One?
                let one = {
                    let mut stack = expr_stack.clone();
                    stack.push((*expr_box).clone());
                    stack.reverse();
                    match_expr(Expression::All(stack), s.clone())
                };

                if one { return true; }

                // None?
                let mut stack = expr_stack.clone();
                stack.reverse();
                return match_expr(Expression::All(stack), s.clone());
            },
        }
        
        if expr_stack.is_empty() {
            return s.is_empty();
        }
    }
}

pub trait SatisfiesRegex : Sized {
    // Returns None on success and an error otherwise.
    fn is_gracefully_satisfied_by(self, s: String)
                                  -> Option<&'static str>;
    fn is_satisfied_by(self, s: String) -> bool {
        None == self.is_gracefully_satisfied_by(s)
    }

    fn is_not_satisfied_by(self, s: String) -> bool { !self.is_satisfied_by(s) }
}

impl SatisfiesRegex for String {
    fn is_gracefully_satisfied_by(self, s: String)
                                  -> Option<&'static str> {
        let tokens = match parse_string(self) {
            Err(e) => return Some(e),
            Ok(t) => t
        };

        let expr = match Expression::new(tokens) {
            Err(e) => return Some(e),
            Ok(ex) => ex
        };

        if match_expr(expr, s.chars().collect()) {
            None
        } else {
            Some("String does not match regex")
        }
    }
}

impl<'a> SatisfiesRegex for &'a str {
    fn is_gracefully_satisfied_by(self, s: String)
                                  -> Option<&'static str> {
        String::from(self).is_gracefully_satisfied_by(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_can_match_literals() {
        assert!("aaaaa".is_satisfied_by(String::from("aaaaa")));
        assert!("aaaaa".is_not_satisfied_by(String::from("abaaa")));
        assert!("hello".is_satisfied_by(String::from("hello")));
        assert!("it's me".is_satisfied_by(String::from("it's me")));

        // These characters aren't special.
        assert!("!@#$%^&&".is_satisfied_by(String::from("!@#$%^&&")));
        assert!("\\*\\*\\*\\*".is_satisfied_by(String::from("****")));
        assert!("\\*\\*\\*\\*".is_not_satisfied_by(String::from("help")));
    }

    #[test]
    fn it_can_match_wildcards() {
        assert!(".....".is_satisfied_by(String::from("hello")));
        assert!(".....".is_satisfied_by(String::from("great")));
        assert!(".u.e".is_satisfied_by(String::from("puce")));
        assert!(".u.e".is_satisfied_by(String::from("lute")));

        assert!("....".is_not_satisfied_by(String::from("sorry")));
        assert!(".u.e".is_not_satisfied_by(String::from("flute")));
    }

    #[test]
    fn it_can_match_none_or_more() {
        assert!(".*".is_satisfied_by(String::from("everything")));
        assert!(".*".is_satisfied_by(String::from("seriously, everything")));
        assert!(".*".is_satisfied_by(String::from("I can do so many weird things here")));
        assert!(".*".is_satisfied_by(String::from("M4yb3 l33t sp33k?")));
        assert!(".*".is_satisfied_by(String::from("Even the empty string:")));
        assert!(".*".is_satisfied_by(String::from("")));
        assert!(".*".is_satisfied_by(String::from("... wow")));

        // Actually, we should be able to catch the empty string always with char*:
        assert!("a*".is_satisfied_by(String::from("")));
        assert!("\\+*".is_satisfied_by(String::from("")));
        assert!("!*".is_satisfied_by(String::from("")));
        assert!("#*".is_satisfied_by(String::from("")));

        // Maybe we should try a few more::
        assert!("ab*a".is_satisfied_by(String::from("aa")));
        assert!("ab*a".is_satisfied_by(String::from("abba")));
        assert!("ab*a".is_satisfied_by(String::from("aba")));
        assert!("ab*a".is_satisfied_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("ab*".is_satisfied_by(String::from("a")));
        assert!("ab*".is_satisfied_by(String::from("abb")));
        assert!("ab*".is_satisfied_by(String::from("ab")));
        assert!("ab*".is_satisfied_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b*a".is_satisfied_by(String::from("a")));
        assert!("b*a".is_satisfied_by(String::from("bba")));
        assert!("b*a".is_satisfied_by(String::from("ba")));
        assert!("b*a".is_satisfied_by(String::from("bbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("b*a".is_not_satisfied_by(String::from("aa")));
        assert!("b*a".is_not_satisfied_by(String::from("ab")));
        assert!("b*a".is_not_satisfied_by(String::from("bab")));
        assert!("b*a".is_not_satisfied_by(String::from("bbbabbbbbbbbbbbbbbbbbbbbbbbbb")));

        // Only the empty string satisfies this...
        assert!("*".is_satisfied_by(String::from("")));
        assert!("*".is_not_satisfied_by(String::from("a")));
        assert!("*".is_not_satisfied_by(String::from("c")));
        assert!("*".is_not_satisfied_by(String::from("anything else, really")));

        // Just playing with escaped special chars now
        assert!("\\+*".is_satisfied_by(String::from("++++++++++++++++++++++++++")));
        assert!("\\+*".is_satisfied_by(String::from("+")));
        assert!("\\?*".is_satisfied_by(String::from("??????????????????????????")));
        assert!("\\?*".is_satisfied_by(String::from("?")));
        assert!("\\**".is_satisfied_by(String::from("**************************")));
        assert!("\\**".is_satisfied_by(String::from("*")));

        assert!("0-9*".is_satisfied_by(String::from("0-")));
        assert!("0-9*".is_satisfied_by(String::from("0-9")));
        assert!("0-9*".is_satisfied_by(String::from("0-99999999")));
        assert!("0-9*".is_not_satisfied_by(String::from("7")));
    }

    #[test]
    fn it_can_match_one_or_more() {
        assert!(".+".is_satisfied_by(String::from("Basically anything")));
        assert!(".+".is_satisfied_by(String::from("well, not anything")));
        assert!(".+".is_satisfied_by(String::from("anything except (!) for the empty string")));
        assert!(".+".is_not_satisfied_by(String::from("")));
        assert!(".+".is_satisfied_by(String::from("Even single letters count:")));
        assert!(".+".is_satisfied_by(String::from("t")));
        assert!(".+".is_satisfied_by(String::from("See?")));

        assert!("ab+a".is_not_satisfied_by(String::from("aa")));
        assert!("ab+a".is_satisfied_by(String::from("abba")));
        assert!("ab+a".is_satisfied_by(String::from("aba")));
        assert!("ab+a".is_satisfied_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("ab+".is_not_satisfied_by(String::from("a")));
        assert!("ab+".is_satisfied_by(String::from("abb")));
        assert!("ab+".is_satisfied_by(String::from("ab")));
        assert!("ab+".is_satisfied_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b+a".is_not_satisfied_by(String::from("a")));
        assert!("b+a".is_satisfied_by(String::from("bba")));
        assert!("b+a".is_satisfied_by(String::from("ba")));
        assert!("b+a".is_satisfied_by(String::from("bbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("b+a".is_not_satisfied_by(String::from("aa")));
        assert!("b+a".is_not_satisfied_by(String::from("ab")));
        assert!("b+a".is_not_satisfied_by(String::from("bab")));
        assert!("b+a".is_not_satisfied_by(String::from("bbbabbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b+ab++".is_satisfied_by(String::from("bab")));
        assert!("b+ab++".is_satisfied_by(String::from("bbbbbabbb")));
        assert!("b+ab++".is_not_satisfied_by(String::from("bbbbbaabbb")));

        // Only the empty string satisfies this...
        assert!("+".is_satisfied_by(String::from("")));
        assert!("+".is_not_satisfied_by(String::from("a")));
        assert!("+".is_not_satisfied_by(String::from("c")));
        assert!("+".is_not_satisfied_by(String::from("anything else, really")));

        // Just playing with escaped special chars now
        assert!("\\++".is_satisfied_by(String::from("++++++++++++++++++++++++++")));
        assert!("\\++".is_satisfied_by(String::from("+")));

        assert!("0-9+".is_not_satisfied_by(String::from("0-")));
        assert!("0-9+".is_satisfied_by(String::from("0-9")));
        assert!("0-9+".is_satisfied_by(String::from("0-99999999")));
        assert!("0-9+".is_not_satisfied_by(String::from("7")));

        // Let's mix some together
        assert!("o*-9+".is_satisfied_by(String::from("-9")));
        assert!("o*-9+".is_satisfied_by(String::from("-99999999")));
        assert!("o*-9+".is_satisfied_by(String::from("oooooooo-9")));
        assert!("o*-9+".is_satisfied_by(String::from("oooooooo-999999")));
        assert!("o*-9+".is_not_satisfied_by(String::from("o-")));
    }

    #[test]
    fn it_can_match_none_or_one() {
        assert!(".?".is_not_satisfied_by(String::from("words")));
        assert!(".?".is_not_satisfied_by(String::from("not letters")));
        assert!(".?".is_satisfied_by(String::from("")));
        assert!(".?".is_satisfied_by(String::from("a")));
        assert!(".?".is_satisfied_by(String::from("z")));
        assert!(".?".is_satisfied_by(String::from("!")));
        assert!(".?".is_satisfied_by(String::from("+")));

        assert!("ab?a".is_satisfied_by(String::from("aa")));
        assert!("ab?a".is_not_satisfied_by(String::from("abba")));
        assert!("ab?a".is_satisfied_by(String::from("aba")));
        assert!("ab?a".is_not_satisfied_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("ab?".is_satisfied_by(String::from("a")));
        assert!("ab?".is_not_satisfied_by(String::from("abb")));
        assert!("ab?".is_satisfied_by(String::from("ab")));
        assert!("ab?".is_not_satisfied_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b?a".is_satisfied_by(String::from("a")));
        assert!("b?a".is_not_satisfied_by(String::from("bba")));
        assert!("b?a".is_satisfied_by(String::from("ba")));
        assert!("b?a".is_not_satisfied_by(String::from("bbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("b?a".is_not_satisfied_by(String::from("aa")));
        assert!("b?a".is_not_satisfied_by(String::from("ab")));
        assert!("b?a".is_not_satisfied_by(String::from("bab")));
        assert!("b?a".is_not_satisfied_by(String::from("bbbabbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b?ab??".is_satisfied_by(String::from("bab")));
        assert!("b?ab??".is_satisfied_by(String::from("ab")));
        assert!("b?ab??".is_satisfied_by(String::from("ba")));
        assert!("b?ab??".is_satisfied_by(String::from("a")));
        assert!("b?ab??".is_not_satisfied_by(String::from("bbbbbabbb")));
        assert!("b?ab??".is_not_satisfied_by(String::from("bbbbbaabbb")));

        // Only the empty string satisfies this...
        assert!("?".is_satisfied_by(String::from("")));
        assert!("?".is_not_satisfied_by(String::from("a")));
        assert!("?".is_not_satisfied_by(String::from("c")));
        assert!("?".is_not_satisfied_by(String::from("anything else, really")));

        // Just playing with escaped special chars now
        assert!("\\??".is_not_satisfied_by(String::from("??????????????????????????")));
        assert!("\\??".is_satisfied_by(String::from("?")));
        assert!("\\??".is_satisfied_by(String::from("")));

        assert!("0-9?".is_satisfied_by(String::from("0-")));
        assert!("0-9?".is_satisfied_by(String::from("0-9")));
        assert!("0-9?".is_not_satisfied_by(String::from("0-99999999")));
        assert!("0-9?".is_not_satisfied_by(String::from("7")));
        assert!("0-9?".is_not_satisfied_by(String::from("")));

        // Let's mix some together
        assert!("o*-9?".is_satisfied_by(String::from("-9")));
        assert!("o+-9?".is_not_satisfied_by(String::from("o-99999999")));
        assert!("o*-9?".is_satisfied_by(String::from("oooooooo-9")));
        assert!("o*-9?".is_not_satisfied_by(String::from("oooooooo-999999")));
        assert!("o*-9?".is_satisfied_by(String::from("o-")));
    }

    #[test]
    fn matches_anything_in_brackets() {
        // Basics?
        assert!("[]".is_satisfied_by(String::from("")));
        assert!("[]".is_not_satisfied_by(String::from("a")));
        assert!("[a]".is_not_satisfied_by(String::from("")));
        assert!("[a]".is_satisfied_by(String::from("a")));
        assert!("[a]".is_not_satisfied_by(String::from("aa")));
        assert!("a[]".is_not_satisfied_by(String::from("")));
        assert!("a[]".is_satisfied_by(String::from("a")));
        assert!("a[]".is_not_satisfied_by(String::from("aa")));
        assert!("[]a".is_not_satisfied_by(String::from("")));
        assert!("[]a".is_satisfied_by(String::from("a")));
        assert!("[]a".is_not_satisfied_by(String::from("aa")));

        assert!("[a]*".is_satisfied_by(String::from("aa")));
        assert!("[a]*".is_satisfied_by(String::from("")));
        assert!("[a]*".is_satisfied_by(String::from("aaaaaaaaa")));

        assert!("[ab]*".is_satisfied_by(String::from("abaabbbbabaaaab")));
        assert!("[ab]*".is_satisfied_by(String::from("")));
        assert!("[ab]*".is_satisfied_by(String::from("aaaaaaaaaa")));
        assert!("[ab]*".is_satisfied_by(String::from("bbbbbbbbbb")));
        assert!("[ab]*".is_not_satisfied_by(String::from("bbbcbbbbbb")));

        // Check ranges
        assert!("[0-9]*".is_satisfied_by(String::from("8675309")));
        assert!("[ a-z]*".is_satisfied_by(String::from("now i can write things")));
        assert!("[ a-zA-Z]*".is_satisfied_by(String::from("now I can write things")));
        assert!("[ :a-z]+".is_satisfied_by(String::from("alphabet: abcdefghijklmnopqrstuvxyz")));
        assert!("[a-z]*".is_satisfied_by(String::from("")));
        assert!("[a-z+]*".is_satisfied_by(String::from(""))); // Ignore special characters in brackets

        assert!("[ a-z]*".is_not_satisfied_by(String::from("now I can write things")));
        assert!("[a-z]*".is_not_satisfied_by(String::from("8675309")));
        assert!("[a-z]+".is_not_satisfied_by(String::from("")));

        // Malformed regexes never match
        assert!("[[]]".is_not_satisfied_by(String::from("")));
        assert!("[[]a]".is_not_satisfied_by(String::from("abcd")));
        assert!("[[bc]]".is_not_satisfied_by(String::from("Anything??")));
        assert!("[+-]zzzz]".is_not_satisfied_by(String::from("Everything!~!~!")));

        assert!("[aa]".is_satisfied_by(String::from("a")));
        assert!("[aa]".is_not_satisfied_by(String::from("")));

        // We ignore special characters inside...
        assert!("[a?]".is_not_satisfied_by(String::from("")));
        assert!("[a?]".is_satisfied_by(String::from("a")));
        assert!("[a?]".is_satisfied_by(String::from("?")));
    }

    #[test]
    fn inversely_matches_anything_in_brackets() {
        // Basics?
        assert!("[^]".is_satisfied_by(String::from("")));
        assert!("[^]".is_not_satisfied_by(String::from("a")));
        assert!("[^a]".is_not_satisfied_by(String::from("")));
        assert!("[^a]".is_not_satisfied_by(String::from("a")));
        assert!("[^a]".is_not_satisfied_by(String::from("aa")));
        assert!("a[^]".is_not_satisfied_by(String::from("")));
        assert!("a[^]".is_satisfied_by(String::from("a")));
        assert!("a[^]".is_not_satisfied_by(String::from("aa")));
        assert!("[^]a".is_not_satisfied_by(String::from("")));
        assert!("[^]a".is_satisfied_by(String::from("a")));
        assert!("[^]a".is_not_satisfied_by(String::from("aa")));

        assert!("[^a]*".is_not_satisfied_by(String::from("aa")));
        assert!("[^a]*".is_satisfied_by(String::from("")));
        assert!("[^a]*".is_not_satisfied_by(String::from("aaaaaaaaa")));
        assert!("[^a]*".is_satisfied_by(String::from("bbbbbbbbb")));

        assert!("[^ab]*".is_not_satisfied_by(String::from("abaabbbbabaaaab")));
        assert!("[^ab]*".is_satisfied_by(String::from("")));
        assert!("[^ab]*".is_not_satisfied_by(String::from("aaaaaaaaaa")));
        assert!("[^ab]*".is_not_satisfied_by(String::from("bbbbbbbbbb")));
        assert!("[^ab]*".is_not_satisfied_by(String::from("bbbcbbbbbb")));
        assert!("[^ab]*".is_satisfied_by(String::from("cdcdcdcdcdcd")));

        // Check ranges
        assert!("[^0-9]*".is_satisfied_by(String::from("now I can write things")));
        assert!("[^ a-z]*".is_not_satisfied_by(String::from("now i can write things")));
        assert!("[^ a-zA-Z]*".is_satisfied_by(String::from("8675309")));
        assert!("[^ :a-z]+".is_satisfied_by(String::from("ALPHABET")));
        assert!("[^a-z]*".is_satisfied_by(String::from("")));
        assert!("[^a-z+]*".is_satisfied_by(String::from(""))); // Ignore special characters in brackets

        assert!("[^a-z]*".is_satisfied_by(String::from("NOW I CAN WRITE THINGS")));
        assert!("[^a-z]*".is_satisfied_by(String::from("8675309")));
        assert!("[^a-z]+".is_not_satisfied_by(String::from("")));

        // Malformed regexes never match
        assert!("[^[^]]".is_not_satisfied_by(String::from("")));
        assert!("[^[^]a]".is_not_satisfied_by(String::from("abcd")));
        assert!("[^[^bc]]".is_not_satisfied_by(String::from("Anything??")));
        assert!("[^+-]zzzz]".is_not_satisfied_by(String::from("Everything!~!~!")));

        assert!("[^aa]".is_not_satisfied_by(String::from("a")));
        assert!("[^aa]".is_not_satisfied_by(String::from("")));
        assert!("[^aa]".is_satisfied_by(String::from("b")));
        assert!("[^aa]".is_satisfied_by(String::from("~")));

        // We ignore special characters inside...
        assert!("[^a?]".is_not_satisfied_by(String::from("")));
        assert!("[^a?]".is_satisfied_by(String::from("c")));
        assert!("[^a?]".is_not_satisfied_by(String::from("a")));
        assert!("[^a?]".is_not_satisfied_by(String::from("?")));
    }

    #[test]
    fn mildly_complex_queries() {
        assert!("(1[-.]?)?".is_satisfied_by("".to_string()));
        assert!("(1[-.]?)?".is_satisfied_by("1".to_string()));
        assert!("(1[-.]?)?".is_satisfied_by("1-".to_string()));
        assert!("(1[-.]?)?".is_satisfied_by("1.".to_string()));
        assert!("(1[-.]?)?".is_not_satisfied_by("11".to_string()));
    }
}
