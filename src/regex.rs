//! A module for matching against regular expressions.
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
//!   assert!("hello".matches_regex("hello"));
//! ```
//!
//! ---
//! Wildcards
//!
//! ```
//!   use regex::regex::SatisfiesRegex;
//!   assert!("hello".matches_regex("h.ll."));
//!   assert!("hilly".matches_regex("h.ll."));
//! ```
//!
//! ---
//! None or more
//!
//! ```
//!   use regex::regex::IsRegex;
//!   assert!("hello*".is_matched_by("hello"));
//!   assert!("hello*".is_matched_by("hell"));
//!   assert!("hello*".is_matched_by("helloooooooooooooooooooo"));
//!   assert!("h.l*y".is_matched_by("hilllllllllly"));
//!   assert!("h.l*y".is_matched_by("hiy"));
//! ```
//!
//! ---
//! One or more
//!
//! ```
//!   use regex::regex::IsRegex;
//!   assert!("hel+o".is_matched_by("hello"));
//!   assert!("hel+o".is_matched_by("helo"));
//!   assert!("hel+o".is_matched_by("hellllllllo"));
//!   assert!("hel+o".is_not_matched_by("heo"));
//! ```
//!
//! ---
//! None or one
//!
//! ```
//!   use regex::regex::IsRegex;
//!   assert!("hello? world".is_matched_by("hello world"));
//!   assert!("hello? world".is_matched_by("hell world"));
//!   assert!("hello ?world".is_matched_by("helloworld"));
//!   assert!("hello ?world".is_matched_by("hello world"));
//!   assert!("hello ?world".is_not_matched_by("hell world"));
//! ```
//!
//! ---
//! Escaped characters
//!
//! ```
//!   use regex::regex::IsRegex;
//!   assert!("hello\\? world".is_matched_by("hello? world"));
//!   assert!("hello\\? world".is_not_matched_by("hell world"));
//!   assert!("h.l+.\\? world".is_matched_by("hilly? world"));
//! ```
//!
//! ---
//! Character sets
//!
//! ```
//!   use regex::regex::IsRegex;
//!   assert!("[a-z ]*".is_matched_by("hello world"));
//!   assert!("[a-z ]*".is_not_matched_by("Hello World"));
//!   assert!("[a-z ]*".is_not_matched_by("hell0 world"));
//!   assert!("[0-9a-z ]*".is_matched_by("hell0 world"));
//!   assert!("[A-Za-z ]*".is_matched_by("Hello World"));
//!   assert!("[WHerdlo ]+".is_matched_by("Hello World"));
//!   assert!("[Hello] [World]".is_matched_by("H W"));
//!   assert!("[Hello] [World]".is_not_matched_by("Hello World"));
//!
//!   // To match none of a character set
//!   assert!("[^A-Za-z ]*".is_matched_by("867-5309"));
//!   assert!("[^A-Z]+".is_matched_by("hello world"));
//!   assert!("[^aeiou]+".is_matched_by("hll wrld"));
//! ```
//!
//! ---
//! Subexpressions
//!
//! ```
//!   use regex::regex::IsRegex;
//!   assert!("(lu)+-lemon".is_matched_by("lulu-lemon"));
//!   assert!("(na )+batman!".is_matched_by(
//!     "na na na na na na na na batman!"));
//!   assert!("ba([a-z]i[0-9])?tman!".is_matched_by("batman!"));
//!   assert!("ba([a-z]i[0-9])?tman!".is_matched_by("baai9tman!"));
//!   assert!("ba([a-z]i[0-9])?tman!".is_not_matched_by("baaitman!"));
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
            },
        }
        
        if expr_stack.is_empty() {
            return s.is_empty();
        }
    }
}

/// A string is a Regular Expression if it can validate other strings
/// that are tested against it.
pub trait IsRegex<T = Self> : Sized {
    /// Validates a string `s`. If there is an error parsing the regular
    /// expression, then that is returned. If there is no error, then
    /// the function returns `None`:
    ///
    /// ```
    ///   use regex::regex::IsRegex;
    ///   assert_eq!("([)]".is_gracefully_matched_by("hi"),
    ///              Some("Unexpected closing bracket!"));
    ///   assert_eq!("hi".is_gracefully_matched_by("hi"), None);
    /// ```
    fn is_gracefully_matched_by(self, s: T)
                                  -> Option<&'static str>;

    /// This function is the same as `is_gracefully_matched_by` except that
    /// it returns false on malformed regular expressions
    fn is_matched_by(self, s: T) -> bool {
        None == self.is_gracefully_matched_by(s)
    }

    /// This function is the inverse of `is_matched_by`
    fn is_not_matched_by(self, s: T) -> bool { !self.is_matched_by(s) }
}

impl IsRegex for String {
    fn is_gracefully_matched_by(self, s: String)
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

impl<'a, 'b> IsRegex<&'b str> for &'a str {
    fn is_gracefully_matched_by(self, s: &'b str)
                                  -> Option<&'static str> {
        self.to_string().is_gracefully_matched_by(s.to_string())
    }
}

impl<'a> IsRegex<String> for &'a str {
    fn is_gracefully_matched_by(self, s: String)
                                  -> Option<&'static str> {
        String::from(self).is_gracefully_matched_by(s)
    }
}

impl<'a> IsRegex<&'a str> for String {
    fn is_gracefully_matched_by(self, s: &'a str)
                                  -> Option<&'static str> {
        self.is_gracefully_matched_by(s.to_string())
    }
}

/// `SatisfiesRegex` is the inverse trait to `IsRegex` to be used
/// depending on whether or not users like saying "regex matches string"
/// or "string matches regex". This trait is implemented for all implementations
/// of `IsRegex`.
pub trait SatisfiesRegex<T = Self> : Sized
    where T : IsRegex<Self> {
    fn matches_regex(self, regex: T) -> bool { regex.is_matched_by(self) }
}

impl SatisfiesRegex for String { }
impl<'a> SatisfiesRegex<&'a str> for String { }
impl<'a> SatisfiesRegex<String> for &'a str { }
impl<'a, 'b> SatisfiesRegex<&'b str> for &'a str { }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_can_match_literals() {
        assert!("aaaaa".is_matched_by(String::from("aaaaa")));
        assert!("aaaaa".is_not_matched_by(String::from("abaaa")));
        assert!("hello".is_matched_by(String::from("hello")));
        assert!("it's me".is_matched_by(String::from("it's me")));

        // These characters aren't special.
        assert!("!@#$%^&&".is_matched_by(String::from("!@#$%^&&")));
        assert!("\\*\\*\\*\\*".is_matched_by(String::from("****")));
        assert!("\\*\\*\\*\\*".is_not_matched_by(String::from("help")));
    }

    #[test]
    fn it_can_match_wildcards() {
        assert!(".....".is_matched_by(String::from("hello")));
        assert!(".....".is_matched_by(String::from("great")));
        assert!(".u.e".is_matched_by(String::from("puce")));
        assert!(".u.e".is_matched_by(String::from("lute")));

        assert!("....".is_not_matched_by(String::from("sorry")));
        assert!(".u.e".is_not_matched_by(String::from("flute")));
    }

    #[test]
    fn it_can_match_none_or_more() {
        assert!(".*".is_matched_by(String::from("everything")));
        assert!(".*".is_matched_by(String::from("seriously, everything")));
        assert!(".*".is_matched_by(String::from("I can do so many weird things here")));
        assert!(".*".is_matched_by(String::from("M4yb3 l33t sp33k?")));
        assert!(".*".is_matched_by(String::from("Even the empty string:")));
        assert!(".*".is_matched_by(String::from("")));
        assert!(".*".is_matched_by(String::from("... wow")));

        // Actually, we should be able to catch the empty string always with char*:
        assert!("a*".is_matched_by(String::from("")));
        assert!("\\+*".is_matched_by(String::from("")));
        assert!("!*".is_matched_by(String::from("")));
        assert!("#*".is_matched_by(String::from("")));

        // Maybe we should try a few more::
        assert!("ab*a".is_matched_by(String::from("aa")));
        assert!("ab*a".is_matched_by(String::from("abba")));
        assert!("ab*a".is_matched_by(String::from("aba")));
        assert!("ab*a".is_matched_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("ab*".is_matched_by(String::from("a")));
        assert!("ab*".is_matched_by(String::from("abb")));
        assert!("ab*".is_matched_by(String::from("ab")));
        assert!("ab*".is_matched_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b*a".is_matched_by(String::from("a")));
        assert!("b*a".is_matched_by(String::from("bba")));
        assert!("b*a".is_matched_by(String::from("ba")));
        assert!("b*a".is_matched_by(String::from("bbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("b*a".is_not_matched_by(String::from("aa")));
        assert!("b*a".is_not_matched_by(String::from("ab")));
        assert!("b*a".is_not_matched_by(String::from("bab")));
        assert!("b*a".is_not_matched_by(String::from("bbbabbbbbbbbbbbbbbbbbbbbbbbbb")));

        // Only the empty string satisfies this...
        assert!("*".is_matched_by(String::from("")));
        assert!("*".is_not_matched_by(String::from("a")));
        assert!("*".is_not_matched_by(String::from("c")));
        assert!("*".is_not_matched_by(String::from("anything else, really")));

        // Just playing with escaped special chars now
        assert!("\\+*".is_matched_by(String::from("++++++++++++++++++++++++++")));
        assert!("\\+*".is_matched_by(String::from("+")));
        assert!("\\?*".is_matched_by(String::from("??????????????????????????")));
        assert!("\\?*".is_matched_by(String::from("?")));
        assert!("\\**".is_matched_by(String::from("**************************")));
        assert!("\\**".is_matched_by(String::from("*")));

        assert!("0-9*".is_matched_by(String::from("0-")));
        assert!("0-9*".is_matched_by(String::from("0-9")));
        assert!("0-9*".is_matched_by(String::from("0-99999999")));
        assert!("0-9*".is_not_matched_by(String::from("7")));
    }

    #[test]
    fn it_can_match_one_or_more() {
        assert!(".+".is_matched_by(String::from("Basically anything")));
        assert!(".+".is_matched_by(String::from("well, not anything")));
        assert!(".+".is_matched_by(String::from("anything except (!) for the empty string")));
        assert!(".+".is_not_matched_by(String::from("")));
        assert!(".+".is_matched_by(String::from("Even single letters count:")));
        assert!(".+".is_matched_by(String::from("t")));
        assert!(".+".is_matched_by(String::from("See?")));

        assert!("ab+a".is_not_matched_by(String::from("aa")));
        assert!("ab+a".is_matched_by(String::from("abba")));
        assert!("ab+a".is_matched_by(String::from("aba")));
        assert!("ab+a".is_matched_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("ab+".is_not_matched_by(String::from("a")));
        assert!("ab+".is_matched_by(String::from("abb")));
        assert!("ab+".is_matched_by(String::from("ab")));
        assert!("ab+".is_matched_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b+a".is_not_matched_by(String::from("a")));
        assert!("b+a".is_matched_by(String::from("bba")));
        assert!("b+a".is_matched_by(String::from("ba")));
        assert!("b+a".is_matched_by(String::from("bbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("b+a".is_not_matched_by(String::from("aa")));
        assert!("b+a".is_not_matched_by(String::from("ab")));
        assert!("b+a".is_not_matched_by(String::from("bab")));
        assert!("b+a".is_not_matched_by(String::from("bbbabbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b+ab++".is_matched_by(String::from("bab")));
        assert!("b+ab++".is_matched_by(String::from("bbbbbabbb")));
        assert!("b+ab++".is_not_matched_by(String::from("bbbbbaabbb")));

        // Only the empty string satisfies this...
        assert!("+".is_matched_by(String::from("")));
        assert!("+".is_not_matched_by(String::from("a")));
        assert!("+".is_not_matched_by(String::from("c")));
        assert!("+".is_not_matched_by(String::from("anything else, really")));

        // Just playing with escaped special chars now
        assert!("\\++".is_matched_by(String::from("++++++++++++++++++++++++++")));
        assert!("\\++".is_matched_by(String::from("+")));

        assert!("0-9+".is_not_matched_by(String::from("0-")));
        assert!("0-9+".is_matched_by(String::from("0-9")));
        assert!("0-9+".is_matched_by(String::from("0-99999999")));
        assert!("0-9+".is_not_matched_by(String::from("7")));

        // Let's mix some together
        assert!("o*-9+".is_matched_by(String::from("-9")));
        assert!("o*-9+".is_matched_by(String::from("-99999999")));
        assert!("o*-9+".is_matched_by(String::from("oooooooo-9")));
        assert!("o*-9+".is_matched_by(String::from("oooooooo-999999")));
        assert!("o*-9+".is_not_matched_by(String::from("o-")));
    }

    #[test]
    fn it_can_match_none_or_one() {
        assert!(".?".is_not_matched_by(String::from("words")));
        assert!(".?".is_not_matched_by(String::from("not letters")));
        assert!(".?".is_matched_by(String::from("")));
        assert!(".?".is_matched_by(String::from("a")));
        assert!(".?".is_matched_by(String::from("z")));
        assert!(".?".is_matched_by(String::from("!")));
        assert!(".?".is_matched_by(String::from("+")));

        assert!("ab?a".is_matched_by(String::from("aa")));
        assert!("ab?a".is_not_matched_by(String::from("abba")));
        assert!("ab?a".is_matched_by(String::from("aba")));
        assert!("ab?a".is_not_matched_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("ab?".is_matched_by(String::from("a")));
        assert!("ab?".is_not_matched_by(String::from("abb")));
        assert!("ab?".is_matched_by(String::from("ab")));
        assert!("ab?".is_not_matched_by(String::from("abbbbbbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b?a".is_matched_by(String::from("a")));
        assert!("b?a".is_not_matched_by(String::from("bba")));
        assert!("b?a".is_matched_by(String::from("ba")));
        assert!("b?a".is_not_matched_by(String::from("bbbbbbbbbbbbbbbbbbbbbbbbbbbbba")));

        assert!("b?a".is_not_matched_by(String::from("aa")));
        assert!("b?a".is_not_matched_by(String::from("ab")));
        assert!("b?a".is_not_matched_by(String::from("bab")));
        assert!("b?a".is_not_matched_by(String::from("bbbabbbbbbbbbbbbbbbbbbbbbbbbb")));

        assert!("b?ab??".is_matched_by(String::from("bab")));
        assert!("b?ab??".is_matched_by(String::from("ab")));
        assert!("b?ab??".is_matched_by(String::from("ba")));
        assert!("b?ab??".is_matched_by(String::from("a")));
        assert!("b?ab??".is_not_matched_by(String::from("bbbbbabbb")));
        assert!("b?ab??".is_not_matched_by(String::from("bbbbbaabbb")));

        // Only the empty string satisfies this...
        assert!("?".is_matched_by(String::from("")));
        assert!("?".is_not_matched_by(String::from("a")));
        assert!("?".is_not_matched_by(String::from("c")));
        assert!("?".is_not_matched_by(String::from("anything else, really")));

        // Just playing with escaped special chars now
        assert!("\\??".is_not_matched_by(String::from("??????????????????????????")));
        assert!("\\??".is_matched_by(String::from("?")));
        assert!("\\??".is_matched_by(String::from("")));

        assert!("0-9?".is_matched_by(String::from("0-")));
        assert!("0-9?".is_matched_by(String::from("0-9")));
        assert!("0-9?".is_not_matched_by(String::from("0-99999999")));
        assert!("0-9?".is_not_matched_by(String::from("7")));
        assert!("0-9?".is_not_matched_by(String::from("")));

        // Let's mix some together
        assert!("o*-9?".is_matched_by(String::from("-9")));
        assert!("o+-9?".is_not_matched_by(String::from("o-99999999")));
        assert!("o*-9?".is_matched_by(String::from("oooooooo-9")));
        assert!("o*-9?".is_not_matched_by(String::from("oooooooo-999999")));
        assert!("o*-9?".is_matched_by(String::from("o-")));
    }

    #[test]
    fn matches_anything_in_brackets() {
        // Basics?
        assert!("[]".is_matched_by(String::from("")));
        assert!("[]".is_not_matched_by(String::from("a")));
        assert!("[a]".is_not_matched_by(String::from("")));
        assert!("[a]".is_matched_by(String::from("a")));
        assert!("[a]".is_not_matched_by(String::from("aa")));
        assert!("a[]".is_not_matched_by(String::from("")));
        assert!("a[]".is_matched_by(String::from("a")));
        assert!("a[]".is_not_matched_by(String::from("aa")));
        assert!("[]a".is_not_matched_by(String::from("")));
        assert!("[]a".is_matched_by(String::from("a")));
        assert!("[]a".is_not_matched_by(String::from("aa")));

        assert!("[a]*".is_matched_by(String::from("aa")));
        assert!("[a]*".is_matched_by(String::from("")));
        assert!("[a]*".is_matched_by(String::from("aaaaaaaaa")));

        assert!("[ab]*".is_matched_by(String::from("abaabbbbabaaaab")));
        assert!("[ab]*".is_matched_by(String::from("")));
        assert!("[ab]*".is_matched_by(String::from("aaaaaaaaaa")));
        assert!("[ab]*".is_matched_by(String::from("bbbbbbbbbb")));
        assert!("[ab]*".is_not_matched_by(String::from("bbbcbbbbbb")));

        // Check ranges
        assert!("[0-9]*".is_matched_by(String::from("8675309")));
        assert!("[ a-z]*".is_matched_by(String::from("now i can write things")));
        assert!("[ a-zA-Z]*".is_matched_by(String::from("now I can write things")));
        assert!("[ :a-z]+".is_matched_by(String::from("alphabet: abcdefghijklmnopqrstuvxyz")));
        assert!("[a-z]*".is_matched_by(String::from("")));
        assert!("[a-z+]*".is_matched_by(String::from(""))); // Ignore special characters in brackets

        assert!("[ a-z]*".is_not_matched_by(String::from("now I can write things")));
        assert!("[a-z]*".is_not_matched_by(String::from("8675309")));
        assert!("[a-z]+".is_not_matched_by(String::from("")));

        // Malformed regexes never match
        assert!("[[]]".is_not_matched_by(String::from("")));
        assert!("[[]a]".is_not_matched_by(String::from("abcd")));
        assert!("[[bc]]".is_not_matched_by(String::from("Anything??")));
        assert!("[+-]zzzz]".is_not_matched_by(String::from("Everything!~!~!")));

        assert!("[aa]".is_matched_by(String::from("a")));
        assert!("[aa]".is_not_matched_by(String::from("")));

        // We ignore special characters inside...
        assert!("[a?]".is_not_matched_by(String::from("")));
        assert!("[a?]".is_matched_by(String::from("a")));
        assert!("[a?]".is_matched_by(String::from("?")));
    }

    #[test]
    fn inversely_matches_anything_in_brackets() {
        // Basics?
        assert!("[^]".is_matched_by(String::from("")));
        assert!("[^]".is_not_matched_by(String::from("a")));
        assert!("[^a]".is_not_matched_by(String::from("")));
        assert!("[^a]".is_not_matched_by(String::from("a")));
        assert!("[^a]".is_not_matched_by(String::from("aa")));
        assert!("a[^]".is_not_matched_by(String::from("")));
        assert!("a[^]".is_matched_by(String::from("a")));
        assert!("a[^]".is_not_matched_by(String::from("aa")));
        assert!("[^]a".is_not_matched_by(String::from("")));
        assert!("[^]a".is_matched_by(String::from("a")));
        assert!("[^]a".is_not_matched_by(String::from("aa")));

        assert!("[^a]*".is_not_matched_by(String::from("aa")));
        assert!("[^a]*".is_matched_by(String::from("")));
        assert!("[^a]*".is_not_matched_by(String::from("aaaaaaaaa")));
        assert!("[^a]*".is_matched_by(String::from("bbbbbbbbb")));

        assert!("[^ab]*".is_not_matched_by(String::from("abaabbbbabaaaab")));
        assert!("[^ab]*".is_matched_by(String::from("")));
        assert!("[^ab]*".is_not_matched_by(String::from("aaaaaaaaaa")));
        assert!("[^ab]*".is_not_matched_by(String::from("bbbbbbbbbb")));
        assert!("[^ab]*".is_not_matched_by(String::from("bbbcbbbbbb")));
        assert!("[^ab]*".is_matched_by(String::from("cdcdcdcdcdcd")));

        // Check ranges
        assert!("[^0-9]*".is_matched_by(String::from("now I can write things")));
        assert!("[^ a-z]*".is_not_matched_by(String::from("now i can write things")));
        assert!("[^ a-zA-Z]*".is_matched_by(String::from("8675309")));
        assert!("[^ :a-z]+".is_matched_by(String::from("ALPHABET")));
        assert!("[^a-z]*".is_matched_by(String::from("")));
        assert!("[^a-z+]*".is_matched_by(String::from(""))); // Ignore special characters in brackets

        assert!("[^a-z]*".is_matched_by(String::from("NOW I CAN WRITE THINGS")));
        assert!("[^a-z]*".is_matched_by(String::from("8675309")));
        assert!("[^a-z]+".is_not_matched_by(String::from("")));

        // Malformed regexes never match
        assert!("[^[^]]".is_not_matched_by(String::from("")));
        assert!("[^[^]a]".is_not_matched_by(String::from("abcd")));
        assert!("[^[^bc]]".is_not_matched_by(String::from("Anything??")));
        assert!("[^+-]zzzz]".is_not_matched_by(String::from("Everything!~!~!")));

        assert!("[^aa]".is_not_matched_by(String::from("a")));
        assert!("[^aa]".is_not_matched_by(String::from("")));
        assert!("[^aa]".is_matched_by(String::from("b")));
        assert!("[^aa]".is_matched_by(String::from("~")));

        // We ignore special characters inside...
        assert!("[^a?]".is_not_matched_by(String::from("")));
        assert!("[^a?]".is_matched_by(String::from("c")));
        assert!("[^a?]".is_not_matched_by(String::from("a")));
        assert!("[^a?]".is_not_matched_by(String::from("?")));
    }

    #[test]
    fn mildly_complex_queries() {
        assert!("(1[-.]?)?".is_matched_by("".to_string()));
        assert!("(1[-.]?)?".is_matched_by("1".to_string()));
        assert!("(1[-.]?)?".is_matched_by("1-".to_string()));
        assert!("(1[-.]?)?".is_matched_by("1.".to_string()));
        assert!("(1[-.]?)?".is_not_matched_by("11".to_string()));
    }
}
