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

#[derive(Debug, PartialEq, Clone)]
enum ExpectedChar {
    Specific(char),
    Wildcard,
    Any(Vec<Character>),
    None(Vec<Character>)
}

#[derive(Debug, PartialEq, Clone)]
enum State {
    Success,

    // In order to transition to the state indexed, it needs a character
    NeedsCharacter(ExpectedChar, usize),

    // Branches into two states
    Branch(usize, usize)
}

impl State {
    fn branch(id1: usize, id2: usize) -> State {
        State::Branch(id1, id2)
    }

    fn offset(self, off: usize) -> State {
        match self {
            State::Success => self,
            State::NeedsCharacter(c, id) => State::NeedsCharacter(c, id + off),
            State::Branch(id1, id2) => State::Branch(id1 + off, id2 + off)
        }
    }

    // Only performs the offset if the states are greater
    // than or equal to from
    fn offset_from(self, from: usize, off: usize) -> State {
        match self {
            State::Success => self,
            State::NeedsCharacter(c, id) => {
                if id >= from {
                    State::NeedsCharacter(c, id + off)
                } else {
                    State::NeedsCharacter(c, id)
                }
            },

            State::Branch(id1, id2) => {
                let n1 = if id1 >= from { id1 + off } else { id1 };
                let n2 = if id2 >= from { id2 + off } else { id2 };
                State::Branch(n1, n2)
            },
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct NFA {
    states: Vec<State>,
}

impl NFA {
    fn new() -> NFA { NFA { states: vec![State::Success] } }

    fn with_char(c: ExpectedChar) -> NFA {
        NFA { states: vec![ State::Success, State::NeedsCharacter(c, 0) ] }
    }

    fn char_st(c: char) -> NFA { NFA::with_char(ExpectedChar::Specific(c)) }
    fn wildcard() -> NFA { NFA::with_char(ExpectedChar::Wildcard) }
    fn any(chars: Vec<Character>) -> NFA { NFA::with_char(ExpectedChar::Any(chars)) }
    fn none(chars: Vec<Character>) -> NFA { NFA::with_char(ExpectedChar::None(chars)) }

    fn insert(&mut self, at: usize, st: State) {
        self.states.insert(at, st);
        self.states = self.states.iter().enumerate().map(|(i, s)| {
            s.clone().offset_from(if i == at { at } else { at - 1 }, 1)
        }).collect();
    }

    // Places all the exit points of self onto the beginning
    // of other...
    fn concat(self, other: NFA) -> NFA {
        // Invariant: first state should be success state
        assert_eq!(self.states[0], State::Success);
        assert_eq!(other.states[0], State::Success);

        // We concatenate the two vectors together, and then
        // update all references of the second to be += first.len()
        let off = other.states.len() - 1;
        assert!(other.states.len() != 0);

        self.states.iter().fold(other, |nfa, state| {
            let s = state.clone();
            match s {
                State::Success => nfa,
                _ => {
                    let mut new_nfa = nfa.clone();
                    new_nfa.states.push(s.offset(off));
                    new_nfa
                }
            }
        })
    }

    fn remove_branches(&self, st: Vec<usize>) -> Vec<usize> {
        let mut check_states = st.clone();
        let mut checked_states: Vec<usize> = Vec::new();
        let mut branchless_states: Vec<usize> = Vec::new();
        loop {
            let st_idx = {
                match check_states.pop() {
                    None => break,
                    Some(st) => st
                }
            };

            match self.states[st_idx].clone() {
                // We can consider some of these states as "empty"
                State::NeedsCharacter(ExpectedChar::Any(chars), next) => {
                    if chars.is_empty() && !checked_states.contains(&next) {
                        check_states.push(next);
                    } else {
                        branchless_states.push(st_idx);
                    }
                },

                State::NeedsCharacter(ExpectedChar::None(chars), next) => {
                    if chars.is_empty() && !checked_states.contains(&next) {
                        check_states.push(next);
                    } else {
                        branchless_states.push(st_idx);
                    }
                },

                // We don't check for success here, but on the next loop
                // iteration we should know that we can...
                State::Branch(id1, id2) => {
                    if !checked_states.contains(&id1) {
                        check_states.push(id1);
                    }

                    if !checked_states.contains(&id2) {
                        check_states.push(id2);
                    }
                },
                _ => branchless_states.push(st_idx)
            }

            checked_states.push(st_idx);
        }

        branchless_states.dedup();
        branchless_states
    }
}

fn build_nfa (expr: Expression) -> NFA {
    match expr {
        Expression::Char(c) => NFA::char_st(c),
        Expression::Wildcard => NFA::wildcard(),
        Expression::Any(chars) => NFA::any(chars),
        Expression::None(chars) => NFA::none(chars),
        Expression::All(exprs) => exprs.iter().fold(NFA::new(), |nfa, e| {
            nfa.concat(build_nfa(e.clone()))
        }),

        Expression::NoneOrMore(expr) => {
            let mut expr_nfa = build_nfa(*expr);
            let last_state_id = expr_nfa.states.len() - 1;

            // Add the none branch
            expr_nfa.states.push(State::branch(0, last_state_id));

            // Add the more branch
            expr_nfa.insert(1, State::branch(0, last_state_id));

            expr_nfa
        },

        Expression::OneOrMore(expr) => {
            let mut expr_nfa = build_nfa(*expr);
            let last_state_id = expr_nfa.states.len() - 1;

            // Add the more branch
            expr_nfa.insert(1, State::branch(0, last_state_id));
            expr_nfa
        },

        Expression::NoneOrOne(expr) => {
            let mut expr_nfa = build_nfa(*expr);
            let last_state_id = expr_nfa.states.len() - 1;

            // Add the none branch
            expr_nfa.states.push(State::branch(0, last_state_id));

            expr_nfa
        }
    }
}

fn match_char(c: Character, s: char) -> bool {
    match c {
        Character::Specific(c) => s == c,
        Character::Numeral(from, to) => "0123456789"[from..(to + 1)].contains(s),
        Character::Lowercase(from, to) => {
            let fidx = ((from as u8) - ('a' as u8)) as usize;
            let tidx = ((to as u8) - ('a' as u8)) as usize;
            "abcdefghijklmnopqrstuvwxyz"[fidx..(tidx + 1)].contains(s)
        },
        Character::Uppercase(from, to) => {
            let fidx = ((from as u8) - ('A' as u8)) as usize;
            let tidx = ((to as u8) - ('A' as u8)) as usize;
            "ABCDEFGHIJKLMNOPQRSTUVWXYZ"[fidx..(tidx + 1)].contains(s)
        }
    }
}

fn matches_expected(e: ExpectedChar, c: char) -> bool {
    match e {
        ExpectedChar::Specific(s) => s == c,
        ExpectedChar::Wildcard => true,
        ExpectedChar::Any(chars) => chars.iter().any(|ch| match_char(*ch, c)),
        ExpectedChar::None(chars) => !matches_expected(ExpectedChar::Any(chars), c)
    }
}

fn match_nfa (nfa: NFA, s: Vec<char>) -> bool {
    // Our entry point is the last state on the nfa.
    let mut check_states: Vec<usize> = vec![nfa.states.len() - 1];

    // Loop until we run out of characters
    for ch in s {

        // If we're out of states, or we only have the success state, then we fail
        // since there is no character-based transition out of it.
        if check_states.is_empty() ||
            (check_states.len() == 1 && nfa.states[check_states[0]] == State::Success) {
            return false;
        }

        // Resolve branches.
        check_states = nfa.remove_branches(check_states);

        // Go through each state and collect all of the states
        // that we can possibly transition to.
        let mut next_states = Vec::new();

        for st_idx in check_states.clone() {

            match nfa.states[st_idx].clone() {
                // We don't check for success here, but on the next loop
                // iteration we should know that we can...
                State::NeedsCharacter(c, next) => {
                    if matches_expected(c, ch) {
                        next_states.push(next);
                    }
                }
                _ => (),
            }
        }

        // De-duplicate states
        check_states = next_states;
        check_states.dedup();
    }

    // One last branch resolution
    check_states = nfa.remove_branches(check_states);
    
    // If we're at the end of the line with our indices, then
    // we need to see if we've reached the success state during the last
    // iteration through our states...
    check_states.iter().any(|&i| { nfa.states[i] == State::Success } )
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

        if match_nfa(build_nfa(expr), s.chars().collect()) {
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

        assert!("a*a+".is_matched_by("a"));
        assert!("a?a".is_matched_by("a"));
        assert!("a?a".is_matched_by("aa"));
        assert!("a?a".is_not_matched_by("aaa"));
    }

    #[test]
    fn some_group_tests() {
        assert!("()".is_matched_by("".to_string()));
        assert!("()()".is_matched_by("".to_string()));
        assert!("()()?".is_matched_by("".to_string()));
        assert!("()*()?".is_matched_by("".to_string()));
    }
}
