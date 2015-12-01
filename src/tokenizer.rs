// tokenizer.rs
// The tokenizer takes an incoming string and constructs a list of tokens
// for the string. The tokens are used to give logical structure so that
// we can parse a bit better.

// A Token is any character in the regular expression that may have a special
// meaning. If it doesn't, then it gets parsed as a char.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Token {
    Char(char),
    Wildcard,
    NoneOrMore,
    OneOrMore,
    NoneOrOne,
    NumeralRange,
    LowercaseRange,
    UppercaseRange,
    OpenBracket,
    ClosedBracket,
    BracketInversion,
    OpenParen,
    ClosedParen,
}

pub fn parse_string(s: String) -> Result<Vec<Token>, &'static str> {
    let mut iter = s.chars();
    let mut tokens : Vec<Token> = Vec::new();
    loop {
        let next_char = iter.next();
        if next_char.is_none() {
            break;
        }

        let token = match next_char.unwrap() {
            '.' => Token::Wildcard,
            '*' => Token::NoneOrMore,
            '+' => Token::OneOrMore,
            '?' => Token::NoneOrOne,
            '\\' => {
                if let Some(c) = iter.next() {
                    Token::Char(c)
                } else {
                    return Err("Parse error: Escaped character escapes nothing");
                }
            },
            '[' => Token::OpenBracket,
            ']' => Token::ClosedBracket,
            '(' => Token::OpenParen,
            ')' => Token::ClosedParen,
            '0' => {
                let next_chars: Vec<char> = iter.clone().take(2).collect();
                if next_chars == vec!['-', '9'] {
                    iter.next();
                    iter.next();
                    Token::NumeralRange
                } else {
                    Token::Char('0')
                }
            }

            'a' => {
                let next_chars: Vec<char> = iter.clone().take(2).collect();
                if next_chars == vec!['-', 'z'] {
                    iter.next();
                    iter.next();
                    Token::LowercaseRange
                } else {
                    Token::Char('a')
                }
            }

            'A' => {
                let next_chars: Vec<char> = iter.clone().take(2).collect();
                if next_chars == vec!['-', 'Z'] {
                    iter.next();
                    iter.next();
                    Token::UppercaseRange
                } else {
                    Token::Char('A')
                }
            }

            c => {
                tokens.last().map_or_else(|| Token::Char(c), |last_token| {
                    if *last_token == Token::OpenBracket && c == '^' {
                        Token::BracketInversion
                    } else {
                        Token::Char(c)
                    }
                })
            }
        };

        tokens.push(token);
    }

    // Return the tokens
    Ok(tokens)
}

pub fn parse(s: &str) -> Result<Vec<Token>, &'static str> {
    parse_string(s.to_string())
}

pub fn unsafe_parse(s: &str) -> Vec<Token> {
    match parse(s) {
        Err(s) => panic!(s),
        Ok(t) => t
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_can_parse_empty_strings() {
        assert_eq!(parse(""), Ok(vec![]));
    }

    #[test]
    fn it_can_parse_simple_strings() {
        assert_eq!(parse("hello"),
                   Ok(vec![Token::Char('h'),
                           Token::Char('e'),
                           Token::Char('l'),
                           Token::Char('l'),
                           Token::Char('o')]));
    }

    #[test]
    fn it_can_recognize_wildcards() {
        assert_eq!(parse("he.lo"),
                   Ok(vec![Token::Char('h'),
                           Token::Char('e'),
                           Token::Wildcard,
                           Token::Char('l'),
                           Token::Char('o')]));

        assert_eq!(parse(".e.lo"),
                   Ok(vec![Token::Wildcard,
                           Token::Char('e'),
                           Token::Wildcard,
                           Token::Char('l'),
                           Token::Char('o')]));

        assert_eq!(parse("."), Ok(vec![Token::Wildcard]));
    }

    #[test]
    fn it_can_recognize_stars() {
        assert_eq!(parse("he*lo"),
                   Ok(vec![Token::Char('h'),
                           Token::Char('e'),
                           Token::NoneOrMore,
                           Token::Char('l'),
                           Token::Char('o')]));

        assert_eq!(parse(".e*lo"),
                   Ok(vec![Token::Wildcard,
                           Token::Char('e'),
                           Token::NoneOrMore,
                           Token::Char('l'),
                           Token::Char('o')]));

        assert_eq!(parse(".*"), Ok(vec![Token::Wildcard,
                                                      Token::NoneOrMore]));
    }

    #[test]
    fn it_can_recognize_pluses() {
        assert_eq!(parse("he+lo"),
                   Ok(vec![Token::Char('h'),
                           Token::Char('e'),
                           Token::OneOrMore,
                           Token::Char('l'),
                           Token::Char('o')]));

        assert_eq!(parse("*e+lo"),
                   Ok(vec![Token::NoneOrMore,
                           Token::Char('e'),
                           Token::OneOrMore,
                           Token::Char('l'),
                           Token::Char('o')]));

        assert_eq!(parse(".+"), Ok(vec![Token::Wildcard,
                                                      Token::OneOrMore]));

        // These aren't valid expressions, but they are valid syntax...
        assert_eq!(parse("*+*"), Ok(vec![Token::NoneOrMore,
                                                       Token::OneOrMore,
                                                       Token::NoneOrMore]));
    }

    #[test]
    fn it_can_recognize_qmarks() {
        assert_eq!(parse("?????"),
                   Ok(vec![Token::NoneOrOne,
                           Token::NoneOrOne,
                           Token::NoneOrOne,
                           Token::NoneOrOne,
                           Token::NoneOrOne]));

        assert_eq!(parse("-?"),
                   Ok(vec![Token::Char('-'),
                           Token::NoneOrOne]));

        assert_eq!(parse("hello? it's me."),
                   Ok(vec![Token::Char('h'),
                           Token::Char('e'),
                           Token::Char('l'),
                           Token::Char('l'),
                           Token::Char('o'),
                           Token::NoneOrOne,
                           Token::Char(' '),
                           Token::Char('i'),
                           Token::Char('t'),
                           Token::Char('\''),
                           Token::Char('s'),
                           Token::Char(' '),
                           Token::Char('m'),
                           Token::Char('e'),
                           Token::Wildcard]));
    }

    #[test]
    fn it_can_escape_characters() {
        assert_eq!(parse("\\?\\.\\+\\*\\a"),
                   Ok(vec![Token::Char('?'),
                           Token::Char('.'),
                           Token::Char('+'),
                           Token::Char('*'),
                           Token::Char('a')]));

        assert_eq!(parse("\\\""),
                   Ok(vec![Token::Char('\"')]));        
    }

    #[test]
    fn it_fails_if_escape_is_at_end_of_string() {
        assert!(parse("\\").is_err());
        assert!(parse("hello\\").is_err());
        assert!(!parse("hel\\lo").is_err());
    }

    #[test]
    fn it_recognizes_numeral_ranges() {
        assert_eq!(parse("0123456789"),
                   Ok(vec![Token::Char('0'),
                           Token::Char('1'),
                           Token::Char('2'),
                           Token::Char('3'),
                           Token::Char('4'),
                           Token::Char('5'),
                           Token::Char('6'),
                           Token::Char('7'),
                           Token::Char('8'),
                           Token::Char('9')]));

        assert_eq!(parse("0-10-20-9"),
                   Ok(vec![Token::Char('0'),
                           Token::Char('-'),
                           Token::Char('1'),
                           Token::Char('0'),
                           Token::Char('-'),
                           Token::Char('2'),
                           Token::NumeralRange]));
                                   
        assert_eq!(parse("9-0-9"),
                   Ok(vec![Token::Char('9'),
                           Token::Char('-'),
                           Token::NumeralRange]));
    }

    #[test]
    fn it_recognizes_lowercase_ranges() {
        assert_eq!(parse("az"),
                   Ok(vec![Token::Char('a'),
                           Token::Char('z')]));

        assert_eq!(parse("0-9a-z"),
                   Ok(vec![Token::NumeralRange,
                           Token::LowercaseRange]));

        assert_eq!(parse("a-z0-9"),
                   Ok(vec![Token::LowercaseRange,
                           Token::NumeralRange]));

        assert_eq!(parse("z-a-z"),
                   Ok(vec![Token::Char('z'),
                           Token::Char('-'),
                           Token::LowercaseRange]));
    }

    #[test]
    fn it_recognizes_uppercase_ranges() {
        assert_eq!(parse("AZ"),
                   Ok(vec![Token::Char('A'),
                           Token::Char('Z')]));

        assert_eq!(parse("0-9a-Z"),
                   Ok(vec![Token::NumeralRange,
                           Token::Char('a'),
                           Token::Char('-'),
                           Token::Char('Z')]));

        assert_eq!(parse("A-Za-z0-9"),
                   Ok(vec![Token::UppercaseRange,
                           Token::LowercaseRange,
                           Token::NumeralRange]));

        assert_eq!(parse("z-A\\-Z"),
                   Ok(vec![Token::Char('z'),
                           Token::Char('-'),
                           Token::Char('A'),
                           Token::Char('-'),
                           Token::Char('Z')]));

        assert_eq!(parse("z-A-Z"),
                   Ok(vec![Token::Char('z'),
                           Token::Char('-'),
                           Token::UppercaseRange]));
    }

    #[test]
    fn it_recognizes_brackets() {
        assert_eq!(parse("["),
                   Ok(vec![Token::OpenBracket]));

        assert_eq!(parse("]["),
                   Ok(vec![Token::ClosedBracket,
                           Token::OpenBracket]));

        assert_eq!(parse("[]"),
                   Ok(vec![Token::OpenBracket,
                           Token::ClosedBracket]));

        assert_eq!(parse("[0-9]"),
                   Ok(vec![Token::OpenBracket,
                           Token::NumeralRange,
                           Token::ClosedBracket]));
    }

    #[test]
    fn it_properly_handles_bracket_inversion() {
        assert_eq!(parse("[^"),
                   Ok(vec![Token::OpenBracket,
                           Token::BracketInversion]));

        assert_eq!(parse("]^["),
                   Ok(vec![Token::ClosedBracket,
                           Token::Char('^'),
                           Token::OpenBracket]));

        assert_eq!(parse("^[^]^"),
                   Ok(vec![Token::Char('^'),
                           Token::OpenBracket,
                           Token::BracketInversion,
                           Token::ClosedBracket,
                           Token::Char('^')]));

        assert_eq!(parse("[^0-9]"),
                   Ok(vec![Token::OpenBracket,
                           Token::BracketInversion,
                           Token::NumeralRange,
                           Token::ClosedBracket]));

        assert_eq!(parse("[0^-9]"),
                   Ok(vec![Token::OpenBracket,
                           Token::Char('0'),
                           Token::Char('^'),
                           Token::Char('-'),
                           Token::Char('9'),
                           Token::ClosedBracket]));

        assert_eq!(parse("[0-9^]"),
                   Ok(vec![Token::OpenBracket,
                           Token::NumeralRange,
                           Token::Char('^'),
                           Token::ClosedBracket]));

        assert_eq!(parse("[\\^-9]"),
                   Ok(vec![Token::OpenBracket,
                           Token::Char('^'),
                           Token::Char('-'),
                           Token::Char('9'),
                           Token::ClosedBracket]));

        assert_eq!(parse("^[-9]"),
                   Ok(vec![Token::Char('^'),
                           Token::OpenBracket,
                           Token::Char('-'),
                           Token::Char('9'),
                           Token::ClosedBracket]));
    }

    #[test]
    fn it_recognizes_parentheses() {
        assert_eq!(parse("("),
                   Ok(vec!(Token::OpenParen)));

        assert_eq!(parse(")("),
                   Ok(vec!(Token::ClosedParen,
                           Token::OpenParen)));

        assert_eq!(parse("()"),
                   Ok(vec!(Token::OpenParen,
                           Token::ClosedParen)));

        assert_eq!(parse("(0-9)"),
                   Ok(vec!(Token::OpenParen,
                           Token::NumeralRange,
                           Token::ClosedParen)));
    }
}
