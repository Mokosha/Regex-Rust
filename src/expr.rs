use tokenizer::Token;
use std::boxed::Box;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Character {
    Specific(char),
    Numeral(usize, usize),
    Lowercase(char, char),
    Uppercase(char, char)
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Char(char),
    Wildcard,

    // Any of the expressions will match
    Any(Vec<Character>),

    // Any of the expressions will cause it to fail
    None(Vec<Character>),

    // All of the expressions must match in order
    All(Vec<Expression>),

    // Modifiers:
    NoneOrMore(Box<Expression>),
    OneOrMore(Box<Expression>),
    NoneOrOne(Box<Expression>),
}

impl Expression {
    pub fn with_char(c: char) -> Expression {
        Expression::Char(c)
    }
}

fn token_to_char(t: &Token) -> Character {
    match *t {
        Token::Char(c) => Character::Specific(c),
        Token::Wildcard => Character::Specific('.'),
        Token::NoneOrMore => Character::Specific('*'),
        Token::OneOrMore => Character::Specific('+'),
        Token::NoneOrOne => Character::Specific('?'),
        Token::OpenBracket => Character::Specific('['),
        Token::ClosedBracket => Character::Specific(']'),
        Token::BracketInversion => Character::Specific('^'),
        Token::OpenParen => Character::Specific('('),
        Token::ClosedParen => Character::Specific(')')
    }
}

fn range_from(start: char, end: char) -> Option<Character> {
    // Check for lowercase alphabetic range
    let low_start_off = ((start as u8) as i32) - (('a' as u8) as i32);
    let low_end_off = ((end as u8) as i32) - (('a' as u8) as i32);

    let up_start_off = ((start as u8) as i32) - (('A' as u8) as i32);
    let up_end_off = ((end as u8) as i32) - (('A' as u8) as i32);

    let num_start_off = ((start as u8) as i32) - (('0' as u8) as i32);
    let num_end_off = ((end as u8) as i32) - (('0' as u8) as i32);

    if low_start_off >= 0 && low_start_off <= low_end_off && low_end_off < 26 {
        Some(Character::Lowercase(start, end))
    } else if up_start_off >= 0 && up_start_off <= up_end_off && up_end_off < 26 {
        Some(Character::Uppercase(start, end))
    } else if num_start_off >= 0 && num_start_off <= num_end_off && num_end_off < 10 {
        Some(Character::Numeral(num_start_off as usize, num_end_off as usize))
    } else {
        None
    }
}

fn characters_from(tokens: Vec<Token>) -> Vec<Character> {
    let mut token_stack = tokens.clone();
    let mut chars = Vec::new();
    loop {
        let t = match token_stack.pop() {
            None => break,
            Some(t) => t
        };

        // Check for a range...
        if t == Token::Char('-') {
            let end = match chars.pop() {
                Some(Character::Specific(c)) => c,
                None => {
                    chars.push(Character::Specific('-'));
                    continue
                },
                Some(x) => {
                    chars.push(x);
                    chars.push(Character::Specific('-'));
                    continue
                }
            };

            let start = match token_stack.pop() {
                None => {
                    chars.push(Character::Specific(end));
                    chars.push(Character::Specific('-'));
                    continue
                }
                Some(Token::Char(c)) => c,
                Some(t2) => {
                    chars.push(Character::Specific(end));
                    chars.push(Character::Specific('-'));
                    chars.push(token_to_char(&t2));
                    continue
                }
            };

            match range_from(start, end) {
                None => {
                    chars.push(Character::Specific(end));
                    chars.push(Character::Specific('-'));
                    chars.push(Character::Specific(start));
                },
                Some(c) => chars.push(c)
            }
        } else {
            chars.push(token_to_char(&t));
        }
    }

    // !SPEED! Not necessary but I'm too lazy to rewrite my tests
    chars.reverse();

    chars
}

fn build_expression(tokens: Vec<Token>) -> Result<Expression, &'static str> {
    let mut itr = tokens.iter();

    // We use this as a stack.
    let mut exprs: Vec<Expression> = Vec::new();

    loop {

        // If there are no more tokens, return what we have
        let next_token: Token = match itr.next() {
            None => return Ok(Expression::All(exprs)),
            Some(t) => t.clone()
        };

        // Deal with the next token...
        match next_token {
            Token::Wildcard => exprs.push(Expression::Wildcard),
            Token::NoneOrMore => {
                // Pop the last expression off the stack -- if none
                // exists, ignore this character...
                if let Some(last_expr) = exprs.pop() {
                    if last_expr.is_multiplyable() {
                        exprs.push(Expression::NoneOrMore(
                            Box::new(last_expr)))
                    } else {
                        exprs.push(last_expr); // If not, put it back
                    }
                }
            }

            Token::OneOrMore => {
                // Pop the last expression off the stack -- if none
                // exists, ignore this character...
                if let Some(last_expr) = exprs.pop() {
                    if last_expr.is_multiplyable() {
                        exprs.push(Expression::OneOrMore(
                            Box::new(last_expr)))
                    } else {
                        exprs.push(last_expr); // If not, put it back
                    }
                }
            }

            Token::NoneOrOne => {
                // Pop the last expression off the stack -- if none
                // exists, ignore this character...
                if let Some(last_expr) = exprs.pop() {
                    if last_expr.is_multiplyable() {
                        exprs.push(Expression::NoneOrOne(
                            Box::new(last_expr)))
                    } else {
                        exprs.push(last_expr); // If not, put it back
                    }
                }
            }

            Token::OpenBracket => {
                // Search for a closing bracket -- if none is found,
                // then our regex is malformed and report it as such
                let bracketed: Vec<Token> = itr
                    .clone()
                    .take_while(|&t: &&Token| *t != Token::ClosedBracket)
                    .map(|t: &Token| t.clone())
                    .collect();

                // Advance the iterator past the tokens inside the brackets...
                let mut advanced = itr.clone();
                for _ in 0..(bracketed.len()) { advanced.next(); }

                if let Some(&Token::ClosedBracket) = advanced.next() {
                    // If they begin with an inversion operator, then we want
                    // none-of the sub expressions, otherwise we want any of them...
                    if !bracketed.is_empty() && bracketed[0] == Token::BracketInversion {
                        let btns : Vec<_> = characters_from(bracketed[1..].iter().map(|t| *t).collect());
                        exprs.push(Expression::None(btns))
                    } else {
                        let btns : Vec<_> = characters_from(bracketed);
                        exprs.push(Expression::Any(btns))
                    }
                    itr = advanced;
                } else {
                    exprs.push(Expression::with_char('['));
                }
            },

            Token::OpenParen => {
                // Search for a closing parenthesis -- if none is found,
                // then our regex is malformed
                let mut depth = 1;
                let grouped: Vec<Token> = itr
                    .clone()
                    .take_while(|&t: &&Token| {
                        if *t == Token::ClosedParen {
                            depth -= 1;
                        } else if *t == Token::OpenParen {
                            depth += 1;
                        }
                        depth > 0
                    })
                    .map(|t: &Token| t.clone())
                    .collect();

                // Skip the ones that we grouped together...
                for _ in 0..(grouped.len()) { itr.next(); }

                // Consume the closed parenthesis and keep going
                if let Some(&Token::ClosedParen) = itr.next() {
                    // We're just grouping everything as one expression...
                    exprs.push(try!(build_expression(grouped)))
                } else {
                    return Err("Parenthesis never closed!");
                }
            },

            // We should never encounter a closed parenthesis, bracket inversion, or closed bracket...
            Token::ClosedBracket => return Err("Unexpected closing bracket!"),
            Token::ClosedParen => return Err("Unexpected closing parenthesis!"),

            // This should really never happen
            // !FIXME! Maybe this should panic?
            Token::BracketInversion => return Err("Internal error: Unexpected bracket inversion!"),

            Token::Char(c) => exprs.push(Expression::with_char(c)),
        }
    }
}

impl Expression {
    pub fn new(tokens: Vec<Token>) -> Result<Expression, &'static str> {
        build_expression(tokens)
    }

    // Returns true if the expression can be multiplied by the
    // operators: +, ?, and *
    // Effectively the answer is that they can't be used on each other,
    // so you should place parentheses around something if you want to
    // combine them.
    fn is_multiplyable(&self) -> bool {
        match *self {
            Expression::NoneOrMore(_) => false,
            Expression::OneOrMore(_) => false,
            Expression::NoneOrOne(_) => false,
            _ => true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokenizer::Token;
    use tokenizer::parse_string;

    fn unsafe_parse(s: &str) -> Vec<Token> {
        match parse_string(s.to_string()) {
            Ok(t) => t,
            Err(e) => panic!(e)
        }
    }

    #[test]
    fn it_can_make_an_empty_expr() {
        assert_eq!(Expression::new(unsafe_parse("")).unwrap(),
                   Expression::All(vec![]));
    }

    #[test]
    fn it_can_make_a_simple_expr() {
        assert_eq!(Expression::new(unsafe_parse("hello")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('h'),
                       Expression::with_char('e'),
                       Expression::with_char('l'),
                       Expression::with_char('l'),
                       Expression::with_char('o')]));
    }

    #[test]
    fn it_can_make_a_wildcard_expr() {
        assert_eq!(Expression::new(unsafe_parse("h.llo")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('h'),
                       Expression::Wildcard,
                       Expression::with_char('l'),
                       Expression::with_char('l'),
                       Expression::with_char('o')]));

        assert_eq!(Expression::new(unsafe_parse(".*")).unwrap(),
                   Expression::All(vec![
                       Expression::NoneOrMore(
                           Box::new(Expression::Wildcard))]));
    }

    #[test]
    fn it_can_make_a_multiplying_expr() {
        assert_eq!(Expression::new(unsafe_parse("+ello")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('e'),
                       Expression::with_char('l'),
                       Expression::with_char('l'),
                       Expression::with_char('o')]));

        assert_eq!(Expression::new(unsafe_parse("h?l*o")).unwrap(),
                   Expression::All(vec![
                       Expression::NoneOrOne(
                           Box::new(Expression::with_char('h'))),
                       Expression::NoneOrMore(
                           Box::new(Expression::with_char('l'))),
                       Expression::with_char('o')]));

        assert_eq!(Expression::new(unsafe_parse("h+l++o")).unwrap(),
                   Expression::All(vec![
                       Expression::OneOrMore(
                           Box::new(Expression::with_char('h'))),
                       Expression::OneOrMore(
                           Box::new(Expression::with_char('l'))),
                       Expression::with_char('o')]));

        assert_eq!(Expression::new(unsafe_parse("h+l*+o")).unwrap(),
                   Expression::All(vec![
                       Expression::OneOrMore(
                           Box::new(Expression::with_char('h'))),
                       Expression::NoneOrMore(
                           Box::new(Expression::with_char('l'))),
                       Expression::with_char('o')]));

        assert_eq!(Expression::new(unsafe_parse("+*?+*+*???*+")).unwrap(),
                   Expression::All(vec![]));

        assert_eq!(Expression::new(unsafe_parse("+*?+*+a*???*+")).unwrap(),
                   Expression::All(vec![
                       Expression::NoneOrMore(
                           Box::new(Expression::with_char('a')))]));
    }

    #[test]
    fn it_groups_parenthesized_expressions() {
        assert_eq!(Expression::new(unsafe_parse("()")).unwrap(),
                   Expression::All(vec![
                       Expression::All(vec![])]));

        assert_eq!(Expression::new(unsafe_parse("((((()))))")).unwrap(),
                   Expression::All(vec![
                       Expression::All(vec![
                           Expression::All(vec![
                               Expression::All(vec![
                                   Expression::All(vec![
                                       Expression::All(vec![])])])])])]));

        assert_eq!(Expression::new(unsafe_parse("()()")).unwrap(),
                   Expression::All(vec![
                       Expression::All(vec![]),
                       Expression::All(vec![])]));

        assert!(Expression::new(unsafe_parse(")(")).is_err());
        assert!(Expression::new(unsafe_parse("(")).is_err());
        assert!(Expression::new(unsafe_parse(")")).is_err());
        assert!(Expression::new(unsafe_parse("(()")).is_err());
        assert!(Expression::new(unsafe_parse("()(()")).is_err());
        assert!(Expression::new(unsafe_parse(")()")).is_err());

        assert_eq!(Expression::new(unsafe_parse("(\\)\\()")).unwrap(),
                   Expression::All(vec![
                       Expression::All(vec![
                           Expression::with_char(')'),
                           Expression::with_char('(')])]));

        assert_eq!(Expression::new(unsafe_parse("a(\\)\\()b")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('a'),
                       Expression::All(vec![
                           Expression::with_char(')'),
                           Expression::with_char('(')]),
                       Expression::with_char('b')]));
    }

    #[test]
    fn it_prevents_non_bracket_range_exprs() {
        assert_eq!(Expression::new(unsafe_parse("ea-zlo")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('e'),
                       Expression::with_char('a'),
                       Expression::with_char('-'),
                       Expression::with_char('z'),
                       Expression::with_char('l'),
                       Expression::with_char('o')]));

        assert_eq!(Expression::new(unsafe_parse("a-Zo")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('a'),
                       Expression::with_char('-'),
                       Expression::with_char('Z'),
                       Expression::with_char('o')]));

        assert_eq!(Expression::new(unsafe_parse("0-9(A-Z)lo")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('0'),
                       Expression::with_char('-'),
                       Expression::with_char('9'),
                       Expression::All(vec![
                           Expression::with_char('A'),
                           Expression::with_char('-'),
                           Expression::with_char('Z')]),
                       Expression::with_char('l'),
                       Expression::with_char('o')]));

        assert_eq!(Expression::new(unsafe_parse("0-9")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('0'),
                       Expression::with_char('-'),
                       Expression::with_char('9')]));
    }

    #[test]
    fn it_allows_bracket_exprs() {
        assert_eq!(Expression::new(unsafe_parse("[0-9]")).unwrap(),
                   Expression::All(vec![
                       Expression::Any(vec![Character::Numeral(0, 9)])]));

        assert_eq!(Expression::new(unsafe_parse("[0-9a-z]")).unwrap(),
                   Expression::All(vec![
                       Expression::Any(vec![
                           Character::Numeral(0, 9),
                           Character::Lowercase('a', 'z')])]));

        assert_eq!(Expression::new(unsafe_parse("[^abc]")).unwrap(),
                   Expression::All(vec![
                       Expression::None(vec![
                           Character::Specific('a'),
                           Character::Specific('b'),
                           Character::Specific('c')])]));

        // Don't worry about duplicates in brackets, they are
        // redundant and serve no functional difference.
        assert_eq!(Expression::new(unsafe_parse("[lol]")).unwrap(),
                   Expression::All(vec![
                       Expression::Any(vec![
                           Character::Specific('l'),
                           Character::Specific('o'),
                           Character::Specific('l')])]));

        // Multipliers in brackets make no sense, but they aren't
        // ambiguous so we can just ignore them.
        assert_eq!(Expression::new(unsafe_parse("[l+ol*]")).unwrap(),
                   Expression::All(vec![
                       Expression::Any(vec![
                           Character::Specific('l'),
                           Character::Specific('+'),
                           Character::Specific('o'),
                           Character::Specific('l'),
                           Character::Specific('*')])]));

        assert_eq!(Expression::new(unsafe_parse("(.[(0-9)])")).unwrap(),
                   Expression::All(vec![
                       Expression::All(vec![
                           Expression::Wildcard,
                           Expression::Any(vec![
                               Character::Specific('('),
                               Character::Numeral(0, 9),
                               Character::Specific(')')])])]));
    }

    #[test]
    fn it_properly_checks_for_nested_brackets() {
        assert!(Expression::new(unsafe_parse("[[lol]]")).is_err());
        assert!(Expression::new(unsafe_parse("[lo[l]]")).is_err());
        assert!(Expression::new(unsafe_parse("([)]")).is_err());
        assert!(Expression::new(unsafe_parse("(.[0-9)]")).is_err());
    }

    #[test]
    fn it_allows_mixed_parentheses_and_brackets() {
        assert_eq!(Expression::new(unsafe_parse("()[]")).unwrap(),
                   Expression::All(vec![
                       Expression::All(vec![]),
                       Expression::Any(vec![])]));

        assert_eq!(Expression::new(unsafe_parse("[]()")).unwrap(),
                   Expression::All(vec![
                       Expression::Any(vec![]),
                       Expression::All(vec![])]));

        assert_eq!(Expression::new(unsafe_parse("l[(o)]l")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('l'),
                       Expression::Any(vec![
                           Character::Specific('('),
                           Character::Specific('o'),
                           Character::Specific(')')]),
                       Expression::with_char('l')]));

        assert_eq!(Expression::new(unsafe_parse("l[0-9(o)]l")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('l'),
                       Expression::Any(vec![
                           Character::Numeral(0, 9),
                           Character::Specific('('),
                           Character::Specific('o'),
                           Character::Specific(')')]),
                       Expression::with_char('l')]));

        assert_eq!(Expression::new(unsafe_parse("l[^0-9(o)]l")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('l'),
                       Expression::None(vec![
                           Character::Numeral(0, 9),
                           Character::Specific('('),
                           Character::Specific('o'),
                           Character::Specific(')')]),
                       Expression::with_char('l')]));

        assert_eq!(Expression::new(unsafe_parse("l[0-9^(o)](.)")).unwrap(),
                   Expression::All(vec![
                       Expression::with_char('l'),
                       Expression::Any(vec![
                           Character::Numeral(0, 9),
                           Character::Specific('^'),
                           Character::Specific('('),
                           Character::Specific('o'),
                           Character::Specific(')')]),
                       Expression::All(vec![
                           Expression::Wildcard])]));
    }
}
