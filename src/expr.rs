use tokenizer::Token;
use std::boxed::Box;

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Char(char),
    Numeral,
    Lowercase,
    Uppercase,
    Wildcard,

    // Any of the expressions will match
    Any(Vec<Expression>),

    // Any of the expressions will cause it to fail
    None(Vec<Expression>),

    // All of the expressions must match in order
    All(Vec<Expression>),

    // Modifiers:
    NoneOrMore(Box<Expression>),
    OneOrMore(Box<Expression>),
    NoneOrOne(Box<Expression>),
}

fn build_expression(tokens: Vec<Token>, within_brackets: bool,
                    allow_brackets: bool) -> Result<Expression, &'static str> {
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
            Token::Wildcard => if within_brackets {
                exprs.push(Expression::Char('.'));
            } else {
                exprs.push(Expression::Wildcard);
            },
            Token::NoneOrMore => {
                // Pop the last expression off the stack -- if none
                // exists, ignore this character...
                if within_brackets {
                    exprs.push(Expression::Char('*'));
                } else {
                    if let Some(last_expr) = exprs.pop() {
                        if last_expr.is_multiplyable() {
                            exprs.push(Expression::NoneOrMore(
                                Box::new(last_expr)))
                        } else {
                            exprs.push(last_expr); // If not, put it back
                        }
                    }
                }
            }

            Token::OneOrMore => {
                if within_brackets {
                    exprs.push(Expression::Char('+'));
                } else {
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
            }

            Token::NoneOrOne => {
                if within_brackets {
                    exprs.push(Expression::Char('?'));
                } else {
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
            }

            Token::NumeralRange => {
                if within_brackets {
                    exprs.push(Expression::Numeral);
                } else {
                    exprs.push(Expression::Char('0'));
                    exprs.push(Expression::Char('-'));
                    exprs.push(Expression::Char('9'));
                }
            },

            Token::LowercaseRange => {
                if within_brackets {
                    exprs.push(Expression::Lowercase);
                } else {
                    exprs.push(Expression::Char('a'));
                    exprs.push(Expression::Char('-'));
                    exprs.push(Expression::Char('z'));
                }
            },

            Token::UppercaseRange => {
                if within_brackets {
                    exprs.push(Expression::Uppercase);
                } else {
                    exprs.push(Expression::Char('A'));
                    exprs.push(Expression::Char('-'));
                    exprs.push(Expression::Char('Z'));
                }
            },

            Token::OpenBracket => {
                if !allow_brackets {
                    return Err("Nested brackets!");
                }

                // Search for a closing bracket -- if none is found,
                // then our regex is malformed and report it as such
                let bracketed: Vec<Token> = itr
                    .clone()
                    .take_while(|&t: &&Token| *t != Token::ClosedBracket)
                    .map(|t: &Token| t.clone())
                    .collect();

                // Advance the iterator past the tokens inside the brackets...
                for _ in 0..(bracketed.len()) { itr.next(); }

                if let Some(&Token::ClosedBracket) = itr.next() {
                    // If they begin with an inversion operator, then we want
                    // none-of the sub expressions, otherwise we want any of them...
                    if !bracketed.is_empty() && bracketed[0] == Token::BracketInversion {
                        let btns = bracketed[1..].to_vec();
                        match build_expression(btns, true, false) {
                            Err(s) => return Err(s),
                            Ok(Expression::All(e)) => exprs.push(Expression::None(e)),
                            Ok(e) => exprs.push(Expression::None(vec![e]))
                        }
                    } else {
                        match build_expression(bracketed, true, false) {
                            Err(s) => return Err(s),
                            Ok(Expression::All(e)) => exprs.push(Expression::Any(e)),
                            Ok(e) => exprs.push(Expression::Any(vec![e]))
                        }
                    }
                } else {
                    return Err("Bracket never closed!");
                }
            }

            Token::OpenParen => {
                if within_brackets {
                    exprs.push(Expression::Char('('));
                } else {
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
                        let e = try!(build_expression(grouped, false, allow_brackets));
                        exprs.push(e)
                    } else {
                        return Err("Parenthesis never closed!");
                    }
                }
            }

            // We should never encounter a closed parenthesis, bracket inversion, or closed bracket...
            Token::ClosedBracket => return Err("Unexpected closing bracket!"),
            Token::ClosedParen => if within_brackets {
                exprs.push(Expression::Char(')'));
            } else {
                return Err("Unexpected closing parenthesis!")
            },

            // This should really never happen
            // !FIXME! Maybe this should panic?
            Token::BracketInversion => return Err("Internal error: Unexpected bracket inversion!"),

            Token::Char(c) => exprs.push(Expression::Char(c)),
        }
    }
}

impl Expression {
    pub fn new(tokens: Vec<Token>) -> Result<Expression, &'static str> {
        build_expression(tokens, false, true)
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
                       Expression::Char('h'),
                       Expression::Char('e'),
                       Expression::Char('l'),
                       Expression::Char('l'),
                       Expression::Char('o')]));
    }

    #[test]
    fn it_can_make_a_wildcard_expr() {
        assert_eq!(Expression::new(unsafe_parse("h.llo")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('h'),
                       Expression::Wildcard,
                       Expression::Char('l'),
                       Expression::Char('l'),
                       Expression::Char('o')]));

        assert_eq!(Expression::new(unsafe_parse(".*")).unwrap(),
                   Expression::All(vec![
                       Expression::NoneOrMore(
                           Box::new(Expression::Wildcard))]));
    }

    #[test]
    fn it_can_make_a_multiplying_expr() {
        assert_eq!(Expression::new(unsafe_parse("+ello")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('e'),
                       Expression::Char('l'),
                       Expression::Char('l'),
                       Expression::Char('o')]));

        assert_eq!(Expression::new(unsafe_parse("h?l*o")).unwrap(),
                   Expression::All(vec![
                       Expression::NoneOrOne(
                           Box::new(Expression::Char('h'))),
                       Expression::NoneOrMore(
                           Box::new(Expression::Char('l'))),
                       Expression::Char('o')]));

        assert_eq!(Expression::new(unsafe_parse("h+l++o")).unwrap(),
                   Expression::All(vec![
                       Expression::OneOrMore(
                           Box::new(Expression::Char('h'))),
                       Expression::OneOrMore(
                           Box::new(Expression::Char('l'))),
                       Expression::Char('o')]));

        assert_eq!(Expression::new(unsafe_parse("h+l*+o")).unwrap(),
                   Expression::All(vec![
                       Expression::OneOrMore(
                           Box::new(Expression::Char('h'))),
                       Expression::NoneOrMore(
                           Box::new(Expression::Char('l'))),
                       Expression::Char('o')]));

        assert_eq!(Expression::new(unsafe_parse("+*?+*+*???*+")).unwrap(),
                   Expression::All(vec![]));

        assert_eq!(Expression::new(unsafe_parse("+*?+*+a*???*+")).unwrap(),
                   Expression::All(vec![
                       Expression::NoneOrMore(
                           Box::new(Expression::Char('a')))]));
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
                           Expression::Char(')'),
                           Expression::Char('(')])]));

        assert_eq!(Expression::new(unsafe_parse("a(\\)\\()b")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('a'),
                       Expression::All(vec![
                           Expression::Char(')'),
                           Expression::Char('(')]),
                       Expression::Char('b')]));
    }

    #[test]
    fn it_prevents_non_bracket_range_exprs() {
        assert_eq!(Expression::new(unsafe_parse("ea-zlo")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('e'),
                       Expression::Char('a'),
                       Expression::Char('-'),
                       Expression::Char('z'),
                       Expression::Char('l'),
                       Expression::Char('o')]));

        assert_eq!(Expression::new(unsafe_parse("a-Zo")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('a'),
                       Expression::Char('-'),
                       Expression::Char('Z'),
                       Expression::Char('o')]));

        assert_eq!(Expression::new(unsafe_parse("0-9(A-Z)lo")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('0'),
                       Expression::Char('-'),
                       Expression::Char('9'),
                       Expression::All(vec![
                           Expression::Char('A'),
                           Expression::Char('-'),
                           Expression::Char('Z')]),
                       Expression::Char('l'),
                       Expression::Char('o')]));

        assert_eq!(Expression::new(unsafe_parse("0-9")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('0'),
                       Expression::Char('-'),
                       Expression::Char('9')]));
    }

    #[test]
    fn it_allows_bracket_exprs() {
        assert_eq!(Expression::new(unsafe_parse("[0-9]")).unwrap(),
                   Expression::All(vec![
                       Expression::Any(vec![Expression::Numeral])]));

        assert_eq!(Expression::new(unsafe_parse("[0-9a-z]")).unwrap(),
                   Expression::All(vec![
                       Expression::Any(vec![
                           Expression::Numeral,
                           Expression::Lowercase])]));

        assert_eq!(Expression::new(unsafe_parse("[^abc]")).unwrap(),
                   Expression::All(vec![
                       Expression::None(vec![
                           Expression::Char('a'),
                           Expression::Char('b'),
                           Expression::Char('c')])]));

        // Don't worry about duplicates in brackets, they are
        // redundant and serve no functional difference.
        assert_eq!(Expression::new(unsafe_parse("[lol]")).unwrap(),
                   Expression::All(vec![
                       Expression::Any(vec![
                           Expression::Char('l'),
                           Expression::Char('o'),
                           Expression::Char('l')])]));

        // Multipliers in brackets make no sense, but they aren't
        // ambiguous so we can just ignore them.
        assert_eq!(Expression::new(unsafe_parse("[l+ol*]")).unwrap(),
                   Expression::All(vec![
                       Expression::Any(vec![
                           Expression::Char('l'),
                           Expression::Char('+'),
                           Expression::Char('o'),
                           Expression::Char('l'),
                           Expression::Char('*')])]));

        assert_eq!(Expression::new(unsafe_parse("(.[(0-9)])")).unwrap(),
                   Expression::All(vec![
                       Expression::All(vec![
                           Expression::Wildcard,
                           Expression::Any(vec![
                               Expression::Char('('),
                               Expression::Numeral,
                               Expression::Char(')')])])]));
    }

    #[test]
    fn it_properly_checks_for_nested_brackets() {
        // Multipliers in brackets make no sense, but they aren't
        // ambiguous so we can just ignore them.
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
                       Expression::Char('l'),
                       Expression::Any(vec![
                           Expression::Char('('),
                           Expression::Char('o'),
                           Expression::Char(')')]),
                       Expression::Char('l')]));

        assert_eq!(Expression::new(unsafe_parse("l[0-9(o)]l")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('l'),
                       Expression::Any(vec![
                           Expression::Numeral,
                           Expression::Char('('),
                           Expression::Char('o'),
                           Expression::Char(')')]),
                       Expression::Char('l')]));

        assert_eq!(Expression::new(unsafe_parse("l[^0-9(o)]l")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('l'),
                       Expression::None(vec![
                           Expression::Numeral,
                           Expression::Char('('),
                           Expression::Char('o'),
                           Expression::Char(')')]),
                       Expression::Char('l')]));

        assert_eq!(Expression::new(unsafe_parse("l[0-9^(o)](.)")).unwrap(),
                   Expression::All(vec![
                       Expression::Char('l'),
                       Expression::Any(vec![
                           Expression::Numeral,
                           Expression::Char('^'),
                           Expression::Char('('),
                           Expression::Char('o'),
                           Expression::Char(')')]),
                       Expression::All(vec![
                           Expression::Wildcard])]));
    }
}
