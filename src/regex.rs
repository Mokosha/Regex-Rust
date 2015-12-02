use expr::Expression;
use tokenizer::parse_string;

fn get_prefixes<T: Clone+Copy>(v: &Vec<T>) -> Vec<Vec<T>> {
    let prefixes: Vec<Vec<T>> = v.iter().scan(Vec::new(), |pv, c| {
        pv.push(*c);
        Some(pv.clone())
    }).collect();

    // Need to stick the empty string on top of it.
    let mut result = vec![Vec::new()];
    for prefix in prefixes.iter() {
        result.push(prefix.clone())
    }
    result
}

fn drop_n<T: Clone>(v: Vec<T>, n: usize) -> Vec<T> {
    v.iter().skip(n).map(|x| x.clone()).collect()
}

#[allow(dead_code)]
fn match_expr_slow(e: Expression, s: Vec<char>) -> bool {
    match e {
        Expression::Char(c) => s.len() == 1 && c == s[0],
        Expression::Numeral => {
            let numerals: Vec<_> = (('0' as u8)..(('9' as u8) + 1)).map(|c| c as char).collect();
            s.len() == 1 && numerals.contains(&s[0])
        },
        Expression::Lowercase => {
            let lowers: Vec<_> = (('a' as u8)..(('z' as u8) + 1)).map(|c| c as char).collect();
            s.len() == 1 && lowers.contains(&s[0])
        },
        Expression::Uppercase => {
            let uppers: Vec<_> = (('A' as u8)..(('Z' as u8) + 1)).map(|c| c as char).collect();
            s.len() == 1 && uppers.contains(&s[0])
        },

        Expression::Wildcard => s.len() == 1,

        Expression::Any(exprs) => {
            if exprs.is_empty() {
                s.is_empty()
            } else {
                exprs.iter().any(move |e| match_expr(e.clone(), s.clone()))
            }
        },

        Expression::None(exprs) => !match_expr(Expression::Any(exprs), s),
        Expression::All(exprs) => {

            // Only the empty string matches empty exprs...
            if exprs.is_empty() {
                return s.is_empty();
            }

            // If s is empty, then maybe it can satisfy each of the exprs in sequence...
            if s.is_empty() {
                return exprs.iter().all(|expr| match_expr(expr.clone(), s.clone()))
            }

            // We can short-circuit this for All's that have only one expr...
            if exprs.len() == 1 {
                return match_expr(exprs[0].clone(), s);
            }

            // Go through each prefix -- if it satisfies the expression AND the
            // remaining part of the string satisfies the rest of the expressions, then
            // return true.

            let expr = exprs.first().unwrap(); // Expressions are non-empty
            for pre in get_prefixes(&s) {
                let rest_of_s = drop_n(s.clone(), pre.len());
                let this_is_good = match_expr(expr.clone(), pre);
                let rest_is_good =
                    match_expr(Expression::All(drop_n(exprs.clone(), 1)), rest_of_s);

                if this_is_good && rest_is_good { return true }
            }

            // If we get to here, it means that we couldn't match this expr...
            false
        },

        Expression::NoneOrMore(expr_box) => {
            // Match it as many times as possible, and if we can't, that's OK.
            for pre in get_prefixes(&s) {
                let rest_of_s = drop_n(s.clone(), pre.len());

                if match_expr((*expr_box).clone(), pre) {
                    return match_expr(Expression::NoneOrMore(expr_box), rest_of_s);
                }
            }

            // We better have matched it none times...
            s.is_empty()
        },

        Expression::OneOrMore(expr_box) => {
            // Match it as many times as possible, but we need to match it at least once.
            if s.is_empty() {
                return false;
            }

            for pre in get_prefixes(&s) {
                let rest_of_s = drop_n(s.clone(), pre.len());

                // If we checked it once, then we need none or more...
                if match_expr((*expr_box).clone(), pre) {
                    return match_expr(Expression::NoneOrMore(expr_box), rest_of_s);
                }
            }

            // We didn't match it
            false
        },

        // Either it's empty (none) or it exactly matches the expr (one)
        Expression::NoneOrOne(expr_box) =>
            s.is_empty() || match_expr((*expr_box).clone(), s.clone())
    }
}

fn match_expr_fast(e: Expression, _s: Vec<char>) -> bool {
    let mut expr_stack = vec![e];
    let mut s = _s.clone();

    loop {
//        println!("{:?}", (expr_stack.clone(), s.clone()));
//        ::std::thread::sleep(::std::time::Duration::new(1, 0));

        let e = expr_stack.pop().unwrap();

        match e {
            Expression::Char(c) => {
                if s.len() == 0 || s[0] != c {
                    return false
                }
                s = drop_n(s.clone(), 1);
            },

            Expression::Numeral => {
                let numerals: Vec<_> = (('0' as u8)..(('9' as u8) + 1))
                    .map(|c| c as char)
                    .collect();
                if s.len() == 0 || !(numerals.contains(&s[0])) {
                    return false;
                }
                s = drop_n(s.clone(), 1);
            },

            Expression::Lowercase => {
                let lowers: Vec<_> = (('a' as u8)..(('z' as u8) + 1))
                    .map(|c| c as char)
                    .collect();
                if s.len() == 0 || !(lowers.contains(&s[0])) {
                    return false;
                }
                s = drop_n(s.clone(), 1);
            },

            Expression::Uppercase => {
                let uppers: Vec<_> = (('A' as u8)..(('Z' as u8) + 1))
                    .map(|c| c as char)
                    .collect();
                if s.len() == 0 || !(uppers.contains(&s[0])) {
                    return false;
                }
                s = drop_n(s.clone(), 1);
            },

            Expression::Wildcard => {
                if s.len() == 0 {
                    return false;
                }
                s = drop_n(s.clone(), 1);
            }
            
            Expression::None(exprs) => {
                // We have to match at least some character...
                if !exprs.is_empty() {
                    if s.is_empty() {
                        return false;
                    } else {
                        return exprs.iter().all(|expr| {
                            !match_expr(expr.clone(), vec![s[0]])
                        });
                    }
                } 
            },

            Expression::Any(exprs) => {
                if exprs.len() <= 1 {
                    for expr in exprs {
                        expr_stack.push(expr);
                    }
                } else {
                    return exprs.iter().any(|expr| {
                        let mut stack = expr_stack.clone();
                        stack.push(expr.clone());
                        stack.reverse();
                        match_expr(Expression::All(stack), s.clone())
                    });
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


fn match_expr(e: Expression, s: Vec<char>) -> bool {
    match_expr_fast(e, s)
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
