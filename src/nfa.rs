use expr::Expression;
use expr::Character;

#[derive(Debug, PartialEq, Clone)]
pub enum ExpectedChar {
    Specific(char),
    Wildcard,
    Any(Vec<Character>),
    None(Vec<Character>)
}

#[derive(Debug, PartialEq, Clone)]
pub enum State {
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
pub struct NFA {
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

    pub fn state_at<'a>(&'a self, at: usize) -> &'a State { &self.states[at] }
    pub fn num_states(&self) -> usize { self.states.len() }

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

    pub fn remove_branches(&self, st: Vec<usize>) -> Vec<usize> {
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
                    if chars.is_empty() {
                        if !checked_states.contains(&next) {
                            check_states.push(next);
                        }
                    } else {
                        branchless_states.push(st_idx);
                    }
                },

                State::NeedsCharacter(ExpectedChar::None(chars), next) => {
                    if chars.is_empty() {
                        if !checked_states.contains(&next) {
                            check_states.push(next);
                        }
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

pub fn build_nfa (expr: Expression) -> NFA {
    match expr {
        Expression::Char(c) => NFA::char_st(c),
        Expression::Wildcard => NFA::wildcard(),
        Expression::Any(chars) => NFA::any(chars),
        Expression::None(chars) => NFA::none(chars),
        Expression::All(exprs) => exprs.iter().fold(NFA::new(), |nfa, e| {
            nfa.concat(build_nfa(e.clone()))
        }),

        Expression::Choice(e1, e2) => {
            let mut e1_nfa = build_nfa(*e1);
            let e2_nfa = build_nfa(*e2);

            let n = e1_nfa.states.len();
            let m = e2_nfa.states.len();

            // Append each state in sequence, which is effectively a concat, but
            // instead of the success state, we need to place an epsilon transition
            // to the success state of the e1 nfa.
            for s in e2_nfa.states {
                if s == State::Success {
                    // !HACK! We need an epsilon transition here, but not necessarily
                    // a branch. A branch where both states end up in the same place
                    // is effectively a singular epsilon transition.
                    e1_nfa.states.push(State::branch(0, 0));
                } else {
                    // Each of these states has 'n' states in front from the other nfa
                    e1_nfa.states.push(s.offset(n));
                }
            }

            e1_nfa.states.push(State::branch(n - 1, n + m - 1));

            e1_nfa
        }

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
