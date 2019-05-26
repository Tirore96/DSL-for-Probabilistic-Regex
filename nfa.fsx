namespace RegexInterpreter
#load "parser.fsx"
open System
open parser


module nfa =
    type Trans = C of char | E | E_l | E_r | E_exit | E_stay
    type Edge = Edge of int * int * Trans * double
    type State = State of int
    type NFA = NFA of (int list) * (Edge list)

    let mutable global_id = 1

    let unique_state_id() =
        global_id <- global_id+1
        global_id

    let rec build_nfa_eps() =
        let state1 = unique_state_id()
        let state2 = unique_state_id()
        let edge = Edge(state1,state2,E,1.0)
        NFA([state1;state2],[edge])

    let rec build_nfa_char c =
        let state1 = unique_state_id()
        let state2 = unique_state_id()
        let edge = Edge(state1,state2,C c,1.0)
        NFA([state1;state2],[edge])

    and build_nfa_base base_var =
        match base_var with
        | Char c -> build_nfa_char c
        | Parenthesis regex -> build_nfa_regex regex
        | Eps _ -> build_nfa_eps()

    and build_nfa_star base_var prob =
        let base_nfa = build_nfa_base base_var
        let (NFA(base_states,base_edges)) = base_nfa
        let state1 = unique_state_id()
        let state2 = unique_state_id()
        let epsilon_template_to_base = Edge(state1,base_states.[0],E_stay,1.0-prob)
        let epsilon_base_to_base = Edge(base_states.[base_states.Length-1],base_states.[0],E_stay,1.0-prob)
        let epsilon_base_to_template = Edge(base_states.[base_states.Length-1],state2,E_exit,prob)
        let epsilon_template_to_template = Edge(state1,state2,E_exit,prob)
        let combined_states = state1 :: base_states @ state2 :: []
        let combined_edges = epsilon_template_to_base :: epsilon_base_to_base :: epsilon_base_to_template 
                                :: epsilon_template_to_template ::   base_edges 
        NFA(combined_states,combined_edges)

    and build_nfa_factor factor =
        match factor with 
        | Base base_var -> build_nfa_base base_var
        | Star (base_var, prob)-> build_nfa_star base_var prob

    and build_nfa_sequence factor term = 
        let factor_nfa = build_nfa_factor factor
        let term_nfa = build_nfa_term term 
        let (NFA(factor_states, factor_edges)) = factor_nfa
        let (NFA(term_states, term_edges)) = term_nfa
        let connecting_edge = Edge(factor_states.[factor_states.Length-1],term_states.[0],E,1.0)
        let combined_states = factor_states @ term_states
        let combined_edges = connecting_edge:: factor_edges @ term_edges
        NFA(combined_states,combined_edges)

    and build_nfa_term term = 
        match term with
        | Factor factor -> build_nfa_factor factor
        | Sequence (factor, term)-> build_nfa_sequence factor term

    and build_nfa_or term regex prob =
        let term_nfa = build_nfa_term term
        let regex_nfa = build_nfa_regex regex
        let state1 = unique_state_id()
        let state2 = unique_state_id()
        let states = [state1;state2]
        let (NFA(term_states, term_edges)) = term_nfa
        let (NFA(regex_states, regex_edges)) = regex_nfa
        let epsilon_template_to_term = Edge(state1,term_states.[0],E_l,  prob)
        let epsilon_template_to_regex = Edge(state1,regex_states.[0],E_r, 1.0-prob)
        let epsilon_term_to_template = Edge(term_states.[term_states.Length-1],state2,E, 1.0)
        let epsilon_regex_to_template = Edge(regex_states.[regex_states.Length-1],state2,E, 1.0)
        let epsilon_edges = [epsilon_template_to_term;epsilon_template_to_regex;epsilon_term_to_template;epsilon_regex_to_template]
        let combined_states = state1 :: term_states @ regex_states @ state2 :: []
        let combined_edges = term_edges @ regex_edges @ epsilon_edges
        NFA(combined_states,combined_edges)

    and build_nfa_regex regex =
        match regex with
        | OR (term, r, p) -> build_nfa_or term r p
        | Term term -> build_nfa_term term