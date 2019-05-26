namespace RegexInterpreter
#load "lexer.fsx"
#load "parser.fsx"
#load "nfa.fsx"
#load "dfa.fsx"
open lexer
open parser
open nfa
open dfa

open System
open System.Collections.Generic
module functions = 

    type DFA_dict = DFA_dict of Dictionary<int,Edge list> * init: int * final: int list
    type Result = IsValid_ret of bool | Generate_ret of string list * Dictionary<string,int> | Prob_ret of double
    
    let rnd = System.Random()

    let valid_probability prob = 
        prob > 0.0 && prob < 1.0

    let build_dfa_dict (dfa : DFA) = 
       let (DFA(states,edges,init,final)) = dfa
       let init_id = init
       let final_ids =  final
       let dict = new Dictionary<int,Edge list>()
       for edge in edges do
           let (Edge(from_state,to_state,trans,_)) = edge
           let has_key = dict.ContainsKey from_state
           match has_key with 
           | true -> 
                   let edge_list = dict.[from_state]
                   dict.[from_state] <- (edge::edge_list)
           | false -> dict.Add(from_state,[edge])
       DFA_dict (dict,init_id,final_ids)

    let get_dfa_state dfa id =
        let (DFA(states,edges,init,final)) = dfa
        let mutable retval = states.[0]
        for state in states do
            let (DFA_state(state_id,_,_,_)) = state
            if state_id = id then
                retval <- state
        let (DFA_state(state_id,_,_,_)) = retval 
        if not (state_id = id) then
            raise(Error("Id doesn't exist in dfa"))
        else 
            retval
        
    let calculate_IsValid dfa =
        let dfa_dict = build_dfa_dict dfa
        let (DFA_dict(dict,init,final)) = dfa_dict
        let (DFA(states,edges,init,final)) = dfa
        let mutable retval = true
        for edge in edges do
            match edge with
            | Edge(from_state,to_state,E_stay,prob) -> 
                        let edges_from_to_state = dict.[to_state]
                        let mutable contains_star_in_star = false
                        for i in edges_from_to_state do
                            match i with
                            | Edge(_,_,E_stay,_) -> contains_star_in_star <- true 
                            | _ -> contains_star_in_star <- contains_star_in_star
                        let valid_prob = valid_probability prob
                        retval <-  retval && (not contains_star_in_star) && valid_prob
            | Edge(_,_,E_exit,prob) -> retval <-  retval && (valid_probability prob)
            | Edge(_,_,E_l,prob) -> retval <-  retval && (valid_probability prob)
            | Edge(_,_,E_r,prob) -> retval <-  retval && (valid_probability prob)
            | _ -> retval <- retval
        retval

    let generate_string dfa dfa_dict  =
        let (DFA(states,edges,init,final)) = dfa
        let (DFA_dict(dict,init,final)) = dfa_dict

        let mutable cur_state = states.[init]
        let mutable end_var = false
        let mutable retval = ""
        while not end_var do
            let (DFA_state(id,nfa_states,s,c_id)) = cur_state
            let state_edges = dict.[id]
            if state_edges.Length = 1 then
                let (Edge(from_state,to_state,trans,p)) = state_edges.[0]
                let  c = 
                    match trans with
                    | C c -> c
                    | _ -> raise(Error("didn't expect other than C transitions from here"))
                retval <- retval + (string)c
                cur_state <- get_dfa_state dfa to_state
            else 
                let (Edge(from_state,to_state,trans,p)) = state_edges.[0]
                let rnd_prob = rnd.NextDouble()
                if rnd_prob <= p then
                    cur_state <- get_dfa_state dfa to_state
                else
                    let (Edge(from_state,to_state,trans,p)) = state_edges.[1]
                    cur_state <- get_dfa_state dfa to_state
            let (DFA_state(id,nfa_states,s,c_id)) = cur_state
            if s then
                end_var <- true
        retval
        
    let calculate_Generate dfa n = 
        let (DFA(states,edges,init,final)) = dfa
        let dfa_dict = build_dfa_dict dfa
        let mutable cur_state = states.[init]
        let mutable retval = [] 
        for i in 1..n do
            retval <- (generate_string dfa dfa_dict) :: retval
        let result_dict = new Dictionary<string,int>()
        for i in retval do
            if result_dict.ContainsKey(i) then
                result_dict.[i]<- result_dict.[i]+1
            else
                result_dict.Add(i,1)
        retval,result_dict

    let rec calculate_Prob dfa (str: string) cur_state prob terminate matched =
        let empty_string  = (str.Length = 0)
        let (DFA_state(id,nfa_states,s,c_id)) = cur_state
        if terminate then
            if s && empty_string then
                prob
            else
                0.0
        else
            let dfa_dict = build_dfa_dict dfa
            let (DFA_dict(dict,_,_)) = dfa_dict
            let state_edges = dict.[id]
            if state_edges.Length = 1 then
                let (Edge(_,to_state,trans,p)) = state_edges.[0]
                let  c = 
                    match trans with
                    | C c -> c
                    | _ -> raise(Error("didn't expect other than C transitions from here"))
                if str.Length > 0 then
                    if c = str.[0] then
                        let new_state = get_dfa_state dfa to_state
                        let new_state_has_no_edges = not (dict.ContainsKey(to_state))
                        if str.Length > 1 then
                            calculate_Prob dfa str.[1..] new_state prob (empty_string|| new_state_has_no_edges) true
                        else
                            calculate_Prob dfa "" new_state prob  (empty_string|| new_state_has_no_edges) true
                    else
                        0.0
                else
                    0.0
            else
                let mutable retval = 0.0
                for edge in state_edges do
                    let (Edge(from_state,to_state,trans,p)) = edge
                    let new_state = get_dfa_state dfa to_state
                    let new_state_has_no_edges = not (dict.ContainsKey(to_state))
                    retval <- retval + (calculate_Prob dfa str new_state (prob*p) (empty_string||new_state_has_no_edges)) false
                retval
 
    let calculate_Prob_wrapper dfa str = 
        let (DFA(states,edges,init,final)) = dfa
        let inital_state = get_dfa_state dfa init
        calculate_Prob dfa str inital_state 1.0 false false

    [<EntryPoint>]
    let main argv = 
        let mutable cond= true
        let mutable verbose = false
        while cond do
            dfa_global_id <- -1
            global_id <- 1
            let input = Console.ReadLine()
            if input = "verbose=true" then
                verbose <- true
            else if input = "verbose=false" then
                verbose <- false 
            else
                try
                    let lexed = lexer input
                    let parsed = parser lexed
                    let parsed_regex =
                        match (parsed) with
                        | IsValid regex      -> regex
                        | Generate (regex,n) -> regex
                        | Prob(regex,str)    -> regex

                    let nfa = build_nfa_regex parsed_regex
                    let dfa = build_dfa nfa

                    let result = 
                        match parsed with
                        | IsValid _      -> IsValid_ret (calculate_IsValid dfa )
                        | Generate (_,n) -> Generate_ret (calculate_Generate dfa n)
                        | Prob(_,str)    -> Prob_ret (calculate_Prob_wrapper dfa str)

                    if verbose then
                        printfn "____________________________"
                        printfn "Lexed expressions %A" lexed
                        printfn "____________________________"
                        printfn "Parse-tree for regex: %A" parsed_regex
                        printfn "____________________________"
                        printfn "NFA from parse-tree: %A" nfa
                        printfn "____________________________"
                        printfn "DFA from NFA: %A" dfa
                        printfn "____________________________"

                    match result with
                    | IsValid_ret result -> printfn "Validity: %A" result
                    | Generate_ret(str,dict) -> 
                        printfn "List of strings: %A" str
                        printfn "Dictionary of occurences: %A" dict

                    | Prob_ret result -> printfn "Probability: %A" result
                with 
                    |Error(str) -> printfn "Error: %A" str
        0