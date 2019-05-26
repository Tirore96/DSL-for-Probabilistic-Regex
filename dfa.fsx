namespace RegexInterpreter
#load "nfa.fsx"
open System
open System.Collections.Generic
open nfa
open parser
module dfa =

    type DFA_state = DFA_state of ID: int * NFA_states: int list * Accepting_state: bool * Content_ID: string
    type DFA = DFA of states: DFA_state list * edges: Edge list * init: int * final: int list 
    type NFA_dict = NFA_dict of Dictionary<int,Edge list> * init: int * final: int

    let mutable dfa_global_id = -1 
    let dfa_unique_state_id() =
       dfa_global_id <- dfa_global_id+1
       dfa_global_id

    let build_nfa_dict (nfa: NFA) = 
        let (NFA(states,edges)) = nfa
        let init_id = states.[0]
        let final_id = states.[states.Length-1]
        let dict = new Dictionary<int,Edge list>()
        for edge in edges do
            let (Edge(from_state,to_state,trans,_)) = edge
            let has_key = dict.ContainsKey from_state
            match has_key with 
            | true -> 
                    let edge_list = dict.[from_state]
                    dict.[from_state] <- (edge::edge_list)
            | false -> dict.Add(from_state,[edge])
        NFA_dict (dict,init_id,final_id)

    let rec find_eps_closure id (edges: Edge list) =
        if edges.Length > 1 then
            match edges.[0] with
            | Edge(id,state2,E,p) -> match p with
                                     | 1.0 -> state2 :: (find_eps_closure id edges.[1..] )
                                     | _ -> find_eps_closure id edges.[1..]
            | _ -> find_eps_closure id edges.[1..]
        else
            match edges.[0] with
            | Edge(id,state2,E,p) -> match p with 
                                     | 1.0 -> state2 :: []
                                     | _ -> []
            | _ -> []

    let rec find_non_eps_closures id (edges: Edge list) =
        if edges.Length > 1 then
            match edges.[0] with
            | Edge(id,state2,t,p) -> 
                match t with
                | E -> match p with 
                       | 1.0 -> find_non_eps_closures id edges.[1..]
                       | _ -> (state2,t,p) ::find_non_eps_closures id edges.[1..]
                | _ -> (state2,t,p) :: find_non_eps_closures id edges.[1..] 
        else
            match edges.[0] with
            | Edge(id,state2,t,p) -> 
                match t with
                | E -> match p with 
                       | 1.0 -> []
                       | _ -> (state2,t,p) :: []

                | _ -> (state2,t,p) :: []

    // calls find_eps_closures for an entire list of ids
    let find_multiple_eps_closures ids (nfa_dict: NFA_dict)= 
        let (NFA_dict(dict,_,_)) = nfa_dict
        let mutable states = []
        for id in ids do
            //fails on nfa state without outgoing state
            if dict.ContainsKey(id) then
                let edges = dict.[id]
                states <- (find_eps_closure id edges) @  states
        states

    // calls find_non_eps_closures for an entire list of ids
    let find_multiple_non_eps_closures ids nfa_dict = 
        let (NFA_dict(dict,_,_)) = nfa_dict
        let mutable states_trans_probs = []
        for id in ids do
            if dict.ContainsKey(id) then
                let edges = dict.[id]
                states_trans_probs <- (find_non_eps_closures id edges) @  states_trans_probs 
        states_trans_probs

    //Calls find_muliple_eps_closures until no new states are returned
    let find_all_eps_closures ids nfa_dict =
        let mutable all_states = find_multiple_eps_closures ids nfa_dict
        let mutable prev_states = all_states
        let mutable continueLoop = true
        while continueLoop do
            let next_states = find_multiple_eps_closures prev_states nfa_dict
            //We assume no bidirectional epsilon edges, maybe error
            if next_states.Length = 0 then
                continueLoop <- false
            else
                all_states <-  all_states @ next_states
                prev_states <- next_states
        all_states
            
    let list_to_string l =
        let mutable retval = ""
        for i in l do
            retval <- retval + (string)i
        retval

    let dfa_contains_state dfa c_id=
        let (DFA(states,edges,_,_)) = dfa
        let mutable retval = false
        for state in states do
            let (DFA_state (_,_,_,state_c_id)) = state
            if state_c_id = c_id then
                retval <- true
        retval

    let get_dfa_state_id_through_cid dfa cid =  
        let (DFA(states,edges,init,final)) = dfa
        let mutable retval_id = -1
        for state in states do
            let (DFA_state(state_id,_,_,state_cid)) = state
            if state_cid = cid then
                retval_id <- state_id
        if retval_id = -1 then
            raise(Error("Cid doesn't exist in dfa"))
        else 
            retval_id

    let add_transitions (dfa: DFA) nfa_dict dfa_index =
        let (DFA (dfa_states,dfa_edges,init,final)) = dfa
        let (DFA_state (_,nfa_states,_,_)) = dfa_states.[dfa_index]
        let non_eps_closure_states_trans_prob = find_multiple_non_eps_closures nfa_states nfa_dict
        let mutable trans_state_dict = new Dictionary<Trans,int list>()
        let mutable trans_prob_dict = new Dictionary<Trans,double>()
        for state_trans_prob in non_eps_closure_states_trans_prob do    
            let (state,trans,prob) = state_trans_prob
            let has_key = trans_state_dict.ContainsKey(trans)
            match has_key with
            | true ->  
                       let state_list = trans_state_dict.[trans]
                       trans_state_dict.Add(trans,state::state_list)

            | false->  trans_state_dict.Add(trans,[state])
            //overriding the prob is not as issue as identical transitions should have identical probabilities (maybe error)
            trans_prob_dict.Add(trans,prob)
        let mutable new_dfa_states = []
        let mutable new_dfa_edges = []

        for KeyValue(trans, states) in trans_state_dict do
            let temp_all_states = find_all_eps_closures states nfa_dict
            let temp_all_states = states @ temp_all_states
            let content_id = list_to_string temp_all_states
            if not (dfa_contains_state dfa content_id) then
                //only allocate id if guaranteed to add it to dfa (to avoid indexing issues)
                let id = dfa_unique_state_id()
                let (DFA_state(prev_dfa_state_id,_,_,_)) = dfa_states.[dfa_index]
                let prob = trans_prob_dict.[trans]
                new_dfa_states <- DFA_state (id,states,false,content_id) :: new_dfa_states
                new_dfa_edges <- Edge(prev_dfa_state_id,id,trans,prob) :: new_dfa_edges
            else if trans = E_exit || trans = E_stay then
                let to_state = states.[0]
                let prob = trans_prob_dict.[trans]
                let (DFA_state(prev_dfa_state_id,_,_,_)) = dfa_states.[dfa_index]
                //find state_id of dfa state that has nfas state prior, making us enter this else statement
                let to_state_id = get_dfa_state_id_through_cid dfa content_id
                new_dfa_edges <- Edge(prev_dfa_state_id,to_state_id,trans,prob) :: new_dfa_edges
        let retval_dfa_states = dfa_states @ new_dfa_states
        let retval_dfa_edges = dfa_edges @ new_dfa_edges
        DFA(retval_dfa_states,retval_dfa_edges,init,final)

    let compute_closure (dfa: DFA) nfa_dict dfa_index = 
        let (DFA (dfa_states,dfa_edges,init,final)) = dfa
        let dfa_state = dfa_states.[dfa_index]
        let (DFA_state (id,nfa_states,s,_)) = dfa_state
        let eps_closure_states = find_all_eps_closures nfa_states nfa_dict 
        let new_nfa_states = nfa_states @ eps_closure_states
        let dfa_state = DFA_state(id,new_nfa_states,s,list_to_string new_nfa_states)
        let content_id = list_to_string new_nfa_states 
        let dfa_left,dfa_right = List.splitAt dfa_index dfa_states
        let dfa_right =
            match dfa_right with
            | [] -> []
            | x::xs -> xs
        let dfa = DFA(dfa_left @ dfa_state::dfa_right,dfa_edges,init,final)
        add_transitions dfa nfa_dict dfa_index 
    
    let initialize_dfa nfa_dict =
        let (NFA_dict (dict,init_id,final_id)) = nfa_dict
        let id = dfa_unique_state_id()
        let initial_dfa_state = DFA_state(id,[init_id],false,"")
        let dfa = DFA([initial_dfa_state],[],id,[-1])
        compute_closure dfa nfa_dict 0

    let mark_final_states (dfa: DFA) nfa_final_id =
        let mutable final_states = []
        let mutable (DFA (dfa_states,dfa_edges,init,final)) = dfa
        for i in 0..dfa_states.Length-1 do
            let (DFA_state (id,nfa_states,_,c_id)) = dfa_states.[i]
            for j in 0..nfa_states.Length-1 do
                if nfa_states.[j] = nfa_final_id then
                    final_states <- id :: final_states
                    let dfa_state = DFA_state(id,nfa_states,true,c_id)
                    let dfa_left,dfa_right = List.splitAt i dfa_states
                    let dfa_right = 
                        match dfa_right with
                        | [] -> []
                        | x::xs -> xs
                    dfa_states <- dfa_left @ dfa_state::dfa_right
        DFA(dfa_states,dfa_edges,init,final_states)

    let build_dfa nfa =
        let (NFA(nfa_states,nfa_edges)) = nfa
        let nfa_dict = build_nfa_dict nfa
        let mutable dfa = initialize_dfa nfa_dict
        let mutable (DFA (dfa_states,dfa_edges,init,final)) = dfa
        let nfa_init_id = nfa_states.[0]
        let nfa_final_id = nfa_states.[nfa_states.Length-1]
        let mutable count = 1
        while count < dfa_states.Length do  
            let (DFA_state(dfa_state_id,_,_,_)) = dfa_states.[count]
            dfa <- compute_closure dfa nfa_dict dfa_state_id
            let (DFA(new_dfa_states,new_dfa_edges,init,final)) = dfa
            dfa_states <- new_dfa_states
            count <- count+1
        mark_final_states dfa nfa_final_id