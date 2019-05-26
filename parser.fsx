namespace RegexInterpreter
#load "lexer.fsx"
open System
open System.Text.RegularExpressions

module parser = 
    type Base = Char of char| Parenthesis of Regex | Eps of string
    and Factor = Base of Base| Star of Base * double
    and Term = Factor of Factor | Sequence of Factor * Term
    and Regex = OR of Term * Regex * double | Term of Term 
    and Exp = IsValid of Regex | Generate of Regex * int | Prob of Regex * string 

    ////////////////////////////////Types/////////////////////////////////////

    exception Error of string

    let more (str: string)= 
        str.Length > 0

    let peek (str: string)=
        if more str then
            str.[0]
        else
            raise(Error("peeking into empty string"))

    let eat (str: string) (c: char) = 
        if c = peek str then
            str.[1..]
        else
            raise(Error("tried to eat"))

    let rec find_occurence (str: string) (c: char) (n: int) =
        if str.[0] = c then
            n
        else if str.Length > 0 then
            find_occurence str.[1..] c n+1
        else raise(Error("doesn't exist in string"))

    let index_of (str: string) (c: char) =
        find_occurence str c 0

    let sub_string (str: string) (start: int) (count: int) = 
        str.[start..count]

    let parse_prob rest =
        let mutable rest = eat rest '('

        let prob_str = sub_string rest 0 ((index_of rest ')')-1)
        let prob = (double) prob_str
        for i in prob_str do
            rest <- eat rest i
        let rest = eat rest ')'
        prob, rest

    let parse_eps rest = 
        let rest = eat rest 'E'
        let rest = eat rest 'p'
        let rest = eat rest 's'
        (Eps ""),rest

    let rec parse_regex regex =
        if not (more regex) then 
            raise(Error("empty regex"))
        let term,rest = parse_term regex
        if (more rest) && peek rest = '|' then
            let rest = eat rest '|'
            let parsed_prob,rest = parse_prob rest
            let parsed_regex,rest = parse_regex rest
            (OR (term, parsed_regex, parsed_prob)),rest
        else
            (Term term),rest

    and parse_term rest =
        if (more rest) && not (peek rest = '|') &&  not (peek rest = ')') then
            let factor,rest = parse_factor rest 
            if (more rest) && not (peek rest = '|') && not (peek rest = ')')then
                let term,rest = parse_term rest
                Sequence( factor, term),rest
            else
                Factor(factor), rest
        else
            raise(Error("not more in parse_term"))

    and parse_factor rest = 
        let parsed_base,rest = parse_base rest
        if (more rest) && peek rest = '*' then
            let rest = eat rest '*'
            let parsed_prob,rest  = parse_prob rest
            (Star (parsed_base, parsed_prob)),rest
        else
            (Base parsed_base),rest

    and parse_base rest = 
        if peek rest = '(' then
            let rest = eat rest '('
            let parsed_regex,rest = parse_regex rest
            let rest = eat rest ')'
            (Parenthesis parsed_regex),rest
        else if peek rest = '\\' then
            let rest = eat rest '\\'
            if peek rest = 'E' then
                (parse_eps rest)
            else 
                let c = peek rest
                let rest = eat rest c
                Char (c),rest
        else
            let c = peek rest
            let rest = eat rest c
            Char (c),rest


    let parse_n n =
        let mutable retval = -1
        try
            retval <- (int) n
        with
        | _ -> printfn "couldnt parse %A to integer" n
        retval

    let parser (tokens : string list) = 
        let regex = tokens.[1]
        let parsed_regex,rest = parse_regex regex 
        match tokens.[0] with
        | "IsValid" -> IsValid parsed_regex
        | "Generate" -> Generate (parsed_regex, (parse_n tokens.[2]))
        | "Prob" -> Prob (parsed_regex, tokens.[2])
        | _ -> raise(Error("failed"))