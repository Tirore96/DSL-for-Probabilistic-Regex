namespace RegexInterpreter
open System
open System.Text.RegularExpressions

module lexer= 

    exception Error of string

    let rec remove_pre_whitespace (line : string) =
        match line.[0] with
        | ' ' -> remove_pre_whitespace line.[1..]
        | _ -> line

    let rec remove_trailing_whitespace (line : string) =
        match line.[line.Length-1] with
        | ' ' -> remove_trailing_whitespace line.[0..(line.Length-2)]
        | _ -> line

    let rec index_of_unescaped_quote (line: string) index =
        match line.[0] with
        | '"' -> index
        | '\\' -> index_of_unescaped_quote line.[2..] index+2
        | _ -> index_of_unescaped_quote line.[1..] index+1

    //Assumes line doesn't have pre white space
    let extract_string (line: string) = 
        let line_clean = remove_pre_whitespace line
        match line_clean.[0] with 
         | '"' -> let index = index_of_unescaped_quote line_clean.[1..] 0
                  line_clean.[1..index],line_clean.[index+2..]
         | _ -> raise(Error("error"))

    let (|Integer|_|) input= 
        let m = Regex.Match(string input,"[0-999999]")
        if (m.Success) then Some m.Groups.[0].Value else None

    let extract_n (line: string) = 
        let line_clean = remove_trailing_whitespace (remove_pre_whitespace line)
        match line with 
        | Integer _ -> line_clean
        | _ -> raise(Error("Error!"))

    let lexer (line: string) = 
        let line_clean: string = remove_trailing_whitespace (remove_pre_whitespace line)
        let split_line = line_clean.Split ' '
        match split_line.[0] with
        | "IsValid" -> 
                    let regex,rest = extract_string line_clean.[7..]
                    "IsValid" :: regex :: []
        | "Generate" -> 
                    let regex,rest = extract_string line_clean.[8..]
                    //printfn "%A %A" regex rest
                    let n = extract_n rest
                    "Generate" :: regex :: n ::  []

        | "Prob" -> 
                    let regex,rest = extract_string line_clean.[4..]
                    let str,_= extract_string rest
                    "Prob" :: regex :: str ::  []

        | _ -> raise(Error("no function of that name"))