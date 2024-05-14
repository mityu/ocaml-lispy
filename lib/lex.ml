open Printf
open Err

type token =
    TokenLParen
    | TokenRParen
    | TokenSingleQuote
    | TokenBackQuote
    | TokenComma
    | TokenCommaAt
    | TokenColon
    | TokenInt of int
    | TokenString of string
    | TokenSymbol of string

let string_of_token t =
    match t with
    | TokenLParen -> "("
    | TokenRParen -> ")"
    | TokenSingleQuote -> "'"
    | TokenBackQuote -> "`"
    | TokenComma -> ","
    | TokenCommaAt -> ",@"
    | TokenColon -> ":"
    | TokenInt v -> sprintf "Int: %d" v
    | TokenString s -> sprintf "String: %s" s
    | TokenSymbol s -> sprintf "Symbol: %s" s

let read_file file =
    let ic = open_in file in
    let size = in_channel_length ic in
    let content = really_input_string ic size in
    let () = close_in ic in
    content

let is_white = String.contains " \n\t\r"

let is_reserved_char = String.contains "()'`,:;\""

let is_digit = String.contains "0123456789"

let is_number s =
    let has_sign_prefix s =
        String.starts_with ~prefix:"+" s || String.starts_with ~prefix:"-" s
    in
    let s = if has_sign_prefix s && String.length s >= 2 then
        String.sub s 1 (String.length s - 1)
    else
        s
    in
    String.fold_left (fun acc c -> acc && (is_digit c)) true s

let lex src =
    let string_of_char = String.make 1 in
    let get_char_at i =
        if i < String.length src then
            Some (String.get src i)
        else
            None
    in
    let next_char i = (i + 1, get_char_at i) in
    let next_substring i len =
        let rec impl i len acc =
            if len = 0 then
                (i, Some acc)
            else
                let (i', c) = next_char i in
                match c with
                | None -> (i, None)
                | Some c -> impl i' (len - 1) (acc ^ string_of_char c)
        in
        let (i', substr) = impl i len "" in
        match substr with
        | None -> (i, None)  (* Do not return advanced index *)
        | Some _ -> (i', substr)
    in
    let next_symbol i =
        (*
            'foo -> FOO
            '\foO -> |fOO|
            'f\Oo -> |FOO|
            '|fOo| -> |fOo|
            'f|oO| -> |FoO|
            12\3 -> |123|
            'f|o|o|o| -> |FoOo|
            #\a -> #\a
            #\ab -> #\aB
            #\ab\c -> #\aBc
            #\newline -> #\Newline
         *)
        let build_return_value i acc in_bar keptcase =
            if in_bar then
                failwith "Bar is not closed."
            else
                let acc =
                    if keptcase && Bool.not (String.starts_with ~prefix:"#" acc) then
                        "|" ^ acc ^ "|"
                    else
                        acc
                in
                (i, acc)
        in
        let rec impl i acc in_bar keptcase =
            let (i', c) = next_char i in
            match c with
            | Some '|' -> impl i' acc (Bool.not in_bar) true
            | Some '\\' ->
                    let (i, c) = next_char i' in
                    (match c with
                    | None -> failwith "No character follows after \\."
                    | Some c -> impl i (acc ^ string_of_char c) in_bar true)
            | Some c when is_reserved_char c -> build_return_value i acc in_bar keptcase
            | Some c ->
                    if in_bar then
                        impl i' (acc ^ string_of_char c) in_bar keptcase
                    else if Bool.not (is_white c) then
                        let s = String.capitalize_ascii (string_of_char c) in
                        impl i' (acc ^ s) in_bar keptcase
                    else
                        build_return_value i' acc in_bar keptcase
            | None -> build_return_value i' acc in_bar keptcase
        in
        let impl i =
            let (i', prefix) = next_substring i 3 in
            match prefix with
            | None -> impl i "" false false
            | Some prefix ->
                    if String.starts_with ~prefix:"#'" prefix then
                        impl (i' - 1) "#'" false false
                    else if String.starts_with ~prefix:"#\\" prefix then
                        impl i' prefix false false
                    else
                        impl i "" false false
        in
        impl i
    in
    let next_string i =
        let string_of_char = String.make 1 in
        let rec impl i acc =
            let (i', c) = next_char i in
            match c with
            | None -> failwith "String is not closed."
            | Some '"' -> (i', acc)
            | Some '\\' ->
                    let (i', c) = next_char i' in
                    (match c with
                    | None -> failwith "No character follows after \\."
                    | Some c -> impl i' (acc ^ "\\" ^ string_of_char c))
            | Some c -> impl i' (acc ^ string_of_char c)
        in
        let (i, c) = next_char i in
        match c with
        | Some '"' -> impl i ""
        | _ -> unreachable ()
    in
    let rec skip_until i target =
        let (i', c) = next_char i in
        match c with
        | Some c -> if c == target then i' else skip_until i' target
        | None -> i
    in
    let normalize_special_symbol symbol =
        let special_symbols = [
            "#\\Newline"; "#\\Tab"; "#\\Linefeed"; "#\\Return"; "#\\Space";
        ] in
        let lower_cased = String.lowercase_ascii symbol in
        let comparer sym = String.equal lower_cased (String.lowercase_ascii sym) in
        match List.find_opt comparer special_symbols with
        | Some symbol -> symbol
        | None -> symbol
    in
    let rec next_token i =
        let (i', c) = next_char i in
        match c with
        | None -> (i', None)
        | Some '(' -> (i', Some TokenLParen)
        | Some ')' -> (i', Some TokenRParen)
        | Some '\'' -> (i', Some TokenSingleQuote)
        | Some '`' -> (i', Some TokenBackQuote)
        | Some ',' ->
                let (i'', c) = next_char i' in
                (match c with
                | Some '@' -> (i'', Some TokenCommaAt)
                | _ -> (i', Some TokenComma))
        | Some ':' -> (i', Some TokenColon)  (* TODO: Handle this properly *)
        | Some ';' -> let i' = skip_until i' '\n' in next_token i'
        | Some '"' -> let (i', s) = next_string i in (i', Some (TokenString s))
        | Some c when is_white c -> next_token i'
        | Some _ ->
                let (i', s) = next_symbol i in
                if String.length s = 0 then
                    next_token i'
                else if is_number s then
                    (i', Some (TokenInt (int_of_string s)))
                else
                    (i', Some (TokenSymbol (normalize_special_symbol s)))
    in
    let rec impl i acc =
        let i, tk = next_token i in
        match tk with
        | None -> List.rev acc
        | Some tk -> impl i (tk :: acc)
    in
    impl 0 []
