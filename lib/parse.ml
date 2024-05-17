open Err
open Expr

let is_digit = String.contains "0123456789"
let is_white = String.contains " \n\t\r"
let is_atom c = Bool.not (String.contains "()\"'`,;" c || is_white c)
let is_number s =
    if String.length s == 0 then
        false
    else
        let s =
            let c = String.get s 0 in
            if String.contains "+-" c then
                String.sub s 1 (String.length s - 1)
            else
                s
        in
        String.fold_left (fun acc c -> acc && is_digit c) true s

let string_of_char = String.make 1

let unwrap v errmsg =
    match v with
    | None -> failwith errmsg
    | Some v -> v

let parse src =
    let read_char i =
        let c =
            if i < String.length src then
                Some (String.get src i)
            else
                None
        in
        (i + 1, c)
    in
    let ensure_char i c =
        match read_char i with
        | i, Some c' when c = c' -> i
        | _ -> unreachable ()
    in
    let rec skip_until i p =
        let (i', c) = read_char i in
        match c with
        | None -> i
        | Some c when p c -> i'
        | _ -> skip_until i' p
    in
    let rec skip_white i =
        let (i', c) = read_char i in
        match c with
        | None -> i
        | Some c when is_white c -> skip_white i'
        | _ -> i
    in
    let parse_string i =
        let rec read_string i acc =
            let (i', c) = read_char i in
            match c with
            | None -> failwith "String is not closed"
            | Some '"' -> (i', acc)
            | Some '\\' ->
                    let (i'', c) = read_char i' in
                    (match c with
                    | None -> failwith "No character follows after \\"
                    | Some c -> read_string i'' (acc ^ "\"" ^  string_of_char c))
            | Some c -> read_string i' (acc ^ string_of_char c)
        in
        let i =
            match read_char i with
            | i, Some '"' -> i
            | _ -> unreachable ()
        in
        let (i, s) = read_string i "" in
        (i, Some (ExprString s))
    in
    let rec parse_exp i quasiquote =
        let i = skip_white i in
        let (_, c) = read_char i in
        match c with
        | None -> (i, None)
        | Some '(' -> parse_list i quasiquote
        | Some ')' -> failwith "Too much closing bracket"
        | Some '"' -> parse_string i
        | Some '\'' -> readmacro_quote i
        | Some '`' -> readmacro_backquote i
        | Some ',' -> readmacro_unquote i quasiquote
        | Some ';' -> let i' = skip_until i (fun c -> c = '\n') in parse_exp i' quasiquote
        | _ ->
                let r = parse_symbol i in
                (match r with
                | _, None -> r
                | i, Some (ExprSymbol s) ->
                        if is_number s then
                            (i, Some (ExprInt (int_of_string s)))
                        else
                            r
                | _ -> unreachable ())
    and parse_list i quasiquote =
        let i =
            match read_char i with
            | i, Some '(' -> i
            | _ -> unreachable ()
        in
        let err_unclosed = "Unclosed parenthesis" in
        let rec do_parse elems i quasiquote =
            let i = skip_white i in
            let (i', c) = read_char i in
            match c with
            | None -> failwith err_unclosed
            | Some ')' -> (i', Some (ExprList (List.rev elems)))
            | _ ->
                    let (i', e) = parse_exp i quasiquote in
                    let e = unwrap e err_unclosed in
                    do_parse (e :: elems) i' quasiquote
        in
        do_parse [] i quasiquote
    and parse_symbol i =
        let rec do_parse acc i in_bar keptcase =
            let (i', c) = read_char i in
            match c with
            | Some '|' -> do_parse acc i' (Bool.not in_bar) keptcase
            | Some '\\' ->
                    (match read_char i' with
                    | i', Some c -> do_parse (acc ^ string_of_char c) i' in_bar true
                    | _ -> failwith "No character follows after \\")
            | Some c when is_atom c || in_bar ->
                    let c = if in_bar then c else Char.uppercase_ascii c in
                    do_parse (acc ^ string_of_char c) i' in_bar keptcase
            | _ ->
                    if acc = "" then
                        (i, None)
                    else
                        let symbol =
                            if keptcase then
                                "|" ^ acc ^ "|"
                            else
                                acc
                        in
                        (i, Some (ExprSymbol symbol))
        in
        match read_char i with
        | _, Some '#' -> parse_hashed_symbol i
        | _ -> do_parse "" i false false
    and parse_hashed_symbol i =
        let i = ensure_char i '#' in
        let unwrap_bar symbol =
            let symbol =
                match symbol with
                | ExprSymbol s -> s
                | _ -> unreachable ()
            in
            if String.starts_with ~prefix:"|" symbol then
                String.sub symbol 1 (String.length symbol - 2)
            else
                symbol
        in
        let (i', c) = read_char i in
        match c with
        | Some '\\' -> todo ()  (* Character literal *)
        | Some '|' -> todo ()  (* Block comment like OCaml *)
        | Some '\'' ->
                (match parse_symbol i' with
                | i', Some symbol ->
                        let symbol = unwrap_bar symbol in
                        (i', Some (ExprSymbol ("#'" ^ symbol)))
                | _ -> (i', None))
        | Some ':' ->
                (* TODO: Check if the given symbol is valid *)
                (match parse_symbol i' with
                | i', Some symbol ->
                        let symbol = unwrap_bar symbol in
                        (i', Some (ExprSymbol ("#:" ^ symbol)))
                | _ -> (i', None))
        | Some c -> failwith ("Invalid character after #: " ^ string_of_char c)
        | _ -> failwith "No character follows after #"
    and readmacro_quote i =
        let i = ensure_char i '\'' in
        let i = skip_white i in
        let (i', exp) = parse_exp i false in
        match exp with
        | None -> failwith "No expression follows after '"
        | Some exp -> (i', Some (ExprList [ExprSymbol "#:QUOTE"; exp]))
    and readmacro_backquote i =
        let i = ensure_char i '`' in
        let i = skip_white i in
        let (i', exp) = parse_exp i true in
        match exp with
        | None -> failwith "No expression follows after `"
        | Some exp -> (i', Some (ExprList [ExprSymbol "#:QUOTE"; exp]))
    and readmacro_unquote i quasiquote =
        let i = ensure_char i ',' in
        let () = if Bool.not quasiquote then failwith "Illegal comma outside of backquote" in
        let (i', splicing) =
            match read_char i with
            | i', Some '@' ->
                    let () =
                        (match read_char i' with
                        | _, Some c when is_atom c -> ()
                        | _ -> failwith "No symbol follows after ,@")
                    in
                    (i', true)
            | _ -> (i, false)
        in
        let (i'', exp) = parse_exp i' quasiquote in
        match exp with
        | Some exp ->
                let op = "#:UNQUOTE" in
                let op = if splicing then op ^ "-SPLICING" else op in
                let exp = ExprList [ExprSymbol op; exp] in
                (i'', Some exp)
        | _ -> failwith ("No expression follows after " ^ (if splicing then ",@" else ","))
    in
    let rec parse exprs i =
        match parse_exp i false with
        | _, None -> List.rev exprs
        | i, Some expr -> parse (expr :: exprs) i
    in
    parse [] 0
