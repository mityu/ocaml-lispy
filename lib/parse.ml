open Lex
open Err

type node =
    NodeQuote of node
    | NodeQuasiquote of node
    | NodeUnquote of node
    | NodeUnquoteSplicing of node
    | NodeNil
    | NodeTrue
    | NodeInt of int
    | NodeString of string
    | NodeSymbol of string
    | NodeConsCell of node * node
    | NodeList of node list

let string_of_node node =
    let rec impl node acc =
        match node with
        | NodeQuote node -> impl node (acc ^ "'")
        | NodeQuasiquote node -> impl node (acc ^ "`")
        | NodeUnquote node -> impl node (acc ^ ",")
        | NodeUnquoteSplicing node -> impl node (acc ^ ",@")
        | NodeNil -> acc ^ "NIL"
        | NodeTrue -> acc ^ "T"
        | NodeInt v -> acc ^ string_of_int v
        | NodeString s -> Printf.sprintf "%s \"%s\"" acc s
        | NodeSymbol s -> acc ^ s
        | NodeConsCell (n1, n2) -> acc ^ Printf.sprintf "(%s . %s)" (impl n1 "") (impl n2 "")
        | NodeList nodes ->
                let s = nodes
                    |> List.map (fun n -> impl n "")
                    |> List.fold_left (fun acc s -> acc ^ " " ^ s) ""
                in
                acc ^ "(" ^ s ^ ")"
    in
    impl node ""

let rec parse_expr tokens =
    match tokens with
    | [] -> unreachable ()
    | hd :: tl ->
            (match hd with
            | TokenLParen -> parse_list tokens
            (*
            | TokenSingleQuote | TokenBackQuote | TokenComma ->
                    let (node, tokens) = parse_expr tl in
                    let node = (match hd, node with
                               | _, NodeNil -> NodeNil
                               | _, NodeInt v -> NodeInt v
                               | TokenSingleQuote, n -> NodeQuote n
                               | TokenBackQuote, n -> NodeSemiquote n
                               | TokenComma, n -> NodeUnsemiquote n
                               | _ -> unreachable ())
                    in
                    (node, tokens)
            *)
            | TokenSingleQuote ->
                    let (node, tokens) = parse_expr tl in
                    (NodeQuote node, tokens)
            | TokenBackQuote ->
                    let (node, tokens) = parse_expr tl in
                    (NodeQuasiquote node, tokens)
            | TokenComma ->
                    let (node, tokens) = parse_expr tl in
                    (NodeUnquote node, tokens)
            | TokenCommaAt ->
                    let (node, tokens) = parse_expr tl in
                    (NodeUnquoteSplicing node, tokens)
            | TokenInt v -> (NodeInt v, tl)
            | TokenString s -> (NodeString s, tl)
            | TokenSymbol s ->
                    (match s with
                    | "NIL" -> (NodeNil, tl)
                    | "T" -> (NodeTrue, tl)
                    | _ -> (NodeSymbol s, tl))
            | TokenRParen -> failwith "Too much closing bracket."
            | TokenColon -> failwith "Not implemented yet")
and parse_list tokens =
    let rec impl tokens children =
        match tokens with
        | [] -> failwith "Missing closing bracket"
        | TokenRParen :: tl ->
                (match children with
                | [] -> (NodeNil, tl)
                | _ -> (NodeList (List.rev children), tl))
        | TokenSymbol "." :: tl when List.length children = 1 ->  (* (SYMBOL . SYMBOL) *)
                let (node, tokens) = parse_expr tl in
                (match tokens with
                | TokenRParen :: tl -> (NodeConsCell (List.hd children, node), tl)
                | _ -> failwith "Invalid cons cell")
        | _ -> let (node, tokens) = parse_expr tokens in impl tokens (node :: children)
    in
    match tokens with
    | TokenLParen :: tl -> impl tl []
    | _ -> unreachable ()

let parse tokens =
    let rec impl tokens exprs =
        let (expr, tokens) = parse_expr tokens in
        match tokens with
        | [] -> List.rev (expr :: exprs)
        | _ -> impl tokens (expr :: exprs)
    in
    impl tokens []
