open Err
open Parse

type expr =
    | ExprNil
    | ExprTrue
    | ExprInt of int
    | ExprString of string
    | ExprSymbol of string
    | ExprConsCell of expr * expr
    | ExprList of expr list
    | ExprFn of fn
    | ExprQuote of expr
    | ExprQuasiquote of expr
    | ExprUnquote of expr
    | ExprUnquoteSplicing of expr
and env = {fns: fn Env.t; vars: expr Env.t; macros: macro Env.t}
and fn = env * string list * expr list  (* (env, params, body) *)
and macro = string list * expr

type datamode =
    | ModeProgram
    | ModeQuote
    | ModeQuasiquote

let rec expr_of_node n =
    match n with
    | NodeQuote node -> ExprQuote (expr_of_node node)
    | NodeQuasiquote node -> ExprQuasiquote (expr_of_node node)
    | NodeUnquote node -> ExprUnquote (expr_of_node node)
    | NodeUnquoteSplicing node -> ExprUnquoteSplicing (expr_of_node node)
    | NodeNil -> ExprNil
    | NodeTrue -> ExprTrue
    | NodeInt v -> ExprInt v
    | NodeString s -> ExprString s
    | NodeSymbol s -> ExprSymbol s
    | NodeConsCell (n1, n2) -> ExprConsCell (expr_of_node n1, expr_of_node n2)
    | NodeList nodes -> ExprList (List.map expr_of_node nodes)

let string_of_expr expr =
    let open Printf in
    let concat_strings l =
        let s = List.fold_left (fun acc s -> acc ^ s ^ " ") "" l in
        String.sub s 0 (String.length s - 1)
    in
    let rec impl acc expr =
        match expr with
        | ExprQuote expr -> impl (acc ^ "'") expr
        | ExprQuasiquote expr -> impl (acc ^ "`") expr
        | ExprUnquote expr -> impl (acc ^ ",") expr
        | ExprUnquoteSplicing expr -> impl (acc ^ ",@") expr
        | ExprNil -> acc ^ "NIL"
        | ExprTrue -> acc ^ "T"
        | ExprInt v -> acc ^ string_of_int v
        | ExprString s -> sprintf "%s \"%s\"" acc s
        | ExprSymbol s -> acc ^ s
        | ExprConsCell (n1, n2) -> acc ^ sprintf "(%s . %s)" (impl "" n1) (impl "" n2)
        | ExprList exprs ->
                let s = concat_strings (List.map (fun e -> impl "" e) exprs) in
                acc ^ "(" ^ s ^ ")"
        | ExprFn fn ->
            let (_, args, body) = fn in
            let args = concat_strings args in
            let body = concat_strings (List.map (impl "") body) in
            sprintf "(lambda (%s)\n%s)" args body
    in
    impl "" expr

let empty_env = {
    fns = Env.empty;
    vars = Env.empty;
    macros = Env.empty;
}

let new_scope env = {
    fns = Env.new_scope env.fns;
    vars = Env.new_scope env.vars;
    macros = Env.new_scope env.macros;
}

let no_such_symbol s = failwith ("No such symbol: " ^ s)
let symbol_required e = failwith ("Symbol required: " ^ string_of_expr e)

let ensure_symbol e =
    match e with
    | ExprSymbol s -> s
    | _ -> symbol_required e
let ensure_list e =
    match e with
    | ExprList l -> l
    | ExprNil -> []
    | _ -> failwith ("List required: " ^ string_of_expr e)

let lookup_symbol env symbol =
    if String.starts_with ~prefix:"#'" symbol then
        let symbol = String.sub symbol 2 (String.length symbol - 2) in
        let fn = Env.find env.fns symbol in
        match fn with
        | None -> None
        | Some fn -> Some (ExprFn fn)
    else
        Env.find env.vars symbol

let builtin_defmacro env args =
    match args with
    | name :: args :: body :: [] ->
            let name = ensure_symbol name in
            let args = List.map ensure_symbol (ensure_list args) in
            let () = Env.add env.macros name (args, body) in
            ExprSymbol name
    | _ -> unreachable ()

let builtin_lambda env args =
    match args with
    | args :: body ->
            let args = List.map ensure_symbol (ensure_list args) in
            ExprFn (env, args, body)
    | _ -> unreachable ()

let builtin_defun env args =
    match args with
    | name :: args :: body ->
            let name = ensure_symbol name in
            let fn = builtin_lambda env (args :: body) in
            let fn = (match fn with ExprFn fn -> fn | _ -> unreachable ()) in
            let () = Env.add env.fns name fn in
            ExprSymbol name
    | _ -> unreachable ()

let builtin_gensym =
    let id = ref 0 in
    let gensym _ _ =
        let v = !id in
        let () = id := v + 1 in
        ExprSymbol ("#:GS" ^ string_of_int v)
    in
    gensym

let pick_list_from_top_of_args fn_name evalfn args =
    let e =
        match args with
        | e :: [] -> evalfn e
        | _ -> unreachable ()
    in
    let l =
        match e with
        | ExprNil -> []
        | ExprList l -> l
        | _ -> failwith @@ Printf.sprintf "%s: %s is not a list" fn_name (string_of_expr e)
    in
    l

let builtin_quote _ args =
    let expr =
        match args with
        | e :: [] -> e
        | _ -> unreachable ()
    in
    ExprQuote expr

let rec eval_one env mode expr =
    match expr with
    | ExprSymbol s ->
            (match mode with
            | ModeProgram ->
                    let v = lookup_symbol env s in
                    (match v with
                    | None -> no_such_symbol s
                    | Some v -> v)
            | _ -> expr)
    | ExprList l -> (* Macro or function application *)
            (match mode with
            | ModeQuote -> expr
            | ModeQuasiquote -> eval_unquote env expr
            | ModeProgram ->
                    (match l with
                    | [] -> unreachable ()
                    | name :: args ->
                            let name = ensure_symbol name in
                            if String.starts_with ~prefix:"BUILTIN-" name then
                                (* Call built-in function *)
                                apply_builtin_fn env name args
                            else
                                let macro = Env.find env.macros name in
                                let fn = Env.find env.fns name in
                                (match macro, fn with
                                | Some macro, _ -> eval_macro_application name env macro args
                                | _, Some fn -> eval_fn_application env fn args
                                | _ -> no_such_symbol name)))
    | ExprQuote child ->
            (match mode with
            | ModeQuasiquote -> ExprQuote (eval_one env mode child)
            | _ -> expr)
    | ExprQuasiquote child ->
            (match mode with
            | ModeProgram -> ExprQuote (eval_one env ModeQuasiquote child)
            | _ -> expr)
    | ExprConsCell (lhs, rhs) ->
            (match mode with
            | ModeQuote -> expr
            | _ ->
                    let lhs = eval_one env mode lhs in
                    let rhs = eval_one env mode rhs in
                    ExprConsCell (lhs, rhs))
    | ExprUnquote _ | ExprUnquoteSplicing _ -> failwith "Comma is illegal outside of backquote"
    | _ -> expr
and eval_unquote env expr =
    match expr with
    | ExprUnquote expr' -> eval_one env ModeProgram expr'
    | ExprUnquoteSplicing _ -> failwith "Invalid use of ,@ here"
    | ExprList l ->
            let rec unquote acc l =
                (match l with
                | [] -> List.rev acc
                | hd :: tl ->
                        (match hd with
                        | ExprUnquoteSplicing e ->
                                let v = eval_one env ModeProgram e in
                                (match v with
                                | ExprList l -> unquote ((List.rev l) @ acc) tl
                                | _ -> failwith "List required for splicing unquote.")
                        | _ -> unquote ((eval_unquote env hd) :: acc) tl))
            in
            ExprList (unquote [] l)
    | ExprConsCell (lhs, rhs) ->
            let lhs = eval_unquote env lhs in
            let rhs = eval_unquote env rhs in
            ExprConsCell (lhs, rhs)
    | _ -> expr
and eval_macro_application name env macro args =
    let parse_params params =
        let rec parse params single =
            match params with
            | [] -> (List.rev single, None)
            | hd :: tl ->
                    if hd = "&BODY" then
                        (match tl with
                        | [] -> failwith "Symbol required after \"&body\""
                        | rest :: [] -> (List.rev single, Some rest)
                        | _ -> failwith "Must be one symbol after \"&body\"")
                    else
                        parse tl (hd :: single)
        in
        parse params []
    in
    let (params, body) = macro in
    let (params, vaparam) = parse_params params in
    let () =
        let nargs = List.length args in
        let nparams = List.length params in
        let err () =
            let msg = Printf.sprintf "%s macro may not be called with %d arguments." name nargs
            in
            failwith msg
        in
        match vaparam with
        | Some _ -> if nargs < nparams then err ()
        | None -> if nargs != nparams then err ()
    in
    let env' = new_scope env in
    let () =
        let rec bind_args params vaparam args =
            match params, args with
            | phd :: ptl, ahd :: atl ->
                    let () = Env.add env'.vars phd ahd in
                    bind_args ptl vaparam atl
            | [], args ->
                    let arg =
                        (match args with
                        | [] -> ExprNil
                        | _ -> ExprList args)
                    in
                    (match vaparam with
                    | Some vaparam -> Env.add env'.vars vaparam arg
                    | None -> ())
            | _ -> ()
        in
        bind_args params vaparam args
    in
    let body' = eval_one env' ModeProgram body in
    let body' =
        match body' with
        | ExprQuote e | ExprQuasiquote e -> e
        | ExprList (ExprSymbol "BUILTIN-QUOTE" :: args) -> ExprList args
        | _ -> body'
    in
    let r = eval_one env ModeProgram body'
    in
    r
and eval_fn_application env fn args =
    (* Handles function application and returns result of function call or partial function *)
    let (fenv, params, body) = fn in
    let nargs = List.length args in
    let nparams = List.length params in
    let () = if nargs > nparams then failwith "Too much arguments" in
    let args = List.map (eval_one env ModeProgram) args in
    let fenv = new_scope fenv in
    let rec call_or_partial params args =
        match params, args with
        | phd :: ptl, ahd :: atl ->
                let () = Env.add fenv.vars phd (eval_one env ModeProgram ahd) in
                call_or_partial ptl atl
        | [], [] -> (* Call function *)
            let vals = List.map (eval_one fenv ModeProgram) body in
            (match vals with
            | [] -> ExprNil
            | _ ->
                    let v = List.hd (List.rev vals) in
                    (match v with
                    | ExprQuote e | ExprQuasiquote e -> e
                    | _ -> v))
        | _, [] -> (* Create partial *)
                ExprFn (fenv, params, body)
        | _ -> unreachable ()
    in
    call_or_partial params args
and apply_builtin_fn env name args =
    let fns = [
        ("BUILTIN-QUOTE", (builtin_quote, Some 1, Some 1));
        ("BUILTIN-GENSYM", (builtin_gensym, Some 0, Some 0));
        ("BUILTIN-DEFMACRO", (builtin_defmacro, Some 3, Some 3));
        ("BUILTIN-LAMBDA", (builtin_lambda, Some 1, None));
        ("BUILTIN-DEFUN", (builtin_defun, Some 2, None));
        ("BUILTIN-LET", (builtin_let, Some 2, None));
        ("BUILTIN-LET*", (builtin_letstar, Some 2, None));
        ("BUILTIN-FLET", (builtin_flet, Some 2, None));
        ("BUILTIN-LABELS", (builtin_labels, Some 2, None));
        ("BUILTIN-CAR", (builtin_car, Some 1, Some 1));
        ("BUILTIN-CDR", (builtin_cdr, Some 1, Some 1));
        ("BUILTIN-EVAL", (builtin_eval, Some 1, Some 1));
        ("BUILTIN-IF", (builtin_if, Some 3, Some 3));
        ("BUILTIN-EQL", (builtin_eql, Some 2, Some 2));
        ("BUILTIN-ADD", (builtin_add, Some 2, Some 2));
        ("BUILTIN-SUB", (builtin_sub, Some 2, Some 2));
        ("BUILTIN-LT", (builtin_lt, Some 2, Some 2));
        ("BUILTIN-LTE", (builtin_lte, Some 2, Some 2));
        ("BUILTIN-AND", (builtin_and, None, None));
        ("BUILTIN-OR", (builtin_or, None, None));
    ] in
    let fn = List.assoc_opt name fns in
    let fn =
        match fn with
        | None -> failwith ("No such function: " ^ name)
        | Some fn -> fn
    in
    let (f, nargs_inf, nargs_sup) = fn in
    let nargs = List.length args in
    let () =
        let ok_inf =
            match nargs_inf with
            | None -> true
            | Some v -> nargs >= v
        in
        let ok_sup =
            match nargs_sup with
            | None -> true
            | Some v -> nargs <= v
        in
        if Bool.not (ok_inf && ok_sup) then
            failwith (Printf.sprintf "%s may not be called with %d arguments." name nargs)
    in
    f env args
and builtin_let_common recdef env args =
    let fn_name = if recdef then "LET*" else "LET" in
    let get_bind_pair env l =
        let l =
            match l with
            | ExprList l -> l
            | _ -> failwith ("List required for each bind of " ^ fn_name)
        in
        let (name, value) =
            match l with
            | (ExprSymbol name) :: value :: [] -> (name, value)
            | _ :: _ :: [] -> symbol_required (List.hd l)
            | _ -> failwith (Printf.sprintf "%s may not called with %d arguments." fn_name (List.length l))
        in
        let value = eval_one env ModeProgram value in
        (name, value)
    in
    let do_bind env (name, value) = Env.add env.vars name value in
    let (binds, body) =
        match args with
        | ExprList binds :: body -> (binds, body)
        | _ :: _ -> failwith ("List required for binds of " ^ fn_name)
        | [] -> unreachable ()
    in
    let env' = new_scope env in
    let () =
        if recdef then
            binds |> List.iter (fun e -> do_bind env' (get_bind_pair env' e))
        else
            binds
                |> List.map (get_bind_pair env')
                |> List.iter (do_bind env')
    in
    let vals = List.map (eval_one env' ModeProgram) body in
    match vals with
    | [] -> ExprNil
    | _ -> List.hd (List.rev vals)
and builtin_let env args = builtin_let_common false env args
and builtin_letstar env args = builtin_let_common true env args
and builtin_flet_common recdef env args =
    let fn_name = if recdef then "LABELS" else "FLET" in
    let get_bind_pair env e =
        let e =
            match e with
            | ExprList e -> e
            | _ -> failwith ("List required for each bind of " ^ fn_name)
        in
        let (name, args, body) =
            match e with
            | ExprSymbol name :: ExprList args :: body -> (name, args, body)
            | _ :: ExprList _ :: _ -> symbol_required (List.hd e)
            | _ :: _ :: _ -> failwith "List required for parameter defenition"
            | _ ->
                    let l = string_of_expr (ExprList e) in
                    failwith (Printf.sprintf "Invalid bind for %s: %s" fn_name l)
        in
        let args = List.map ensure_symbol args in
        let fn = (env, args, body) in
        (name, fn)
    in
    let do_bind env name fn = Env.add env.fns name fn in
    let (binds, body) =
        match args with
        | ExprList binds :: body -> (binds, body)
        | _ :: _ -> failwith ("List required for bind of " ^ fn_name)
        | _ -> unreachable ()
    in
    let env' =
        if recdef then
            let env' = new_scope env in
            let () = binds
                |> List.map (get_bind_pair env')
                |> List.iter (fun (name, fn) -> do_bind env' name fn)
            in
            env'
        else
            let binds = List.map (fun b -> get_bind_pair (new_scope env) b) binds in
            let env' = new_scope env in
            let () = List.iter (fun (name, fn) -> do_bind env' name fn) binds in
            env'
    in
    let vals = List.map (eval_one env' ModeProgram) body in
    match vals with
    | [] -> ExprNil
    | _ -> List.hd (List.rev vals)
and builtin_flet env args = builtin_flet_common false env args
and builtin_labels env args = builtin_flet_common true env args
and builtin_eval env args =
    let expr =
        match args with
        | e :: [] -> e
        | _ -> unreachable ()
    in
    let expr =
        match expr with
        | ExprQuote e -> e
        | ExprQuasiquote e -> eval_one env ModeProgram e
        | e -> e
    in
    print_endline @@ string_of_expr expr;
    eval_one env ModeProgram expr
and builtin_car env args =
    let l = pick_list_from_top_of_args "CAR" (eval_one env ModeProgram) args in
    match l with
    | [] -> ExprNil
    | hd :: _ -> hd
and builtin_cdr env args =
    let l = pick_list_from_top_of_args "CDR" (eval_one env ModeProgram) args in
    match l with
    | [] | _ :: [] -> ExprNil
    | _ :: tl -> ExprList tl
and builtin_eql env args =
    let (e1, e2) =
        match args with
        | e1 :: e2 :: [] -> (e1, e2)
        | _ -> unreachable ()
    in
    let e1 = eval_one env ModeProgram e1 in
    let e2 = eval_one env ModeProgram e2 in
    if e1 = e2 then
        ExprTrue
    else
        ExprNil
and builtin_if env args =
    let (cond, e1, e2) =
        match args with
        | cond :: e1 :: e2 :: [] -> (cond, e1, e2)
        | _ -> unreachable ()
    in
    let cond = eval_one env ModeProgram cond in
    if cond != ExprNil then
        eval_one env ModeProgram e1
    else
        eval_one env ModeProgram e2
and builtin_arithmetic op env args =
    let args = List.map (eval_one env ModeProgram) args in
    match args with
    | ExprInt v1 :: ExprInt v2 :: [] -> ExprInt (op v1 v2)
    | _ -> failwith ("Requires 2 integers: " ^ string_of_expr (ExprList args))
and builtin_add env args = builtin_arithmetic ( + ) env args
and builtin_sub env args = builtin_arithmetic ( - ) env args
and builtin_conditional op env args =
    let args = List.map (eval_one env ModeProgram) args in
    match args with
    | ExprInt v1 :: ExprInt v2 :: [] -> if op v1 v2 then ExprTrue else ExprNil
    | _ -> failwith ("Requires 2 integers: " ^ string_of_expr (ExprList args))
and builtin_lt env args = builtin_conditional ( < ) env args
and builtin_lte env args = builtin_conditional ( <= ) env args
and builtin_and env args =
    let rec impl env args =
        match args with
        | [] -> ExprTrue
        | e :: [] -> eval_one env ModeProgram e
        | hd :: tl ->
                (match eval_one env ModeProgram hd with
                | ExprNil -> ExprNil
                | _ -> impl env tl)
    in
    impl env args
and builtin_or env args =
    let rec impl env args =
        match args with
        | [] -> ExprNil
        | e :: [] -> eval_one env ModeProgram e
        | hd :: tl ->
                (match eval_one env ModeProgram hd with
                | ExprNil -> impl env tl
                | v -> v)
    in
    impl env args



let eval env nodes =
    let exprs = List.map expr_of_node nodes in
    (env, List.map (eval_one env ModeProgram) exprs)
