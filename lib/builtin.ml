open Expr
open Table
open Err

let specific_required kind op e =
    let s = string_of_expr e in
    let m = kind ^ " required: " ^ s in
    if op = "" then
        failwith m
    else
        failwith (op ^ ": " ^ m)

let symbol_required = specific_required "Symbol"
let list_required = specific_required "List"

let ensure_symbol op expr =
    match expr with
    | ExprSymbol s -> s
    | _ -> symbol_required op expr

let ensure_list op expr =
    match expr with
    | ExprList l -> l
    | _ -> list_required op expr


let is_generated_symbol = String.starts_with ~prefix:"#:GSYM:"

let is_builtin_fn_symbol s =
    let open String in
    let open Bool in
    starts_with ~prefix:"#:" s && (not (is_generated_symbol s))


let list_duplicate_items _ = todo ()

let eval_body eval env body =
    let rec do_eval retval eval env body =
        match body with
        | [] -> retval
        | hd :: tl -> do_eval (eval env hd) eval env tl
    in
    do_eval (ExprList []) eval env body

let f_gensym =
    let id = ref 0 in
    let gensym _ _ _ =
        let v = !id in
        let () = id := v + 1 in
        ExprSymbol ("#:GSYM:" ^ string_of_int v)
    in
    gensym

let f_list eval env args =
    let args = List.map (eval env) args in
    ExprList args

let f_car eval env args =
    let expr =
        match args with
        | expr :: [] -> expr
        | _ -> unreachable ()
    in
    match eval env expr with
    | ExprList l ->
            (match l with
            | [] -> ExprList []
            | hd :: _ -> hd)
    | _ -> list_required "CAR" expr

let f_cdr eval env args =
    let expr =
        match args with
        | expr :: [] -> expr
        | _ -> unreachable ()
    in
    match eval env expr with
    | ExprList l ->
            (match l with
            | [] -> ExprList []
            | _ :: tl -> ExprList tl)
    | _ -> list_required "CDR" expr

let f_cons eval env args =
    let (car, cdr) =
        match args with
        | car :: cdr :: [] -> (car, cdr)
        | _ -> unreachable ()
    in
    let car = eval env car in
    let cdr = eval env cdr in
    let cdr = ensure_list "CONS" cdr in
    ExprList (car :: cdr)

let f_append eval env args =
    let ensure_evaluated_in_list env exp =
        match eval env exp with
        | ExprList l -> l
        | _ -> list_required "APPEND" exp
    in
    let (lhs, rhs) =
        match args with
        | lhs :: rhs :: [] -> (lhs, rhs)
        | _ -> unreachable ()
    in
    let lhs = ensure_evaluated_in_list env lhs in
    let rhs = ensure_evaluated_in_list env rhs in
    ExprList (List.append lhs rhs)

let f_quote eval env args =
    let rec unquote_in_list acc eval env exprs =
        let do_unquote splicing expr tl =
            let expr =
                match expr with
                | e :: [] -> e
                | _ -> unreachable ()
            in
            let tl = unquote_in_list [] eval env tl in
            let expr = eval env expr in
            if splicing then
                ExprList [ExprSymbol "#:APPEND"; expr; tl]
            else
                ExprList [ExprSymbol "#:CONS"; expr; tl]
        in
        match exprs with
        | [] -> ExprList (List.rev acc)
        | ExprList (ExprSymbol "#:UNQUOTE" :: expr) :: tl ->
                do_unquote false expr tl
        | ExprList (ExprSymbol "#:UNQUOTE-SPLICING" :: expr) :: tl ->
                do_unquote true expr tl
        | hd :: tl -> unquote_in_list (hd :: acc) eval env tl
    in
    let unquote eval env expr =
        match expr with
        | ExprList (ExprSymbol "#:UNQUOTE" :: tl) ->  (* Handles `,x *)
                (match tl with
                | expr :: [] -> eval env expr
                | _ -> unreachable ())
        | ExprList (ExprSymbol "#:UNQUOTE-SPLICING" :: _) ->  (* Handles `,@x *)
                failwith "Synbax `,@form is invalid"
        | ExprList l ->  (* Handles `(... ,x ...) *)
                unquote_in_list [] eval env l
        | ExprCons _ -> todo ()  (* TODO: fix this when we introduce cons list *)
        | _ -> expr
    in
    let expr = List.hd args in
    unquote eval env expr

let f_setq eval env args =
    let (denv, lenv) = env in
    let (symbol, value) =
        match args with
        | e1 :: e2 :: [] -> (e1, e2)
        | _ -> unreachable ()
    in
    let symbol = ensure_symbol "SETQ" symbol in
    let value = eval env value in
    let () =
        match ScopedTable.find lenv symbol with
        | Some _ -> ScopedTable.replace_existing lenv symbol value
        | None -> Table.set denv.vars symbol value
    in
    value

let f_progn eval env args =
    let () =
        match args with
        | [] -> unreachable ()
        | _ -> ()
    in
    let rec do_eval env args =
        match args with
        | [] -> unreachable ()
        | e :: [] -> eval env e
        | hd :: tl -> let () = ignore (eval env hd) in do_eval env tl
    in
    do_eval env args

let f_if eval env args =
    let (cond, ifthen, ifelse) =
        match args with
        | e1 :: e2 :: e3 :: _ -> (e1, e2, e3)
        | _ -> unreachable ()
    in
    let cond = eval env cond in
    match cond with
    | ExprList [] -> eval env ifelse
    | _ -> eval env ifthen

let f_defmacro _ env args =
    let (name, expr) =
        match args with
        | hd :: tl -> (hd, tl)
        | _ -> unreachable ()
    in
    let name = ensure_symbol "DEFMACRO" name in
    let () = Macro.define env name expr in
    ExprSymbol name

let (f_macroexpand_1, f_macroexpand) =
    let eval_args eval env args =
        let expr =
            match args with
            | e :: [] -> e
            | _ -> unreachable ()
        in
        eval env expr
    in
    let find_macro table expr =
        let elems =
            match expr with
            | ExprList l -> l
            | _ -> unreachable ()
        in
        match elems with
        | ExprSymbol name :: args ->
                (match Table.find table name with
                | Some (ExprMacro _) -> Some (name, args)
                | _ -> None)
        | _ -> None
    in
    let macroexpand_1 eval env args =
        let expr = eval_args eval env args in
        let (denv, _) = env in
        match find_macro denv.fns expr with
        | Some (name, args) -> Macro.apply eval env name args
        | _ -> expr
    in
    let macroexpand eval env args =
        let rec do_expand table expr =
            match find_macro table expr with
            | Some (name, args) ->
                    let expr = Macro.apply eval env name args in
                    do_expand table expr
            | _ -> expr
        in
        let expr = eval_args eval env args in
        let (denv, _) = env in
        do_expand denv.fns expr
    in
    (macroexpand_1, macroexpand)

let parse_fn_params params =
    let rec do_parse acc params =
        match params with
        | [] -> (List.rev acc, None)
        | hd :: tl ->
                if hd = "&REST" then
                    (match tl with
                    | rest :: [] -> (List.rev acc, Some rest)
                    | _ -> failwith "One symbol required after \"&REST\"")
                else
                    do_parse (hd :: acc) tl
    in
    do_parse [] params

let parse_function_definition op defs =
    let (params, body) =
        match defs with
        | hd :: tl -> (hd, tl)
        | _ -> unreachable ()
    in
    let params = ensure_list op params in
    let params = List.map (ensure_symbol op) params in
    (* TODO: Check for duplicate symbols in parameter list *)
    let params = parse_fn_params params in
    (params, body)

let gen_lambda_id =
    let id = ref 0 in
    let gen () =
        let v = !id in
        let () = id := v + 1 in
        v
    in
    gen

let f_lambda _ env args =
    let (params, body) = parse_function_definition "LAMBDA" args in
    let (_, lenv) = env in
    let name = "LAMBDA-" ^ string_of_int @@ gen_lambda_id () in
    ExprFn (name, ref lenv, params, body)

let f_defun _ env args =
    let (name, fndef) =
        match args with
        | name :: fndef -> (name, fndef)
        | _ -> unreachable ()
    in
    let name = ensure_symbol "DEFUN" name in
    let (params, body) = parse_function_definition ("DEFUN: " ^ name) fndef in
    let (denv, lenv) = env in
    let fn = ExprFn (name, ref lenv, params, body) in
    let () = Table.set denv.fns name fn in
    fn

let let_common recdef eval env args =
    let op = if recdef then "LET*" else "LET" in
    let (binds, body) =
        match args with
        | binds :: body -> (binds, body)
        | _ -> unreachable ()
    in
    let binds = ensure_list op binds in
    let binds =
        let ensure e =
            match e with
            | ExprList (symbol :: expr :: []) ->
                    let symbol = ensure_symbol op symbol in
                    (symbol, expr)
            | _ -> failwith (op ^ ": List with two elements required: " ^ string_of_expr e)
        in
        List.map ensure binds
    in
    (* TODO: Check variable duplicates *)
    let (denv, lenv) = env in
    let lenv =
        if recdef then
            let do_bind eval env (name, value) =
                let value = eval env value in
                let (_, lenv) = env in
                ScopedTable.set lenv name value
            in
            let lenv = ScopedTable.new_scope lenv in
            let () = List.iter (do_bind eval env) binds in
            lenv
        else
            let binds = List.map (fun (n, e) -> (n, eval env e)) binds in
            let lenv = ScopedTable.new_scope lenv in
            let () = List.iter (fun (n, v) -> ScopedTable.set lenv n v) binds
            in
            lenv
    in
    eval_body eval (denv, lenv) body

let f_let eval env args = let_common false eval env args
let f_letstar eval env args = let_common true eval env args

let f_eval eval env args =
    let expr =
        match args with
        | e :: [] -> e
        | _ -> unreachable ()
    in
    eval env expr

let fn_table = [
    ("GENSYM", (f_gensym, Some 0, Some 0));
    ("DEFMACRO", (f_defmacro, Some 2, None));
    ("MACROEXPAND-1", (f_macroexpand_1, Some 1, Some 1));
    ("MACROEXPAND", (f_macroexpand, Some 1, Some 1));
    ("CAR", (f_car, Some 1, Some 1));
    ("CDR", (f_cdr, Some 1, Some 1));
    ("CONS", (f_cons, Some 2, Some 2));
    ("APPEND", (f_append, Some 2, Some 2));
    ("LIST", (f_list, None, None));
    ("QUOTE", (f_quote, Some 1, None));
    ("EVAL", (f_eval, Some 1, Some 1));
    ("LAMBDA", (f_lambda, Some 1, None));
    ("DEFUN", (f_defun, Some 2, None));
    ("LET", (f_let, Some 1, None));
    ("LET*", (f_letstar, Some 1, None));
    ("IF", (f_if, Some 3, Some 3));
    ("PROGN", (f_progn, Some 1, None));
    ("SETQ", (f_setq, Some 2, Some 2));
]

let find name = List.assoc_opt name fn_table
