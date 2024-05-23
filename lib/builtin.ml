open Err
open Table
open Expr

let specific_required kind op e =
    let s = string_of_expr e in
    let m = kind ^ " required: " ^ s in
    if op = "" then
        failwith m
    else
        failwith (op ^ ": " ^ m)

let symbol_required = specific_required "Symbol"
let list_required = specific_required "List"
let int_required = specific_required "Int"

let ensure_symbol op expr =
    match expr with
    | ExprSymbol s -> s
    | _ -> symbol_required op expr

let ensure_list op expr =
    if is_list expr then
        list_of_clist expr
    else
        list_required op expr

let ensure_int op expr =
    match expr with
    | ExprInt v -> v
    | _ -> int_required op expr


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
    do_eval ExprNil eval env body

let f_gensym =
    let id = ref 0 in
    let gensym _ _ _ =
        let v = !id in
        let () = id := v + 1 in
        ExprSymbol ("#:GSYM:" ^ string_of_int v)
    in
    gensym

let f_list eval env args =
    let args = List.map (eval env) (list_of_clist args) in
    clist_of_list args

let f_car eval env args =
    let arg =
        match args with
        | ExprCons (e, ExprNil) -> e
        | _ -> unreachable ()
    in
    match eval env arg with
    | ExprCons (car, _) -> car
    | _ -> list_required "CAR" arg

let f_cdr eval env args =
    let arg =
        match args with
        | ExprCons (e, ExprNil) -> e
        | _ -> unreachable ()
    in
    match eval env arg with
    | ExprCons (_, cdr) -> cdr
    | _ -> list_required "CDR" arg

let f_cons eval env args =
    let (car, cdr) =
        match args with
        | ExprCons (car, ExprCons (cdr, ExprNil)) -> (car, cdr)
        | _ -> unreachable ()
    in
    let car = eval env car in
    let cdr = eval env cdr in
    ExprCons (car, cdr)

let f_append eval env args =
    let rec rev_append lhs rhs =
        match lhs with
        | ExprCons (e1, ExprNil) -> ExprCons (e1, rhs)
        | ExprCons (e1, e2) -> rev_append e2 (ExprCons (e1, rhs))
        | _ -> unreachable ()
    in
    let ensure_evaluated_in_list env exp =
        match eval env exp with
        | ExprCons (e1, e2) -> ExprCons (e1, e2)
        | _ -> list_required "APPEND" exp
    in
    let (lhs, rhs) =
        match list_of_clist args with
        | lhs :: rhs :: [] -> (lhs, rhs)
        | _ -> unreachable ()
    in
    let lhs = ensure_evaluated_in_list env lhs in
    let rhs = ensure_evaluated_in_list env rhs in
    rev_append (rev_clist lhs) rhs

let f_quote eval env args =
    let expr =
        match args with
        | ExprCons (e, ExprNil) -> e
        | _ -> unreachable ()
    in
    eval env (ExprSpOp (OpQuote expr))

let f_setq eval env args =
    let (denv, lenv) = env in
    let args = list_of_clist args in
    let () =
        if List.length args mod 2 != 0 then
            failwith ("SETQ: Odd number of arguments: " ^ string_of_expr @@ clist_of_list args)
    in
    let rec do_bind retval args =
        match args with
        | [] -> retval
        | symbol :: value :: tl ->
                let symbol = ensure_symbol "SETQ" symbol in
                let value = eval env value in
                let () =
                    (match ScopedTable.find lenv.lvars symbol with
                    | Some _ -> ScopedTable.replace_existing lenv.lvars symbol value
                    | None -> Table.set denv.vars symbol value)
                in
                do_bind value tl
        | _ -> unreachable ()
    in
    do_bind ExprNil args

let f_progn eval env args =
    let () =
        match args with
        | ExprNil -> unreachable ()
        | _ -> ()
    in
    let rec do_eval env args =
        match args with
        | ExprCons (e, ExprNil) -> eval env e
        | ExprCons (hd, tl) -> let () = ignore (eval env hd) in do_eval env tl
        | _ -> unreachable ()
    in
    do_eval env args

let f_if eval env args =
    let (cond, ifthen, ifelse) =
        match list_of_clist args with
        | e1 :: e2 :: e3 :: [] -> (e1, e2, e3)
        | _ -> unreachable ()
    in
    let cond = eval env cond in
    match cond with
    | ExprNil -> eval env ifelse
    | _ -> eval env ifthen

let f_defmacro _ env args =
    let (name, expr) =
        match args with
        | ExprCons (hd, tl) -> (hd, tl)
        | _ -> unreachable ()
    in
    let name = ensure_symbol "DEFMACRO" name in
    let () = Macro.define env name expr in
    ExprSymbol name

let (f_macroexpand_1, f_macroexpand) =
    let eval_args eval env args =
        let expr =
            match args with
            | ExprCons (e, ExprNil) -> e
            | _ -> unreachable ()
        in
        eval env expr
    in
    let find_macro table expr =
        let (name, args) =
            match expr with
            | ExprCons (e1, e2) -> (e1, e2)
            | _ -> unreachable ()
        in
        match name with
        | ExprSymbol name ->
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
        let find_macro table expr =
            match expr with
            | ExprCons _ -> find_macro table expr
            | _ -> None
        in
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
        match list_of_clist defs with
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
    ExprFn (name, lenv, params, body)

let f_defun _ env args =
    let (name, fndef) =
        match args with
        | ExprCons (name, fndef) -> (name, fndef)
        | _ -> unreachable ()
    in
    let name = ensure_symbol "DEFUN" name in
    let (params, body) = parse_function_definition ("DEFUN: " ^ name) fndef in
    let (denv, lenv) = env in
    let fn = ExprFn (name, lenv, params, body) in
    let () = Table.set denv.fns name fn in
    fn

let let_common recdef eval env args =
    let op = if recdef then "LET*" else "LET" in
    let (binds, body) =
        match args with
        | ExprCons (binds, body) -> (binds, body)
        | _ -> unreachable ()
    in
    let binds = ensure_list op binds in
    let binds =
        let ensure e =
            match e with
            | ExprCons (symbol, ExprCons (expr, ExprNil)) ->
                    let symbol = ensure_symbol op symbol in
                    (symbol, expr)
            | ExprCons (symbol, ExprNil) ->
                    let symbol = ensure_symbol op symbol in
                    (symbol, ExprNil)
            | _ -> failwith (op ^ ": List with 1 to 2 element(s) required: " ^ string_of_expr e)
        in
        List.map ensure binds
    in
    let (denv, lenv) = env in
    let lenv =
        if recdef then
            let do_bind eval env (name, value) =
                let value = eval env value in
                let (_, lenv) = env in
                ScopedTable.set lenv.lvars name value
            in
            let lenv = {lenv with lvars = ScopedTable.new_scope lenv.lvars} in
            let () = List.iter (do_bind eval (denv, lenv)) binds in
            lenv
        else
            let binds = List.map (fun (n, e) -> (n, eval env e)) binds in
            let lenv = {lenv with lvars = ScopedTable.new_scope lenv.lvars} in
            let () = List.iter (fun (n, v) -> ScopedTable.set lenv.lvars n v) binds
            in
            lenv
    in
    eval_body eval (denv, lenv) (list_of_clist body)

let f_let eval env args = let_common false eval env args
let f_letstar eval env args = let_common true eval env args

let flet_common recdef eval env args =
    let op = if recdef then "LABELS" else "FLET"
    in
    let (binds, body) =
        match args with
        | ExprCons (binds, body) -> (binds, body)
        | _ -> unreachable ()
    in
    let binds = ensure_list op binds in
    let binds =
        let err_invalid_bind expr = failwith (op ^ ": List with 2 to 3 elements required: " ^ string_of_expr expr)
        in
        let ensure e =
            match e with
            | ExprCons (symbol, ExprCons (params, expr)) ->
                    let expr = ensure_list op expr in
                    let symbol = ensure_symbol op symbol in
                    let params = ensure_list op params in
                    let params = List.map (ensure_symbol op) params in
                    let params = parse_fn_params params in
                    (symbol, params, expr)
            | _ -> err_invalid_bind e
        in
        List.map ensure binds
    in
    let (denv, lenv) = env in
    let lenv =
        let lenv' = {lenv with lfns = ScopedTable.new_scope lenv.lfns}  in
        let do_bind lenv (symbol, params, expr) =
            let fn = ExprFn (symbol, lenv, params, expr) in
            ScopedTable.set lenv'.lfns symbol fn
        in
        if recdef then
            let () = List.iter (do_bind lenv') binds in
            lenv'
        else
            let () = List.iter (do_bind lenv) binds in
            lenv'
    in
    eval_body eval (denv, lenv) (list_of_clist body)

let f_flet eval env args = flet_common false eval env args
let f_labels eval env args = flet_common true eval env args

let f_eval eval env args =
    let expr =
        match args with
        | ExprCons (e, ExprNil) -> e
        | _ -> unreachable ()
    in
    eval env expr

let f_add eval env args =
    let args = List.map (eval env) (list_of_clist args) in
    let args = List.map (ensure_int "ADD") args in
    let v = List.fold_left ( + ) 0 args in
    ExprInt v

let f_sub eval env args =
    let args = List.map (eval env) (list_of_clist args) in
    let args = List.map (ensure_int "ADD") args in
    let (seed, args) =
        match args with
        | v :: [] -> (0, [v])
        | hd :: tl -> (hd, tl)
        | [] -> unreachable ()
    in
    let v = List.fold_left ( - ) seed args in
    ExprInt v

let f_mul eval env args =
    let args = List.map (eval env) (list_of_clist args) in
    let args = List.map (ensure_int "ADD") args in
    let v = List.fold_left ( * ) 1 args in
    ExprInt v

let f_and eval env args =
    let args = list_of_clist args in
    let rec calc retval exprs =
        match exprs with
        | [] -> retval
        | hd :: tl ->
                (match eval env hd with
                | ExprNil -> ExprNil
                | v -> calc v tl)
    in
    calc ExprT args

let f_or eval env args =
    let args = list_of_clist args in
    let rec calc exprs =
        match exprs with
        | [] -> ExprNil
        | hd ::tl ->
                (match eval env hd with
                | ExprNil -> calc tl
                | v -> v)
    in
    calc args

let f_eql eval env args  =
    let (lhs, rhs) =
        match args with
        | ExprCons (lhs, ExprCons (rhs, ExprNil)) -> (lhs, rhs)
        | _ -> unreachable ()
    in
    let lhs = eval env lhs in
    let rhs = eval env rhs in
    if lhs = rhs then
        ExprT
    else
        ExprNil

let lt_common name op eval env args =
    let args = list_of_clist args in
    let args = List.map (eval env) args in
    let args = List.map (ensure_int name) args in
    let rec fold args =
        match args with
        | _ :: [] -> ExprT
        | e1 :: e2 :: tl ->
                if op e1 e2 then
                    fold (e2 :: tl)
                else
                    ExprNil
        | _ -> unreachable ()
    in
    fold args

let f_lt eval env args = lt_common "<" ( < ) eval env args
let f_lte eval env args = lt_common "<=" ( <= ) eval env args

let f_apply eval env args =
    let construct_args args =
        let args = List.rev args in
        let (l, rest) =
            match args with
            | l :: rest -> (l, rest)
            | _ -> unreachable ()
        in
        let () = if Bool.not @@ is_list l then list_required "APPLY" l
        in
        let rec construct acc rest =
            match rest with
            | [] -> acc
            | hd :: tl -> construct (ExprCons (hd, acc)) tl
        in
        construct l rest
    in
    let args = List.map (eval env) (list_of_clist args) in
    let (fn, args) =
        match args with
        | fn :: args -> (fn, args)
        | _ -> unreachable ()
    in
    let (fn, env') =
        match fn with
        | ExprBuiltinFn fn -> (ExprSymbol ("#:" ^ fn), env)
        | ExprFn fn ->
                (* Make "..." must points to the desired function *)
                let name = f_gensym eval env ExprNil in
                let name = ensure_symbol "APPEND: unreachable:" name in
                let (denv, lenv) = env in
                let lenv' = {lenv with lfns = ScopedTable.new_scope lenv.lfns} in
                let () = ScopedTable.set lenv'.lfns name (ExprFn fn) in
                (ExprSymbol name, (denv, lenv'))
        | _ ->
                let s = string_of_expr fn in
                failwith ("APPLY: a function is required for the first argument: " ^ s)
    in
    let args = construct_args args in
    eval env' (ExprCons (fn, args))


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
    ("FLET", (f_flet, Some 1, None));
    ("LABELS", (f_labels, Some 1, None));
    ("IF", (f_if, Some 3, Some 3));
    ("PROGN", (f_progn, Some 1, None));
    ("SETQ", (f_setq, Some 2, None));
    ("+", (f_add, Some 1, None));
    ("-", (f_sub, Some 1, None));
    ("*", (f_mul, Some 1, None));
    ("AND", (f_and, None, None));
    ("OR", (f_or, None, None));
    ("EQL", (f_eql, Some 2, Some 2));
    ("<", (f_lt, Some 1, None));
    ("<=", (f_lte, Some 1, None));
    ("APPLY", (f_apply, Some 2, None));
]

let find name = List.assoc_opt name fn_table
