open Err
open Expr

let unique_id_generator () =
    let id = ref 0 in
    let gen () =
        let v = !id in
        let () = id := v + 1 in
        v
    in
    gen

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

let eval_body eval env body cont =
    let rec do_eval retval eval env body cont =
        match body with
        | [] -> cont retval
        | hd :: tl -> eval env hd (fun hd -> do_eval hd eval env tl cont)
    in
    do_eval ExprNil eval env body cont

let gensym =
    let genid = unique_id_generator () in
    let gensym () =
        "#:GSYM:" ^ string_of_int (genid ())
    in
    gensym

(* Builtin functions *)
let f_gensym _ _ _ cont = cont (ExprSymbol (gensym ()))

let f_list _ _ args cont = cont @@ clist_of_list args

let f_car _ _ args cont =
    let arg =
        match args with
        | [e] -> e
        | _ -> unreachable ()
    in
    match arg with
    | ExprCons (car, _) -> cont car
    | ExprNil -> cont ExprNil
    | _ -> list_required "CAR" arg

let f_cdr _ _ args cont =
    let arg =
        match args with
        | [e] -> e
        | _ -> unreachable ()
    in
    match arg with
    | ExprCons (_, cdr) -> cont cdr
    | ExprNil -> cont ExprNil
    | _ -> list_required "CDR" arg

let f_cons _ _ args cont =
    let (car, cdr) =
        match args with
        | car :: cdr :: [] -> (car, cdr)
        | _ -> unreachable ()
    in
    cont (ExprCons (car, cdr))

let f_append _ _ args cont =
    let ensure_list v = if is_list v then () else list_required "APPEND" v in
    let rec rev_append lhs rhs =
        match lhs with
        | ExprNil -> rhs
        | ExprCons (e1, e2) -> rev_append e2 (ExprCons (e1, rhs))
        | _ -> unreachable ()
    in
    let (lhs, rhs) =
        match args with
        | lhs :: rhs :: [] -> (lhs, rhs)
        | _ -> unreachable ()
    in
    let () = ensure_list lhs in
    let () = ensure_list rhs in
    cont @@ rev_append (rev_clist lhs) rhs

let f_add _ _ args cont =
    let args = List.map (ensure_int "ADD") args in
    let v = List.fold_left ( + ) 0 args in
    cont (ExprInt v)

let f_sub _ _ args cont =
    let args = List.map (ensure_int "SUB") args in
    let (seed, args) =
        match args with
        | v :: [] -> (0, [v])
        | hd :: tl -> (hd, tl)
        | [] -> unreachable ()
    in
    let v = List.fold_left ( - ) seed args in
    cont (ExprInt v)

let f_mul _ _ args cont =
    let args = List.map (ensure_int "MUL") args in
    let v = List.fold_left ( * ) 1 args in
    cont (ExprInt v)

let f_eql _ _ args cont =
    let (lhs, rhs) =
        match args with
        | lhs :: rhs :: [] -> (lhs, rhs)
        | _ -> unreachable ()
    in
    if lhs = rhs then
        cont ExprT
    else
        cont ExprNil

let lt_common name op args cont =
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
    cont (fold args)

let f_lt _ _ args cont = lt_common "<" ( < ) args cont
let f_lte _ _ args cont = lt_common "<=" ( <= ) args cont

let f_eval eval env args cont =
    let expr =
        match args with
        | e :: [] -> e
        | _ -> unreachable ()
    in
    eval env expr cont

let f_apply eval env args cont =
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
                let name = gensym () in
                let env' = Env.new_scope env in
                let () = Env.set_fn env' name (ExprFn fn) in
                (ExprSymbol name, env')
        | _ ->
                let s = string_of_expr fn in
                failwith ("APPLY: a function is required for the first argument: " ^ s)
    in
    let args = construct_args args in
    eval env' (ExprCons (fn, args)) cont

let (f_macroexpand_1, f_macroexpand) =
    let find_macro env expr =
        let (name, args) =
            match expr with
            | ExprCons (e1, e2) -> (e1, e2)
            | _ -> unreachable ()
        in
        match name with
        | ExprSymbol name ->
                (match Env.find_fn env name with
                | Some (ExprMacro _) -> Some (name, args)
                | _ -> None)
        | _ -> None
    in
    let macroexpand_1 eval env args cont =
        let expr = List.hd args in
        match find_macro env expr with
        | Some (name, args) -> Macro.apply eval env name args cont
        | _ -> cont expr
    in
    let macroexpand eval env args cont =
        let find_macro env expr =
            match expr with
            | ExprCons _ -> find_macro env expr
            | _ -> None
        in
        let rec do_expand env expr cont =
            match find_macro env expr with
            | Some (name, args) ->
                    Macro.apply eval env name args (fun expr ->
                        do_expand env expr cont)
            | _ -> cont expr
        in
        let expr = List.hd args in
        do_expand env expr cont
    in
    (macroexpand_1, macroexpand)

(* Special forms *)
let f_progn eval env args cont =
    let () =
        match args with
        | ExprNil -> unreachable ()
        | _ -> ()
    in
    let rec do_eval env args cont =
        match args with
        | ExprCons (e, ExprNil) -> eval env e cont
        | ExprCons (hd, tl) -> eval env hd (fun _ -> do_eval env tl cont)
        | _ -> unreachable ()
    in
    do_eval env args cont

let f_and eval env args cont =
    let args = list_of_clist args in
    let rec calc retval exprs cont =
        match exprs with
        | [] -> cont retval
        | hd :: tl ->
                eval env hd (fun hd ->
                    match hd with
                    | ExprNil -> cont ExprNil
                    | v -> calc v tl cont)
    in
    calc ExprT args cont

let f_or eval env args cont =
    let args = list_of_clist args in
    let rec calc exprs cont =
        match exprs with
        | [] -> cont ExprNil
        | hd ::tl ->
                eval env hd (fun hd ->
                    match hd with
                    | ExprNil -> calc tl cont
                    | v -> cont v)
    in
    calc args cont

let f_quote eval env args cont =
    let expr =
        match args with
        | ExprCons (e, ExprNil) -> e
        | _ -> unreachable ()
    in
    eval env (ExprSpOp (OpQuote expr)) cont

let f_setq eval env args cont =
    let args = list_of_clist args in
    let () =
        if List.length args mod 2 != 0 then
            failwith ("SETQ: Odd number of arguments: " ^ string_of_expr @@ clist_of_list args)
    in
    let rec do_bind retval args =
        match args with
        | [] -> cont retval
        | symbol :: value :: tl ->
                let symbol = ensure_symbol "SETQ" symbol in
                eval env value (fun value ->
                    let () =
                        match Env.find_var env symbol with
                        | Some _ -> Env.replace_existing_var env symbol value
                        | None -> Env.set_var env symbol value
                    in
                    do_bind value tl)
        | _ -> unreachable ()
    in
    do_bind ExprNil args

let f_if eval env args cont =
    let (cond, ifthen, ifelse) =
        match list_of_clist args with
        | e1 :: e2 :: e3 :: [] -> (e1, e2, e3)
        | _ -> unreachable ()
    in
    eval env cond (fun cond ->
        match cond with
        | ExprNil -> eval env ifelse cont
        | _ -> eval env ifthen cont)

let f_defmacro _ env args cont =
    let (name, expr) =
        match args with
        | ExprCons (hd, tl) -> (hd, tl)
        | _ -> unreachable ()
    in
    let name = ensure_symbol "DEFMACRO" name in
    let () = Macro.define env name expr in
    cont (ExprSymbol name)

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

let f_lambda eval env args cont =
    let gen_lambda_id = unique_id_generator () in
    let f_lambda _ env args cont =
        let (params, body) = parse_function_definition "LAMBDA" args in
        let name = "LAMBDA-" ^ string_of_int @@ gen_lambda_id () in
        cont (ExprFn (name, env, params, body))
    in
    f_lambda eval env args cont

let f_defun _ env args cont =
    let (name, fndef) =
        match args with
        | ExprCons (name, fndef) -> (name, fndef)
        | _ -> unreachable ()
    in
    let name = ensure_symbol "DEFUN" name in
    let (params, body) = parse_function_definition ("DEFUN: " ^ name) fndef in
    let fn = ExprFn (name, env, params, body) in
    let () = Env.set_fn env name fn in
    cont fn

let let_common recdef eval env args cont =
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
    let do_bind eval env binds cont =
        if recdef then
            let rec do_bind eval env binds cont =
                match binds with
                | (name, value) :: rest ->
                        eval env value (fun value ->
                            let () = Env.set_var env name value in
                            do_bind eval env rest cont)
                | [] -> cont env
            in
            let env = Env.new_scope env in
            do_bind eval env binds cont
        else
            let rec eval_binds acc eval env binds cont =
                match binds with
                | (name, value) :: rest ->
                        eval env value (fun value ->
                            eval_binds ((name, value) :: acc) eval env rest cont)
                | [] -> cont @@ List.rev acc
            in
            let do_bind eval env binds cont =
                eval_binds [] eval env binds (fun binds ->
                    let () = List.iter (fun (n, v) -> Env.set_var env n v) binds in
                    cont env)
            in
            do_bind eval env binds cont
    in
    do_bind eval env binds (fun env -> eval_body eval env (list_of_clist body) cont)

let f_let eval env args cont = let_common false eval env args cont
let f_letstar eval env args cont = let_common true eval env args cont


let flet_common recdef eval env args cont =
    let op = if recdef then "LABELS" else "FLET"
    in
    let (binds, body) =
        match args with
        | ExprCons (binds, body) -> (binds, body)
        | _ -> unreachable ()
    in
    let binds = ensure_list op binds in
    let binds =
        let err_invalid_bind expr =
            failwith (op ^ ": List with 2 to 3 elements required: " ^ string_of_expr expr)
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
    let env' =
        let env' = Env.new_scope env in
        let do_bind env' (symbol, params, expr) =
            let fnenv = if recdef then env' else env in
            let fn = ExprFn (symbol, fnenv, params, expr) in
            Env.set_fn env' symbol fn
        in
        let () = List.iter (do_bind env') binds in
        env'
    in
    eval_body eval env' (list_of_clist body) cont

let f_flet eval env args cont = flet_common false eval env args cont
let f_labels eval env args cont = flet_common true eval env args cont

let f_reset eval env args cont =
    let expr =
        match args with
        | ExprCons (expr, ExprNil) -> expr
        | _ -> unreachable ()
    in
    cont @@ eval env expr (fun x -> x)

let f_shift eval env args cont =
    let (fname, expr) =
        match args with
        | ExprCons (fname, ExprCons (expr, ExprNil)) -> (fname, expr)
        | _ -> unreachable ()
    in
    let fname = ensure_symbol "SHIFT" fname in
    let fn =
        let param = gensym () in
        let body = clist_of_list [
            ExprSymbol "#:RESET";
            clist_of_list [ExprContinuation cont; ExprSymbol param]
        ] in
        ExprFn (fname, env, ([param], None), [body])
    in
    let env' = Env.new_scope env in
    let () = Env.set_fn env' fname fn in
    let expr = ExprCons (ExprSymbol "#:RESET", ExprCons (expr, ExprNil)) in
    eval env' expr (fun x -> x)

let fn_table = [
    ("GENSYM", (f_gensym, Some 0, Some 0));
    ("MACROEXPAND-1", (f_macroexpand_1, Some 1, Some 1));
    ("MACROEXPAND", (f_macroexpand, Some 1, Some 1));
    ("CAR", (f_car, Some 1, Some 1));
    ("CDR", (f_cdr, Some 1, Some 1));
    ("CONS", (f_cons, Some 2, Some 2));
    ("APPEND", (f_append, Some 2, Some 2));
    ("LIST", (f_list, None, None));
    ("EVAL", (f_eval, Some 1, Some 1));
    ("+", (f_add, Some 1, None));
    ("-", (f_sub, Some 1, None));
    ("*", (f_mul, Some 1, None));
    ("EQL", (f_eql, Some 2, Some 2));
    ("<", (f_lt, Some 1, None));
    ("<=", (f_lte, Some 1, None));
    ("APPLY", (f_apply, Some 2, None));
]

let sp_table = [
    ("DEFMACRO", (f_defmacro, Some 2, None));
    ("PROGN", (f_progn, Some 1, None));
    ("AND", (f_and, None, None));
    ("OR", (f_or, None, None));
    ("LAMBDA", (f_lambda, Some 1, None));
    ("DEFUN", (f_defun, Some 2, None));
    ("LET", (f_let, Some 1, None));
    ("LET*", (f_letstar, Some 1, None));
    ("FLET", (f_flet, Some 1, None));
    ("LABELS", (f_labels, Some 1, None));
    ("IF", (f_if, Some 3, Some 3));
    ("SETQ", (f_setq, Some 2, None));
    ("QUOTE", (f_quote, Some 1, None));
    ("RESET", (f_reset, Some 1, Some 1));
    ("SHIFT", (f_shift, Some 2, Some 2));
]

let find_fn name = List.assoc_opt name fn_table
let find_sp name = List.assoc_opt name sp_table
