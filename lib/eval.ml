open Err
open Expr
open Table

let lookup_function env symbol =
    if String.starts_with ~prefix:"#:" symbol then
        let name = String.sub symbol 2 (String.length symbol - 2) in
        match Builtin.find name with
        | Some _ -> Some (ExprBuiltinFn name)
        | None -> None
    else
        let (denv, _) = env in
        let fn = Table.find denv.fns symbol in
        match fn, Builtin.find symbol with
        | Some (ExprFn fn), _ -> Some (ExprFn fn)
        | None, Some _ -> Some (ExprBuiltinFn symbol)
        | _ -> None

let lookup_symbol env symbol =
    let (denv, lenv) = env in
    if String.starts_with ~prefix:"#:" symbol then
        lookup_function env symbol
    else if String.starts_with ~prefix:"#'" symbol then
        let symbol = String.sub symbol 2 (String.length symbol - 2) in
        lookup_function env symbol
    else
        (* lexical scope has much search priority than dynamic scope. *)
        match ScopedTable.find lenv symbol with
        | None -> Table.find denv.vars symbol
        | v -> v

let rec eval env expr =
    match expr with
    | ExprSymbol symbol ->
            let v = lookup_symbol env symbol in
            (match v with
            | None -> failwith ("No such symbol: " ^ symbol)
            | Some v -> v)
    | ExprCons (e1, e2) ->
            let e1 = eval env e1 in
            let e2 = eval env e2 in
            ExprCons (e1, e2)
    | ExprList _ ->
            (match Macro.expand_all eval env expr with
            | ExprList l ->
                    (match l with
                    | [] -> ExprList []
                    | symbol :: args -> apply_function env symbol args)
            | v -> v)
    | expr -> expr
and apply_function env symbol args =
    let err_invalid_app () =
        let src = string_of_expr (ExprList (symbol :: args)) in
        failwith ("Invalid function application: " ^ src)
    in
    let symbol =
        match symbol with
        | ExprSymbol s -> s
        | _ -> err_invalid_app ()
    in
    let fn = lookup_function env symbol in
    match fn with
    | None -> failwith ("No such symbol: " ^ symbol)
    | Some (ExprBuiltinFn name) -> apply_builtin_function env name args
    | Some (ExprFn fn) -> apply_user_function env fn args
    | _ -> err_invalid_app ()
and apply_builtin_function env name args =
    let (fn, nargs_min, nargs_max) =
        match Builtin.find name with
        | None -> unreachable ()
        | Some fn -> fn
    in
    let nargs = List.length args in
    let () =
        match nargs_min with
        | None -> ()
        | Some nargs_min ->
                if nargs < nargs_min then
                    let exp = string_of_expr (ExprList (ExprSymbol name :: args)) in
                    failwith ("Too few arguments for " ^ name  ^ ": " ^ exp)
    in
    let () =
        match nargs_max with
        | None -> ()
        | Some nargs_max ->
                if nargs > nargs_max then
                    let exp = string_of_expr (ExprList (ExprSymbol name :: args)) in
                    failwith ("Too many arguments for " ^ name  ^ ": " ^ exp)
    in
    fn eval env args
and apply_user_function env fn args =
    let rec bind_args lenv params vaparam args =
        (* Bind function arguments in environment in function closure *)
        match params, vaparam, args with
        | hdp :: tlp, _, hda :: tla ->
                let () = ScopedTable.set lenv hdp hda in
                bind_args lenv tlp vaparam tla
        | [], Some vaparam, rest -> ScopedTable.set lenv vaparam (ExprList rest)
        | [], None, [] -> ()  (* Already bound all the values.  Do nothing. *)
        | _ ->
                (*
                   Correspondance between the count of function parameters and
                   the count of arguments should be checked before this
                   function is called.
                 *)
                unreachable ()
    in
    let (fn_name, fnenv, (params, vaparam), body) = fn in
    let nargs = List.length args in
    let nparams = List.length params in
    let () =
        if nargs < nparams then
            failwith ("Too few arguments to function " ^ fn_name)
        else if vaparam = None && nargs != nparams then
            failwith ("Too many arguments to function " ^ fn_name)
    in
    let args =
        let rec eval_args acc env args =
            match args with
            | [] -> List.rev acc
            | hd :: tl ->
                    let v = eval env hd in
                    eval_args (v :: acc) env tl
        in
        eval_args [] env args
    in
    let fnenv = ScopedTable.new_scope !fnenv in
    let () = bind_args fnenv params vaparam args in
    let (denv, _) = env in
    let rec do_eval retval env body =
        match body with
        | [] -> retval
        | hd :: tl -> do_eval (eval env hd) env tl
    in
    (* Evaluate the function body under the environment in the function closure *)
    do_eval (ExprList []) (denv, fnenv) body


let eval_all env exprs =
    let rec do_eval acc env exprs =
        match exprs with
        | [] -> List.rev acc
        | hd :: tl -> do_eval (eval env hd :: acc) env tl
    in
    do_eval [] env exprs
