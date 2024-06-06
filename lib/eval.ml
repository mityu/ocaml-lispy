open Err
open Expr

let lookup_function env symbol =
    if Builtin.is_builtin_fn_symbol symbol then
        (* Find function from builtin functions *)
        let name = String.sub symbol 2 (String.length symbol - 2) in
        match Builtin.find_fn name with
        | Some _ -> Some (ExprBuiltinFn name)
        | None -> None
    else
        (* Find function from user defined functions *)
        let userfn = Env.find_fn env symbol in
        let systemfn = Builtin.find_fn symbol in
        match userfn, systemfn with
        | Some (ExprFn fn), _ -> Some (ExprFn fn)
        | Some (ExprContinuation fn), _ -> Some (ExprContinuation fn)
        | None, Some _ -> Some (ExprBuiltinFn symbol)
        | _ -> None

let lookup_applicable env symbol =
    let symbol =
        if Builtin.is_builtin_fn_symbol symbol then
            String.sub symbol 2 (String.length symbol - 2)
        else
            symbol
    in
    match Builtin.find_sp symbol with
    | Some _ -> Some (ExprSpecialForm symbol)
    | None -> lookup_function env symbol

let lookup_symbol env symbol =
    if Builtin.is_builtin_fn_symbol symbol then
        lookup_applicable env symbol
    else if String.starts_with ~prefix:"#'" symbol then
        let symbol = String.sub symbol 2 (String.length symbol - 2) in
        lookup_function env symbol
    else
        Env.find_var env symbol

let rec unquote eval env expr cont =
    match expr with
    | ExprCons (ExprSpOp op, e2) ->
            (match op with
            | OpUnquote e1 ->
                    (* ,x y -> (cons x y) *)
                    eval env e1 (fun e1 ->
                        unquote eval env e2 (fun e2 ->
                            cont (ExprCons (e1, e2))))
            | OpUnquoteSplicing e1 ->
                    (* ,@x y -> (append x y) *)
                    eval env e1 (fun e1 ->
                        unquote eval env e2 (fun e2 ->
                            let e1 = Builtin.ensure_list ",@form" e1 in
                            let e2 = Builtin.ensure_list ",@form" e2 in
                            cont @@ clist_of_list (List.append e1 e2)))
            | _ -> cont expr)
    | ExprCons (e1, e2) ->
            unquote eval env e1 (fun e1 ->
                unquote eval env e2 (fun e2 ->
                    cont (ExprCons (e1, e2))))
    | ExprSpOp op ->
            (match op with
            | OpUnquote expr' -> eval env expr' cont
            | OpUnquoteSplicing _ -> failwith "The syntax `,@form is invalid."
            | _ -> cont expr)
    | _ -> cont expr

let validate_argument_count name args nargs_min nargs_max =
    let nargs = List.length @@ list_of_clist args in
    let () =
        match nargs_min with
        | None -> ()
        | Some nargs_min ->
                if nargs < nargs_min then
                    let exp = string_of_expr (ExprCons (ExprSymbol name, args)) in
                    failwith ("Too few arguments for " ^ name  ^ ": " ^ exp)
    in
    let () =
        match nargs_max with
        | None -> ()
        | Some nargs_max ->
                if nargs > nargs_max then
                    let exp = string_of_expr (ExprCons (ExprSymbol name, args)) in
                    failwith ("Too many arguments for " ^ name  ^ ": " ^ exp)
    in
    ()

let rec eval env expr cont =
    match expr with
    | ExprSymbol symbol ->
            let v = lookup_symbol env symbol in
            (match v with
            | None -> failwith ("No such symbol: " ^ symbol)
            | Some v -> cont v)
    | ExprCons _ ->
            Macro.expand_all eval env expr (fun expr ->
                match expr with
                | ExprCons (symbol, args) -> apply_function env symbol args cont
                | v -> eval env v cont)
    | ExprSpOp op ->
            (match op with
            | OpQuote expr -> cont expr
            | OpQuasiQuote expr -> unquote eval env expr cont
            | _ -> unreachable ())
    | expr -> cont expr
and apply_function env car args cont =
    let () =
        if Bool.not @@ is_list args then
            let src = string_of_expr (ExprCons (car, args)) in
            failwith ("List required for function application: " ^ src)
    in
    let err_invalid_app () =
        let src = string_of_expr (ExprCons (car, args)) in
        failwith ("Invalid function application: " ^ src)
    in
    let do_apply env fn args cont =
        match fn with
        | ExprBuiltinFn name -> apply_builtin_function env name args cont
        | ExprSpecialForm name -> apply_special_form env name args cont
        | ExprFn fn -> apply_user_function env fn args cont
        | _ -> err_invalid_app ()
    in
    match car with
    | ExprCons _ -> eval env car (fun fn -> do_apply env fn args cont)
    | ExprSymbol s ->
            (match lookup_applicable env s with
            | None -> failwith ("No such symbol: " ^ s)
            | Some v -> do_apply env v args cont)
    | ExprContinuation fncont -> apply_continuation env fncont args cont
    | _ -> err_invalid_app ()
and apply_special_form env name args cont =
    let (fn, nargs_min, nargs_max) =
        match Builtin.find_sp name with
        | None -> unreachable ()
        | Some fn -> fn
    in
    let () = validate_argument_count name args nargs_min nargs_max in
    fn eval env args cont
and apply_builtin_function env name args cont =
    let (fn, nargs_min, nargs_max) =
        match Builtin.find_fn name with
        | None -> unreachable ()
        | Some fn -> fn
    in
    let () = validate_argument_count name args nargs_min nargs_max in
    let eval_args =
        let rec eval_args acc env args cont =
            match args with
            | ExprNil -> cont @@ List.rev acc
            | ExprCons (hd, tl) ->
                    eval env hd (fun hd -> eval_args (hd :: acc) env tl cont)
            | _ -> unreachable ()
        in
        eval_args []
    in
    eval_args env args (fun args -> fn eval env args cont)
and apply_user_function env fn args cont =
    let rec bind_args env params vaparam args =
        (* Bind function arguments in environment in function closure *)
        match params, vaparam, args with
        | hdp :: tlp, _, ExprCons (hda, tla) ->
                let () = Env.set_var env hdp hda in
                bind_args env tlp vaparam tla
        | [], Some vaparam, rest -> Env.set_var env vaparam rest
        | [], None, ExprNil -> ()  (* Already bound all the values.  Do nothing. *)
        | _ ->
                (*
                   Correspondance between the count of function parameters and
                   the count of arguments should be checked before this
                   function is called.
                 *)
                unreachable ()
    in
    let (fn_name, fnenv, (params, vaparam), body) = fn in
    let nargs = List.length @@ list_of_clist args in
    let nparams = List.length params in
    let () =
        if nargs < nparams then
            failwith ("Too few arguments to function " ^ fn_name)
        else if vaparam = None && nargs != nparams then
            failwith ("Too many arguments to function " ^ fn_name)
    in
    let eval_fn_body args body cont =
        let rec eval_fn_body retval env body cont =
            match body with
            | [] -> cont retval
            | hd :: tl -> eval env hd (fun hd -> eval_fn_body hd env tl cont)
        in
        let fnenv = Env.new_scope fnenv in
        let () = bind_args fnenv params vaparam args in
        eval_fn_body ExprNil fnenv body cont
    in
    let eval_args =
        let rec eval_args acc env args cont =
            match args with
            | ExprNil -> cont (rev_clist acc)
            | ExprCons (hd, tl) ->
                    eval env hd (fun hd ->
                        eval_args (ExprCons (hd, acc)) env tl cont)
            | _ -> unreachable ()
        in
        eval_args ExprNil
    in
    eval_args env args (fun args ->
        eval_fn_body args body (fun retval -> cont retval))
and apply_continuation env fn args cont =
    let arg =
        match args with
        | ExprCons (arg, ExprNil) -> arg
        | _ -> failwith ("Too many arguments to continuation: " ^ string_of_expr args)
    in
    eval env arg (fun arg -> cont (fn arg))

let eval_all env exprs =
    let rec do_eval acc env exprs =
        match exprs with
        | [] -> (List.rev acc)
        | hd :: tl ->
                let v = eval env hd (fun x -> x) in
                do_eval (v :: acc) env tl
    in
    do_eval [] env exprs
