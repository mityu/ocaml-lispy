open Expr
open Table

let check_unique l =
    let rec checker checked l =
        match l with
        | [] -> true
        | hd :: tl ->
                if List.exists (fun e -> e = hd) checked then
                    false
                else
                    checker (hd :: checked) tl
    in
    checker [] l


let define env name expr =
    let failwith msg = failwith (Printf.sprintf "DEFMACRO %s: %s" name msg) in
    let ensure_symbol e =
        match e with
        | ExprSymbol s -> s
        | _ -> failwith ("Symbol required: " ^ (string_of_expr e))
    in
    let parse_params params =
        let rec parse params single =
            match params with
            | [] -> (List.rev single, None)
            | hd :: tl ->
                    if hd = "&BODY" then
                        (match tl with
                        | [] -> failwith "Symbol required after \"&BODY\""
                        | rest :: [] -> (List.rev single, Some rest)
                        | _ -> failwith "Must be one symbol after \"&BODY\"")
                    else
                        parse tl (hd :: single)
        in
        parse params []
    in
    let (params, body) =
        match expr with
        | params :: body -> (params, body)
        | _ -> failwith "At least one argument is reauired."
    in
    let params =
        match params with
        | ExprList l -> l
        | _ -> failwith ("List required: " ^ string_of_expr params)
    in
    let params = List.map ensure_symbol params in
    let () =
        if (Bool.not @@ check_unique params) then
            (* TODO: lookup duplicate item *)
            failwith (name ^ ": duplicate symbol appears in parameters")
    in
    let params = parse_params params in
    let (denv, lenv) = env in
    Table.set denv.fns name (ExprMacro (name, ref lenv, params, body))

let apply eval env name args =
    let bind_params params vaparams args =
        let rec bind acc params vaparams args =
            match params, args with
            | [], [] ->
                    (match vaparams with
                    | None -> acc
                    | Some vaparams -> (vaparams, ExprList []) :: acc)
            | [], _ :: _ ->
                    (match vaparams with
                    | Some vaparams -> (vaparams, ExprList args) :: acc
                    | None -> failwith (name ^ ": Too much arguments"))
            | _, [] -> failwith (name ^ ": Too few arguments")
            | phd :: ptl, ahd :: atl ->
                    bind ((phd, ahd) :: acc) ptl vaparams atl
        in
        bind [] params vaparams args
    in
    let (denv, _) = env in
    let (_, menv, (params, vaparam), body) =
        match Table.find denv.fns name with
        | Some (ExprMacro m) -> m
        | _ -> failwith ("Internal error: macro not found: " ^ name)
    in
    let binds = bind_params params vaparam args in
    let menv = ScopedTable.new_scope !menv in
    let () = List.iter (fun (n, v) -> ScopedTable.set menv n v) binds in
    match (List.map (eval (denv, menv)) body) with
    | [] -> ExprList []
    | v -> List.hd (List.rev v)

let expand_all eval env expr =
    let rec do_expand eval env expr =
        let (denv, _ ) = env in
        match expr with
        | ExprList (ExprSymbol name :: args) ->
                (match Table.find denv.fns name with
                | Some (ExprMacro _) ->
                        let expr = apply eval env name args in
                        do_expand eval env expr
                | _ ->
                        let tl = List.map (do_expand eval env) args in
                        ExprList (ExprSymbol name :: tl))
        | _ -> expr
    in
    do_expand eval env expr
