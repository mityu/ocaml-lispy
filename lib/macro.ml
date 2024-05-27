open Err
open Expr

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
        | ExprCons (params, body) -> (params, body)
        | _ -> failwith "At least one argument is reauired."
    in
    let params =
        if is_list params then
            list_of_clist params
        else
            failwith ("List required: " ^ string_of_expr params)
    in
    let params = List.map ensure_symbol params in
    let () =
        if (Bool.not @@ check_unique params) then
            (* TODO: lookup duplicate item *)
            failwith (name ^ ": duplicate symbol appears in parameters")
    in
    let params = parse_params params in
    Env.set_fn env name (ExprMacro (name, env, params, list_of_clist body))

let apply eval env name args =
    let bind_params params vaparam args =
        let rec bind acc params vaparam args =
            match params, args with
            | [], ExprNil ->
                    (match vaparam with
                    | None -> acc
                    | Some vaparam -> (vaparam, ExprNil) :: acc)
            | [], ExprCons (e1, e2) ->
                    (match vaparam with
                    | Some vaparam -> (vaparam, ExprCons (e1, e2)) :: acc
                    | None -> failwith (name ^ ": Too much arguments"))
            | _, ExprNil -> failwith (name ^ ": Too few arguments")
            | hdp :: tlp, ExprCons (hda, tla) ->
                    bind ((hdp, hda) :: acc) tlp vaparam tla
            | _ -> unreachable ()
        in
        bind [] params vaparam args
    in
    let (_, menv, (params, vaparam), body) =
        match Env.find_fn env name with
        | Some (ExprMacro m) -> m
        | _ -> failwith ("Internal error: macro not found: " ^ name)
    in
    let binds = bind_params params vaparam args in
    let menv = Env.new_scope menv in
    let () = List.iter (fun (n, v) -> Env.set_var menv n v) binds in
    match (List.map (eval menv) body) with
    | [] -> ExprNil
    | v -> List.hd (List.rev v)

let expand_all eval env expr =
    let to_list clist =
        let rec impl acc expr =
            match expr with
            | ExprCons (e1, e2) -> impl (e1 :: acc) e2
            | ExprNil -> List.rev acc
            | _ -> List.rev (expr :: acc)
        in
        impl [] clist
    in
    let to_clist is_list l =
        let rec impl acc l =
            match l with
            | [] -> acc
            | hd :: tl -> impl (ExprCons (hd, acc)) tl
        in
        let l = List.rev l in
        let (seed, l) =
            if is_list then
                (ExprNil, l)
            else
                match l with
                | e1 :: e2 :: rest -> (ExprCons (e2, e1), rest)
                | _ -> unreachable ()
        in
        impl seed l
    in
    let rec do_expand eval env expr =
        (* Check if (m ...) is expandable macro and expand macro if it is. *)
        match expr with
        | ExprCons (ExprSymbol name, args) ->
                (match Env.find_fn env name with
                | Some (ExprMacro _) when is_list args ->
                        let expr = apply eval env name args in
                        do_expand eval env expr
                | _ ->
                        let is_list = is_list args in
                        let elems = to_list args in
                        let elems = List.map (do_expand eval env) elems in
                        ExprCons (ExprSymbol name, to_clist is_list elems))
        | _ -> expr
    in
    do_expand eval env expr
