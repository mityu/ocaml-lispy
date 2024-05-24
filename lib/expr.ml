open Table
open Err

type expr =
    | ExprSymbol of string
    | ExprKeyword of string
    | ExprNil
    | ExprT
    | ExprCons of expr * expr
    | ExprInt of int
    | ExprString of string
    | ExprFn of fn
    | ExprBuiltinFn of string (* Holds function name *)
    | ExprMacro of fn
    | ExprSpOp of spop
and spop =
    | OpQuote of expr
    | OpQuasiQuote of expr
    | OpUnquote of expr
    | OpUnquoteSplicing of expr
and lenv = {lfns: expr ScopedTable.t; lvars: expr ScopedTable.t;}  (* lexical scope environment *)
and fn = string * lenv * (string list * string option) * expr list
(* fn: (name, closure, (params, vaparam), body) *)

(* Dynamic scope environment *)
type denv = {fns: expr Table.t; vars: expr Table.t;}
type env = denv * lenv

let empty_lenv () = {
    lfns = ScopedTable.empty ();
    lvars = ScopedTable.empty ();
}
let empty_denv () = {
    fns = Table.empty ();
    vars = Table.empty ();
}

let rec is_list expr =
    match expr with
    | ExprNil -> true
    | ExprCons (_, v) -> is_list v
    | _ -> false

(* clist stands for cons cell list *)
let clist_of_list exprs =
    let rec impl acc exprs =
        match exprs with
        | [] -> acc
        | hd :: tl -> impl (ExprCons (hd, acc)) tl
    in
    impl ExprNil (List.rev exprs)

let list_of_clist expr =
    let rec to_list acc expr =
        match expr with
        | ExprNil -> List.rev acc
        | ExprCons (e1, e2) -> to_list (e1 :: acc) e2
        | _ -> unreachable ()
    in
    to_list [] expr

let rev_clist l =
    let rec do_rev acc l =
        match l with
        | ExprNil -> ExprNil  (* In case of the empty list *)
        | ExprCons (e1, ExprNil) -> ExprCons (e1, acc)
        | ExprCons (e1, ExprCons (car, cdr)) -> do_rev (ExprCons (e1, acc)) (ExprCons (car, cdr))
        | ExprCons (_, _) -> failwith "Internal error: list must be ends with NIL."
        | _ -> unreachable ()
    in
    do_rev ExprNil l

let rec string_of_expr e =
    let string_of_cons (e1, e2) =
        let rec concat acc e1 e2 =
            let e1 = string_of_expr e1 in
            match e2 with
            | ExprCons (e1', e2') -> concat (acc ^ e1 ^ " ") e1' e2'
            | ExprNil -> acc ^ e1
            | e -> acc ^ e1 ^ " . " ^ string_of_expr e
        in
        "(" ^ (concat "" e1 e2) ^ ")"
    in
    match e with
    | ExprSymbol s -> s
    | ExprKeyword s -> ":" ^ s
    | ExprNil -> "NIL"
    | ExprT -> "T"
    | ExprCons (e1, e2) -> string_of_cons (e1, e2)
    | ExprInt v -> string_of_int v
    | ExprString s -> "\"" ^ s ^ "\""
    | ExprFn fn ->
            let (name, _, _, _) = fn in
            Printf.sprintf "#<FUNCTION:%s>" name
    | ExprBuiltinFn name -> Printf.sprintf "#<SYSTEM-FUNCTION:%s>" name
    | ExprMacro macro ->
            let (name, _, _, _) = macro in
            Printf.sprintf "#<MACRO:%s>" name
    | ExprSpOp op ->
            (match op with
            | OpQuote expr -> "'" ^ string_of_expr expr
            | OpQuasiQuote expr -> "`" ^ string_of_expr expr
            | OpUnquote expr -> "," ^ string_of_expr expr
            | OpUnquoteSplicing expr -> ",@" ^ string_of_expr expr)
