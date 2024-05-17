open Table

type expr =
    | ExprSymbol of string
    | ExprList of expr list
    | ExprCons of expr * expr
    | ExprInt of int
    | ExprString of string
    | ExprFn of fn
    | ExprBuiltinFn of string (* Holds function name *)
    | ExprMacro of fn
and lenv = expr ScopedTable.t  (* lexical scope environment *)
and fn = string * lenv ref * (string list * string option) * expr list
(* fn: (name, closure, (params, vaparam), body) *)

(* Dynamic scope environment *)
type denv = {fns: expr Table.t; vars: expr Table.t;}
type env = denv * lenv

let empty_lenv = ScopedTable.empty
let empty_denv () = {
    fns = Table.empty ();
    vars = Table.empty ();
}

let rec string_of_expr e =
    let string_of_list l =
        let elems = List.fold_left (fun acc v -> acc ^ v ^ " ") "" l in
        let elems = String.sub elems 0 (String.length elems - 1) in
        "(" ^ elems ^ ")"
    in
    match e with
    | ExprSymbol s -> s
    | ExprList l ->
            if l = [] then
                "NIL"
            else
                let l = List.map string_of_expr l in
                string_of_list l
    | ExprCons (e1, e2) ->
            let e1 = string_of_expr e1 in
            let e2 = string_of_expr e2 in
            Printf.sprintf "(%s . %s)" e1 e2
    | ExprInt v -> string_of_int v
    | ExprString s -> "\"" ^ s ^ "\""
    | ExprFn fn ->
            let (name, _, _, _) = fn in
            Printf.sprintf "#<FUNCTION:%s>" name
    | ExprBuiltinFn name -> Printf.sprintf "#<SYSTEM-FUNCTION:%s>" name
    | ExprMacro macro ->
            let (name, _, _, _) = macro in
            Printf.sprintf "#<MACRO:%s>" name
