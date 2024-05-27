open Err

module Map = Map.Make(String)

type 'a envt = 'a Map.t ref list
type 'a t = {fns: 'a envt; vars: 'a envt;}

let empty () = {
    fns = [ref Map.empty];
    vars = [ref Map.empty];
}

let new_scope env = {
    fns = ref Map.empty :: env.fns;
    vars = ref Map.empty :: env.vars;
}

let rec find tbl name =
    match tbl with
    | [] -> None
    | hd :: tl ->
            (match Map.find_opt name !hd with
            | None -> find tl name
            | v -> v)

(* Remove a bind when it exists in the current environment *)
let remove tbl name =
    match tbl with
    | cur :: _ -> cur := Map.remove name !cur
    | _ -> ()

(* Make a new bind in the current environment *)
let set tbl name value =
    match tbl with
    | cur :: _ -> cur := Map.add name value !cur
    | _ -> unreachable ()

(* Replace an existing bind in the entire environment *)
let rec replace_existing tbl name value =
    match tbl with
    | cur :: outer ->
            (match Map.find_opt name !cur with
            | Some _ -> cur := Map.add name value !cur
            | None -> replace_existing outer name value)
    | [] -> raise (Invalid_argument ("Symbol not bound: " ^ name))

let find_fn env name = find env.fns name
let remove_fn env name = remove env.fns name
let set_fn env name value = set env.fns name value
let replace_existing_fn env name value = replace_existing env.fns name value

let find_var env name = find env.vars name
let remove_var env name = remove env.vars name
let set_var env name value = set env.vars name value
let replace_existing_var env name value = replace_existing env.vars name value
