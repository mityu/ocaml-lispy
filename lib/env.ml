open Err

module Ht = Hashtbl.Make(struct
        type t = string
        let equal = ( = )
        let hash = Hashtbl.hash
    end)

type 'a t = 'a Ht.t list

let empty = []

let rec find tbls key =
    match tbls with
    | [] -> None
    | hd :: tl ->
            let v = Ht.find_opt hd key in
            (match v with
            | None -> find tl key
            | _ -> v)

let add tbls key value =
    match tbls with
    | [] -> unreachable ()
    | hd :: _ -> Ht.add hd key value

let rec replace tbls key value =
    match tbls with
    | [] -> raise Not_found
    | hd :: tl ->
            (match Ht.find_opt hd key with
            | None -> replace tl key value
            | _ -> Ht.replace hd key value)

let new_scope tbl = Ht.create 64 :: tbl
