open Err

module Table = struct
    module Ht = Hashtbl.Make(struct
        type t = string
        let equal = ( = )
        let hash = Hashtbl.hash
    end)

    type 'a t = 'a Ht.t

    let empty () = Ht.create 64

    let find = Ht.find_opt

    (* Remove a bind *)
    let remove = Ht.remove

    (* Make a new bind and hides the previous bind(s) *)
    let set = Ht.add
end

module ScopedTable = struct
    type 'a t = 'a Table.t list

    let empty () = [Table.empty ()]

    let new_scope tbl = Table.empty () :: tbl

    let rec find tbl name =
        match tbl with
        | [] -> None
        | hd :: tl ->
                (match Table.find hd name with
                | None -> find tl name
                | v -> v)

    let remove tbl name =
        match tbl with
        | tbl :: _ -> Table.remove tbl name
        | _ -> ()

    let set tbl name value =
        match tbl with
        | tbl :: _ -> Table.set tbl name value
        | _ -> unreachable ()

    let rec replace_existing tbl name value =
        match tbl with
        | cur :: outer ->
                (match Table.find cur name with
                | Some _ -> Table.set cur name value
                | None -> replace_existing outer name value)
        | [] -> raise (Invalid_argument ("Symbol not bound: " ^ name))
end
