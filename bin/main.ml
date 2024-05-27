open Lispy


let rec repl env =
    try
        let () = print_string "> " in
        let () = flush stdout in
        let s = read_line () in
        let r = Eval.eval_all env (Parse.parse s) in
        let () = List.iter (fun e -> print_endline @@ Expr.string_of_expr e) r in
        repl env
    with
    | End_of_file -> exit 0
    | Failure e ->
            let () = print_endline e in
            let () = Printexc.print_backtrace stdout in
            repl env
    | e ->
            let () = print_string "Fatal error: " in
            let () = print_endline (Printexc.to_string e) in
            let () = Printexc.print_backtrace stdout in
            repl env

let repl () =
    let () = Printexc.record_backtrace true in
    let env = Env.empty () in
    let () = ignore (Eval.eval_all env (Parse.parse (Bootstrap.get_src ()))) in
    repl env

(* TODO: Read from file *)
let main () =
    if Array.length Sys.argv > 1 then
        ()
    else
        ()
let () = ignore main

let () = repl ()
