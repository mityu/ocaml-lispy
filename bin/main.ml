open Lispy


let bootstrap = {lisp|
(builtin-defmacro defmacro (name args body) `(builtin-defmacro ,name ,args ,body))
(defmacro gensym () '(builtin-gensym))
(defmacro lambda (args &body body) `(builtin-lambda ,args ,@body))
(defmacro defun (name args &body body) `(builtin-defun ,name ,args ,@body))
(defmacro let (binds &body body) `(builtin-let ,binds ,@body))
(defmacro let* (binds &body body) `(builtin-let* ,binds ,@body))
(defmacro flet (binds &body body) `(builtin-flet ,binds ,@body))
(defmacro labels (binds &body body) `(builtin-labels ,binds ,@body))
(defmacro eval (expr) `(builtin-eval ,expr))
(defmacro car (expr) `(builtin-car ,expr))
(defmacro cdr (expr) `(builtin-cdr ,expr))
(defmacro if (cond e1 e2) `(builtin-if ,cond ,e1 ,e2))
(defmacro eql (e1 e2) `(builtin-eql ,e1 ,e2))
(defmacro and (&body body) `(builtin-and ,@body))
(defmacro or (&body body) `(builtin-or ,@body))
(defmacro quote (expr) `(builtin-quote ,expr))
(defun + (x y) (builtin-add x y))
(defun - (x y) (builtin-sub x y))
(defun < (x y) (builtin-lt x y))
(defun <= (x y) (builtin-lte x y))
(defun not (x) (if x nil t))
(defmacro progn (&body body)
  (let ((x (gensym)))
    `(labels ((,x (exprs retval)
                    (if exprs
                      (,x (cdr exprs) (eval (car exprs)))
                      retval)))
       (,x (quote ,body) ()))))
|lisp}

let rec repl env =
    try
        let () = print_string "> " in
        let () = flush stdout in
        let s = read_line () in
        let (env, r) = Eval.eval env (Parse.parse (Lex.lex s)) in
        let () = List.iter (fun e -> print_endline @@ Eval.string_of_expr e) r in
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
    let env = Eval.new_scope Eval.empty_env in
    let (env, _) = Eval.eval env (Parse.parse (Lex.lex bootstrap)) in
    repl env

let main () =
    if Array.length Sys.argv > 1 then
        ()
    else
        ()
let () = ignore main

let () = repl ()
