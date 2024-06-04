open Lispy.Expr
open Lispy.Parse
open Lispy.Eval

let expr_t =
    let open Lispy.Expr in
    let pp fmt v = Format.fprintf fmt "%s" (string_of_expr v) in
    let compare e1 e2 =
        match e1, e2 with
        | ExprFn (n1, _, _, _), ExprFn (n2, _, _, _) -> n1 = n2
        | ExprBuiltinFn n1, ExprBuiltinFn n2 -> n1 = n2
        | ExprMacro (n1, _, _, __), ExprMacro (n2, _, _, _) -> n1 = n2
        | _ -> e1 = e2
    in
    Alcotest.testable pp compare

let run s =
    let env = Lispy.Env.empty () in
    eval_all env (parse s)

let check = Alcotest.(check (list expr_t))
let check_failure = Alcotest.check_raises "failwith call"

let listform_of = clist_of_list
let fn_of name = ExprFn (name, Lispy.Env.empty (), ([], None), [])

let test_parse () =
    let check v src = check ("parse: " ^ src) v (parse src) in
    check [ExprSpOp (OpQuote (ExprSymbol "XYZ"))] "'xyz";
    check
        [ExprSpOp (OpQuasiQuote (listform_of [
                ExprSpOp (OpUnquote (ExprSymbol "X"))]))]
        "`(,x)";
    check [ExprInt 123] "123";
    check [ExprInt 123] "+123";
    check [ExprInt (-123)] "-123";
    check [ExprSymbol "+-123"] "+-123";
    check [ExprSymbol "1+"] "1+";
    check [ExprSymbol "+"] "+";
    check [ExprCons (ExprInt 1, ExprInt 2)] "(1 . 2)";
    check [ExprNil] "()";
    check [ExprNil] "nil";
    check [ExprNil] "'()";
    check [ExprNil] "'nil";
    check [ExprT] "t";
    check [ExprT] "'t";
    check [ExprSpOp (OpQuasiQuote (listform_of [ExprSpOp (OpUnquote (ExprSymbol "N"))]))] "`(,n)";
    check [ExprSpOp (OpQuasiQuote (listform_of [ExprSpOp (OpUnquoteSplicing (ExprSymbol "N"))]))] "`(,@n)";
    check [ExprKeyword "||"] ":";
    check [ExprKeyword "TEST"] ":test";
    check [ExprKeyword "|#ABC|"] ":#abc";
    ()

let test_expr_is_list () =
    let check = Alcotest.(check bool) in
    let check v src = check ("is_list: " ^ src) v (is_list @@ List.hd @@ parse src) in
    check true "()";
    check true "(1 2 3)";
    check true "(1 . ())";
    check false "(1 . (2 . 3))";
    check false "(1 . 2)";
    ()

let test_expr_clist_of_list () =
    let check = Alcotest.(check expr_t) in
    let check v l = check ("cilst_of_exprs") v (clist_of_list l) in
    check (ExprCons (ExprInt 5, ExprCons (ExprInt 11, ExprNil))) [ExprInt 5; ExprInt 11];
    ()

let test_expr_list_of_clist () =
    let check = Alcotest.(check (list expr_t)) in
    let check v =
        let clist = clist_of_list v in
        check ("list_of_clist: " ^ string_of_expr clist) v (list_of_clist clist) in
    check [ExprInt 3; ExprInt 5];
    ()

let test_expr_rev_clist () =
    let check = Alcotest.(check string) in
    let check v src =
        let src = List.hd @@ parse src in
        check ("rev_clist: " ^ v) v (string_of_expr @@ rev_clist src)
    in
    check "(1 2 3 C B A)" "(a b c 3 2 1)";
    ()

let test_eval_value () =
    let check v src = check ("eval: " ^ src) v (run src) in
    check [ExprSymbol "FOO"] "'foo";
    check [ExprSymbol "XYZ"] "' xyz";
    ()

let test_eval_expr () =
    let check v src = check ("eval: " ^ src) v (run src) in
    check [ExprSymbol "XYZ"] "(quote xyz)";
    check [listform_of [ExprSymbol "QUOTE"; ExprSymbol "XYZ"]] "'(quote xyz)";
    check [fn_of "F"; fn_of "F"] "(defun f ()) #'f";
    check [fn_of "F"; ExprSymbol "XYZ"] "(defun f () 'xyz) (f)";
    check [fn_of "F"; ExprInt 3] "(defun f (x) x) (f 3)";
    check [ExprSymbol "VAL"] "(let ((x 'val)) x)";
    check [ExprSymbol "XYZ"] "(if () 'abc 'xyz)";
    check [ExprSymbol "ABC"] "(if '(a) 'abc 'xyz)";
    check [ExprInt 3; ExprInt 3] "(setq x 3) x";
    check [ExprNil] "(let ((x)) x)";
    check [ExprInt 12] "(+ 2 3 7)";
    check [ExprInt 3] "(+ 3)";
    check [ExprInt (-3)] "(- 3)";
    check [ExprInt 1] "(- 3 2)";
    check [ExprInt 6] "(- 13 2 5)";
    check [ExprInt 7] "(* 7)";
    check [ExprInt 105] "(* 7 3 5)";
    check [ExprInt 5; ExprSymbol "XYZ"; ExprInt 5]
                "(setq x 'xyz y 5) x y";
    check_failure (Failure "SETQ: Odd number of arguments: (X Y Z)")
                (fun () -> ignore @@ run "(setq x y z)");
    check [ExprT] "(and)";
    check [ExprInt 1] "(and 1)";
    check [ExprSymbol "UNKNOWN"; ExprNil; ExprSymbol "OK"]
                "(setq x 'unknown) (and 'abc (setq x 'ok) nil (setq x 'ng)) x";
    check [ExprNil] "(or)";
    check [ExprSymbol "UNKNOWN"; ExprSymbol "OK"; ExprSymbol "OK"]
                "(setq x 'unknown) (or nil (setq x 'ok) 'abc (setq x 'ng)) x";
    check [ExprInt 3] "(car '(3 5 7))";
    check [listform_of [ExprInt 5; ExprInt 7]] "(cdr '(3 5 7))";
    check [ExprCons (ExprInt 3, ExprSymbol "XYZ")] "(cons 3 'xyz)";
    check [listform_of [ExprInt 1; ExprInt 2; ExprInt 3; ExprInt 4]]
                "(append '(1 2) '(3 4))";
    check [ExprNil] "(append nil nil)";
    check [ExprCons (ExprInt 3, ExprNil)] "(append nil '(3))";
    check [ExprCons (ExprInt 5, ExprNil)] "(append '(5) nil)";
    check [ExprT] "(eql 'abc 'abc)";
    check [ExprNil] "(eql ''abc 'abc)";
    check [ExprNil] "(eql 3 'abc)";
    check [ExprT] {code|(eql "abc" "abc")|code};
    check [ExprNil] {code|(eql "abc" "xyz")|code};
    check [ExprT] "(eql '(1 2 3) '(1 2 3))";
    check [ExprNil] "(eql '(1 2 . 3) '(1 2 3))";
    check [ExprT] "(< 1)";
    check [ExprT] "(< 1 2)";
    check [ExprT] "(< 1 2 3)";
    check [ExprNil] "(< 1 3 2)";
    check [ExprT] "(<= 1)";
    check [ExprT] "(<= 1 1)";
    check [ExprT] "(<= 1 2 2 3)";
    check [ExprNil] "(<= 1 3 3 2)";
    check [ExprInt 7] "(apply #'+ '(2 5))";
    check [ExprInt 37] "(apply #'+ 7 9 '(2 5 14))";
    check [fn_of "F"; fn_of "F"; ExprSymbol "F"; ExprInt 5;] {code|
                (defun f (x) x)
                (setq fn #'f)
                (defmacro f (x) ''macro)
                (apply fn '(5))
        |code};
    check [ExprInt 10] "((lambda (x) (+ x 3)) 7)";
    ()

let test_eval_unquote () =
    let check v src = check ("eval: " ^ src) v (run src) in
    check [ExprInt 3; listform_of [ExprInt 3; ExprInt 3]] "(setq x 3) `(,x ,x)";
    check [
            listform_of [ExprInt 1; ExprInt 2];
            listform_of [ExprInt 1; ExprInt 2; ExprInt 3; ExprInt 4]
        ] "(setq x '(1 2)) `(,@x 3 4)";
    check [
            listform_of [ExprInt 1; ExprInt 2];
            listform_of [ExprInt 1; ExprInt 2; ExprInt 1; ExprInt 2]
        ] "(setq x '(1 2)) `(,@x ,@x)";
    ()

let test_eval_macro () =
    let check v src = check ("eval: " ^ src) v (run src) in
    check [ExprSymbol "M"; ExprSymbol "MACRO-M"] "(defmacro m () ''macro-m) (m)";
    check [ExprSymbol "M"; ExprSymbol "ABC"] "(defmacro m (x) `,x) (m 'abc)";
    check [ExprSymbol "M"; ExprSymbol "MACRO"] "(defmacro m () 'macro) (macroexpand-1 '(m))";
    check [ExprSymbol "M"; ExprSymbol "MACRO"] "(defmacro m () 'macro) (macroexpand '(m))";
    ()

let test_eval_scope () =
    let check = check "same expr" in
    let last_value retvals = [List.hd @@ List.rev retvals] in
    check [ExprSymbol "MACRO"]
        (last_value @@ run {code|
            (defmacro m () ''macro)
            (defun call-m () (m))
            (defun m () 'fn)
            (call-m)
        |code});
    check [ExprSymbol "FN"]
        (last_value @@ run {code|
            (defmacro m () ''macro)
            (defun m () 'fn)
            (m)
        |code});
    check [fn_of "F"; ExprSymbol "OUTER"; ExprSymbol "OUTER"]
        (run {code|
            (defun f (x) 'OUTER)
            (flet ((f (x)
                        (if x (f x) 'INNER)))
                (f 'x))
            (f 'x)
        |code});
    check [fn_of "F"; ExprSymbol "INNER"; ExprSymbol "OUTER"]
        (run {code|
            (defun f (x) 'OUTER)
            (labels ((f (x)
                        (if x (f nil) 'INNER)))
                (f 'x))
            (f 'x)
        |code});
    check_failure (Failure "No such symbol: #'M") (fun () -> ignore @@ run {code|
            (defun m () 'fun)
            (defmacro m () ''macro)
            #'m
        |code});
    ()

let test_eval_bootstrap () =
    let run s =
        let env = Lispy.Env.empty () in
        let () = ignore @@ eval_all env (parse @@ Lispy.Bootstrap.get_src ()) in
        eval_all env (parse s)
    in
    let check v src = check ("eval: " ^ src) v (run src) in
    check [ExprInt 8] "(1+ 7)";
    check [ExprInt 6] "(1- 7)";
    check [ExprT] "(not nil)";
    check [ExprNil] "(not 3)";
    check [ExprNil] "(not t)";
    check [ExprInt 0] "(length ())";
    check [ExprInt 3] "(length '(1 2 3))";
    check [
            ExprNil;
            listform_of [ExprInt 3; ExprInt 2; ExprInt 1];
            ExprNil;
            listform_of [ExprInt 1; ExprInt 2; ExprInt 3];
        ] {code|
            (setq retval ())
            (setq x '(3 2 1))
            (while x
                (setq retval (cons (car x) retval))
                (setq x (cdr x)))
            retval
        |code};
    check [ExprNil] "(reverse nil)";
    check [listform_of [
            ExprSymbol "Z";
            ExprSymbol "Y";
            ExprSymbol "X";
            ExprSymbol "C";
            ExprSymbol "B";
            ExprSymbol "A";
        ]] "(reverse '(a b c x y z))";
    check [listform_of [ExprSymbol "B"; ExprInt 5]] "(assoc 'b '((a 3) (b 5) (c 7)))";
    check [listform_of [ExprNil; ExprInt 5]] "(assoc nil '(nil (nil 5) (c 7)))";
    check [ExprNil] "(assoc 'not-exist '((a 3) (b 5) (c 7)))";
    check [ExprT] "(> 3 2 1)";
    check [ExprNil] "(> 2 3 1)";
    check [ExprT] "(>= 3 2 2 1)";
    check [ExprNil] "(>= 2 3 3 1)";
    check [ExprInt 13] "(max 3 5 13 7 11)";
    check [ExprInt 3] "(min 3 5 13 7 11)";
    ()

let () =
    let open Alcotest in
    run "lispy"
        [
            ("expr", [
                test_case "is_list" `Quick test_expr_is_list;
                test_case "clist_of_list" `Quick test_expr_clist_of_list;
                test_case "list_of_clist" `Quick test_expr_list_of_clist;
                test_case "rev_clist" `Quick test_expr_rev_clist;
            ]);
            ("parse", [
                test_case "parse" `Quick test_parse;
            ]);
            ("eval", [
                test_case "value" `Quick test_eval_value;
                test_case "expr" `Quick test_eval_expr;
                test_case "unquote" `Quick test_eval_unquote;
                test_case "macro" `Quick test_eval_macro;
                test_case "scope" `Quick test_eval_scope;
                test_case "bootstrap" `Quick test_eval_bootstrap;
            ]);
        ]
