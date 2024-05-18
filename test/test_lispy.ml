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
    let env = (Lispy.Expr.empty_denv (), Lispy.Expr.empty_lenv ()) in
    eval_all env (parse s)

let check = Alcotest.(check (list expr_t))
let check_failure = Alcotest.check_raises "failwith call"

let listform_of = clist_of_list
let fn_of name = ExprFn (name, ref @@ empty_lenv (), ([], None), [])

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
    check [ExprCons (ExprInt 1, ExprInt 2)] "(1 . 2)";
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
    ()

(* let test_eval_unquote () = () *)

let test_eval_macro () =
    let check v src = check ("eval: " ^ src) v (run src) in
    check [ExprSymbol "M"; ExprSymbol "MACRO-M"] "(defmacro m () ''macro-m) (m)";
    check [ExprSymbol "M"; ExprSymbol "ABC"] "(defmacro m (x) `,x) (m 'abc)";
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
    check_failure (Failure "No such symbol: #'M") (fun () -> ignore @@ run {code|
            (defun m () 'fun)
            (defmacro m () ''macro)
            #'m
        |code});
    ()

let () =
    let open Alcotest in
    run "lispy"
        [
            ("expr", [
                test_case "is_list" `Quick test_expr_is_list;
                test_case "clist_of_list" `Quick test_expr_clist_of_list;
                test_case "list_of_clist" `Quick test_expr_list_of_clist;
            ]);
            ("parse", [
                test_case "parse" `Quick test_parse;
            ]);
            ("eval", [
                test_case "value" `Quick test_eval_value;
                test_case "macro" `Quick test_eval_macro;
                test_case "expr" `Quick test_eval_expr;
                test_case "scope" `Quick test_eval_scope;
            ]);
        ]
