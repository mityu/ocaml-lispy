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

let check = Alcotest.(check (list expr_t)) "same expr"
let check_failure = Alcotest.check_raises "failwith call"

let listform_of l = ExprList l
let fn_of name = ExprFn (name, ref @@ empty_lenv (), ([], None), [])

let test_parse () =
    check [listform_of [ExprSymbol "#:QUOTE"; ExprSymbol "XYZ"]] (parse "'xyz");
    check
        [listform_of [
            ExprSymbol "#:QUOTE";
            ExprList [listform_of [ExprSymbol "#:UNQUOTE"; ExprSymbol "X"]]
        ]]
        (parse "`(,x)");
    check [ExprInt 123] (parse "123");
    check [ExprInt 123] (parse "+123");
    check [ExprInt (-123)] (parse "-123");
    check [ExprSymbol "+-123"] (parse "+-123");
    ()

let test_eval_value () =
    check [ExprSymbol "FOO"] (run "'foo");
    check [ExprSymbol "XYZ"] (run "' xyz");
    ()

(* let test_eval_unquote () = () *)

let test_eval_macro () =
    check [ExprSymbol "M"; ExprSymbol "MACRO-M"] (run "(defmacro m () 'macro-m) (m)");
    check [ExprSymbol "M"; ExprSymbol "ABC"] (run "(defmacro m (x) `,x) (m 'abc)");
    ()

let test_eval_expr () =
    check [ExprSymbol "XYZ"] (run "(quote xyz)");
    check [ExprList [ExprSymbol "QUOTE"; ExprSymbol "XYZ"]] (run "'(quote xyz)");
    check [fn_of "F"; fn_of "F"] (run "(defun f ()) #'f");
    check [ExprSymbol "VAL"] (run "(let ((x 'val)) x)");
    check [ExprSymbol "XYZ"] (List.tl (run "(defun f () 'xyz) (f)"));
    check [ExprSymbol "ARG"] (List.tl (run "(defun f (x) x) (f 'arg)"));
    check [ExprSymbol "XYZ"] (run "(if () 'abc 'xyz)");
    check [ExprSymbol "ABC"] (run "(if '(a) 'abc 'xyz)");
    ()

let test_eval_scope () =
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
