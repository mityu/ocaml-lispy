let testable_token =
    let open Lispy.Lex in
    let pp fmt v = Format.fprintf fmt "%s" (string_of_token v) in
    Alcotest.testable pp ( = )

let testable_node =
    let open Lispy.Parse in
    let pp fmt v = Format.fprintf fmt "%s" (string_of_node v) in
    Alcotest.testable pp ( = )

let testable_expr =
    let open Lispy.Eval in
    let pp fmt v = Format.fprintf fmt "%s" (string_of_expr v) in
    Alcotest.testable pp ( = )

let test_lex_symbol () =
    let open Lispy.Lex in
    let symbol_of_string s = [TokenSymbol s] in
    let check = Alcotest.(check (list testable_token)) "same token list" in
    check (lex "abc") (symbol_of_string "ABC");
    check (lex "|abc|") (symbol_of_string "|abc|");
    check (lex "|aBc|") (symbol_of_string "|aBc|");
    check (lex "a\\bc") (symbol_of_string "|AbC|");
    check (lex "a\\bc; foo-comment") (symbol_of_string "|AbC|");
    check (lex "|a\nb|") (symbol_of_string "|a\nb|");
    check (lex "#\\a") (symbol_of_string "#\\a");
    check (lex "#\\ab\\c") (symbol_of_string "#\\aBc");
    check (lex "#\\newline") (symbol_of_string "#\\Newline");
    ()

let test_lex_number () =
    let open Lispy.Lex in
    let token_of_number v = [TokenInt v] in
    let symbol_of_string s = [TokenSymbol s] in
    let check = Alcotest.(check (list testable_token)) "same token list" in
    check (lex "123") (token_of_number 123);
    check (lex "+321") (token_of_number 321);
    check (lex "-246") (token_of_number (-246));
    check (lex "+-125") (symbol_of_string "+-125");
    check (lex "125.789") (symbol_of_string "125.789");
    check (lex "-987; comment") (token_of_number (-987));
    ()

let test_lex_list () =
    let open Lispy.Lex in
    let check = Alcotest.(check (list testable_token)) "same token list" in
    let check_raises = Alcotest.check_raises "Check failwith is invoked" in
    check (lex "()") [TokenLParen; TokenRParen];
    check (lex "(foo)") [TokenLParen; TokenSymbol "FOO"; TokenRParen];
    check (lex "|a b| a b") [TokenSymbol "|a b|"; TokenSymbol "A"; TokenSymbol "B"];
    check (lex "\\ab x") [TokenSymbol "|aB|"; TokenSymbol "X"];
    check (lex "`(*foo* ,bar ,(baz))") [
        TokenBackQuote;
        TokenLParen;
        TokenSymbol "*FOO*";
        TokenComma;
        TokenSymbol "BAR";
        TokenComma;
        TokenLParen;
        TokenSymbol "BAZ";
        TokenRParen;
        TokenRParen;
        ];
    check_raises (Failure "String is not closed.") (fun () -> ignore (lex "\""));
    check_raises (Failure "String is not closed.") (fun () -> ignore (lex "\"foo"));
    check_raises (Failure "Bar is not closed.") (fun () -> ignore (lex "|"));
    check_raises (Failure "Bar is not closed.") (fun () -> ignore (lex "|aaa|bbb|"));
    check_raises (Failure "No character follows after \\.") (fun () -> ignore (lex "\\"));
    check_raises (Failure "No character follows after \\.") (fun () -> ignore (lex "\"\\"));
    ()

let test_parse_builtin_symbol () =
    let open Lispy.Parse in
    let check = Alcotest.(check (pair testable_node (list testable_token))) "same node and tokens" in
    let parse s = parse_expr (Lispy.Lex.lex s) in
    check (parse "()") (NodeNil, []);
    check (parse "nil") (NodeNil, []);
    check (parse "t") (NodeTrue, []);
    ()

let test_parse_list () =
    let open Lispy.Parse in
    let check = Alcotest.(check (pair testable_node (list testable_token))) "same node and tokens" in
    let parse s = parse_expr (Lispy.Lex.lex s) in
    check (parse "(() . ())") (NodeConsCell (NodeNil, NodeNil), []);
    check (parse "('foo `bar nil t)") (NodeList [
        NodeQuote (NodeSymbol "FOO");
        NodeQuasiquote (NodeSymbol "BAR");
        NodeNil;
        NodeTrue;
    ], []);
    check (parse "((a b) (x y z)) (foo)") (NodeList [
        NodeList [NodeSymbol "A"; NodeSymbol "B"];
        NodeList [NodeSymbol "X"; NodeSymbol "Y"; NodeSymbol "Z"];
    ], [TokenLParen; TokenSymbol "FOO"; TokenRParen]);
    check (parse "`(foo ,bar)") (NodeQuasiquote (NodeList [
        NodeSymbol "FOO"; NodeUnquote (NodeSymbol "BAR");
    ]), []);
    ()

let new_env () = let open Lispy.Eval in new_scope empty_env

let test_eval_value () =
    let open Lispy in
    let open Lispy.Eval in
    let check = Alcotest.(check (list testable_expr)) "same expr" in
    let eval s = let (_, e) = (Eval.eval (new_env ()) (Parse.parse (Lex.lex s))) in e in
    check (eval "()") [ExprNil];
    check (eval "nil") [ExprNil];
    check (eval "13") [ExprInt 13];
    check (eval "t") [ExprTrue];
    check (eval "t nil 17 ()") [ExprTrue; ExprNil; ExprInt 17; ExprNil];
    ()

let test_eval_expr () =
    let open Lispy in
    let open Lispy.Eval in
    let check = Alcotest.(check (list testable_expr)) "same expr" in
    let check_raises = Alcotest.check_raises "Check failwith is invoked" in
    let eval s = let (_, e) = (Eval.eval (new_env ()) (Parse.parse (Lex.lex s))) in e in
    check (eval "(builtin-defun fst (x y) x)") [ExprSymbol "FST"];
    check (eval "(builtin-let ((v 3)) v)") [ExprInt 3];
    check (eval "(builtin-let* ((x 5) (y x)) y)") [ExprInt 5];
    check (eval "(builtin-defun fst (x y) x) (fst \"a\" \"b\")") [
        ExprSymbol "FST"; ExprString "a"
    ];
    check (eval "(builtin-defun snd (x y) y) (snd \"a\" \"b\")") [
        ExprSymbol "SND"; ExprString "b"
    ];
    check_raises (Failure "No such symbol: X")
        (fun () -> ignore (eval "(builtin-let ((x 5) (y x)) y)"));
    ()

let test_eval_macro () = (* TODO: *)
    let open Lispy in
    let open Lispy.Eval in
    let check = Alcotest.(check (list testable_expr)) "same expr" in
    let check_raises = Alcotest.check_raises "Check failwith is invoked" in
    let eval s = let (_, e) = (Eval.eval (new_env ()) (Parse.parse (Lex.lex s))) in e in
    check (eval "(builtin-defmacro add (x y) (builtin-add x y))") [ExprSymbol "ADD"];
    check_raises (Failure "No such symbol: X")
        (fun () -> ignore (eval "(builtin-let ((x 5) (y x)) y)"));
    ()

let () =
    let open Alcotest in
    run "lispy"
        [
            ("lex", [
                test_case "symbol" `Quick test_lex_symbol;
                test_case "number" `Quick test_lex_number;
                test_case "parenthesis" `Quick test_lex_list;
            ]);
            ("parse", [
                test_case "builtin-symbol" `Quick test_parse_builtin_symbol;
                test_case "list" `Quick test_parse_list;
            ]);
            ("eval", [
                test_case "value" `Quick test_eval_value;
                test_case "expr" `Quick test_eval_expr;
                test_case "macro" `Quick test_eval_macro;
            ]);
        ]
