(lang dune 3.15)

(name lispy)

(generate_opam_files true)

(source
 (github mityu/ocaml-lispy))

(authors "mityu")

(maintainers "mityu")

(license "Tbe MIT License")

(documentation https://github.com/mityu/ocaml-lispy)

(package
 (name lispy)
 (synopsis "A toy LISP-like language interpreter.")
 (description "A toy interpreter of LISP-like language written in OCaml.")
 (depends ocaml dune)
 (tags
  ("LISP-interpreter")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
