(lang dune 3.15)

(name lispy)

(generate_opam_files true)

(source
 (github mityu/ocaml-lispy))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name lispy)
 (synopsis "A toy LISP-like language interpreter.")
 (description "A toy interpreter of LISP-like language written in OCaml.")
 (depends ocaml dune)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
