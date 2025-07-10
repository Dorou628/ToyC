(lang dune 2.0)
(using menhir 2.0)

(name toyc)
(version 0.1.0)
(license MIT)

(generate_opam_files true)

(package
 (name toyc)
 (synopsis "A toy C compiler")
 (description "A toy C compiler implementation")
 (depends
  (ocaml (>= 4.08.0))
  (dune (>= 2.0))
  (menhir (>= 2.0))))