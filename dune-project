(lang dune 2.9)

(name icon)

(generate_opam_files true)

(package
 (name icon)
 (synopsis "icon-why3")
 (description "why3 plugin for icon project")
 (depends
  (ocaml
   (>= "4.14"))
  (why3
   (>= "1.7.0"))
  re
  (ocamlformat
   (and
    :with-test
    (= "0.26.1")))))
