(lang dune 3.11)
(package
  (name olorin)
  (allow_empty)
  (depends
    (ocaml
      (>= 5.2.0))
    narya
    dune
    zarith
    uuseg
    bwd
    algaeff
    asai
    yuujinchou
    react
    lwt
    lambda-term
    fmlib
    fileutils
    pprint))
(generate_opam_files)
