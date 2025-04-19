(lang dune 3.11)
(license GPL-3.0-or-later)
(authors "Michael Shulman <shulman@sandiego.edu>")
(maintainers "Michael Shulman <shulman@sandiego.edu>")
(source (github gwaithimirdain/olorin))
(package
  (name olorin)
  (synopsis "A graphical game for first-order logic")
  (allow_empty)
  (depends
    (ocaml
      (>= 5.2.1))
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
    pprint
    ppx_blob
    zarith_stubs_js))
(generate_opam_files)
