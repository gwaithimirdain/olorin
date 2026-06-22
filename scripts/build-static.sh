#!/usr/bin/env bash
# Build everything the browser app (and the test suite) needs into static/.
#
# Mirrors the GitHub Actions "Build" workflow: compiles the OCaml proof checker to
# JavaScript via js_of_ocaml, bundles the client with webpack, and copies the Z3 and
# cross-origin-isolation runtime assets into static/.
#
# Prerequisites: an opam switch with the project's OCaml deps (see dune-project), node,
# and the `narya` submodule checked out (git submodule update --init --recursive).
set -euo pipefail
cd "$(dirname "$0")/.."

echo "==> dune build (OCaml -> JS)"
opam exec -- dune build olorin.opam
opam exec -- dune build

echo "==> webpack bundle"
npm run build

echo "==> copying runtime assets into static/"
# Use install so repeated runs overwrite the (read-only) dune output cleanly.
install -m 0644 _build/default/bin/olorin.bc.js static/olorin.bc.js
install -m 0644 node_modules/coi-serviceworker/coi-serviceworker.js static/coi-serviceworker.js
install -m 0644 node_modules/z3-solver/build/z3-built.js node_modules/z3-solver/build/z3-built.wasm static/

echo "==> done. static/ is ready to serve."
