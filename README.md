# Olorin: A graphical proof game for predicate logic

Olorin is a graphical frontend for Narya that allows the user to prove simple statements in predicate logic.  It runs in a web browser, but once loaded it works offline without a server connection.  See the "about" page for more information.

## Building Olorin

Olorin contains Narya as a git submodule, along with custom code in both OCaml, to be compiled with [js_of_ocaml](https://ocsigen.org/js_of_ocaml/latest/manual/overview), plus pure JavaScript to manage the graphics and interaction with the browser.  To compile it, you'll need all the necessary packages to build Narya, as well as the JavaScript package manager `npm`.  Then run the following commands:
```
opam install zarith_stubs_js
cd olorin
git submodule update
dune build
npm install webpack
npm run build
```

## Serving Olorin

After compiling it, to make Olorin accessible from a web server, place the following files in a directory that will be served by a web server:

- All the files in the directory `static`, including the `main.bundle.js` which should be placed there by `npm run build`.
- `_build/default/bin/olorin.bc.js`, which should be created by `dune build`.
- `node_modules/coi-serviceworker/coi-serviceworker.js`.  This enables SharedArrayBuffer by reloading the page to turn on Cross-Origin Isolation.  It could be avoided if the page is being served by a custom server that can set the [cross-origin headers](https://web.dev/coop-coep/) correctly server-side.
- `node_modules/z3-solver/build/z3-built.js` and `node_modules/z3-solver/build/z3-built.wasm`.  Apparently bundling these file with webpack would prevent them from loading correctly.

For instance, to test Olorin locally, you can run:
```
cd static
ln -s ../_build/default/bin/olorin.bc.js .
ln -s ../node_modules/coi-serviceworker/coi-serviceworker.js .
ln -s ../node_modules/z3-solver/build/z3-built.* .
npx http-server . -o -p 9999
```
If you create symlinks like this rather than copying the files, then changes to the Olorin OCaml code will take effect as soon as you re-run `dune build` and reload the web page.  Changes to the JavaScript side (`client/main.js`) will always take effect as soon as you re-run `npm run build` and reload the web page.  (In both cases, you may need to Shift+Reload.)

## Olorin server

The above instructions compile a version of Olorin that runs entirely client-side in the user's browser, saving the list of completed levels locally in the browser.  There is also a version that stores that information on a server associated with the user's email address; this is intended mainly for students in a class, so that the instructor can download a spreadsheet of grades by student and level.  To compile this version of Olorin, simply change the definition `SERVER = false` in `client/main.js` to say `true` instead, and proceed as above.

The server program is in the `server/` directory; place `server.js` in a directory on your server that contains a subdirectory `static` with the same files from `static` as before, and run it with `node`.  It's designed to communicate with a `couchdb` database using `cradle`, so you'll need to install those things on your server too (for `cradle` you can use `npm`), and it expects a JSON file in its directory called `config.json` that defines the `username` and `password` for the couchdb instance (it assumes localhost and the standard port).

There is also an `sslserver.js` that's designed to use a self-signed certificate (for encryption, not identity verification) and serves the grade-downloading page for instructors, expecting to find `grades.html` and `grades.bundle.js` from `static` in an `sslstatic` subdirectory.  It expects `config.json` to also define the `keyfile` and `crtfile`.
