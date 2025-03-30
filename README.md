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

## Building Reduce

To automatically prove algebraic implications, Olorin uses the [reduce](https://reduce-algebra.sourceforge.io/) computer algebra system, which can also be compiled to JavaScript and WebAssembly using Emscripten.  You don't really need to compile Reduce yourself; you can just grab the compiled files from https://reduce-algebra.sourceforge.io/web-reduce/generated/reduce.web.js and https://reduce-algebra.sourceforge.io/web-reduce/generated/reduce.web.wasm.  However, for completeness, here is how to compile it.

First install emscripten 2.0.34 (no other version is known to work):
```
git clone https://github.com/emscripten-core/emsdk.git
cd emsdk
./emsdk install 2.0.34
./emsdk activate 2.0.34
source ./emsdk_env.sh
```
(You'll need to do the `source` command again every time you open a new terminal, unless you put it in your shell initialization file.)  Now install Node.js v16 (no other version is known to work); how to do this may depend on your OS but one possibility is:
```
snap switch node --channel=16
snap refresh node
```
Then you can obtain and compile webreduce, starting with the following.  Version 6789 is the only one known to work.
```
svn checkout -r6789 svn://svn.code.sf.net/p/reduce-algebra/code/trunk reduce-algebra
cd reduce-algebra
./configure --with-csl
cd csl/new-embedded/for-emscripten
```
Now you need to edit the Makefile to add `--host none` to the options with which `../../../../libraries/crlibm/configure` is invoked; you can put it right before `--prefix` on line 167.  Finally, you can run:
```
make webreduce
```
It may be tempting to try to make a somewhat smaller `reduce.web.wasm` file using the `mini-webreduce` mentioned in the Makefile.  However, I have not been able to get that to work.  For one thing, the package `redlog` that Olorin uses is omitted by default from `mini-webreduce`, but even when uncommenting its lines from `package.map` I haven't been able to make a `mini-webreduce` that works (and it doesn't end up being that much smaller anyway).

My experience also suggests that you should not move the directory `reduce-algebra` after you've done any of the compilations steps in it.  If you need to put it somewhere else, delete it and re-clone and re-build.

## Serving Olorin

To make Olorin accessible from a web server, place all the files in the directory `static`, along with `_build/default/bin/olorin.bc.js` and the reduce files `reduce.web.js` and `reduce.web.wasm` (or links to them), in a directory that will be served by a web server.  For instance, to test it locally, you can run:
```
cd static
ln -s ../_build/default/bin/olorin.bc.js .
ln -s ../reduce-algebra/csl/new-embedded/for-emscripten/reduce.web.* .
npx http-server . -o -p 9999
```
If you create symlinks like this rather than copying the files, then changes to the Olorin OCaml code will take effect as soon as you re-run `dune build` and reload the web page.  Changes to the JavaScript side (`client/main.js`) will always take effect as soon as you re-run `npm run build` and reload the web page.  (In both cases, you may need to Shift+Reload.)

## Olorin server

The above instructions compile a version of Olorin that runs entirely client-side in the user's browser, saving the list of completed levels locally in the browser.  There is also a version that stores that information on a server associated with the user's email address; this is intended mainly for students in a class, so that the instructor can download a spreadsheet of grades by student and level.  To compile this version of Olorin, simply change the definition `SERVER = false` in `client/main.js` to say `true` instead, and proceed as above.

The server program is in the `server/` directory; place `server.js` in a directory on your server that contains a subdirectory `static` with the same files from `static` as before, and run it with `node`.  It's designed to communicate with a `couchdb` database using `cradle`, so you'll need to install those things on your server too (for `cradle` you can use `npm`), and it expects a JSON file in its directory called `config.json` that defines the `username` and `password` for the couchdb instance (it assumes localhost and the standard port).

There is also an `sslserver.js` that's designed to use a self-signed certificate (for encryption, not identity verification) and serves the grade-downloading page for instructors, expecting to find `grades.html` and `grades.bundle.js` from `static` in an `sslstatic` subdirectory.  It expects `config.json` to also define the `keyfile` and `crtfile`.
