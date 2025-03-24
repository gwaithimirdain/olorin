# Olorin: A graphical proof game for predicate logic

Olorin is a graphical frontend for Narya that allows the user to prove abstract statements in predicate logic.  See the "about" page for more information.

## Installation

To create an Olorin web page, you will need the JavaScript package manager `npm`.  Once you have this, run the following commands:
```
opam install zarith_stubs_js
cd olorin
dune build
npm install webpack
npm run build
```
Now place all the files `index.html`, `styles.css`, `main.bundle.js`, and `resize-handle-right.svg` from `static`, along with `_build/default/bin/olorin.bc.js`, in a directory that will be served by a web server.  For instance, to test it locally, you can run:
```
cd static
ln -s ../../_build/default/bin/olorin.bc.js .
npx http-server . -o -p 9999
```
With this, changes to the OCaml code will take effect as soon as you re-run `dune build` and reload the web page, while changes to the JavaScript side (`client/main.js`) will take effect as soon as you re-run `npm run build` and reload the web page.

The above instructions compile a version of Olorin that runs entirely client-side in the user's browser, saving the list of completed levels locally in the browser.  There is also a version that stores that information on a server associated with the user's email address; this is intended mainly for students in a class, so that the instructor can download a spreadsheet of grades by student and level.  To compile this version of Olorin, simply change the definition `SERVER = false` in `client/main.js` to say `true` instead, and proceed as above.

The server program is in the `server/` directory; place `server.js` in a directory on your server that contains a subdirectory `static` with the same files from `static` as before, and run it with `node`.  It's designed to communicate with a `couchdb` database using `cradle`, so you'll need to install those things too (for `cradle` you can use `npm`), and it expects a JSON file in its directory called `config.json` that defines the `username` and `password` for the couchdb instance (it assumes localhost and the standard port).

The `sslserver.js` version is designed to use a self-signed certificate (for encryption, not identity verification) and serves the grade-downloading page for instructors, expecting to find `grades.html` and `grades.bundle.js` from `static` in an `sslstatic` subdirectory.  It expects `config.json` to also define the `keyfile` and `crtfile`.
