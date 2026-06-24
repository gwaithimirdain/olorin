# Olorin: A graphical proof game for predicate logic

Olorin is a graphical frontend for [Narya](https://github.com/gwaithimirdain/narya) that allows the user to prove simple statements in predicate logic.  It runs in a web browser, but once loaded it works offline without a server connection.  See the "about" page for more information.

## Prerequisites

Olorin contains Narya as a git submodule, along with custom code in OCaml (compiled with [js_of_ocaml](https://ocsigen.org/js_of_ocaml/latest/manual/overview)) plus pure JavaScript that manages the graphics and browser interaction.  To build it you need:

- An **OCaml/opam** environment with everything required to build Narya (see Narya's own build instructions).  This compiles the proof checker to JavaScript.
- **Node.js and npm**, for the JavaScript client and the build/test tooling.

## Installing dependencies

One-time setup, from the repository root:
```
git submodule update --init --recursive   # fetch the Narya submodule
dune build olorin.opam                     # generate the opam file
opam install . --deps-only                 # install the OCaml dependencies (incl. Narya's)
npm install                                # install the JavaScript dependencies
```

`npm install` also installs the build tools (webpack) and the test runner (`@playwright/test`); see [Testing](#testing) for the extra one-time step of downloading a browser.

## Building Olorin

After the one-time setup above, build everything the browser needs into `static/` with:
```
npm run build:static
```
This compiles the OCaml to JavaScript (`dune build`), bundles the client with webpack (`npm run build`), and copies the runtime assets — `olorin.bc.js`, `z3-built.js`/`z3-built.wasm`, and `coi-serviceworker.js` — into `static/`.  This is the only command you need to rebuild after changing anything.

If you have **only** changed JavaScript or CSS (not the OCaml), you can skip the OCaml step and just run `npm run build`, which refreshes `static/main.bundle.js`.  (In both cases you may need to Shift+Reload the page to pick up the new files.)

## Serving Olorin

Once `static/` has been built, it is self-contained: serve that directory with any static file server.  For local use:
```
npx http-server static -o -p 9999
```
The page needs [cross-origin isolation](https://web.dev/coop-coep/) (for `SharedArrayBuffer`, used by Z3); `coi-serviceworker.js` provides this by reloading the page to turn it on, so a plain static server like `http-server` works.  Alternatively, serve it from a custom server that sets the cross-origin headers itself, in which case `coi-serviceworker.js` is unnecessary.

The runtime assets (`main.bundle.js`, `olorin.bc.js`, `z3-built.*`, `coi-serviceworker.js`) are not checked into git, so a fresh checkout has none of them until you build — `npm run build:static` puts them all in `static/`.

For development, you can instead symlink the generated files into `static/` rather than copying them, so OCaml changes take effect as soon as you re-run `dune build` (and JavaScript changes as soon as you re-run `npm run build`), without re-running the full `build:static`:
```
cd static
ln -s ../_build/default/bin/olorin.bc.js .
ln -s ../node_modules/coi-serviceworker/coi-serviceworker.js .
ln -s ../node_modules/z3-solver/build/z3-built.* .
```

## Testing

Olorin has a Playwright suite that drives the **real built app** in headless Chromium (selecting levels, dragging rules, wiring ports, etc.); see [`test/README.md`](test/README.md) for details.

One-time setup (in addition to `npm install` above):
```
npx playwright install chromium   # download the browser
```
On Linux you may also need its system libraries: `npx playwright install-deps` (requires `sudo`).

The tests run against the built `static/` directory.  The simplest way to run them is:
```
npm test
```
which rebuilds `static/` (via `build:static`, so the `dune` build is incremental — fast unless something actually changed) and then runs the suite, so you never test a stale build.  If you've already built and want to skip straight to the tests, run `npm run test:e2e` instead.  The runner automatically starts a static server with the correct cross-origin headers (`test/server.js`, on port 8123) for the duration of the run.  Use `npm run test:e2e:headed` to watch the tests in a visible browser.

Run the suite via `npm run test:e2e` (not a bare `playwright test`): the npm script uses the project's local `@playwright/test`, whereas a global `playwright` is the browser-automation package only and will report `error: unknown command 'test'`.

## Olorin server

The above instructions compile a version of Olorin that runs entirely client-side in the user's browser, saving the list of completed levels locally in the browser.  There is also a version that stores that information on a server associated with the user's email address; this is intended mainly for students in a class, so that the instructor can download a spreadsheet of grades by student and level.  To compile this version of Olorin, simply change the definition `SERVER = false` in `client/main.js` to say `true` instead, and proceed as above.

The server program is in the `server/` directory; place `server.js` in a directory on your server that contains a subdirectory `static` with the same files from `static` as before, and run it with `node`.  It's designed to communicate with a `couchdb` database using `cradle`, so you'll need to install those things on your server too (for `cradle` you can use `npm`), and it expects a JSON file in its directory called `config.json` that defines the `username` and `password` for the couchdb instance (it assumes localhost and the standard port).

There is also an `sslserver.js` that's designed to use a self-signed certificate (for encryption, not identity verification) and serves the grade-downloading page for instructors, expecting to find `grades.html` and `grades.bundle.js` from `static` in an `sslstatic` subdirectory.  It expects `config.json` to also define the `keyfile` and `crtfile`.
