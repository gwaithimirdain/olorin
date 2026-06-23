# Olorin browser tests

Automated, repeatable browser-interaction tests for the Olorin client, using
[Playwright](https://playwright.dev/). They drive the **real built app** in headless
Chromium: selecting levels, dragging rules from the palette, wiring ports, and clicking
the Save / Load / Clear buttons, then asserting on the resulting proof state.

## Layout

```
playwright.config.js      # Playwright config (repo root): test dir, auto-starts the server
scripts/build-static.sh   # Builds static/ (dune -> js, webpack bundle, copy runtime assets)
test/
  server.js               # Static file server with cross-origin-isolation headers
  helpers/olorin.js       # Page-object: open, selectLevel, dragRule, connect, save/load/clear, state readers
  e2e/                    # Test specs
    autosave.spec.js      # autosave + reload/discard-prompt tests
    exportimport.spec.js  # Export/Import (incl. cross-level switch) tests
```

## Running

The tests run against the built `static/` directory, so build it first. This needs an
opam switch with the project's OCaml dependencies, Node, and the `narya` submodule:

```bash
git submodule update --init --recursive
npm install
npx playwright install chromium     # one-time: download the browser
npm run build:static                # dune build + webpack + copy z3/coi assets
```

Then:

```bash
npm run test:e2e            # headless
npm run test:e2e:headed     # watch it in a real browser window
```

`playwright.config.js` starts `test/server.js` automatically (on port 8123, overridable
with `OLORIN_PORT`) and tears it down at the end. If you already have the server running it
is reused.

After a code change, re-run `npm run build:static` (or at least `npm run build` if only the
client `*.js` changed) before re-testing, since the suite serves the built bundle.

## How interactions are driven

Most gestures are genuine browser events:

- **Level selection / buttons / hint dismissal** — real clicks.
- **Palette drag-and-drop** — real HTML5 `dragstart`/`dragover`/`drop` events that share one
  `DataTransfer`, exactly the contract the app's drop handler reads.

Two things go through a tiny **test seam** instead, `window.__olorin`, which the app exposes
**only** when loaded with `?test` in the URL (it is inert in normal use):

- **Creating wire connections.** Dragging between jsPlumb endpoints is not reliably
  reproducible with synthetic mouse events, so `__olorin.connect(source, target)` makes the
  connection through the same `instance.connect` path a user drag would trigger (it still
  fires the app's connection handler, typechecking, and labelling).
- **Reading proof state for assertions** — `__olorin.nodes()`, `connections()`,
  `complete()`, `savedProofKey()`.

Ports are identified the way the app identifies them: `{ vertex, sort, label }`, e.g.
`{ vertex: 'hyp0', sort: 'output' }` or `{ vertex: andId, sort: 'input', label: 'fst' }`.

## Adding tests

Instantiate the page object and go:

```js
const { Olorin } = require('../helpers/olorin');

test('my scenario', async ({ page }) => {
    const olorin = new Olorin(page);
    await olorin.open();
    await olorin.selectLevel('1-1-1');
    // ...build a proof, save, load, assert with olorin.structuralState()
});
```

`structuralState()` returns a normalized snapshot (nodes tagged by rule + position rather
than by their auto-generated ids, which change when a level is reset) so you can assert that
a Save → Clear → Load cycle reproduces the proof exactly.
