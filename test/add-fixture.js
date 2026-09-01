// File a hand-made proof as a test fixture.
//
// The auto-solver in generate-fixtures.js only knows a few propositional strategies, so most
// levels have to be captured by hand: solve one in the app, click Export, save the JSON, and run
//   node test/add-fixture.js <exported.json>
//
// The exported proof carries the statement of the level it was made on, so this needs no level
// name: it files the proof under the hash of that statement (see lib/fixtures.js), which is where
// levels.spec.js looks for it -- before and after any renumbering of the levels.

const fs = require('fs');
const { allLevels } = require('./lib/levels');
const { canonicalStatement, statementHash, fixturePath, hasFixture, levelOfFixture, writeFixture } =
    require('./lib/fixtures');

function die(msg) {
    console.error(msg);
    process.exit(1);
}

const file = process.argv[2];
if (!file) die('Usage: node test/add-fixture.js <exported-proof.json>');

let state;
try {
    state = JSON.parse(fs.readFileSync(file, 'utf8'));
} catch (e) {
    die(`Can't read ${file}: ${e.message}`);
}

const stated = levelOfFixture(state);
if (!stated) {
    die(`${file} has no "level" field, so there's no telling what it proves.\n`
        + 'Re-export the proof from the level itself (Export includes the level it was made on).');
}
if (!Array.isArray(state.nodes)) die(`${file} doesn't look like an exported proof (no "nodes").`);
if (state.complete === false) {
    die(`${file} is not a complete proof.  Fixtures are the proofs levels.spec.js asserts\n`
        + 'complete, so finish the proof in the app and export it again.');
}

const level = allLevels().find((l) => canonicalStatement(l) === canonicalStatement(stated));
if (!level) {
    die(`No level in client/levels.js states ${canonicalStatement(stated)}.\n`
        + 'A fixture for a statement no game level makes would never be run (probably a custom level).');
}

const existed = hasFixture(level);
writeFixture(level, state);
console.log(`${existed ? 'Replaced' : 'Added'} the fixture for level ${level.name} (${statementHash(level)})`);
console.log(`  ${fixturePath(level)}`);
