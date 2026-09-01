// Proof fixtures, stored by WHAT a level states rather than where it sits in the game.
//
// A fixture's filename is a hash of the level's canonical statement -- the same
// parameters/variables/hypotheses/conclusion the app itself keys saved proofs by.  So moving a
// level, inserting one before it, or renaming a world leaves its fixture exactly where the tests
// look for it, and only *editing a statement* retires a fixture (rightly: the old proof may no
// longer prove it).  Hand-written fixtures survive renumbering for the same reason.
//
// Each fixture is self-describing: an exported proof carries the level it was made on in its
// "level" field, which `levelOfFixture` reads back, so a bare hash filename loses nothing.

const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const FIXTURE_DIR = path.join(__dirname, '..', 'fixtures', 'proofs');

// The statement of a level, as a canonical string: field order and level metadata (name, hints,
// stage) can't affect it, only the mathematics.  Accepts a level from lib/levels.js, its
// `saveable`, or the `level` field of an exported proof.
function canonicalStatement(level) {
    const s = level.saveable || level;
    if (!s || !s.conclusion) throw new Error('Not a level statement: ' + JSON.stringify(level));
    return JSON.stringify([
        (s.parameters || []).map((p) => [p.name, p.ty]),
        (s.variables || []).map((v) => [v.name, v.ty]),
        (s.hypotheses || []).map((h) => h.ty),
        s.conclusion.ty,
    ]);
}

// The fixture id of a level: the first 64 bits of the sha-256 of its statement.
function statementHash(level) {
    return crypto.createHash('sha256').update(canonicalStatement(level), 'utf8').digest('hex').slice(0, 16);
}

const fixturePath = (level) => path.join(FIXTURE_DIR, `${statementHash(level)}.json`);
const hasFixture = (level) => fs.existsSync(fixturePath(level));
const readFixtureText = (level) => fs.readFileSync(fixturePath(level), 'utf8');
const readFixture = (level) => JSON.parse(readFixtureText(level));

function writeFixture(level, state) {
    fs.mkdirSync(FIXTURE_DIR, { recursive: true });
    fs.writeFileSync(fixturePath(level), JSON.stringify(state, null, 2) + '\n');
    return fixturePath(level);
}

// The statement an exported proof was made on, or null if it doesn't carry one (proofs exported
// before the level was included in the export).
const levelOfFixture = (state) => (state && state.level && state.level.conclusion ? state.level : null);

// Whether a fixture proves the statement it is filed under -- it always should, since the filename
// is derived from the statement, but a hand-filed proof could have been dropped in by hand.
function fixtureMatches(level, state) {
    const stated = levelOfFixture(state);
    return stated === null || canonicalStatement(stated) === canonicalStatement(level);
}

// Every fixture file on disk, split into the levels they cover and orphans (files whose statement
// is no longer in levels.js -- an edited or deleted level).
function coverage(allLevels) {
    const files = fs.existsSync(FIXTURE_DIR)
        ? fs.readdirSync(FIXTURE_DIR).filter((f) => f.endsWith('.json'))
        : [];
    const byHash = new Map(allLevels.map((l) => [statementHash(l), l]));
    const covered = [];
    const orphans = [];
    for (const file of files.sort()) {
        const level = byHash.get(path.basename(file, '.json'));
        if (level) covered.push({ file, level });
        else orphans.push(file);
    }
    return { covered, orphans, dir: FIXTURE_DIR };
}

module.exports = {
    FIXTURE_DIR, canonicalStatement, statementHash, fixturePath, hasFixture,
    readFixture, readFixtureText, writeFixture, levelOfFixture, fixtureMatches, coverage,
};
