// The proofs the "Arrange" button is tried out on: every proof fixture (see lib/fixtures.js), plus
// the layouts in fixtures/arrange/ -- proofs kept for how they are laid out rather than for what
// they prove, each on one of the game's levels.  Every case is found by its statement, so none of
// this depends on where the levels are.

const fs = require('fs');
const path = require('path');
const { fixtureLevels } = require('./levels');
const { FIXTURE_DIR, statementHash, levelOfFixture } = require('./fixtures');

const ARRANGE_DIR = path.join(__dirname, '..', 'fixtures', 'arrange');

// Every case, as { name, file, level, state }, where `level` is the level (as lib/levels.js gives
// it) to restore `state` onto.  A file whose statement no level makes is left out.
function arrangeCases() {
    const byHash = new Map(fixtureLevels().map((l) => [statementHash(l), l]));
    const cases = [];
    for (const dir of [FIXTURE_DIR, ARRANGE_DIR]) {
        if (!fs.existsSync(dir)) continue;
        for (const file of fs.readdirSync(dir).filter((f) => f.endsWith('.json')).sort()) {
            const state = JSON.parse(fs.readFileSync(path.join(dir, file), 'utf8'));
            const stated = levelOfFixture(state);
            const level = stated && byHash.get(statementHash(stated));
            if (!level) continue;
            cases.push({ name: path.basename(file, '.json'), file: path.join(dir, file), level, state });
        }
    }
    return cases;
}

// Open a case's level and restore its proof, with an Olorin page object (helpers/olorin.js) that
// has already been opened -- with the case's course code, if its level is in a course.
async function loadCase(olorin, c) {
    await olorin.selectLevel(c.level.name);
    await olorin.restore(c.state);
}

module.exports = { ARRANGE_DIR, arrangeCases, loadCase };
