// One test per level: load a known-correct proof from a JSON fixture, restore it onto the
// level, and verify the app accepts it as complete.  This guards every level against being
// broken by future changes to the rules, typechecker, or restore logic.
//
// Fixtures live in test/fixtures/proofs/<level-name>.json and are generated/refreshed with
//   node test/generate-fixtures.js
// (which solves a proof in a browser and saves its exported JSON).  Levels that don't yet have
// a fixture show up as `fixme` (a tracked TODO) rather than failing, so coverage can grow
// incrementally without breaking the build.

const fs = require('fs');
const path = require('path');
const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels } = require('../lib/levels');

const FIXTURE_DIR = path.join(__dirname, '..', 'fixtures', 'proofs');

function fixturePath(name) {
    return path.join(FIXTURE_DIR, `${name}.json`);
}

test.describe('Levels have a working proof', () => {
    for (const level of allLevels()) {
        const file = fixturePath(level.name);

        if (!fs.existsSync(file)) {
            // No proof captured yet for this level: track it as an explicit TODO.
            test.fixme(`level ${level.name}`, () => {});
            continue;
        }

        test(`level ${level.name}`, async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.selectLevel(level.name);

            const state = JSON.parse(fs.readFileSync(file, 'utf8'));
            await olorin.restore(state);

            expect(await olorin.isComplete()).toBe(true);
        });
    }
});
