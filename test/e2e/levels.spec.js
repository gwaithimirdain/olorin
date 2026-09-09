// One test per level: load a known-correct proof from a JSON fixture, restore it onto the
// level, and verify the app accepts it as complete.  This guards every level against being
// broken by future changes to the rules, typechecker, or restore logic.
//
// Fixtures live in test/fixtures/proofs/, named by a hash of the level's statement (see
// lib/fixtures.js), and are generated/refreshed with
//   node test/generate-fixtures.js
// (which solves a proof in a browser and saves its exported JSON).  Levels that don't yet have
// a fixture show up as `fixme` (a tracked TODO) rather than failing, so coverage can grow
// incrementally without breaking the build.
//
// A proof is only a proof of the level if the player could have built it there, so each test also
// checks the fixture against the palette the app actually offers on that level -- its stage's
// `rules` plus the level's own `extrarules` (see client/levels.js).  Fixtures are filed by
// statement, so one can be shared by two levels stating the same thing in different stages, and a
// level's palette can be narrowed long after its proof was captured; either way the proof stops
// being reachable on the level and the test says so, instead of restoring blocks no player could
// have placed.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels } = require('../lib/levels');
const { hasFixture, readFixture, fixtureMatches, proofRules, unavailableRules } =
    require('../lib/fixtures');

test.describe('Levels have a working proof', () => {
    for (const level of allLevels()) {
        if (!hasFixture(level)) {
            // No proof captured yet for this level: track it as an explicit TODO.
            test.fixme(`level ${level.name}`, () => {});
            continue;
        }

        test(`level ${level.name}`, async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.selectLevel(level.name);

            const state = readFixture(level);
            // The filename is derived from the statement, so a fixture always proves the level it
            // is filed under -- unless one was hand-filed under the wrong name.
            expect(fixtureMatches(level, state)).toBe(true);

            // Every block the proof uses has to be in this level's palette -- restore doesn't ask,
            // so without this a fixture could prove the level with a rule it never offers.
            const palette = await olorin.paletteRules();
            expect(palette).toEqual(expect.arrayContaining(level.rules));
            expect({ level: level.name, used: proofRules(state), unavailable: unavailableRules(state, palette) })
                .toEqual({ level: level.name, used: proofRules(state), unavailable: [] });

            await olorin.restore(state);

            expect(await olorin.isComplete()).toBe(true);
        });
    }
});
