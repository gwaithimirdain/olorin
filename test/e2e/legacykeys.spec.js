// Levels are stored under the statement they ask you to prove.  When the notation for prefix minus
// changed (∸ to −, April 2025), the levels that used it would have become different levels and
// their records orphaned, so those levels carry a `saveable` block naming the statement they used
// to have, and everything was keyed by that instead.
//
// That is now deprecated: the key is the level's real statement, and records still filed under the
// old one are copied across when the game opens.  These tests cover that migration, and go away
// with it (see client/levels.js).

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels, completionKey, legacyCompletionKeys } = require('../lib/levels');

// A level whose statement's notation changed, so its records may be under the older key.
const MOVED = allLevels().find((l) => l.legacySaveables.length > 0);
if (!MOVED) {
    throw new Error('No level carries a legacy `saveable` block any more; delete this spec with it.');
}
// The statement it was stored under before it was restated.
const OLD_KEY = legacyCompletionKeys(MOVED)[0];

const record = (page, key) => page.evaluate((k) => {
    const v = localStorage.getItem(k);
    return v ? JSON.parse(v) : null;
}, key);

test.describe('Records under a level\'s pre-2025 key', () => {
    const solved = JSON.stringify({ complete: true, difficulty: 1, times: { 0: 3 } });
    const proof = JSON.stringify({ nodes: [], connections: [] });

    test('are copied to the key the level uses now', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed([
            [OLD_KEY, solved],
            ['proof:0:' + OLD_KEY, proof],
        ]);
        await olorin.open();

        // The completion and the saved proof are now filed under the current key...
        expect(await record(page, completionKey(MOVED))).toEqual(JSON.parse(solved));
        expect(await record(page, 'proof:0:' + completionKey(MOVED))).toEqual(JSON.parse(proof));
        // ...and the level reads as completed, which is the point of the exercise.
        expect((await olorin.levelStates(MOVED.name))[0]).toBe('completed');
        // The old copies are left where they are, for an older cached build of the game.
        expect(await record(page, OLD_KEY)).toEqual(JSON.parse(solved));
    });

    test('never overwrite what is already stored under the current key', async ({ page }) => {
        const newer = JSON.stringify({ complete: true, difficulty: 2 });
        const olorin = new Olorin(page);
        await olorin.seed([
            [OLD_KEY, solved],
            [completionKey(MOVED), newer],
        ]);
        await olorin.open();

        expect(await record(page, completionKey(MOVED))).toEqual(JSON.parse(newer));
    });

    test('a proof exported before the change still imports into its level', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(allLevels()[0].name);

        // An export from before the notation changed names the statement the level had then.
        await olorin.importText(JSON.stringify({
            level: MOVED.legacySaveables[0], complete: false, difficulty: 0, nodes: [], connections: [],
        }));

        // It's recognized as that level, rather than offering to build a custom one from it.
        expect(await olorin.currentLevelName()).toBe(MOVED.name);
    });

    test('a level that never moved is untouched', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const staying = allLevels().filter((l) => l.legacySaveables.length === 0);
        // Nothing was invented for the levels with no old key: a fresh profile stays empty.
        const keys = await page.evaluate(() => Object.keys(localStorage));
        expect(keys.filter((k) => k.startsWith('{'))).toEqual([]);
        expect(staying.length).toBeGreaterThan(0);
    });
});
