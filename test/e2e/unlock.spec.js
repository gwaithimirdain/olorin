// Tests for the per-difficulty unlock rule (world / stage / level structure + completion %).
// Each level A-B-C at difficulty K unlocks only if ALL of:
//   1. world A-1 >= 80% complete at K          (unless A is the first world)
//   2. world A+1 >= 50% complete at K-1        (unless K=0 or A is the last world)
//   3. world A-2 >= 50% complete at K+1        (unless A is first/second world or K=2)
//   4. world A stage B-1 >= 70% complete at K  (unless B is the first stage)
//   5. all but 2 of the levels before C in the stage are complete at K

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels } = require('../lib/levels');

const LV = allLevels();
const key = (name) => JSON.stringify(LV.find((l) => l.name === name).saveable);
const inWorld = (A) => LV.filter((l) => l.name.startsWith(A + '-')).map((l) => l.name);
const inStage = (A, B) => LV.filter((l) => l.name.startsWith(A + '-' + B + '-')).map((l) => l.name);
// Build completion records (highest difficulty = difficulty) for a set of level names.
const done = (names, difficulty) => names.map((n) => [key(n), JSON.stringify({ complete: true, difficulty })]);

async function open(page, pairs) {
    const olorin = new Olorin(page);
    if (pairs) await olorin.seed(pairs);
    await olorin.open();
    return olorin;
}

test.describe('Per-difficulty unlocking', () => {
    test('a fresh player has only the first levels of world 1 stage 1 unlocked (novice)', async ({ page }) => {
        const olorin = await open(page);
        expect(await olorin.levelStates('1-1-1')).toEqual(['unlocked', 'locked', 'locked']);
        // A later stage stays locked until the previous stage is 70% done (rule 4).
        expect((await olorin.levelStates('1-2-1'))[0]).toBe('locked');
    });

    test('rule 4 + 5: finishing a stage opens the next, with its first three levels available', async ({ page }) => {
        // Stage 1-1 fully done at novice opens stage 1-2 (rule 4: >= 70% of the previous stage).
        const olorin = await open(page, done(inStage('1', '1'), 0));
        expect((await olorin.levelStates('1-2-1'))[0]).toBe('unlocked');
        expect((await olorin.levelStates('1-2-3'))[0]).toBe('unlocked');
        // The 4th level needs at least one of the first three done (rule 5).
        expect((await olorin.levelStates('1-2-4'))[0]).toBe('locked');
    });

    test('rule 5: the 4th level of a stage unlocks once one of the first three is complete', async ({ page }) => {
        const olorin = await open(page, done(inStage('1', '1').concat(['1-2-1']), 0));
        expect((await olorin.levelStates('1-2-4'))[0]).toBe('unlocked');
    });

    test('rule 1: world 2 opens only when world 1 is >= 80% complete at novice', async ({ page }) => {
        const w1 = inWorld('1'); // 48 levels; 80% = 38.4, so 39 unlocks, 38 does not
        let olorin = await open(page, done(w1.slice(0, 38), 0));
        expect((await olorin.levelStates('2-2-1'))[0]).toBe('locked');
        await page.close();
    });

    test('rule 1: world 2 is reachable at >= 80%', async ({ page }) => {
        const w1 = inWorld('1');
        const olorin = await open(page, done(w1.slice(0, 39), 0));
        expect((await olorin.levelStates('2-2-1'))[0]).toBe('unlocked');
    });

    test('rule 2: adept of a level unlocks once the next world is >= 50% complete at novice', async ({ page }) => {
        // Fresh: 1-1-1 adept is locked.
        let olorin = await open(page);
        expect((await olorin.levelStates('1-1-1'))[1]).toBe('locked');
        await page.close();
    });

    test('rule 2: adept unlocks with enough novice progress in the next world', async ({ page }) => {
        const w2 = inWorld('2'); // 27 levels; 50% = 13.5 -> 14
        const olorin = await open(page, done(w2.slice(0, 14), 0));
        expect((await olorin.levelStates('1-1-1'))[1]).toBe('unlocked');
    });
});
