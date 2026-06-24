// Tests for the per-difficulty unlock rule (world / stage / level structure + completion %).
// Level A-B-C at difficulty K unlocks only if ALL of:
//   1. world A-1 >= 80% complete at K          (unless A is the first world)
//   2. world A+1 >= 50% complete at K-1        (unless K=0 or A is the last world)
//   3. world A-2 >= 50% complete at K+1        (unless A is first/second world or K=2)
//   4. world A stage B-1 >= 70% complete at K  (unless B is the first stage)
//   5. all but 2 of the levels before C in the stage are complete at K
//   6. (novice only) every earlier level in the stage that has a hint is complete
//
// Hint facts used below (from levels.js): 1-1-1, 1-1-2, 1-2-1 and 1-2-3 all have hints.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels } = require('../lib/levels');

const LV = allLevels();
const key = (name) => JSON.stringify(LV.find((l) => l.name === name).saveable);
const inWorld = (A) => LV.filter((l) => l.name.startsWith(A + '-')).map((l) => l.name);
const inStage = (A, B) => LV.filter((l) => l.name.startsWith(A + '-' + B + '-')).map((l) => l.name);
const done = (names, difficulty) => names.map((n) => [key(n), JSON.stringify({ complete: true, difficulty })]);

async function open(page, pairs) {
    const olorin = new Olorin(page);
    if (pairs) await olorin.seed(pairs);
    await olorin.open();
    return olorin;
}

test.describe('Per-difficulty unlocking', () => {
    test('a fresh player has only level 1-1-1 unlocked (novice)', async ({ page }) => {
        const olorin = await open(page);
        expect(await olorin.levelStates('1-1-1')).toEqual(['unlocked', 'locked', 'locked']);
        // 1-1-2 is locked: its predecessor 1-1-1 has a hint and isn't completed (rule 6).
        expect((await olorin.levelStates('1-1-2'))[0]).toBe('locked');
        // The next stage is locked until the previous stage is 70% done (rule 4).
        expect((await olorin.levelStates('1-2-1'))[0]).toBe('locked');
    });

    test('"active" levels (an unlocked, uncompleted difficulty) are highlighted', async ({ page }) => {
        // 1-1-1 completed at every difficulty -> not active; 1-1-2 then unlocked at novice -> active.
        const olorin = await open(page, done(['1-1-1'], 2));
        expect(await olorin.levelActive('1-1-1')).toBe(false); // fully completed
        expect(await olorin.levelActive('1-1-2')).toBe(true);  // unlocked, not done
        expect(await olorin.levelActive('1-2-1')).toBe(false); // locked
    });

    test('rule 6: a level unlocks once the hinted level before it is completed', async ({ page }) => {
        const olorin = await open(page, done(['1-1-1'], 0));
        expect((await olorin.levelStates('1-1-2'))[0]).toBe('unlocked');
    });

    test('rule 6 is novice-only: adept ignores the hint prerequisite', async ({ page }) => {
        // World 2 >= 50% at novice satisfies rule 2 for 1-1-2 adept; 1-1-1 is NOT completed.
        const olorin = await open(page, done(inWorld('2').slice(0, 14), 0));
        // Novice stays locked (rule 6 wants 1-1-1 done); adept unlocks (rule 6 doesn't apply).
        // 1-1-2 is autoComplete, but its novice isn't solved, so it isn't auto-completed -- it just
        // unlocks at adept.
        expect(await olorin.levelStates('1-1-2')).toEqual(['locked', 'unlocked', 'locked']);
    });

    test('auto-complete: a trivial level stays merely unlocked until its novice is solved', async ({ page }) => {
        // 1-1-1 unlocks at adept (world 2 >= 50% novice) but its novice hasn't been solved, so it is
        // NOT auto-completed -- the player must solve it at least once.
        const olorin = await open(page, done(inWorld('2').slice(0, 14), 0));
        expect(await olorin.levelStates('1-1-1')).toEqual(['unlocked', 'unlocked', 'locked']);
    });

    test('auto-complete: once novice is solved, a trivial level completes its higher difficulties', async ({ page }) => {
        // With 1-1-1's novice solved and adept unlocked, adept auto-completes (no wires worth
        // redoing).  Master stays locked (needs world 2 at adept).
        const olorin = await open(page, done(inWorld('2').slice(0, 14), 0).concat(done(['1-1-1'], 0)));
        expect(await olorin.levelStates('1-1-1')).toEqual(['completed', 'completed', 'locked']);
        // Auto-completing never advances the global completion counter.
        expect(await page.evaluate(() => localStorage.getItem('time'))).toBeNull();
    });

    test('rule 4: a stage opens when the previous stage is 70% complete', async ({ page }) => {
        // Stage 1-1 fully done opens stage 1-2; its first level (no hinted predecessor) unlocks.
        const olorin = await open(page, done(inStage('1', '1'), 0));
        expect((await olorin.levelStates('1-2-1'))[0]).toBe('unlocked');
    });

    test('rule 1: world 2 opens only when world 1 is >= 80% complete at novice', async ({ page }) => {
        const w1 = inWorld('1'); // 48 levels; 80% = 38.4, so 39 unlocks but 38 does not
        const a = await open(page, done(w1.slice(0, 38), 0));
        expect((await a.levelStates('2-2-1'))[0]).toBe('locked');
        await page.close();
    });

    test('rule 1: world 2 is reachable at >= 80%', async ({ page }) => {
        const olorin = await open(page, done(inWorld('1').slice(0, 39), 0));
        expect((await olorin.levelStates('2-2-1'))[0]).toBe('unlocked');
    });

    test('rule 2: adept of a level needs the next world >= 50% complete at novice', async ({ page }) => {
        const a = await open(page);
        expect((await a.levelStates('1-1-1'))[1]).toBe('locked');
        await page.close();
    });

    test('rule 2: adept unlocks with enough novice progress in the next world', async ({ page }) => {
        // 1-1-1 adept unlocks with world 2 >= 50% novice (rule 2).  Its novice isn't solved here, so
        // it isn't auto-completed -- it just unlocks.
        const olorin = await open(page, done(inWorld('2').slice(0, 14), 0));
        expect((await olorin.levelStates('1-1-1'))[1]).toBe('unlocked');
    });

    // For 1-2-4 adept: rule 2 (world 2 >= 50% novice), rule 4 (stage 1-1 >= 70% adept), and rule 5
    // (>= 1 of the first three of stage 1-2 done at adept).  Rule 6 doesn't apply at adept.
    const rule5Base = () => done(inWorld('2').slice(0, 14), 0).concat(done(inStage('1', '1'), 1));

    test('rule 5: a 4th level is locked with none of its predecessors done (adept)', async ({ page }) => {
        const olorin = await open(page, rule5Base());
        expect((await olorin.levelStates('1-2-4'))[1]).toBe('locked');
    });

    test('rule 5: that 4th level unlocks once one predecessor is done (adept)', async ({ page }) => {
        const olorin = await open(page, rule5Base().concat(done(['1-2-1'], 1)));
        expect((await olorin.levelStates('1-2-4'))[1]).toBe('unlocked');
    });

    // Adept of 1-2-5 (a non-trivial, non-auto-completed level) is reachable once world 2 is >= 50%
    // novice (rule 2), stage 1-1 is complete at adept (rule 4), and its stage-1-2 predecessors are
    // complete at adept (rule 5); rule 7 then gates it on how recently this level's novice was
    // completed (global "time" counts completions).
    const rule7Base = (time, noviceTime) => done(inWorld('2').slice(0, 14), 0)
        .concat(done(inStage('1', '1'), 1))
        .concat(done(['1-2-1', '1-2-2', '1-2-3', '1-2-4'], 1))
        .concat([
            ['time', String(time)],
            [key('1-2-5'), JSON.stringify({ complete: true, difficulty: 0, times: { 0: noviceTime } })],
        ]);

    test('rule 7: a recently-completed lower difficulty re-locks the higher one', async ({ page }) => {
        // Novice completed at time 10, only 5 completions ago (global time 15) -> adept re-locked.
        const olorin = await open(page, rule7Base(15, 10));
        expect((await olorin.levelStates('1-2-5'))[1]).toBe('locked');
    });

    test('rule 7: the higher difficulty unlocks again after more than 10 completions', async ({ page }) => {
        // Novice completed 15 completions ago (global time 25) -> adept available again.
        const olorin = await open(page, rule7Base(25, 10));
        expect((await olorin.levelStates('1-2-5'))[1]).toBe('unlocked');
    });
});
