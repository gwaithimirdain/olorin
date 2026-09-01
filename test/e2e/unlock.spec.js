// Tests for the per-difficulty unlock rule (world / stage / level structure + completion %).
// Level A-B-C at difficulty K unlocks only if ALL of:
//   1. world A-1 >= 80% complete at K          (unless A is the first world)
//   2. world A+1 >= 50% complete at K-1        (unless K=0 or A is the last world)
//   3. world A-2 >= 50% complete at K+1        (unless A is first/second world or K=2)
//   4. world A stage B-1 >= 70% complete at K  (unless B is the first stage; a stage can name
//      other stages to require with a `previous` list -- see the last describe block)
//   5. all but 2 of the levels before C in the stage are complete at K
//   6. (novice only) every earlier level in the stage that has a hint is complete
//
// The levels below are selected structurally from levels.js (the first level, its stage, the stage
// after it), never by id: inserting a level renumbers everything after it.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { inWorld, inStage, stagesInWorld, firstLevel, completions, thresholdCount } = require('../lib/levels');

const FIRST = firstLevel();                            // all a fresh player has unlocked
const STAGE1 = inStage(FIRST.world, FIRST.stage);      // the stage it opens in
const AFTER_FIRST = STAGE1[1];                         // gated on FIRST's hint at novice (rule 6)
const STAGE2 = inStage(FIRST.world, FIRST.stage + 1);  // the stage after it (rule 4)
const FOURTH = STAGE2[3];                              // 3 predecessors, so rule 5 wants 1 of them
// A level that is NOT auto-completed at a higher difficulty (it has wires worth redoing), so its
// adept can be locked and unlocked on its own for rules 5 and 7.
const MANUAL = STAGE2.find((l) => !l.autoComplete);

// The tests below read these facts out of levels.js; say so plainly if it stops providing them.
for (const [ok, what] of [
    [FIRST.hint, 'the first level has a hint (rule 6)'],
    [FIRST.trivial && FIRST.autoComplete, 'the first level is trivial and auto-completing'],
    [AFTER_FIRST, 'the first stage has at least two levels'],
    [FOURTH, 'the second stage has at least four levels'],
    [MANUAL && MANUAL.index > 1, 'the second stage has a non-auto-completing level after its first'],
]) {
    if (!ok) throw new Error(`This suite assumes ${what}; update its selectors for levels.js.`);
}

const W1 = inWorld(FIRST.world);
const W2 = inWorld(FIRST.world + 1);
// Completion counts that match the app's world gates, derived from the actual level totals so the
// tests don't break when a world's size changes:
const W2_HALF = thresholdCount(W2.length, 0.5); // world 2 >= 50% novice (rule 2)
const W1_MOST = thresholdCount(W1.length, 0.8); // world 1 >= 80% novice (rule 1); W1_MOST-1 is below
// A level of the next world, locked until this world is 80% done (rule 1); the first one has no
// stage or predecessor gates of its own.
const NEXT_WORLD = W2[0];

async function open(page, pairs) {
    const olorin = new Olorin(page);
    if (pairs) await olorin.seed(pairs);
    await olorin.open();
    return olorin;
}

test.describe('Per-difficulty unlocking', () => {
    test('a fresh player has only the first level unlocked (novice)', async ({ page }) => {
        const olorin = await open(page);
        expect(await olorin.levelStates(FIRST.name)).toEqual(['unlocked', 'locked', 'locked']);
        // The next level in the stage is locked: its predecessor has a hint and isn't completed (rule 6).
        expect((await olorin.levelStates(AFTER_FIRST.name))[0]).toBe('locked');
        // The next stage is locked until the previous stage is 70% done (rule 4).
        expect((await olorin.levelStates(STAGE2[0].name))[0]).toBe('locked');
    });

    test('"active" levels (an unlocked, uncompleted difficulty) are highlighted', async ({ page }) => {
        // The first level completed at every difficulty -> not active; the next one then unlocks at
        // novice -> active.
        const olorin = await open(page, completions([FIRST], 2));
        expect(await olorin.levelActive(FIRST.name)).toBe(false);       // fully completed
        expect(await olorin.levelActive(AFTER_FIRST.name)).toBe(true);  // unlocked, not done
        expect(await olorin.levelActive(STAGE2[0].name)).toBe(false);   // locked
    });

    test('rule 6: a level unlocks once the hinted level before it is completed', async ({ page }) => {
        const olorin = await open(page, completions([FIRST], 0));
        expect((await olorin.levelStates(AFTER_FIRST.name))[0]).toBe('unlocked');
    });

    test('rule 6 is novice-only: adept ignores the hint prerequisite', async ({ page }) => {
        // World 2 >= 50% at novice satisfies rule 2 for adept; the first level is NOT completed.
        const olorin = await open(page, completions(W2.slice(0, W2_HALF), 0));
        // Novice stays locked (rule 6 wants the hinted level done); adept unlocks (rule 6 doesn't
        // apply).  An auto-completing level whose novice isn't solved isn't auto-completed either --
        // it just unlocks at adept.
        expect(await olorin.levelStates(AFTER_FIRST.name)).toEqual(['locked', 'unlocked', 'locked']);
    });

    test('auto-complete: a trivial level stays merely unlocked until its novice is solved', async ({ page }) => {
        // The first level unlocks at adept (world 2 >= 50% novice) but its novice hasn't been solved,
        // so it is NOT auto-completed -- the player must solve it at least once.
        const olorin = await open(page, completions(W2.slice(0, W2_HALF), 0));
        expect(await olorin.levelStates(FIRST.name)).toEqual(['unlocked', 'unlocked', 'locked']);
    });

    test('auto-complete: once novice is solved, a trivial level completes its higher difficulties', async ({ page }) => {
        // With its novice solved and adept unlocked, adept auto-completes (no wires worth redoing).
        // Master stays locked (needs world 2 at adept).
        const olorin = await open(page, completions(W2.slice(0, W2_HALF), 0).concat(completions([FIRST], 0)));
        expect(await olorin.levelStates(FIRST.name)).toEqual(['completed', 'completed', 'locked']);
        // Auto-completing never advances the global completion counter.
        expect(await page.evaluate(() => localStorage.getItem('time'))).toBeNull();
    });

    test('rule 4: a stage opens when the previous stage is 70% complete', async ({ page }) => {
        // The first stage fully done opens the next one; its first level (no hinted predecessor) unlocks.
        const olorin = await open(page, completions(STAGE1, 0));
        expect((await olorin.levelStates(STAGE2[0].name))[0]).toBe('unlocked');
    });

    test('rule 1: the next world opens only when this one is >= 80% complete at novice', async ({ page }) => {
        // One short of 80% of world 1 -> world 2 stays locked.
        const a = await open(page, completions(W1.slice(0, W1_MOST - 1), 0));
        expect((await a.levelStates(NEXT_WORLD.name))[0]).toBe('locked');
        await page.close();
    });

    test('rule 1: the next world is reachable at >= 80%', async ({ page }) => {
        const olorin = await open(page, completions(W1.slice(0, W1_MOST), 0));
        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('unlocked');
    });

    test('rule 2: adept of a level needs the next world >= 50% complete at novice', async ({ page }) => {
        const a = await open(page);
        expect((await a.levelStates(FIRST.name))[1]).toBe('locked');
        await page.close();
    });

    test('rule 2: adept unlocks with enough novice progress in the next world', async ({ page }) => {
        // Adept unlocks with world 2 >= 50% novice (rule 2).  This level's novice isn't solved here,
        // so it isn't auto-completed -- it just unlocks.
        const olorin = await open(page, completions(W2.slice(0, W2_HALF), 0));
        expect((await olorin.levelStates(FIRST.name))[1]).toBe('unlocked');
    });

    // For the 4th level of the second stage at adept: rule 2 (world 2 >= 50% novice), rule 4 (the
    // first stage >= 70% adept), and rule 5 (>= 1 of the three levels before it done at adept).
    // Rule 6 doesn't apply at adept.
    const rule5Base = () => completions(W2.slice(0, W2_HALF), 0).concat(completions(STAGE1, 1));

    test('rule 5: a 4th level is locked with none of its predecessors done (adept)', async ({ page }) => {
        const olorin = await open(page, rule5Base());
        expect((await olorin.levelStates(FOURTH.name))[1]).toBe('locked');
    });

    test('rule 5: that 4th level unlocks once one predecessor is done (adept)', async ({ page }) => {
        const olorin = await open(page, rule5Base().concat(completions([STAGE2[0]], 1)));
        expect((await olorin.levelStates(FOURTH.name))[1]).toBe('unlocked');
    });

    // Adept of a non-auto-completed level is reachable once world 2 is >= 50% novice (rule 2), the
    // first stage is complete at adept (rule 4), and its own stage predecessors are complete at
    // adept (rule 5); rule 7 then gates it on how recently this level's novice was completed
    // (the global "time" counts completions).
    const rule7Base = (time, noviceTime) => completions(W2.slice(0, W2_HALF), 0)
        .concat(completions(STAGE1, 1))
        .concat(completions(STAGE2.slice(0, MANUAL.index - 1), 1))
        .concat([['time', String(time)]])
        .concat(completions([MANUAL], 0, { times: { 0: noviceTime } }));

    test('rule 7: a recently-completed lower difficulty re-locks the higher one', async ({ page }) => {
        // Novice completed at time 10, only 5 completions ago (global time 15) -> adept re-locked.
        const olorin = await open(page, rule7Base(15, 10));
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('locked');
    });

    test('rule 7: the higher difficulty unlocks again after more than 10 completions', async ({ page }) => {
        // Novice completed 15 completions ago (global time 25) -> adept available again.
        const olorin = await open(page, rule7Base(25, 10));
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('unlocked');
    });
});

// Rule 4 normally looks at the stage immediately before this one.  A stage can say otherwise with
// a `previous` list of how many stages back each of its prerequisites is (default [1]) -- so two
// tracks can run side by side, or a stage can require several, or none.  No stage in levels.js
// declares one yet, so these drive it through test mode's setStagePrevious.
test.describe('Rule 4: a stage\'s "previous" list', () => {
    const STAGES = stagesInWorld(FIRST.world);
    if (STAGES.length < 3) {
        throw new Error('This suite assumes the first world has at least three stages; update it.');
    }
    const [S1, S2, S3] = STAGES;

    // Complete a whole stage (at novice), which is what rule 4 asks about.
    const stageDone = (levels) => completions(levels, 0);

    test('by default a stage needs the one right before it', async ({ page }) => {
        const olorin = await open(page, stageDone(S1));
        expect((await olorin.levelStates(S2[0].name))[0]).toBe('unlocked'); // its stage is done
        expect((await olorin.levelStates(S3[0].name))[0]).toBe('locked');  // stage 2 isn't
    });

    test('previous: [2] looks past the stage in between', async ({ page }) => {
        const olorin = await open(page, stageDone(S1));
        await olorin.setStagePrevious(FIRST.world, 3, [2]);
        // Stage 3 now asks for stage 1, which is complete -- stage 2 no longer matters.
        expect((await olorin.levelStates(S3[0].name))[0]).toBe('unlocked');
    });

    test('previous: [1, 2] requires both of them', async ({ page }) => {
        const olorin = await open(page, stageDone(S1));
        await olorin.setStagePrevious(FIRST.world, 3, [1, 2]);
        expect((await olorin.levelStates(S3[0].name))[0]).toBe('locked'); // stage 2 still isn't done
        await page.close();
    });

    test('previous: [1, 2] unlocks once both are complete', async ({ page }) => {
        const olorin = await open(page, stageDone(S1).concat(stageDone(S2)));
        await olorin.setStagePrevious(FIRST.world, 3, [1, 2]);
        expect((await olorin.levelStates(S3[0].name))[0]).toBe('unlocked');
    });

    test('previous: [] asks for no stage at all', async ({ page }) => {
        const olorin = await open(page); // nothing completed anywhere
        expect((await olorin.levelStates(S2[0].name))[0]).toBe('locked');
        await olorin.setStagePrevious(FIRST.world, 2, []);
        expect((await olorin.levelStates(S2[0].name))[0]).toBe('unlocked');
    });

    test('prerequisites reaching back past the first stage are ignored', async ({ page }) => {
        const olorin = await open(page);
        // Stage 1 has no stage before it, so [1] (and [3]) name nothing and impose nothing.
        await olorin.setStagePrevious(FIRST.world, 1, [1, 3]);
        expect((await olorin.levelStates(FIRST.name))[0]).toBe('unlocked');
    });

    test('clearing it restores the default', async ({ page }) => {
        const olorin = await open(page, stageDone(S1));
        await olorin.setStagePrevious(FIRST.world, 3, [2]);
        expect((await olorin.levelStates(S3[0].name))[0]).toBe('unlocked');
        await olorin.setStagePrevious(FIRST.world, 3, null);
        expect((await olorin.levelStates(S3[0].name))[0]).toBe('locked');
    });
});
