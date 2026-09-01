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
const { inWorld, inStage, stagesInWorld, prereqStages, firstLevel, completions, thresholdCount } = require('../lib/levels');

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
// tracks can run side by side, or a stage can require several, or none.  These set the list
// themselves through test mode's setStageOption, so they hold whatever levels.js declares.
test.describe('Rule 4: a stage\'s "previous" list', () => {
    const STAGES = stagesInWorld(FIRST.world);
    if (STAGES.length < 3) {
        throw new Error('This suite assumes the first world has at least three stages; update it.');
    }
    // The third stage, with the two before it: enough to tell [1], [2] and [1, 2] apart.
    const [S1, S2, TARGET] = STAGES;
    const done = (stage) => completions(stage.levels, 0);
    // Set TARGET's list (null = whatever levels.js says) and read its first level's novice state.
    async function stateWith(olorin, previous) {
        await olorin.setStageOption(FIRST.world, TARGET.number, 'previous', previous);
        return (await olorin.levelStates(TARGET.levels[0].name))[0];
    }

    test('with no list, a stage needs the one right before it', async ({ page }) => {
        const olorin = await open(page, done(S1));
        expect(await stateWith(olorin, null)).toBe('locked'); // the stage before it isn't done
        await page.close();
    });

    test('previous: [2] looks past the stage in between', async ({ page }) => {
        const olorin = await open(page, done(S1));
        // The stage two back is complete, and the one in between no longer matters.
        expect(await stateWith(olorin, [2])).toBe('unlocked');
    });

    test('previous: [1, 2] requires both of them', async ({ page }) => {
        const olorin = await open(page, done(S1));
        expect(await stateWith(olorin, [1, 2])).toBe('locked'); // the nearer stage isn't done
        await page.close();
    });

    test('previous: [1, 2] unlocks once both are complete', async ({ page }) => {
        const olorin = await open(page, done(S1).concat(done(S2)));
        expect(await stateWith(olorin, [1, 2])).toBe('unlocked');
    });

    test('previous: [] asks for no stage at all', async ({ page }) => {
        const olorin = await open(page); // nothing completed anywhere
        expect(await stateWith(olorin, [1])).toBe('locked');
        expect(await stateWith(olorin, [])).toBe('unlocked');
    });

    test('prerequisites reaching back past the first stage are ignored', async ({ page }) => {
        const olorin = await open(page);
        // The first stage has nothing before it, so [1] (and [3]) name nothing and impose nothing.
        await olorin.setStageOption(FIRST.world, 1, 'previous', [1, 3]);
        expect((await olorin.levelStates(FIRST.name))[0]).toBe('unlocked');
    });

    test('the list levels.js declares is what applies until overridden', async ({ page }) => {
        // Whatever TARGET declares, completing exactly the stages it names unlocks its first level.
        const olorin = await open(page, prereqStages(TARGET, STAGES).flatMap(done));
        expect((await olorin.levelStates(TARGET.levels[0].name))[0]).toBe('unlocked');
    });
});

// A `bonus` stage is extra credit: its levels are left out of its world's totals, so the
// percentages that open worlds (rules 1-3) are of the non-bonus levels only.  The stage rules
// (4-6) still treat it like any other stage.
test.describe('A stage marked "bonus"', () => {
    const STAGES = stagesInWorld(FIRST.world);
    const EXTRA = STAGES[STAGES.length - 1];    // the stage these tests mark as bonus
    const REST = W1.filter((l) => l.stage !== EXTRA.number);
    // What rule 1 asks of this world with and without the bonus stage counted.
    const NEED_ALL = thresholdCount(W1.length, 0.8);
    const NEED_REST = thresholdCount(REST.length, 0.8);
    if (NEED_REST >= NEED_ALL) {
        throw new Error('This suite assumes the first world\'s last stage is big enough to move the '
                        + '80% gate; update its selectors for levels.js.');
    }
    const done = (stage) => completions(stage.levels, 0);

    test('its levels are dropped from the world percentage that opens the next world', async ({ page }) => {
        // Enough of the other stages to pass 80% of the non-bonus levels, but not of all of them.
        const olorin = await open(page, completions(REST.slice(0, NEED_REST), 0));
        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('locked');

        await olorin.setStageOption(FIRST.world, EXTRA.number, 'bonus', true);

        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('unlocked');
    });

    test('completing bonus levels does not help open the next world', async ({ page }) => {
        // One short of 80% of the non-bonus levels, plus the whole bonus stage: enough to pass 80%
        // of the world as a whole, but the bonus levels don't count.
        const olorin = await open(page, completions(REST.slice(0, NEED_REST - 1), 0).concat(done(EXTRA)));
        expect(NEED_REST - 1 + EXTRA.levels.length).toBeGreaterThanOrEqual(NEED_ALL);

        await olorin.setStageOption(FIRST.world, EXTRA.number, 'bonus', true);

        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('locked');
    });

    test('its own levels still unlock by the ordinary stage rules', async ({ page }) => {
        // Rule 4 is about stages, not the world, so a bonus stage opens exactly as it would have:
        // complete the stages it names as prerequisites and its first level is available.
        const olorin = await open(page, prereqStages(EXTRA, STAGES).flatMap(done));
        await olorin.setStageOption(FIRST.world, EXTRA.number, 'bonus', true);
        expect((await olorin.levelStates(EXTRA.levels[0].name))[0]).toBe('unlocked');
    });

    test('it still counts for the stage after it', async ({ page }) => {
        // A stage that requires only the one before it, so marking that one bonus is the only
        // change in play.
        const AFTER = STAGES.find((st) => st.number > 1 && st.previous.length === 1 && st.previous[0] === 1);
        const BEFORE = STAGES[AFTER.number - 2];
        const olorin = await open(page);
        await olorin.setStageOption(FIRST.world, BEFORE.number, 'bonus', true);
        // Not complete: still locked, exactly as an ordinary predecessor would leave it.
        expect((await olorin.levelStates(AFTER.levels[0].name))[0]).toBe('locked');
        await page.close();
    });

    test('and satisfies that stage once complete', async ({ page }) => {
        const AFTER = STAGES.find((st) => st.number > 1 && st.previous.length === 1 && st.previous[0] === 1);
        const BEFORE = STAGES[AFTER.number - 2];
        const olorin = await open(page, prereqStages(BEFORE, STAGES).flatMap(done).concat(done(BEFORE)));
        await olorin.setStageOption(FIRST.world, BEFORE.number, 'bonus', true);
        expect((await olorin.levelStates(AFTER.levels[0].name))[0]).toBe('unlocked');
    });
});
