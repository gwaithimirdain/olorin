// Tests for the per-difficulty unlock rule (world / stage / level structure + completion %).
// Level A-B-C at difficulty K unlocks only if ALL of:
//   1. every world A follows is >= 80% complete at K       (the first world follows none)
//   2. every world that follows A is >= 50% complete at K-1 (unless K=0)
//   3. every world followed by a world A follows is >= 50% complete at K+1 (unless K=2)
//   4. world A stage B-1 >= 70% complete at K  (unless B is the first stage; a stage can name
//      other stages to require with a `previous` list -- see the "Rule 4" describe block)
//   5. all but 2 of the levels before C in the stage are complete at K
//   6. (novice only) every earlier level in the stage that has a hint is complete
//
// Which worlds a world follows is its own declared `previous` list, so rules 1-3 are about that
// relation and not about world order: world 1 here is followed by both world 2 and world 3.  The
// levels and worlds below are therefore selected structurally from levels.js -- the first level,
// its stage, the stage after it, a world that follows its world -- and never by id or by position.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { inWorld, inStage, stagesInWorld, prereqStages, firstLevel, completions,
        thresholdCount, worlds, world, followerWorlds, worldGateSeeds } = require('../lib/levels');

const FIRST = firstLevel();                            // all a fresh player has unlocked
const STAGE1 = inStage(FIRST.world, FIRST.stage);      // the stage it opens in
const AFTER_FIRST = STAGE1[1];                         // gated on FIRST's hint at novice (rule 6)
// The stage whose rule-4 prerequisite is the first level's stage and nothing else, so completing
// that stage is exactly what opens this one -- which need not be the stage that comes next.
const STAGES1 = stagesInWorld(FIRST.world);
const STAGE2S = STAGES1.find((st) => {
    const pre = prereqStages(st, STAGES1);
    return pre.length === 1 && pre[0].number === FIRST.stage;
});
const STAGE2 = STAGE2S ? STAGE2S.levels : [];
const FOURTH = STAGE2[3];                              // 3 predecessors, so rule 5 wants 1 of them
// A level that is NOT auto-completed at a higher difficulty (it has wires worth redoing), so its
// adept can be locked and unlocked on its own for rules 5 and 7.
const MANUAL = STAGE2.find((l) => !l.autoComplete);

// Seeds that open the first level's world at adept.  Rule 2 asks about every world that FOLLOWS
// it, which is the declared relation and not "the world after it", so this comes from the same
// model of the relation the app uses.
const OPEN_ADEPT = worldGateSeeds(FIRST.world, 1);
// A world that follows this one and nothing else, so this world alone gates it (rule 1), and the
// first of its levels, which has no stage or predecessor gates of its own.
const NEXT = followerWorlds(FIRST.world).find((w) => w.previous.length === 1);
const NEXT_WORLD = NEXT && NEXT.levels[0];
// The levels this world's percentage is of -- a bonus stage doesn't count towards its world -- and
// the fewest of them that reach rule 1's 80%; one less stays below the gate.
const W1 = world(FIRST.world).counted;
const W1_MOST = thresholdCount(W1.length, 0.8);

// The tests below read these facts out of levels.js; say so plainly if it stops providing them.
for (const [ok, what] of [
    [FIRST.hint, 'the first level has a hint (rule 6)'],
    [FIRST.trivial && FIRST.autoComplete, 'the first level is trivial and auto-completing'],
    [AFTER_FIRST, 'the first stage has at least two levels'],
    [FOURTH, 'the second stage has at least four levels'],
    [MANUAL && MANUAL.index > 1, 'the second stage has a non-auto-completing level after its first'],
    [NEXT_WORLD, 'some world follows the first world and only it'],
    [STAGE2S, 'some stage of the first world is gated on the first level\'s stage alone'],
]) {
    if (!ok) throw new Error(`This suite assumes ${what}; update its selectors for levels.js.`);
}


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
        // The worlds that follow this one are >= 50% at novice, satisfying rule 2 for adept; the
        // first level itself is NOT completed.
        const olorin = await open(page, OPEN_ADEPT);
        // Novice stays locked (rule 6 wants the hinted level done); adept unlocks (rule 6 doesn't
        // apply).  An auto-completing level whose novice isn't solved isn't auto-completed either --
        // it just unlocks at adept.
        expect(await olorin.levelStates(AFTER_FIRST.name)).toEqual(['locked', 'unlocked', 'locked']);
    });

    test('auto-complete: a trivial level stays merely unlocked until its novice is solved', async ({ page }) => {
        // The first level unlocks at adept (rule 2 satisfied) but its novice hasn't been solved, so
        // it is NOT auto-completed -- the player must solve it at least once.
        const olorin = await open(page, OPEN_ADEPT);
        expect(await olorin.levelStates(FIRST.name)).toEqual(['unlocked', 'unlocked', 'locked']);
    });

    test('auto-complete: once novice is solved, a trivial level completes its higher difficulties', async ({ page }) => {
        // With its novice solved and adept unlocked, adept auto-completes (no wires worth redoing).
        // Master stays locked (rule 2 would want the following worlds at adept).
        const olorin = await open(page, OPEN_ADEPT.concat(completions([FIRST], 0)));
        expect(await olorin.levelStates(FIRST.name)).toEqual(['completed', 'completed', 'locked']);
        // Auto-completing never advances the global completion counter.
        expect(await page.evaluate(() => localStorage.getItem('time'))).toBeNull();
    });

    test('rule 4: a stage opens when the previous stage is 70% complete', async ({ page }) => {
        // The first stage fully done opens the next one; its first level (no hinted predecessor) unlocks.
        const olorin = await open(page, completions(STAGE1, 0));
        expect((await olorin.levelStates(STAGE2[0].name))[0]).toBe('unlocked');
    });

    test('rule 1: a following world opens only when this one is >= 80% complete at novice', async ({ page }) => {
        // One short of 80% of this world -> the world that follows it stays locked.
        const a = await open(page, completions(W1.slice(0, W1_MOST - 1), 0));
        expect((await a.levelStates(NEXT_WORLD.name))[0]).toBe('locked');
        await page.close();
    });

    test('rule 1: the following world is reachable at >= 80%', async ({ page }) => {
        const olorin = await open(page, completions(W1.slice(0, W1_MOST), 0));
        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('unlocked');
    });

    test('rule 2: adept of a level needs the worlds following it >= 50% complete at novice', async ({ page }) => {
        const a = await open(page);
        expect((await a.levelStates(FIRST.name))[1]).toBe('locked');
        await page.close();
    });

    test('rule 2: adept unlocks with enough novice progress in the worlds that follow', async ({ page }) => {
        // Adept unlocks once every world that follows this one is >= 50% novice (rule 2).  This
        // level's novice isn't solved here, so it isn't auto-completed -- it just unlocks.
        const olorin = await open(page, OPEN_ADEPT);
        expect((await olorin.levelStates(FIRST.name))[1]).toBe('unlocked');
    });

    // For the 4th level of the second stage at adept: rules 1-3 for its world, rule 4 (the first
    // stage >= 70% adept), and rule 5 (>= 1 of the three levels before it done at adept).  Rule 6
    // doesn't apply at adept.
    const rule5Base = () => OPEN_ADEPT.concat(completions(STAGE1, 1));

    test('rule 5: a 4th level is locked with none of its predecessors done (adept)', async ({ page }) => {
        const olorin = await open(page, rule5Base());
        expect((await olorin.levelStates(FOURTH.name))[1]).toBe('locked');
    });

    test('rule 5: that 4th level unlocks once one predecessor is done (adept)', async ({ page }) => {
        const olorin = await open(page, rule5Base().concat(completions([STAGE2[0]], 1)));
        expect((await olorin.levelStates(FOURTH.name))[1]).toBe('unlocked');
    });

    // Adept of a non-auto-completed level is reachable once its world's gates pass at adept (rules
    // 1-3), the first stage is complete at adept (rule 4), and its own stage predecessors are
    // complete at adept (rule 5); rule 7 then gates it on how recently this level's novice was
    // completed (the global "time" counts completions).
    const rule7Base = (time, noviceTime) => OPEN_ADEPT
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
    // A stage with two stages before it that declares no `previous` of its own, so setting the
    // list to null exercises the default rather than whatever levels.js wrote.  Two predecessors
    // is enough to tell [1], [2] and [1, 2] apart.
    const AT = STAGES.findIndex((st, i) => i >= 2 && st.declared === undefined);
    if (AT < 0) {
        throw new Error('This suite assumes the first world has a third-or-later stage that '
                      + 'declares no `previous` of its own; update it.');
    }
    const [S1, S2, TARGET] = [STAGES[AT - 2], STAGES[AT - 1], STAGES[AT]];
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
    if (STAGES.some((st) => st.bonus)) {
        throw new Error('This suite marks a stage bonus itself, so it assumes the first world has '
                      + 'none already; update its selectors for levels.js.');
    }
    const ALL = world(FIRST.world).levels;      // nothing is bonus yet, so all of them count
    const EXTRA = STAGES[STAGES.length - 1];    // the stage these tests mark as bonus
    const REST = ALL.filter((l) => l.stage !== EXTRA.number);
    // What rule 1 asks of this world with and without the bonus stage counted.
    const NEED_ALL = thresholdCount(ALL.length, 0.8);
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

// Which worlds a world follows is its own `previous` list, defaulting to [1].  All three of the
// rules that open a world quantify over the relation: every world it follows must be 80% done at
// this difficulty, every world THEY follow 50% done one difficulty up, and every world that follows
// THIS one 50% done one difficulty down.  These set the lists through test mode's setWorldOption.
test.describe('Rules 1-3: a world\'s "previous" list', () => {
    // A world with no `previous` of its own, far enough in to have two worlds before it, so that
    // clearing the override on it exercises the default rather than a list levels.js wrote.
    const DEFAULTED = worlds().find((w) => w.declared === undefined && w.number >= 3);
    if (worlds().length < 3 || !DEFAULTED) {
        throw new Error('This suite assumes at least three worlds, one of which (not the first two) '
                      + 'declares no `previous` of its own; update it.');
    }
    // The first level of a world, whose own stage and level rules ask for nothing.
    const opener = (w) => inWorld(w)[0];
    const done = (w, difficulty) => completions(inWorld(w), difficulty);
    const state = async (olorin, w) => (await olorin.levelStates(opener(w).name))[0];
    const adept = async (olorin, w) => (await olorin.levelStates(opener(w).name))[1];

    // These tests need a relation they control completely: a world's followers (rule 2) and its
    // predecessors' predecessors (rule 3) depend on what EVERY other world declares, so whatever
    // levels.js happens to say would leak into all of them.  So each test first puts every world
    // on the plain chain -- each following the one before it -- and then sets the list under test.
    async function chain(olorin, overrides = {}) {
        for (const w of worlds()) {
            const has = Object.prototype.hasOwnProperty.call(overrides, w.number);
            await olorin.setWorldOption(w.number, 'previous', has ? overrides[w.number] : [1]);
        }
    }

    test('a world with no list of its own defaults to the one before it', async ({ page }) => {
        const w = DEFAULTED.number;
        // Every world before it is finished except the one right before, so [1] locks it and
        // looking past that one doesn't.
        const olorin = await open(page, worlds()
            .filter((x) => x.number < w && x.number !== w - 1)
            .flatMap((x) => done(x.number, 2)));
        await chain(olorin, { [w]: null }); // no list of its own -> the default
        expect(await state(olorin, w)).toBe('locked');
        await olorin.setWorldOption(w, 'previous', [2]); // ...which was indeed the world before it
        expect(await state(olorin, w)).toBe('unlocked');
    });

    test('by default a world follows the one before it', async ({ page }) => {
        // World 1 is finished, but world 3 waits on world 2, not on world 1.
        const olorin = await open(page, done(1, 0));
        await chain(olorin);
        expect(await state(olorin, 3)).toBe('locked');
        await page.close();
    });

    test('previous: [2] looks past the world in between', async ({ page }) => {
        const olorin = await open(page, done(1, 0));
        await chain(olorin, { 3: [2] });
        // World 3 now follows world 1, which is done -- and world 1 follows nothing, so the
        // grandparent rule asks for nothing either.
        expect(await state(olorin, 3)).toBe('unlocked');
    });

    test('previous: [1, 2] waits for both of them', async ({ page }) => {
        // World 1 done at adept (so the grandparent rule is satisfied too), world 2 untouched.
        const olorin = await open(page, done(1, 1));
        await chain(olorin, { 3: [1, 2] });
        expect(await state(olorin, 3)).toBe('locked');
        await page.close();
    });

    test('previous: [1, 2] opens once both are done', async ({ page }) => {
        const olorin = await open(page, done(1, 1).concat(done(2, 0)));
        await chain(olorin, { 3: [1, 2] });
        expect(await state(olorin, 3)).toBe('unlocked');
    });

    test('previous: [] follows no world at all', async ({ page }) => {
        const olorin = await open(page); // nothing completed anywhere
        await chain(olorin);
        expect(await state(olorin, 2)).toBe('locked');
        await olorin.setWorldOption(2, 'previous', []);
        expect(await state(olorin, 2)).toBe('unlocked');
    });

    test('a world\'s followers gate its higher difficulties', async ({ page }) => {
        // World 1 done at adept opens world 2 at novice, but world 2's ADEPT waits on the world
        // that follows it (rule 2), which nothing has been done in.
        const olorin = await open(page, done(1, 1));
        await chain(olorin);
        expect(await adept(olorin, 2)).toBe('locked');

        // Point world 3 elsewhere and world 2 has no follower left to wait for.
        await olorin.setWorldOption(3, 'previous', []);
        expect(await adept(olorin, 2)).toBe('unlocked');
    });

    test('the worlds a world\'s predecessors follow gate it one difficulty up', async ({ page }) => {
        // Worlds 1 and 2 done at novice: world 3 still waits on world 1 at ADEPT (rule 3).
        const olorin = await open(page, done(1, 0).concat(done(2, 0)));
        await chain(olorin);
        expect(await state(olorin, 3)).toBe('locked');

        // World 3 following world 1 directly leaves nothing beyond it to ask about.
        await olorin.setWorldOption(3, 'previous', [2]);
        expect(await state(olorin, 3)).toBe('unlocked');
    });

    test('...and opens once they are done at that difficulty', async ({ page }) => {
        const olorin = await open(page, done(1, 1).concat(done(2, 0)));
        await chain(olorin);
        expect(await state(olorin, 3)).toBe('unlocked');
    });
});
