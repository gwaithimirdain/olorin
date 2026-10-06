// Tests for the per-difficulty unlock rule (world / stage / level structure + completion %).
// Level A-B-C at difficulty K unlocks only if ALL of:
//   1. every world A follows is PREVIOUS_WORLD_FRACTION complete at K  (the first world follows none)
//   2. every world that follows A is FOLLOWING_WORLD_FRACTION complete at K-1 (unless K=0)
//   3. every world followed by a world A follows is EARLIER_WORLD_FRACTION complete at K+1
//      (unless K=2)
//   4. world A stage B-1 PREVIOUS_STAGE_FRACTION complete at K  (unless B is the first stage; a
//      stage can name other stages to require with a `previous` list -- see the "Rule 4" describe
//      block)
//   5. all but SKIPPABLE_EARLIER_LEVELS of the levels before C in the stage are complete at K
//   6. (novice only) every earlier level in the stage that has a hint is complete
//   7. (K>0) this level's K-1 was not completed within the last RECENT_COMPLETION_WINDOW
//      completions (see the rule 7 tests)
//   8. (K>0) this level itself is complete at K-1
//
// (The capitalized names are the constants in client/unlock-rules.js, which tests read as UNLOCK.)
//
// A world belonging to a course (see courses.spec.js) is not in this game at all -- it gates
// nothing here and nothing here gates it -- and has a rule of its own instead; everything below
// is about the game's own worlds.
//
// Which worlds a world follows is its own declared `previous` list, so rules 1-3 are about that
// relation and not about world order: world 1 here is followed by both world 2 and world 3.  The
// levels and worlds below are therefore selected structurally from levels.js -- the first level,
// its stage, the stage after it, a world that follows its world -- and never by id or by position.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels, inWorld, inStage, stagesInWorld, prereqStages, firstLevel, completions,
        completionKey, thresholdCount, worlds, world, countedAt, followerWorlds,
        worldGateSeeds, UNLOCK, ruleOn, needsRule } = require('../lib/levels');

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
// The first level of that stage with too many predecessors for rule 5 to waive them all: it wants
// just one of them.
const FOURTH = STAGE2[UNLOCK.SKIPPABLE_EARLIER_LEVELS + 1];
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
// the fewest of them that reach rule 1's fraction; one less stays below the gate.
const W1 = world(FIRST.world).counted;
const W1_MOST = thresholdCount(W1.length, UNLOCK.PREVIOUS_WORLD_FRACTION);

// The tests below read these facts out of levels.js; say so plainly if it stops providing them.
for (const [ok, what] of [
    [FIRST.hint, 'the first level has a hint (rule 6)'],
    [FIRST.trivial && FIRST.autoComplete, 'the first level is trivial and auto-completing'],
    [AFTER_FIRST, 'the first stage has at least two levels'],
    [FOURTH, 'the second stage has a level rule 5 gates'],
    [MANUAL && MANUAL.index > 1, 'the second stage has a non-auto-completing level after its first'],
    [NEXT_WORLD, 'some world follows the first world and only it'],
    [STAGE2S, 'some stage of the first world is gated on the first level\'s stage alone'],
]) {
    if (!ok) throw new Error(`This suite assumes ${what}; update its selectors for levels.js.`);
}


// Adept of a non-auto-completed level is reachable once its world's gates pass at adept (rules
// 1-3), the first stage is complete at adept (rule 4), and its own stage predecessors are
// complete at adept (rule 5); rule 7 then gates it on how recently this level's novice was
// completed (the global "time" counts completions).
const rule7Base = (time, noviceTime) => OPEN_ADEPT
    .concat(completions(STAGE1, 1))
    .concat(completions(STAGE2.slice(0, MANUAL.index - 1), 1))
    .concat([['time', String(time)]])
    .concat(completions([MANUAL], 0, { times: { 0: noviceTime } }));

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
        // The next stage is locked until enough of the previous stage is done (rule 4).
        if (ruleOn(4)) expect((await olorin.levelStates(STAGE2[0].name))[0]).toBe('locked');
    });

    test('"active" levels (an unlocked, uncompleted difficulty) are highlighted', async ({ page }) => {
        // The first level completed at every difficulty -> not active; the next one then unlocks at
        // novice -> active.
        const olorin = await open(page, completions([FIRST], 2));
        expect(await olorin.levelActive(FIRST.name)).toBe(false);       // fully completed
        expect(await olorin.levelActive(AFTER_FIRST.name)).toBe(true);  // unlocked, not done
        if (ruleOn(4)) expect(await olorin.levelActive(STAGE2[0].name)).toBe(false);   // locked
    });

    test('rule 6: a level unlocks once the hinted level before it is completed', async ({ page }) => {
        const olorin = await open(page, completions([FIRST], 0));
        expect((await olorin.levelStates(AFTER_FIRST.name))[0]).toBe('unlocked');
    });

    test('rule 6 is novice-only: adept ignores the hint prerequisite', async ({ page }) => {
        // The worlds that follow this one are far enough along at novice, satisfying rule 2 for adept, and
        // this level is solved at novice (rule 8); the hinted first level is NOT completed.  Adept
        // opens anyway, since rule 6 doesn't apply there (and may then auto-complete).
        const olorin = await open(page, OPEN_ADEPT.concat(completions([AFTER_FIRST], 0)));
        expect((await olorin.levelStates(AFTER_FIRST.name))[1]).not.toBe('locked');
    });

    test('rule 8: a level stays locked above novice until its novice is solved', async ({ page }) => {
        // The first level's world is open at adept (rule 2 satisfied), but its novice hasn't been
        // solved, so its adept stays shut -- and so a trivial level isn't auto-completed there
        // either: the player must solve it at least once.
        const olorin = await open(page, OPEN_ADEPT);
        expect(await olorin.levelStates(FIRST.name)).toEqual(['unlocked', 'locked', 'locked']);
        expect(await olorin.lockExplanation(FIRST.name, 1)).toContain('Complete this level at Novice');
    });

    test('rule 8: master waits for adept, however open the world is at master', async ({ page }) => {
        // MANUAL's world and stage open at master, and its novice solved long ago -- but not adept.
        const olorin = await open(page, worldGateSeeds(FIRST.world, 2)
            .concat(completions(STAGE1, 2))
            .concat(completions(STAGE2.slice(0, MANUAL.index - 1), 2))
            .concat([['time', '100']])
            .concat(completions([MANUAL], 0, { times: { 0: 1 } })));
        expect((await olorin.levelStates(MANUAL.name)).slice(1)).toEqual(['unlocked', 'locked']);
        expect(await olorin.lockExplanation(MANUAL.name, 2)).toContain('Complete this level at Adept');
    });

    test('auto-complete: once novice is solved, a trivial level completes its higher difficulties', async ({ page }) => {
        // With its novice solved and adept unlocked, adept auto-completes (no wires worth redoing).
        // Master stays locked (rule 2 would want the following worlds at adept).
        const olorin = await open(page, OPEN_ADEPT.concat(completions([FIRST], 0)));
        expect(await olorin.levelStates(FIRST.name))
            .toEqual(['completed', 'completed', ruleOn(2) ? 'locked' : 'completed']);
        // Auto-completing never advances the global completion counter.
        expect(await page.evaluate(() => localStorage.getItem('time'))).toBeNull();
    });

    test('rule 4: a stage opens when enough of the previous stage is complete', async ({ page }) => {
        // The first stage fully done opens the next one; its first level (no hinted predecessor) unlocks.
        const olorin = await open(page, completions(STAGE1, 0));
        expect((await olorin.levelStates(STAGE2[0].name))[0]).toBe('unlocked');
    });

    test('rule 1: a following world opens only when enough of this one is complete at novice', async ({ page }) => {
        needsRule(test, 1);
        // One short of rule 1's fraction of this world -> the world that follows it stays locked.
        const a = await open(page, completions(W1.slice(0, W1_MOST - 1), 0));
        expect((await a.levelStates(NEXT_WORLD.name))[0]).toBe('locked');
        await page.close();
    });

    test('rule 1: the following world is reachable at rule 1\'s fraction', async ({ page }) => {
        const olorin = await open(page, completions(W1.slice(0, W1_MOST), 0));
        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('unlocked');
    });

    test('rule 1 above novice leaves out the levels that complete themselves there', async ({ page }) => {
        needsRule(test, 1);
        // Enough at adept of this world's levels that aren't autoComplete, and none of those that
        // are: enough to open the world after it at adept (with rule 2's followers seeded too).
        const auto = W1.filter((l) => l.autoComplete);
        if (auto.length === 0) throw new Error('This test needs autoComplete levels in the first world.');
        const manual = countedAt(world(FIRST.world), 1);
        expect(thresholdCount(manual.length, UNLOCK.PREVIOUS_WORLD_FRACTION))
            .toBeLessThan(thresholdCount(W1.length, UNLOCK.PREVIOUS_WORLD_FRACTION));
        const olorin = await open(page, worldGateSeeds(NEXT.number, 1));
        for (const l of auto) expect((await olorin.levelStates(l.name))[1], l.name).not.toBe('completed');
        await olorin.openChooser();
        const adept = page.locator(`#worldMap .world-node[data-world="${NEXT.number}"] .lvmark >> nth=1`);
        expect(await adept.getAttribute('class')).not.toContain('locked');
    });

    test('rule 2: adept of a level needs enough of the worlds following it complete at novice', async ({ page }) => {
        needsRule(test, 2);
        const a = await open(page, completions([FIRST], 0));
        expect((await a.levelStates(FIRST.name))[1]).toBe('locked');
        await page.close();
    });

    test('rule 2: adept unlocks with enough novice progress in the worlds that follow', async ({ page }) => {
        // Adept unlocks once enough of every world that follows this one is novice (rule 2), with this
        // level's own novice solved (rule 8) -- whereupon, being trivial, it auto-completes.
        const olorin = await open(page, OPEN_ADEPT.concat(completions([FIRST], 0)));
        expect((await olorin.levelStates(FIRST.name))[1]).toBe('completed');
    });

    // For FOURTH at adept: rules 1-3 for its world, rule 4 (enough of the first stage at adept),
    // rule 5 (>= 1 of the levels before it done at adept), and rule 8
    // (its own novice solved).  Rule 6 doesn't apply at adept.
    const rule5Base = () => OPEN_ADEPT.concat(completions(STAGE1, 1)).concat(completions([FOURTH], 0));

    test('rule 5: a level past the waived ones is locked with none of its predecessors done (adept)', async ({ page }) => {
        const olorin = await open(page, rule5Base());
        expect((await olorin.levelStates(FOURTH.name))[1]).toBe('locked');
    });

    test('rule 5: that level unlocks once one predecessor is done (adept)', async ({ page }) => {
        const olorin = await open(page, rule5Base().concat(completions([STAGE2[0]], 1)));
        expect((await olorin.levelStates(FOURTH.name))[1]).not.toBe('locked');
    });

    test('rule 7: a recently-completed lower difficulty re-locks the higher one', async ({ page }) => {
        // Novice completed at time 10, just RECENT_COMPLETION_WINDOW completions ago -> adept re-locked.
        const olorin = await open(page, rule7Base(10 + UNLOCK.RECENT_COMPLETION_WINDOW, 10));
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('locked');
    });

    test('rule 7: the higher difficulty unlocks again after more than RECENT_COMPLETION_WINDOW completions', async ({ page }) => {
        // Novice completed one more completion ago than that -> adept available again.
        const olorin = await open(page, rule7Base(11 + UNLOCK.RECENT_COMPLETION_WINDOW, 10));
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('unlocked');
    });

    // The wait is counted in completions, so a player with nothing left to complete would be
    // waiting for something they have no way to make happen: with the whole game finished at
    // novice, the levels whose novice they finished last would be the only ones left at adept, and
    // all of them shut.  So finishing every level at the difficulty below lifts the wait.  "Every
    // level" means every level this player has: a world belonging to a course they aren't taking is
    // no part of their game, and allLevels() leaves those out as the app does.
    const finished = (time) => completions(allLevels(), 0)
        .concat(completions(STAGE1, 1))
        .concat(completions(STAGE2.slice(0, MANUAL.index - 1), 1))
        .concat([['time', String(time)]])
        // This level's novice was the last thing solved, so its adept is inside the window.
        .concat(completions([MANUAL], 0, { times: { 0: time } }));
    // Some level elsewhere, to leave unsolved: not one of the seeds above.
    const ELSEWHERE = allLevels().filter((l) => l !== MANUAL && !STAGE1.includes(l)
                                           && !STAGE2.slice(0, MANUAL.index - 1).includes(l)).pop();

    test('rule 7: is lifted when every level is complete at the difficulty below', async ({ page }) => {
        const olorin = await open(page, finished(20));
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('unlocked');
    });

    test('rule 7: ...but not while some level of it is still unsolved', async ({ page }) => {
        // The same, minus one level nobody has solved: there is still something to do, so the
        // window is a wait the player can actually finish.
        const olorin = await open(page, finished(20).filter(([key]) => key !== completionKey(ELSEWHERE)));
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('locked');
    });
});

// With a level under the pointer, the chooser's preview panel says, for each difficulty of it that's
// locked, what remains to be done to open it.
test.describe('The preview of a locked difficulty', () => {
    test('names the hinted level still to be solved (rule 6)', async ({ page }) => {
        const olorin = await open(page);
        const tip = await olorin.lockExplanation(AFTER_FIRST.name, 0);
        expect(tip).toMatch(/^To unlock Novice:\n/);
        expect(tip).toContain(`Complete level ${FIRST.name}, which introduces something new`);
    });

    test('counts the levels still wanted in the world before (rule 1)', async ({ page }) => {
        needsRule(test, 1);
        const olorin = await open(page, completions(W1.slice(0, W1_MOST - 1), 0));
        expect(await olorin.lockExplanation(NEXT_WORLD.name, 0))
            .toContain(`Complete 1 more level of ${world(FIRST.world).name}`);
    });

    test('counts the completions still to wait out (rule 7)', async ({ page }) => {
        // Novice completed at time 10, partway through the window: the rest of it plus one more
        // completion take it past.
        const ago = Math.floor(UNLOCK.RECENT_COMPLETION_WINDOW / 2);
        const olorin = await open(page, rule7Base(10 + ago, 10));
        const n = UNLOCK.RECENT_COMPLETION_WINDOW - ago + 1;
        expect(await olorin.lockExplanation(MANUAL.name, 1)).toBe(
            `To unlock Adept:\n• You solved this level at Novice too recently: complete ${n} more level${n === 1 ? '' : 's'} ` +
            'first (or every level at Novice)');
    });

    test('is absent once the difficulty is unlocked', async ({ page }) => {
        const olorin = await open(page, completions([FIRST], 0));
        expect(await olorin.lockExplanation(AFTER_FIRST.name, 0)).toBeNull();
    });
});

// Rule 4 normally looks at the stage immediately before this one.  A stage can say otherwise with
// a `previous` list naming its prerequisites among its world's stages -- so two tracks can run
// side by side, or a stage can require several, or none.  These set the list
// themselves through test mode's setStageOption, so they hold whatever levels.js declares.
test.describe('Rule 4: a stage\'s "previous" list', () => {
    const STAGES = stagesInWorld(FIRST.world);
    // A stage with two stages before it that declares no `previous` of its own, so setting the
    // list to null exercises the default rather than whatever levels.js wrote.  Two predecessors
    // is enough to tell naming one, the other, and both apart.
    const AT = STAGES.findIndex((st, i) => i >= 2 && st.declared === undefined);
    if (AT < 0) {
        throw new Error('This suite assumes the first world has a third-or-later stage that '
                      + 'declares no `previous` of its own; update it.');
    }
    const [S1, S2, TARGET] = [STAGES[AT - 2], STAGES[AT - 1], STAGES[AT]];
    const done = (stage) => completions(stage.levels, 0);
    // Set TARGET's list to name these stages (null = no list of its own) and read its first
    // level's novice state.
    async function stateWith(olorin, stages) {
        await olorin.setStageOption(FIRST.world, TARGET.number, 'previous',
                                    stages && stages.map((st) => st.name));
        return (await olorin.levelStates(TARGET.levels[0].name))[0];
    }

    test('with no list, a stage needs the one right before it', async ({ page }) => {
        needsRule(test, 4);
        const olorin = await open(page, done(S1));
        expect(await stateWith(olorin, null)).toBe('locked'); // the stage before it isn't done
        await page.close();
    });

    test('previous can look past the stage in between', async ({ page }) => {
        const olorin = await open(page, done(S1));
        // The stage two back is complete, and the one in between no longer matters.
        expect(await stateWith(olorin, [S1])).toBe('unlocked');
    });

    test('previous with two stages requires both of them', async ({ page }) => {
        needsRule(test, 4);
        const olorin = await open(page, done(S1));
        expect(await stateWith(olorin, [S2, S1])).toBe('locked'); // the nearer stage isn't done
        await page.close();
    });

    test('previous with two stages unlocks once both are complete', async ({ page }) => {
        const olorin = await open(page, done(S1).concat(done(S2)));
        expect(await stateWith(olorin, [S2, S1])).toBe('unlocked');
    });

    test('previous: [] asks for no stage at all', async ({ page }) => {
        needsRule(test, 4);
        const olorin = await open(page); // nothing completed anywhere
        expect(await stateWith(olorin, [S2])).toBe('locked');
        expect(await stateWith(olorin, [])).toBe('unlocked');
    });

    test('the list levels.js declares is what applies until overridden', async ({ page }) => {
        // Whatever TARGET declares, completing exactly the stages it names unlocks its first level.
        const olorin = await open(page, prereqStages(TARGET, STAGES).flatMap(done));
        expect((await olorin.levelStates(TARGET.levels[0].name))[0]).toBe('unlocked');
    });
});

// A `bonus` stage is extra credit: its levels are left out of its world's totals, so the
// percentages that open worlds (rules 1-3) are of the non-bonus levels only -- but a bonus level
// solved counts towards them, in place of one that isn't.  The stage rules (4-6) still treat it
// like any other stage.
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
    const NEED_ALL = thresholdCount(ALL.length, UNLOCK.PREVIOUS_WORLD_FRACTION);
    const NEED_REST = thresholdCount(REST.length, UNLOCK.PREVIOUS_WORLD_FRACTION);
    if (UNLOCK.PREVIOUS_WORLD_FRACTION > 0 && NEED_REST >= NEED_ALL) {
        throw new Error('This suite assumes the first world\'s last stage is big enough to move the '
                        + 'rule 1 gate; update its selectors for levels.js.');
    }
    const done = (stage) => completions(stage.levels, 0);

    test('its levels are dropped from the world percentage that opens the next world', async ({ page }) => {
        needsRule(test, 1);
        // Enough of the other stages to pass rule 1's fraction of the non-bonus levels, but not of
        // all of them.
        const olorin = await open(page, completions(REST.slice(0, NEED_REST), 0));
        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('locked');

        await olorin.setStageOption(FIRST.world, EXTRA.number, 'bonus', true);

        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('unlocked');
    });

    test('a bonus level solved counts towards it, in place of one that is not', async ({ page }) => {
        needsRule(test, 1);
        // One short of rule 1's fraction of the non-bonus levels, and one bonus level: short of it
        // for the whole world, but, with the bonus stage left out of the total, enough.
        const olorin = await open(page, completions(REST.slice(0, NEED_REST - 1).concat([EXTRA.levels[0]]), 0));
        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('locked');

        await olorin.setStageOption(FIRST.world, EXTRA.number, 'bonus', true);

        expect((await olorin.levelStates(NEXT_WORLD.name))[0]).toBe('unlocked');
    });

    test('its own levels still unlock by the ordinary stage rules', async ({ page }) => {
        // Rule 4 is about stages, not the world, so a bonus stage opens exactly as it would have:
        // complete the stages it names as prerequisites and its first level is available.
        const olorin = await open(page, prereqStages(EXTRA, STAGES).flatMap(done));
        await olorin.setStageOption(FIRST.world, EXTRA.number, 'bonus', true);
        expect((await olorin.levelStates(EXTRA.levels[0].name))[0]).toBe('unlocked');
    });

    test('it still counts for the stage after it', async ({ page }) => {
        needsRule(test, 4);
        // A stage that requires only the one before it, so marking that one bonus is the only
        // change in play.
        const AFTER = STAGES.find((st) => st.previous.length === 1 && st.previous[0] === st.number - 1);
        const BEFORE = STAGES[AFTER.number - 2];
        const olorin = await open(page);
        await olorin.setStageOption(FIRST.world, BEFORE.number, 'bonus', true);
        // Not complete: still locked, exactly as an ordinary predecessor would leave it.
        expect((await olorin.levelStates(AFTER.levels[0].name))[0]).toBe('locked');
        await page.close();
    });

    test('and satisfies that stage once complete', async ({ page }) => {
        const AFTER = STAGES.find((st) => st.previous.length === 1 && st.previous[0] === st.number - 1);
        const BEFORE = STAGES[AFTER.number - 2];
        const olorin = await open(page, prereqStages(BEFORE, STAGES).flatMap(done).concat(done(BEFORE)));
        await olorin.setStageOption(FIRST.world, BEFORE.number, 'bonus', true);
        expect((await olorin.levelStates(AFTER.levels[0].name))[0]).toBe('unlocked');
    });
});

// Which worlds a world follows is its own `previous` list of names.  All three of the
// rules that open a world quantify over the relation: every world it follows must be far enough
// along at this difficulty, every world THEY follow one difficulty up, and every world that follows
// THIS one one difficulty down.  These set the lists through test mode's setWorldOption.
test.describe('Rules 1-3: a world\'s "previous" list', () => {
    if (worlds().length < 3) {
        throw new Error('This suite assumes at least three worlds; update it.');
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
    // `overrides` maps a world's number to the numbers of the worlds it should follow instead.
    async function chain(olorin, overrides = {}) {
        const all = worlds();
        for (const [i, w] of all.entries()) {
            const has = Object.prototype.hasOwnProperty.call(overrides, w.number);
            const follows = has ? overrides[w.number] : i > 0 ? [all[i - 1].number] : [];
            await follow(olorin, w.number, follows);
        }
    }
    // Make world `w` follow the worlds numbered `ws`, by name.
    const follow = (olorin, w, ws) =>
        olorin.setWorldOption(w, 'previous', ws.map((x) => world(x).name));

    test('a world following the one before it waits on that one only', async ({ page }) => {
        needsRule(test, 1);
        // World 1 is finished, but world 3 waits on world 2, not on world 1.  (Finished at adept,
        // so that rule 3, asking after world 1 one difficulty up, isn't what holds world 3 back.)
        const olorin = await open(page, done(1, 1));
        await chain(olorin);
        expect(await state(olorin, 3)).toBe('locked');
        await page.close();
    });

    test('previous can look past the world in between', async ({ page }) => {
        const olorin = await open(page, done(1, 0));
        await chain(olorin, { 3: [1] });
        // World 3 now follows world 1, which is done -- and world 1 follows nothing, so the
        // grandparent rule asks for nothing either.
        expect(await state(olorin, 3)).toBe('unlocked');
    });

    test('previous with two worlds waits for both of them', async ({ page }) => {
        needsRule(test, 1);
        // World 1 done at adept (so the grandparent rule is satisfied too), world 2 untouched.
        const olorin = await open(page, done(1, 1));
        await chain(olorin, { 3: [2, 1] });
        expect(await state(olorin, 3)).toBe('locked');
        await page.close();
    });

    test('previous with two worlds opens once both are done', async ({ page }) => {
        const olorin = await open(page, done(1, 1).concat(done(2, 0)));
        await chain(olorin, { 3: [2, 1] });
        expect(await state(olorin, 3)).toBe('unlocked');
    });

    test('previous: [] follows no world at all', async ({ page }) => {
        needsRule(test, 1);
        const olorin = await open(page); // nothing completed anywhere
        await chain(olorin);
        expect(await state(olorin, 2)).toBe('locked');
        await follow(olorin, 2, []);
        expect(await state(olorin, 2)).toBe('unlocked');
    });

    test('a world\'s followers gate its higher difficulties', async ({ page }) => {
        needsRule(test, 2);
        // World 1 done at adept opens world 2 at novice, but world 2's ADEPT waits on the world
        // that follows it (rule 2), which nothing has been done in.  (Its level is solved at
        // novice, for rule 8.)
        const olorin = await open(page, done(1, 1).concat(completions([opener(2)], 0)));
        await chain(olorin);
        expect(await adept(olorin, 2)).toBe('locked');

        // Point world 3 elsewhere and world 2 has no follower left to wait for.
        await follow(olorin, 3, []);
        expect(await adept(olorin, 2)).not.toBe('locked');
    });

    test('the worlds a world\'s predecessors follow gate it one difficulty up', async ({ page }) => {
        needsRule(test, 3);
        // Worlds 1 and 2 done at novice: world 3 still waits on world 1 at ADEPT (rule 3).  World
        // 1's novice was all solved just now, so rule 7 keeps its adept shut and none of its
        // levels can auto-complete there.
        const olorin = await open(page, completions(inWorld(1), 0, { times: { 0: 1 } })
            .concat(done(2, 0)).concat([['time', '1']]));
        await chain(olorin);
        expect(await state(olorin, 3)).toBe('locked');

        // World 3 following world 1 directly leaves nothing beyond it to ask about.
        await follow(olorin, 3, [1]);
        expect(await state(olorin, 3)).toBe('unlocked');
    });

    test('...and opens once they are done at that difficulty', async ({ page }) => {
        const olorin = await open(page, done(1, 1).concat(done(2, 0)));
        await chain(olorin);
        expect(await state(olorin, 3)).toBe('unlocked');
    });
});
