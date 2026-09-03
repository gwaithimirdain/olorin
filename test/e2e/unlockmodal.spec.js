// Tests for the modal that announces when completing a level opens a new world at a difficulty
// (via the inter-world rules 1-3), including the difficulty explanation the first time a
// difficulty becomes available.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { worlds, world, followerWorlds, worldGateSeeds, oneWireLevel, completions,
        thresholdCount } = require('../lib/levels');
const { hasFixture, readFixture } = require('../lib/fixtures');

// Levels and worlds are chosen structurally, never by id or by position: which worlds completing
// one opens is the declared `previous` relation, not the order the worlds appear in.

// For the novice announcement: a level proved by one wire, and a world that follows its world --
// which finishing 80% of that world opens (rule 1).
const FIRST = oneWireLevel();
const OPENED = followerWorlds(FIRST.world)[0];
// A world's percentage is of its non-bonus levels, and this is the fewest of them that reach
// rule 1's 80%; one less stays below it.
const W1 = world(FIRST.world).counted;
const W1_MOST = thresholdCount(W1.length, 0.8);

// For the adept announcement: the first world follows no world, so rules 1 and 3 ask nothing of it
// and its Adept is gated by rule 2 alone -- every world that follows it at >= 50% novice.  Pushing
// the last of those over that half therefore opens it at Adept, and it is the first Adept unlock.
const TARGET = worlds()[0];
const half = (w) => thresholdCount(w.counted.length, 0.5);
// The world to push over: one that follows TARGET and whose own first level has a captured proof,
// so the test can just restore it (an opener has no stage or predecessor gates of its own).
const CROSSER = followerWorlds(TARGET.number).find((w) => hasFixture(w.levels[0]));
const SOLVE = CROSSER && CROSSER.levels[0];

for (const [ok, what] of [
    [OPENED, 'some world follows the first level\'s world'],
    [CROSSER, 'some world follows the first world and has a fixture proof for its first level'],
    [SOLVE && half(CROSSER) >= 2, 'that world needs at least two levels to reach half complete'],
]) {
    if (!ok) throw new Error(`This suite assumes ${what}; update its selectors for levels.js.`);
}

test.describe('Unlock announcement', () => {
    test('opening a new world is announced (without a difficulty explanation for novice)', async ({ page }) => {
        const olorin = new Olorin(page);
        // One short of world 1's 80% (excluding the level we'll solve); finishing it reaches the
        // threshold, which opens the next world (rule 1).
        await olorin.seed(completions(W1.filter((l) => l !== FIRST).slice(0, W1_MOST - 1), 0));
        await olorin.open();
        await olorin.selectLevel(FIRST.name);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.page.waitForTimeout(200);

        expect(await olorin.unlockModalVisible()).toBe(true);
        const text = await olorin.unlockModalText();
        expect(text).toContain(`${OPENED.name} is now unlocked at Novice difficulty!`);
        // Novice isn't a newly-available difficulty, so no explanation is included.
        expect(text).not.toContain('At Novice difficulty');
    });

    test('the first unlock at a new difficulty includes that difficulty\'s explanation', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed(
            // Enough of TARGET to open CROSSER at novice, so the level we solve is reachable.
            worldGateSeeds(CROSSER.number, 0)
            // Every other world that follows TARGET already past its half, so CROSSER is the last
            // one holding rule 2 shut.
            .concat(followerWorlds(TARGET.number)
                .filter((w) => w.number !== CROSSER.number)
                .flatMap((w) => completions(w.counted.slice(0, half(w)), 0)))
            // And CROSSER itself one short of its half, not counting the level we're about to solve.
            .concat(completions(
                CROSSER.counted.filter((l) => l !== SOLVE).slice(0, half(CROSSER) - 1), 0)));
        await olorin.open();
        await olorin.selectLevel(SOLVE.name);
        expect((await olorin.levelStates(SOLVE.name))[0]).toBe('unlocked');

        // Solving it takes CROSSER to half complete at novice, which opens TARGET at Adept.
        await olorin.restore(readFixture(SOLVE));
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);

        const text = await olorin.unlockModalText();
        expect(text).toContain(`${TARGET.name} is now unlocked at Adept difficulty!`);
        // First time Adept becomes available -> its explanation from the About box is shown.
        expect(text).toContain('At Adept difficulty');
    });
});
