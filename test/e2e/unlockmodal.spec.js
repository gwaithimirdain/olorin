// Tests for the modal that announces when completing a level opens a new world at a difficulty
// (via the inter-world rules 1-3), including the difficulty explanation the first time a
// difficulty becomes available.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { inWorld, worldNames, oneWireLevel, iffIdentityLevel, completions, thresholdCount } = require('../lib/levels');

// Levels and worlds come from levels.js rather than being named, since ids shift when levels are
// added or reordered: a level proved by one wire in the first world, and a "P ⇔ P" in any later
// world (the second test is about the world before that one, whichever it turns out to be).
const FIRST = oneWireLevel();
const IFF = iffIdentityLevel((l) => l.world > FIRST.world);
const WORLDS = worldNames();
const W1 = inWorld(FIRST.world);
const W2 = inWorld(IFF.world);
// Counts derived from the actual world sizes, so the tests don't break when a world's size changes.
const W1_MOST = thresholdCount(W1.length, 0.8); // world 1 >= 80% novice (rule 1)
const W2_HALF = thresholdCount(W2.length, 0.5); // world 2 >= 50% novice (rule 2)

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
        expect(text).toContain(`${WORLDS[FIRST.world]} is now unlocked at Novice difficulty!`);
        // Novice isn't a newly-available difficulty, so no explanation is included.
        expect(text).not.toContain('At Novice difficulty');
    });

    test('the first unlock at a new difficulty includes that difficulty\'s explanation', async ({ page }) => {
        const olorin = new Olorin(page);
        // One short of world 2's 50% (excluding the level we'll solve); finishing it reaches 50% at
        // novice, which opens world 1 at Adept -- the first Adept unlock (rule 2).
        await olorin.seed(completions(W2.filter((l) => l !== IFF).slice(0, W2_HALF - 1), 0));
        await olorin.open();
        await olorin.selectLevel(IFF.name);

        // Prove P ⇔ P: an iff-introduction whose two brackets connect assumption to subgoal.
        const iff = await olorin.dragRule('iffI', 500, 250);
        await olorin.connect({ vertex: iff, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.connect({ vertex: iff, sort: 'assumption', label: 'ltor' }, { vertex: iff, sort: 'subgoal', label: 'ltor' });
        await olorin.connect({ vertex: iff, sort: 'assumption', label: 'rtol' }, { vertex: iff, sort: 'subgoal', label: 'rtol' });
        await olorin.page.waitForTimeout(200);
        expect(await olorin.isComplete()).toBe(true);

        const text = await olorin.unlockModalText();
        expect(text).toContain(`${WORLDS[IFF.world - 2]} is now unlocked at Adept difficulty!`);
        // First time Adept becomes available -> its explanation from the About box is shown.
        expect(text).toContain('At Adept difficulty');
    });
});
