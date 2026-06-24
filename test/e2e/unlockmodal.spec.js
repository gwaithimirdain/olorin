// Tests for the modal that announces when completing a level opens a new world at a difficulty
// (via the inter-world rules 1-3), including the difficulty explanation the first time a
// difficulty becomes available.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels } = require('../lib/levels');

const LV = allLevels();
const key = (name) => JSON.stringify(LV.find((l) => l.name === name).saveable);
const inWorld = (A) => LV.filter((l) => l.name.startsWith(A + '-')).map((l) => l.name);
const done = (names, difficulty) => names.map((n) => [key(n), JSON.stringify({ complete: true, difficulty })]);

test.describe('Unlock announcement', () => {
    test('opening a new world is announced (without a difficulty explanation for novice)', async ({ page }) => {
        const olorin = new Olorin(page);
        // 38 of world 1's 48 levels done (excluding 1-1-1); finishing 1-1-1 reaches 80% (rule 1).
        await olorin.seed(done(inWorld('1').filter((n) => n !== '1-1-1').slice(0, 38), 0));
        await olorin.open();
        await olorin.selectLevel('1-1-1');
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.page.waitForTimeout(200);

        expect(await olorin.unlockModalVisible()).toBe(true);
        const text = await olorin.unlockModalText();
        expect(text).toContain('Advanced proposition world is now unlocked at Novice difficulty!');
        // Novice isn't a newly-available difficulty, so no explanation is included.
        expect(text).not.toContain('At Novice difficulty');
    });

    test('the first unlock at a new difficulty includes that difficulty\'s explanation', async ({ page }) => {
        const olorin = new Olorin(page);
        // 13 of world 2's 27 levels done (excluding 2-2-1); finishing 2-2-1 reaches 50% at novice,
        // which opens world 1 ("Proposition world") at Adept -- the first Adept unlock (rule 2).
        await olorin.seed(done(inWorld('2').filter((n) => n !== '2-2-1').slice(0, 13), 0));
        await olorin.open();
        await olorin.selectLevel('2-2-1');

        // Prove P <=> P: an iff-introduction whose two brackets connect assumption to subgoal.
        const iff = await olorin.dragRule('iffI', 500, 250);
        await olorin.connect({ vertex: iff, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.connect({ vertex: iff, sort: 'assumption', label: 'ltor' }, { vertex: iff, sort: 'subgoal', label: 'ltor' });
        await olorin.connect({ vertex: iff, sort: 'assumption', label: 'rtol' }, { vertex: iff, sort: 'subgoal', label: 'rtol' });
        await olorin.page.waitForTimeout(200);
        expect(await olorin.isComplete()).toBe(true);

        const text = await olorin.unlockModalText();
        expect(text).toContain('Proposition world is now unlocked at Adept difficulty!');
        // First time Adept becomes available -> its explanation from the About box is shown.
        expect(text).toContain('At Adept difficulty');
    });
});
