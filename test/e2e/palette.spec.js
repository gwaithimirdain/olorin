// Which rules a level's palette offers: its stage's `rules`, plus any the level itself lists in
// `extrarules` -- for a level that needs a box the rest of its stage doesn't.  And that every
// block in it says what it does, on hovering.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { find, inStage } = require('../lib/levels');

// The extra rules to hand a level.  Any two would do; the ∧ boxes are in the earliest stage that
// has any, so a stage without them is easy to come by.
const EXTRA = ['andI', 'andE'];

// A level whose stage offers rules of its own but neither of those, with a sibling level to check
// the extras don't leak onto.  Levels declare `extrarules` themselves, so the test sets one rather
// than naming a level that happens to carry one today.
const LEVEL = find((l) => l.rules.length > 0 && EXTRA.every((r) => !l.rules.includes(r))
                       && inStage(l.world, l.stage).length > 1,
    'in a stage that offers rules of its own but neither ∧ rule, and holds more than one level');
const SIBLING = inStage(LEVEL.world, LEVEL.stage).find((l) => l.name !== LEVEL.name);

test.describe("A level's extra rules", () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('are added to the palette on top of its stage\'s own', async () => {
        await olorin.selectLevel(LEVEL.name);
        const stageRules = await olorin.paletteRules();
        expect(stageRules).not.toContain('andI');

        await olorin.setLevelOption(LEVEL.world, LEVEL.stage, LEVEL.index, 'extrarules', EXTRA);
        await olorin.selectLevel(LEVEL.name);

        const withExtras = await olorin.paletteRules();
        // Everything the stage offered is still there, with the level's own added to it.
        expect(withExtras).toEqual(expect.arrayContaining(stageRules.concat(EXTRA)));
        expect(withExtras).toHaveLength(stageRules.length + EXTRA.length);
    });

    test('are the declaring level\'s alone, not its stage\'s', async () => {
        await olorin.selectLevel(SIBLING.name);
        const before = await olorin.paletteRules();

        await olorin.setLevelOption(LEVEL.world, LEVEL.stage, LEVEL.index, 'extrarules', EXTRA);
        await olorin.selectLevel(SIBLING.name);
        expect(await olorin.paletteRules()).toEqual(before);

        // And clearing the field puts the declaring level's own palette back.
        await olorin.selectLevel(LEVEL.name);
        expect(await olorin.paletteRules()).toEqual(expect.arrayContaining(EXTRA));
        await olorin.setLevelOption(LEVEL.world, LEVEL.stage, LEVEL.index, 'extrarules', null);
        await olorin.selectLevel(LEVEL.name);
        expect(await olorin.paletteRules()).not.toContain('andI');
    });

    test('can be dragged onto the diagram like any other rule', async () => {
        await olorin.setLevelOption(LEVEL.world, LEVEL.stage, LEVEL.index, 'extrarules', EXTRA);
        await olorin.selectLevel(LEVEL.name);

        const id = await olorin.dragRule('andI', 400, 300);
        expect((await olorin.nodes()).find((n) => n.id === id).rule).toBe('andI');
    });
});

test.describe('Every block in the palette', () => {
    test('says what it is for, so a player can find out by hovering it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // A custom level offers the whole palette, so this sees every block there is.
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: 'P', conclusion: 'P' });
        const untitled = await page.evaluate(() =>
            Array.from(document.getElementById('palette').children)
                .filter((e) => e.classList.contains('rule'))
                .filter((e) => !(e.title || '').trim())
                .map((e) => e.id));
        expect(untitled).toEqual([]);
    });
});
