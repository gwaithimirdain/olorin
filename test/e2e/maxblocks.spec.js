// A level's "maxrules" budget: at most that many blocks, not counting the variable, hypothesis and
// conclusion blocks the level starts with.  A budgeted level shows its running block count at the
// top until it is finished, in red once the count goes over; a proof that is correct but over
// budget doesn't complete the level, and the completion pop-up carries the final count.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { conjunctionLevel, oneWireLevel } = require('../lib/levels');

// P, Q |- P∧Q, in a stage with the ∧ rules: provable with a single andI box.  Selected from
// levels.js so a renumbering can't break it.
const LEVEL = conjunctionLevel();

// Prove LEVEL the intended way: both hypotheses into one andI box, and that into the conclusion.
async function proveWithAndI(olorin) {
    const andId = await olorin.dragRule('andI', 500, 250);
    await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: andId, sort: 'input', label: 'fst' });
    await olorin.connect({ vertex: 'hyp1', sort: 'output' }, { vertex: andId, sort: 'input', label: 'snd' });
    await olorin.connect({ vertex: andId, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
    await olorin.waitForTypecheck();
    return andId;
}

// Give LEVEL a budget of `n` blocks, and a ⊤ box in its palette -- a block with an output and no
// inputs, so a spare one left unwired is waste that doesn't stop the proof typechecking.  Both
// have to be set before the level is opened: the palette and the budget are read as it loads.
async function openWithBudget(olorin, n) {
    await olorin.setLevelOption(LEVEL.world, LEVEL.stage, LEVEL.index, 'maxrules', n);
    await olorin.setLevelOption(LEVEL.world, LEVEL.stage, LEVEL.index, 'extrarules', ['topI']);
    await olorin.selectLevel(LEVEL.name);
}

test.describe('Block budgets', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('a level with no budget counts nothing, and any number of blocks completes it', async () => {
        await olorin.selectLevel(LEVEL.name);
        expect(await olorin.blockBanner()).toBe(null);

        await olorin.dragRule('andI', 500, 450);  // a spare box, over any budget there might be
        expect(await olorin.blockBanner()).toBe(null);

        await proveWithAndI(olorin);
        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.completeBannerVisible()).toBe(true);
        expect(await olorin.completeBannerText()).toBe('Level Complete!');
        expect(await olorin.blockBanner()).toBe(null);
    });

    test('counts up from the empty proof as blocks are added', async () => {
        await openWithBudget(olorin, 3);
        expect(await olorin.blockBanner()).toEqual({ text: 'Blocks used: 0/3', over: false });

        await olorin.dragRule('topI', 500, 350);
        await olorin.waitForTypecheck();
        expect(await olorin.blockBanner()).toEqual({ text: 'Blocks used: 1/3', over: false });

        const spare = await olorin.dragRule('topI', 500, 450);
        await olorin.waitForTypecheck();
        expect(await olorin.blockBanner()).toEqual({ text: 'Blocks used: 2/3', over: false });

        await olorin.deleteNode(spare);
        await olorin.waitForTypecheck();
        expect(await olorin.blockBanner()).toEqual({ text: 'Blocks used: 1/3', over: false });
    });

    test('goes red once the count is over, before the proof is anywhere near correct', async () => {
        await openWithBudget(olorin, 1);
        await olorin.dragRule('topI', 500, 350);
        await olorin.dragRule('topI', 500, 450);
        await olorin.waitForTypecheck();

        expect(await olorin.blockBanner()).toEqual({ text: 'Too many blocks!  Used: 2/1', over: true });
        expect(await olorin.isComplete()).toBe(false);
    });

    test('the completion pop-up replaces the count, and carries it', async () => {
        await openWithBudget(olorin, 2);
        await proveWithAndI(olorin);

        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.blockBanner()).toBe(null);
        expect(await olorin.completeBannerVisible()).toBe(true);
        expect(await olorin.completeBannerText()).toBe('Level Complete! Blocks used: 1/2');
    });

    test('a correct proof over the budget is refused, and completes once cut back to it', async () => {
        await openWithBudget(olorin, 1);
        await proveWithAndI(olorin);
        expect(await olorin.isComplete()).toBe(true);

        // A second block -- correct, but one more than the budget allows.
        const spare = await olorin.dragRule('topI', 500, 450);
        await olorin.waitForTypecheck();
        expect(await olorin.blockBanner()).toEqual({ text: 'Too many blocks!  Used: 2/1', over: true });
        // Not complete: no pop-up, and the conclusion stays uncolored.
        expect(await olorin.completeBannerVisible()).toBe(false);
        expect(await olorin.isComplete()).toBe(false);

        // Deleting the spare block brings it back within budget, and it completes as usual.
        await olorin.deleteNode(spare);
        await olorin.waitForTypecheck();
        expect(await olorin.blockBanner()).toBe(null);
        expect(await olorin.completeBannerVisible()).toBe(true);
        expect(await olorin.completeBannerText()).toBe('Level Complete! Blocks used: 1/1');
        expect(await olorin.isComplete()).toBe(true);
    });

    test('an over-budget proof is not recorded as a completion', async () => {
        await openWithBudget(olorin, 1);
        await olorin.dragRule('topI', 500, 450);
        await proveWithAndI(olorin);
        expect(await olorin.blockBanner()).toEqual({ text: 'Too many blocks!  Used: 2/1', over: true });

        expect(await olorin.levelStates(LEVEL.name)).not.toContain('completed');
    });

    test('the budget belongs to the level: leaving for one without it drops the count', async () => {
        await openWithBudget(olorin, 1);
        expect(await olorin.blockBanner()).toEqual({ text: 'Blocks used: 0/1', over: false });

        await olorin.selectLevel(oneWireLevel().name);
        expect(await olorin.blockBanner()).toBe(null);
    });
});
