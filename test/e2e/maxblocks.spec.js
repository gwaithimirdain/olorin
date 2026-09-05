// A level's "maxrules" budget: at most that many blocks, not counting the variable, hypothesis and
// conclusion blocks the level starts with.  The budget is shown with the level's name and
// difficulty, and a proof that is correct but over it doesn't complete the level -- a red pop-up
// says so instead of the "Level Complete!" one.

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

    test('a level with no budget shows none, and any number of blocks completes it', async () => {
        await olorin.selectLevel(LEVEL.name);
        expect(await olorin.maxBlocksText()).toBe(null);

        await olorin.dragRule('andI', 500, 450);  // a spare box, over any budget there might be
        await proveWithAndI(olorin);
        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.completeBannerVisible()).toBe(true);
        expect(await olorin.tooManyBlocksVisible()).toBe(false);
    });

    test('shows the budget, and completes a proof that keeps to it', async () => {
        await openWithBudget(olorin, 1);
        expect(await olorin.maxBlocksText()).toBe('Max blocks: 1');

        await proveWithAndI(olorin);
        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.completeBannerVisible()).toBe(true);
        expect(await olorin.tooManyBlocksVisible()).toBe(false);
    });

    test('a correct proof over the budget is refused, and completes once cut back to it', async () => {
        await openWithBudget(olorin, 1);
        await proveWithAndI(olorin);
        expect(await olorin.isComplete()).toBe(true);

        // A second block -- correct, but one more than the budget allows.
        const spare = await olorin.dragRule('topI', 500, 450);
        await olorin.waitForTypecheck();
        expect(await olorin.tooManyBlocksVisible()).toBe(true);
        expect(await olorin.tooManyBlocksText()).toBe('Too many blocks!  Maximum: 1');
        // Not complete: no pop-up, and the conclusion stays uncolored.
        expect(await olorin.completeBannerVisible()).toBe(false);
        expect(await olorin.isComplete()).toBe(false);

        // Deleting the spare block brings it back within budget, and it completes as usual.
        await olorin.deleteNode(spare);
        await olorin.waitForTypecheck();
        expect(await olorin.tooManyBlocksVisible()).toBe(false);
        expect(await olorin.completeBannerVisible()).toBe(true);
        expect(await olorin.isComplete()).toBe(true);
    });

    test('an over-budget proof is not recorded as a completion', async () => {
        await openWithBudget(olorin, 1);
        await olorin.dragRule('topI', 500, 450);
        await proveWithAndI(olorin);
        expect(await olorin.tooManyBlocksVisible()).toBe(true);

        expect(await olorin.levelStates(LEVEL.name)).not.toContain('completed');
    });

    test('an incomplete proof over the budget shows the errors, not the budget warning', async () => {
        await openWithBudget(olorin, 1);
        // Two blocks, and nothing wired to the conclusion: over budget, but incomplete anyway.
        await olorin.dragRule('topI', 500, 350);
        await olorin.dragRule('topI', 500, 450);
        await olorin.waitForTypecheck();
        expect(await olorin.tooManyBlocksVisible()).toBe(false);
        expect(await olorin.isComplete()).toBe(false);
    });

    test('the budget belongs to the level: leaving for one without it drops it', async () => {
        await openWithBudget(olorin, 1);
        expect(await olorin.maxBlocksText()).toBe('Max blocks: 1');

        await olorin.selectLevel(oneWireLevel().name);
        expect(await olorin.maxBlocksText()).toBe(null);
    });
});
