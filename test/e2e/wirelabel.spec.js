// The "Label this wire" dialog, which pops up above novice difficulty whenever a wire is drawn
// between two blocks.  Its Cancel button puts the dialog away; a wire just drawn goes with it,
// since it was never labelled, while a label being corrected on a wire that already has one leaves
// that wire exactly as it was.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// P∧Q ⊢ P∧Q at adept, taken apart and put back together: the wires between the two blocks are
// the ones that prompt (a wire from a hypothesis or to the conclusion doesn't).
async function openLevel(page, difficulty) {
    const olorin = new Olorin(page);
    await olorin.seed([['difficulty', String(difficulty)]]);
    await olorin.open();
    await olorin.buildCustom({
        parameters: 'P : Type\nQ : Type', variables: '',
        hypotheses: 'P∧Q', conclusion: 'P∧Q',
    });
    const nodes = await olorin.nodes();
    const andE = await olorin.dragRule('andE', 350, 250);
    const andI = await olorin.dragRule('andI', 650, 250);
    await olorin.connect({ vertex: nodes.find((n) => n.rule === 'hypothesis').id, sort: 'output' },
                         { vertex: andE, sort: 'input' });
    return { olorin, andE, andI };
}

// Draw the wire that prompts: the ∧-elimination's first half into the ∧-introduction's.
const drawWire = (olorin, andE, andI) =>
    olorin.connect({ vertex: andE, sort: 'output', label: 'fst' },
                   { vertex: andI, sort: 'input', label: 'fst' });

const wireBetween = async (olorin, andE, andI) =>
    (await olorin.connections()).find((c) => c.source.vertex === andE && c.target.vertex === andI);

for (const [name, difficulty] of [['adept', 1], ['master', 2]]) {
    test.describe(`The wire-label dialog on ${name}`, () => {
        test('pops up for a new wire between two blocks', async ({ page }) => {
            const { olorin, andE, andI } = await openLevel(page, difficulty);
            await drawWire(olorin, andE, andI);
            await expect(page.locator('#wireBG')).toBeVisible();
        });

        test('Cancel closes it and takes the new wire away again', async ({ page }) => {
            const { olorin, andE, andI } = await openLevel(page, difficulty);
            await drawWire(olorin, andE, andI);
            await page.click('#cancelWire');

            await expect(page.locator('#wireBG')).toBeHidden();
            expect(await wireBetween(olorin, andE, andI)).toBeUndefined();
        });

        test('and the wire can simply be drawn again afterwards', async ({ page }) => {
            const { olorin, andE, andI } = await openLevel(page, difficulty);
            await drawWire(olorin, andE, andI);
            await page.click('#cancelWire');
            await drawWire(olorin, andE, andI);

            await expect(page.locator('#wireBG')).toBeVisible();
            // The box comes up empty, not still holding what the cancelled one had.
            expect(await page.inputValue('#wire')).toBe('');
            await page.fill('#wire', 'P');
            await page.click('#submitWire');
            await olorin.waitForTypecheck();
            expect((await wireBetween(olorin, andE, andI)).ty).toBe('P');
        });

        // Clicking a wire's label reopens the dialog to correct it.  That wire is not new, so
        // cancelling has to leave it alone.
        test('Cancel on a label being corrected leaves the wire and its label alone', async ({ page }) => {
            const { olorin, andE, andI } = await openLevel(page, difficulty);
            await drawWire(olorin, andE, andI);
            await page.fill('#wire', 'P');
            await page.click('#submitWire');
            await olorin.waitForTypecheck();

            await page.click('.userLabel');
            await expect(page.locator('#wireBG')).toBeVisible();
            await page.fill('#wire', 'Q');
            await page.click('#cancelWire');

            await expect(page.locator('#wireBG')).toBeHidden();
            expect((await wireBetween(olorin, andE, andI)).ty).toBe('P');
        });
    });
}
