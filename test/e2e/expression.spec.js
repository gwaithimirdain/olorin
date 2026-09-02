// An expression box carries a written expression (x−1, say).  It asks for one when it's dropped,
// and double-clicking it re-opens that dialog to edit what it says, in place -- the box keeps its
// id, its position, and its wires.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// A level with an integer variable, where expression boxes are in the palette and make sense.
const LEVEL = { variables: 'x ∈ ℤ', hypotheses: 'x=1', conclusion: 'x=1' };

// Fill in the expression dialog and submit it.
async function enterExpression(page, text) {
    await page.waitForSelector('#expressionBG', { state: 'visible' });
    await page.fill('#expression', text);
    await page.click('#submitExpression');
}

// The text an expression box shows (without its close button).
const boxText = (page, id) =>
    page.evaluate((i) => document.getElementById(i).childNodes[0].textContent.trim(), id);

// The value the app has recorded for a node, which is what gets typechecked and saved.
const nodeValue = async (olorin, id) => (await olorin.nodes()).find((n) => n.id === id).value;

test.describe('Expression boxes', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom(LEVEL);
    });

    test('double-clicking one re-opens the dialog, pre-filled, and edits it in place', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');
        expect(await boxText(page, id)).toBe('x−1');

        await page.dblclick('#' + id);

        // The dialog comes back with the expression that's there now, ready to be corrected.
        await expect(page.locator('#expressionBG')).toBeVisible();
        expect(await page.inputValue('#expression')).toBe('x−1');

        await page.fill('#expression', 'x+2');
        await page.click('#submitExpression');

        expect(await page.isVisible('#expressionBG')).toBe(false);
        expect(await boxText(page, id)).toBe('x+2');
        expect(await nodeValue(olorin, id)).toBe('x+2');
        // Same box: it wasn't deleted and re-made, and re-rendering it left exactly one close button.
        expect((await olorin.nodes()).filter((n) => n.rule === 'expr')).toHaveLength(1);
        expect(await page.locator(`#${id} .closebutton`).count()).toBe(1);
    });

    test('an edit keeps the box wired up as it was', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');
        await olorin.connect({ vertex: 'var0', sort: 'output' }, { vertex: id, sort: 'input' });
        const before = await olorin.connections();
        expect(before).toHaveLength(1);

        await page.dblclick('#' + id);
        await page.fill('#expression', 'x+2');
        await page.click('#submitExpression');

        expect(await olorin.connections()).toEqual(before);
    });

    test('cancelling an edit leaves the box and its expression alone', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');

        await page.dblclick('#' + id);
        await page.fill('#expression', 'x+2');
        await page.click('#cancelExpression');

        expect(await page.isVisible('#expressionBG')).toBe(false);
        expect(await boxText(page, id)).toBe('x−1');
        expect(await nodeValue(olorin, id)).toBe('x−1');
    });

    test('cancelling the prompt for a NEW box still removes it', async ({ page }) => {
        await olorin.dragRule('expr', 420, 240);
        await page.waitForSelector('#expressionBG', { state: 'visible' });
        await page.click('#cancelExpression');

        expect((await olorin.nodes()).some((n) => n.rule === 'expr')).toBe(false);
    });

    test('an invalid expression is refused and the box keeps the old one', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');

        await page.dblclick('#' + id);
        await page.fill('#expression', 'x +');
        await page.click('#submitExpression'); // the alert is auto-accepted by open()

        // The dialog stays open on a bad expression, and the box still says what it said.
        await expect(page.locator('#expressionBG')).toBeVisible();
        await page.click('#cancelExpression');
        expect(await boxText(page, id)).toBe('x−1');
    });

    test('a restored expression box can be edited too', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');
        const state = await olorin.serialize();

        await olorin.restore(state);
        const restored = (await olorin.nodes()).find((n) => n.rule === 'expr').id;
        await page.dblclick('#' + restored);

        await expect(page.locator('#expressionBG')).toBeVisible();
        expect(await page.inputValue('#expression')).toBe('x−1');
        await page.fill('#expression', 'x+2');
        await page.click('#submitExpression');
        expect(await boxText(page, restored)).toBe('x+2');
    });
});
