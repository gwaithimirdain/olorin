// Pressing Delete or Backspace with boxes selected removes them all, as if each red X were clicked
// (the fixed context nodes -- hypotheses, variables, conclusion -- have no X and are kept).

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// Rubber-band select the whole diagram (covering every node) with a real mouse drag.
async function selectAll(page) {
    const d = await page.evaluate(() => {
        const r = document.getElementById('diagram').getBoundingClientRect();
        return { l: r.left, t: r.top, r: r.right, b: r.bottom };
    });
    await page.mouse.move(d.l + 5, d.t + 5);
    await page.mouse.down();
    await page.mouse.move(d.r - 5, d.b - 5, { steps: 10 });
    await page.mouse.up();
}

const ruleCount = (nodes, rule) => nodes.filter((n) => n.rule === rule).length;

test.describe('Deleting selected nodes', () => {
    test('Delete removes all selected rule boxes but keeps the fixed context nodes', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel('1-2-1'); // P, Q |- P∧Q : two hypotheses, one conclusion
        await olorin.dragRule('andI', 400, 200);
        await olorin.dragRule('andI', 400, 400);
        expect(ruleCount(await olorin.nodes(), 'andI')).toBe(2);

        await selectAll(page); // selects the two andI boxes and the fixed nodes
        await page.keyboard.press('Delete');

        const nodes = await olorin.nodes();
        expect(ruleCount(nodes, 'andI')).toBe(0);        // deletable boxes removed
        expect(ruleCount(nodes, 'hypothesis')).toBe(2);  // fixed nodes kept
        expect(ruleCount(nodes, 'conclusion')).toBe(1);
    });

    test('Backspace deletes the selection too', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel('1-2-1');
        await olorin.dragRule('andI', 400, 250);
        await selectAll(page);
        await page.keyboard.press('Backspace');
        expect(ruleCount(await olorin.nodes(), 'andI')).toBe(0);
    });
});
