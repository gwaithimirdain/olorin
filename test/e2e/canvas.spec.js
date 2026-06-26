// The diagram is a viewport onto a larger #canvas: nodes dropped or dragged far out grow the canvas
// (so they stay reachable by scrolling) rather than disappearing off the window edge, and nodes
// pulled up/left past the origin are clamped back so they can't be lost there either.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

const geom = (page) =>
    page.evaluate(() => {
        const d = document.getElementById('diagram');
        const c = document.getElementById('canvas');
        return { viewW: d.clientWidth, viewH: d.clientHeight, canvasW: c.offsetWidth, canvasH: c.offsetHeight };
    });

const nodePos = (page, id) =>
    page.evaluate((id) => {
        const el = document.getElementById(id);
        return { left: el.offsetLeft, top: el.offsetTop };
    }, id);

test.describe('Scrollable diagram canvas', () => {
    test('a node dropped past the right edge grows the canvas and stays reachable', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel('1-2-1');

        const before = await geom(page);
        // No scrolling needed yet: the canvas just fills the viewport.
        expect(before.canvasW).toBe(before.viewW);

        // Drop a rule box well beyond the right edge of the viewport.
        const id = await olorin.dragRule('andI', before.viewW + 800, 200);

        const after = await geom(page);
        const pos = await nodePos(page, id);
        expect(pos.left).toBeGreaterThan(before.viewW); // it really is out past the old edge
        // The canvas grew to contain it, so it can be scrolled into view.
        expect(after.canvasW).toBeGreaterThan(pos.left);
        expect(after.canvasW).toBeGreaterThan(before.viewW);
    });

    test('a node dragged up/left past the origin is clamped back onto the canvas', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel('1-2-1');
        const id = await olorin.dragRule('andI', 300, 300);

        // Drag it far up and to the left, past the top-left corner.
        await olorin.dragNode(id, -1000, -1000);

        const pos = await nodePos(page, id);
        expect(pos.left).toBeGreaterThanOrEqual(0);
        expect(pos.top).toBeGreaterThanOrEqual(0);
    });

    test('deleting a far-out node lets the canvas shrink back to the viewport', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel('1-2-1');
        const view = (await geom(page)).viewW;

        const id = await olorin.dragRule('andI', view + 600, 200);
        expect((await geom(page)).canvasW).toBeGreaterThan(view);

        // Remove it via its close button; the canvas should collapse back to just fill the viewport.
        await page.evaluate((id) => document.querySelector('#' + id + ' .closebutton').click(), id);
        const after = await geom(page);
        expect(after.canvasW).toBe(after.viewW);
    });
});
