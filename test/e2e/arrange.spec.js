// The "Arrange" button, which tidies up the layout of a proof (client/arrange.js).  For every case
// in lib/arrange.js -- every proof fixture, and the layouts kept in fixtures/arrange/ -- arranging
// must leave the proof itself alone and give a layout that keeps the rules a tidy one keeps: no
// blocks on top of each other, wires running left to right, every subproof between its bracket's
// uprights and on its side of the bar.  It must keep each block in the subproof the player drew it
// in, save what it did, and be undoable.  And arranging a tidy layout again must hardly move it.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { arrangeCases, loadCase } = require('../lib/arrange');

// A bracket's uprights are this wide (see client/arrange.js).
const UPRIGHT = 22;
// How far a block may move when an arrangement is arranged again.
const SETTLED = 10;

const bracketOf = (region) => region.slice(0, region.lastIndexOf('/'));
const sideOf = (region) => region.slice(region.lastIndexOf('/') + 1);
const portX = (b, p) => b.x + p.dx + (p.right ? b.w : 0);

test.describe('Arrange', () => {
    // A big proof takes a while to restore (its algebra goes to Z3) and to arrange, twice over.
    test.describe.configure({ timeout: 120000 });

    for (const c of arrangeCases()) {
        test(`arranges ${c.name} (level ${c.level.name})`, async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open({ code: c.level.code });
            await loadCase(olorin, c);

            const complete = await olorin.isComplete();
            const connections = await olorin.connections();
            const placed = await olorin.nodes();
            // What arranging will do (it works it out the same way when the button is clicked).
            const plan = await olorin.arrangement();
            expect(plan.unresolved).toBeLessThan(0.5);

            await olorin.arrange();
            expect(await olorin.arrangeButtonText()).toBe('Undo Arrange');

            // The proof itself is just as it was.
            expect(await olorin.connections()).toEqual(connections);
            expect(await olorin.isComplete()).toBe(complete);

            const model = await olorin.layoutModel();
            const byId = Object.fromEntries(model.blocks.map((b) => [b.id, b]));

            // No block on top of another.
            const overlaps = [];
            model.blocks.forEach((a, i) => model.blocks.slice(i + 1).forEach((b) => {
                if (a.x + a.w > b.x + 1 && b.x + b.w > a.x + 1 && a.y + a.h > b.y + 1 && b.y + b.h > a.y + 1) {
                    overlaps.push([a.id, b.id]);
                }
            }));
            expect(overlaps).toEqual([]);

            // Every wire runs left to right, but those in a cycle that can't.
            const allowed = new Set(plan.backward.map((w) => w.join('>')));
            const backward = model.wires.filter((w) => {
                const s = byId[w.src.block], t = byId[w.tgt.block];
                return s !== t && !allowed.has(s.id + '>' + t.id)
                    && portX(t, t.ports[w.tgt.port]) < portX(s, s.ports[w.src.port]);
            }).map((w) => [w.src.block, w.tgt.block]);
            expect(backward).toEqual([]);

            // Every block of a subproof between its bracket's uprights and on its side of the bar.
            const strays = Object.entries(plan.regions).filter(([id, region]) => {
                if (!region) return false;
                const b = byId[id], k = byId[bracketOf(region)];
                const between = b.x >= k.x + UPRIGHT - 1 && b.x + b.w <= k.x + k.w - UPRIGHT + 1;
                const side = sideOf(region) === 'lower' ? b.y >= k.y + k.h - 1 : b.y + b.h <= k.y + 1;
                return !(between && side);
            }).map(([id, region]) => [id, region]);
            expect(strays).toEqual([]);

            // Arranging it again keeps every block in the same subproof, and hardly moves anything.
            const again = await olorin.arrangement();
            expect(again.regions).toEqual(plan.regions);
            const moved = model.blocks.filter((b) => {
                const p = again.positions[b.id];
                return Math.abs(p.x - b.x) > SETTLED || Math.abs(p.y - b.y) > SETTLED
                    || (p.w !== undefined && Math.abs(p.w - b.w) > SETTLED);
            }).map((b) => [b.id, { x: b.x, y: b.y, w: b.w }, again.positions[b.id]]);
            expect(moved).toEqual([]);

            // The proof was saved as it now stands.
            const saved = await page.evaluate(() =>
                JSON.parse(localStorage.getItem(window.__olorin.savedProofKey())));
            const now = await olorin.nodes();
            // (A saved proof leaves out a width the box doesn't set.)
            expect(saved.nodes.map((n) => [n.id, n.left, n.top, n.width || '']))
                .toEqual(now.map((n) => [n.id, n.left, n.top, n.width]));

            // Undoing it puts every block back exactly where it was.
            await olorin.arrange();
            expect(await olorin.arrangeButtonText()).toBe('Arrange');
            expect(await olorin.nodes()).toEqual(placed);
        });
    }

    // The case that takes longest to arrange: the one with the most blocks.
    const biggest = () => arrangeCases().reduce((a, b) => (b.state.nodes.length > a.state.nodes.length ? b : a));

    test('works out where the blocks go without holding up the page, and can be cancelled', async ({ page }) => {
        const olorin = new Olorin(page);
        const c = biggest();
        await olorin.open({ code: c.level.code });
        await loadCase(olorin, c);
        expect(await page.evaluate(() => window.__olorin.arrangeWorker())).toBe(true);
        const placed = await olorin.nodes();

        await page.click('#arrangeProof');
        // The page answers while the arrangement is being worked out (a page that was busy working
        // it out itself couldn't say so until it was done)...
        expect(await olorin.arrangeButtonText()).toBe('Cancel Arrange');
        // ...and clicking again stops it, leaving everything where it was.
        await page.click('#arrangeProof');
        expect(await olorin.arrangeButtonText()).toBe('Arrange');
        expect(await page.evaluate(() => window.__olorin.arranging())).toBe(false);
        expect(await olorin.nodes()).toEqual(placed);

        // And after that, it still arranges.
        await olorin.arrange();
        expect(await olorin.arrangeButtonText()).toBe('Undo Arrange');
        expect(await olorin.nodes()).not.toEqual(placed);
    });

    test('still arranges where there is no worker to work it out', async ({ page }) => {
        await page.addInitScript(() => { window.Worker = undefined; });
        const olorin = new Olorin(page);
        const c = arrangeCases().find((x) => x.name === 'vertical-brackets');
        await olorin.open({ code: c.level.code });
        await loadCase(olorin, c);
        expect(await page.evaluate(() => window.__olorin.arrangeWorker())).toBe(false);
        const placed = await olorin.nodes();
        await olorin.arrange();
        expect(await olorin.arrangeButtonText()).toBe('Undo Arrange');
        expect(await olorin.nodes()).not.toEqual(placed);
    });

    test('panning around the diagram leaves an arrangement undoable', async ({ page }) => {
        const olorin = new Olorin(page);
        const c = arrangeCases().find((x) => x.name === 'vertical-brackets');
        await olorin.open({ code: c.level.code });
        await loadCase(olorin, c);
        const px = (v) => parseFloat(v);
        const placed = await olorin.nodes();
        await olorin.arrange();
        const arranged = await olorin.nodes();

        // Dragging the background down and to the right, with the view at the top left, has
        // nowhere to scroll to, so it slides the whole diagram along instead.
        const d = await page.locator('#diagram').boundingBox();
        await olorin.panBackground(d.x + 5, d.y + 5, d.x + 125, d.y + 85);
        expect(await olorin.arrangeButtonText()).toBe('Undo Arrange');
        const panned = await olorin.nodes();
        const shift = { x: px(panned[0].left) - px(arranged[0].left), y: px(panned[0].top) - px(arranged[0].top) };
        expect(shift.x).toBeGreaterThan(0);
        expect(shift.y).toBeGreaterThan(0);
        expect(panned.map((n, i) => [px(n.left) - px(arranged[i].left), px(n.top) - px(arranged[i].top)]))
            .toEqual(panned.map(() => [shift.x, shift.y]));

        // Undoing puts everything back where it was, slid along with the rest.
        await olorin.arrange();
        expect(await olorin.arrangeButtonText()).toBe('Arrange');
        expect((await olorin.nodes()).map((n) => [n.id, px(n.left), px(n.top), n.width]))
            .toEqual(placed.map((n) => [n.id, px(n.left) + shift.x, px(n.top) + shift.y, n.width]));
    });

    test('any change to the diagram makes an arrangement too late to undo', async ({ page }) => {
        const olorin = new Olorin(page);
        const c = arrangeCases().find((x) => x.state.nodes.length > 3);
        await olorin.open({ code: c.level.code });
        await loadCase(olorin, c);
        await olorin.arrange();
        expect(await olorin.arrangeButtonText()).toBe('Undo Arrange');
        // Deleting a block (the last one the player added) is a change like any other.
        const nodes = await olorin.nodes();
        await olorin.deleteNode(nodes[nodes.length - 1].id);
        await olorin.waitForTypecheck();
        expect(await olorin.arrangeButtonText()).toBe('Arrange');
    });
});
