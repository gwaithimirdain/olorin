// The "Arrange" button, which tidies up the layout of a proof (client/arrange.js).  For every case
// in lib/arrange.js -- every proof fixture, and the layouts kept in fixtures/arrange/ -- arranging
// must leave the proof itself alone and give a layout that keeps the rules a tidy one keeps: no
// blocks on top of each other, wires running left to right, every subproof between its bracket's
// uprights and on its side of the bar.  It must keep each block in the subproof the player drew it
// in, save what it did, and be undoable (by the Undo button, as any change is: see undo.spec.js).  And arranging a tidy layout again must hardly move it.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { arrangeCases, loadCase } = require('../lib/arrange');
const { fixedRules } = require('../lib/fixtures');

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
            // A layout that is tidy already, and near enough what arranging it would make it, is left
            // as it is (see arrange in client/arrange.js), and then there is nothing to undo.
            expect(await olorin.undoDepth()).toEqual({ undo: plan.settled ? 0 : 1, redo: 0 });

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

            // A block wired straight to a bracket in the same subproof is beside the bracket, not
            // above or below it: to its left if it feeds the bracket, and to its right if the
            // bracket feeds it.
            const besides = model.wires.map((w) => [byId[w.src.block], byId[w.tgt.block]])
                .filter(([s, t]) => s !== t && (s.branches || t.branches)
                        && plan.regions[s.id] === plan.regions[t.id])
                .filter(([s, t]) => s.x + s.w > t.x + 1 && t.x + t.w > s.x + 1)
                .map(([s, t]) => [s.id, t.id]);
            expect(besides).toEqual([]);

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

            // A layout left as it was hasn't moved, but to whole pixels; any other, undoing puts
            // every block back exactly where it was.
            if (plan.settled) {
                const px = (n) => ['left', 'top', 'width'].map((k) => parseFloat(n[k]) || 0);
                const off = now.filter((n, i) => px(n).some((v, k) => Math.abs(v - px(placed[i])[k]) > 1))
                    .map((n) => n.id);
                expect(off).toEqual([]);
                return;
            }
            await olorin.undo();
            expect(await olorin.undoDepth()).toEqual({ undo: 0, redo: 1 });
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
        expect(await olorin.arrangeButtonText()).toBe('Arrange');
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
        expect(await olorin.undoDepth()).toEqual({ undo: 1, redo: 0 });
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
        expect(await olorin.undoDepth()).toEqual({ undo: 1, redo: 0 });
        const panned = await olorin.nodes();
        const shift = { x: px(panned[0].left) - px(arranged[0].left), y: px(panned[0].top) - px(arranged[0].top) };
        expect(shift.x).toBeGreaterThan(0);
        expect(shift.y).toBeGreaterThan(0);
        expect(panned.map((n, i) => [px(n.left) - px(arranged[i].left), px(n.top) - px(arranged[i].top)]))
            .toEqual(panned.map(() => [shift.x, shift.y]));

        // Undoing puts everything back where it was, slid along with the rest.
        await olorin.undo();
        expect((await olorin.nodes()).map((n) => [n.id, px(n.left), px(n.top), n.width]))
            .toEqual(placed.map((n) => [n.id, px(n.left) + shift.x, px(n.top) + shift.y, n.width]));
    });

    test('each arrangement is a change of its own, undone in turn with the others', async ({ page }) => {
        const olorin = new Olorin(page);
        const c = arrangeCases().find((x) => x.state.nodes.length > 3);
        await olorin.open({ code: c.level.code });
        await loadCase(olorin, c);
        const placed = await olorin.nodes();
        await olorin.arrange();
        const arranged = await olorin.nodes();
        // Deleting a block (the last one the player added) after arranging is a change of its own.
        await olorin.deleteNode(arranged[arranged.length - 1].id);
        await olorin.waitForTypecheck();
        expect(await olorin.undoDepth()).toEqual({ undo: 2, redo: 0 });
        await olorin.undo();
        expect(await olorin.nodes()).toEqual(arranged);
        await olorin.undo();
        expect(await olorin.nodes()).toEqual(placed);
        // And redoing the arrangement slides them back where it put them.
        await olorin.redo();
        expect(await olorin.nodes()).toEqual(arranged);
    });
    test('puts a block drawn in the wrong branch of a bracket in the branch that uses it', async ({ page }) => {
        // In this proof, casing on whether x≤0 or 0<x, the case on x+y is drawn above the bar of the
        // case on x, but what it proves is used only below it (in the case on y, inside the case
        // 0<x): drawn inside that bracket, it belongs in the branch that uses it, not outside.
        const olorin = new Olorin(page);
        const c = arrangeCases().find((x) => x.name === 'subsubproof');
        await olorin.open({ code: c.level.code });
        await loadCase(olorin, c);
        const [nodes, conns] = [await olorin.nodes(), await olorin.connections()];
        const rule = Object.fromEntries(nodes.map((n) => [n.id, n]));
        const into = (id, label) => conns.find((w) => w.target.vertex === id && w.target.label === label);
        // The case on x is the ∨-elimination proving the conclusion; the case on x+y is the one
        // whose disjunction comes from comparing an expression (x+y) with something.
        const outer = conns.find((w) => rule[w.target.vertex].rule === 'conclusion').source.vertex;
        const inner = nodes.find((n) => {
            if(n.rule !== 'orE') { return false; }
            const cmp = into(n.id, undefined);
            if(!cmp || rule[cmp.source.vertex].rule !== 'tord') { return false; }
            const x = into(cmp.source.vertex, 'x');
            return x && rule[x.source.vertex].rule === 'expr';
        }).id;
        expect(rule[outer].rule).toBe('orE');

        await olorin.arrange();
        const blocks = Object.fromEntries((await olorin.layoutModel()).blocks.map((b) => [b.id, b]));
        expect(blocks[inner].y).toBeGreaterThanOrEqual(blocks[outer].y + blocks[outer].h);
    });

    test.describe('a bracket too narrow for the labels inside its uprights', () => {
        const BRACKETS = ['impI', 'allI', 'negI', 'cnegI', 'natInd', 'orE', 'iffI', 'natE'];
        const FIXED = fixedRules();

        // The rectangles of the labels on a bracket's own ports, as { x, y, w, h }.
        const labelsOn = (page, id) => page.evaluate((id) => {
            const box = document.getElementById(id).getBoundingClientRect();
            return Array.from(document.querySelectorAll(
                '#canvas .upperOutputLabel, #canvas .lowerOutputLabel, #canvas .middleOutputLabel, '
                + '#canvas .upperInputLabel, #canvas .lowerInputLabel, #canvas .middleInputLabel'))
                .map((l) => l.getBoundingClientRect())
                .filter((r) => r.x + r.width / 2 > box.x && r.x + r.width / 2 < box.right
                        && r.y + r.height / 2 > box.y - 30 && r.y + r.height / 2 < box.bottom + 30)
                .map((r) => ({ x: r.x, y: r.y, w: r.width, h: r.height }));
        }, id);
        const meeting = (rs) => rs.some((a, i) => rs.slice(i + 1).some((b) =>
            a.x < b.x + b.w && b.x < a.x + a.w && a.y < b.y + b.h && b.y < a.y + a.h));
        const widthOf = (page, id) => page.evaluate((id) => document.getElementById(id).offsetWidth, id);

        // Restore a proof with one of its brackets unwired from its assumptions and subgoals (the
        // labels beside a bracket's ports show only on ports with nothing wired to them), and saved
        // as narrow as a bracket can be made by hand.  Whether its labels then meet depends on how
        // long they are, so try brackets until the typecheck after restoring has had to widen one.
        // Returns its id on the page.
        async function widenedBracket(page, olorin) {
            let opened = null;
            for (const c of arrangeCases()) {
                for (const n of c.state.nodes.filter((n) => BRACKETS.includes(n.rule))) {
                    if (opened !== (c.level.code || '')) {
                        await olorin.open({ code: c.level.code });
                        opened = c.level.code || '';
                    }
                    const state = JSON.parse(JSON.stringify(c.state));
                    state.connections = state.connections.filter((w) =>
                        !(w.source.vertex === n.id && w.source.sort === 'assumption')
                        && !(w.target.vertex === n.id && w.target.sort === 'subgoal'));
                    state.nodes.find((m) => m.id === n.id).width = '100px';
                    await loadCase(olorin, { ...c, state });
                    // Restoring renumbers the blocks, but puts back the player's own in the order saved.
                    const own = (ns) => ns.filter((m) => !FIXED.includes(m.rule));
                    const id = own(await olorin.nodes())[own(state.nodes).findIndex((m) => m.id === n.id)].id;
                    if (await widthOf(page, id) > 100) { return id; }
                }
            }
            return null;
        }

        test('is widened as soon as a typecheck puts its labels there', async ({ page }) => {
            const olorin = new Olorin(page);
            const id = await widenedBracket(page, olorin);
            expect(id).not.toBeNull();
            expect(meeting(await labelsOn(page, id))).toBe(false);
            // And saved so.
            const saved = await page.evaluate(() =>
                JSON.parse(localStorage.getItem(window.__olorin.savedProofKey())));
            expect(saved.nodes.find((n) => n.id === id).width).toBe((await widthOf(page, id)) + 'px');
        });

        test('is widened by arranging', async ({ page }) => {
            const olorin = new Olorin(page);
            const id = await widenedBracket(page, olorin);
            expect(id).not.toBeNull();
            // Squeeze it again behind the typecheck's back.
            await page.evaluate((id) => window.__olorin.setWidth(id, '100px'), id);
            expect(meeting(await labelsOn(page, id))).toBe(true);
            await olorin.arrange();
            expect(meeting(await labelsOn(page, id))).toBe(false);
        });

        test('cannot be resized narrower than that by hand', async ({ page }) => {
            const olorin = new Olorin(page);
            const id = await widenedBracket(page, olorin);
            expect(id).not.toBeNull();
            const least = await widthOf(page, id);
            // Drag its right-hand resize handle far off to the left.
            const handle = await page.locator('#' + id + ' .resize-handle-right').boundingBox();
            await page.mouse.move(handle.x + handle.width / 2, handle.y + handle.height / 2);
            await page.mouse.down();
            await page.mouse.move(handle.x - 600, handle.y + handle.height / 2, { steps: 20 });
            await page.mouse.up();
            expect(await widthOf(page, id)).toBeGreaterThanOrEqual(least - 1);
            expect(meeting(await labelsOn(page, id))).toBe(false);
        });
    });
});
