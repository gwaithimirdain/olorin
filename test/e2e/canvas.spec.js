// The diagram is a viewport onto an unbounded canvas.  Dropping or dragging a box past the right or
// bottom edge grows the canvas under it (so it stays reachable by scrolling); holding a dragged box
// against any edge pans the canvas along underneath, so a box can be carried any distance in any
// direction, including off the top or left, where the browser has no scroll room and the whole
// diagram slides the other way instead.  Ctrl-dragging the blank background pans it directly.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { conjunctionLevel, oneWireLevel, otherLevel, wrappableStatementLevel } = require('../lib/levels');

// P, Q |- P∧Q, in a stage with the ∧ rules: two hypotheses, one conclusion, and both
// andI and andE in the palette.  Selected from levels.js so a renumbering can't break it.
const LEVEL = conjunctionLevel();
// Any other level, to switch away to and back from, and one proved by a single wire, for putting a
// saved proof on a second level cheaply.
const ELSEWHERE = otherLevel(LEVEL);
const ONEWIRE = oneWireLevel();

// A level whose statement has somewhere to re-wrap, for pinning that a box on the canvas never does.
const WORDY = wrappableStatementLevel();

const geom = (page) =>
    page.evaluate(() => {
        const d = document.getElementById('diagram');
        const c = document.getElementById('canvas');
        return {
            viewW: d.clientWidth, viewH: d.clientHeight,
            canvasW: c.offsetWidth, canvasH: c.offsetHeight,
            scrollW: d.scrollWidth, scrollH: d.scrollHeight,
            scrollX: d.scrollLeft, scrollY: d.scrollTop,
        };
    });

const nodePos = (page, id) =>
    page.evaluate((id) => {
        const el = document.getElementById(id);
        return { left: el.offsetLeft, top: el.offsetTop, width: el.offsetWidth, height: el.offsetHeight };
    }, id);

// The smallest left/top over every node: the top-left corner of the diagram, which panning must
// never leave in negative territory, where no scrollbar could reach it.
const nodeMinimum = (page) =>
    page.evaluate(() => window.__olorin.nodes().reduce(
        (m, n) => {
            const el = document.getElementById(n.id);
            return { left: Math.min(m.left, el.offsetLeft), top: Math.min(m.top, el.offsetTop) };
        }, { left: Infinity, top: Infinity }));

// Whether a node is inside the visible part of the diagram, i.e. whether the player can see it.
const isVisible = (page, id) =>
    page.evaluate((id) => {
        const r = document.getElementById(id).getBoundingClientRect();
        const d = document.getElementById('diagram').getBoundingClientRect();
        return r.left >= d.left && r.right <= d.right && r.top >= d.top && r.bottom <= d.bottom;
    }, id);

// Where every node sits on the screen, in the order the diagram holds them -- so two snapshots can
// be compared across a restore, which gives the recreated boxes new ids but keeps their order.
const screenRects = (page) =>
    page.evaluate(() => window.__olorin.nodes().map((n) => {
        const r = document.getElementById(n.id).getBoundingClientRect();
        return { rule: n.rule, x: Math.round(r.x), y: Math.round(r.y) };
    }));

// The ids of any nodes the player can't currently see.
const offScreen = async (page) => {
    const ids = (await page.evaluate(() => window.__olorin.nodes().map((n) => n.id)));
    const shown = await Promise.all(ids.map((id) => isVisible(page, id)));
    return ids.filter((id, i) => !shown[i]);
};

test.describe('Scrollable diagram canvas', () => {
    test('a node dropped past the right edge grows the canvas and stays reachable', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);

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

    test('a node dragged up/left past the origin stays where the scrollbars can reach it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);
        const id = await olorin.dragRule('andI', 300, 300);

        // Drag it far up and to the left, past the top-left corner of the window.
        await olorin.dragNode(id, -1000, -1000);

        // The diagram slid down and right to make room, rather than the node being lost off the
        // corner: every node, this one included, is somewhere the scrollbars can still get to.
        const min = await nodeMinimum(page);
        expect(min.left).toBeGreaterThanOrEqual(0);
        expect(min.top).toBeGreaterThanOrEqual(0);
        // And the view followed the node it was carrying, rather than being left behind.
        expect(await isVisible(page, id)).toBe(true);
    });

    test('deleting a far-out node lets the canvas shrink back to the viewport', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);
        const view = (await geom(page)).viewW;

        const id = await olorin.dragRule('andI', view + 600, 200);
        expect((await geom(page)).canvasW).toBeGreaterThan(view);

        // Remove it via its close button; the canvas should collapse back to just fill the viewport.
        await page.evaluate((id) => document.querySelector('#' + id + ' .closebutton').click(), id);
        const after = await geom(page);
        expect(after.canvasW).toBe(after.viewW);
    });

    test('holding a dragged node against the right edge pans the canvas out to meet it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);
        const before = await geom(page);
        const id = await olorin.dragRule('andI', 300, 300);

        // Hold it against the right-hand edge of the window for a moment.
        const view = page.viewportSize();
        await olorin.dragNodeTo(id, view.width - 2, 400, 500);

        const pos = await nodePos(page, id);
        const after = await geom(page);
        // The pointer can only reach the edge of the window, so anywhere past it is the pan's doing.
        expect(pos.left).toBeGreaterThan(before.viewW);
        // The canvas grew out there and the view scrolled along, keeping the node in sight.
        expect(after.scrollX).toBeGreaterThan(0);
        expect(after.scrollW).toBeGreaterThan(after.viewW);
        expect(await isVisible(page, id)).toBe(true);
    });

    test('holding a dragged node against the left edge pans the diagram the other way', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);
        const id = await olorin.dragRule('andI', 400, 300);
        const conclusion = (await olorin.nodes()).find((n) => n.rule === 'conclusion').id;
        const conclusionBefore = (await nodePos(page, conclusion)).left;

        // Hold it against the left-hand edge, just inside the diagram.
        const diagramLeft = (await page.locator('#diagram').boundingBox()).x;
        await olorin.dragNodeTo(id, diagramLeft + 2, 300, 500);

        // There's no scrolling to be had past the left edge, so the rest of the diagram moved right
        // instead, opening up room to the left of everything for the node being carried there.
        expect((await nodePos(page, conclusion)).left).toBeGreaterThan(conclusionBefore + 100);
        expect((await nodePos(page, id)).left).toBeLessThan(conclusionBefore);
        const min = await nodeMinimum(page);
        expect(min.left).toBeGreaterThanOrEqual(0);
        expect(await isVisible(page, id)).toBe(true);
    });

    test('a node being dragged past the right edge keeps its text on one line', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(WORDY.name);
        const id = (await olorin.nodes()).find((n) => n.rule === 'hypothesis').id;
        const before = await nodePos(page, id);

        // Part-way out past the right-hand edge of the canvas the box has less room than its text
        // needs, which must not make it re-wrap (and spill out of the box, which has a fixed height).
        const view = page.viewportSize();
        const box = await page.locator('#' + id).boundingBox();
        await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2);
        await page.mouse.down();
        await page.mouse.move(view.width - 8, 400, { steps: 5 });
        const during = await nodePos(page, id);
        await page.mouse.up();

        expect(during.width).toBe(before.width);
        expect((await nodePos(page, id)).width).toBe(before.width);
    });
});

test.describe('Panning the canvas', () => {
    test('ctrl-dragging the background carries the whole diagram with it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);
        const before = await olorin.nodeRects();

        // Pan right and down, into the space above and to the left of the diagram...
        await olorin.panBackground(700, 500, 900, 600);
        const moved = await olorin.nodeRects();
        Object.keys(before).forEach((id) => {
            expect(moved[id].x).toBeCloseTo(before[id].x + 200, 0);
            expect(moved[id].y).toBeCloseTo(before[id].y + 100, 0);
        });

        // ... and back again, leaving every box on screen exactly where it started.
        await olorin.panBackground(900, 600, 700, 500);
        const back = await olorin.nodeRects();
        Object.keys(before).forEach((id) => {
            expect(back[id].x).toBeCloseTo(before[id].x, 0);
            expect(back[id].y).toBeCloseTo(before[id].y, 0);
        });
        const min = await nodeMinimum(page);
        expect(min.left).toBeGreaterThanOrEqual(0);
        expect(min.top).toBeGreaterThanOrEqual(0);
    });

    test('a rule dropped on a panned canvas lands under the pointer', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);
        await olorin.panBackground(700, 500, 500, 300);

        const diagram = await page.locator('#diagram').boundingBox();
        const id = await olorin.dragRule('andI', 300, 250);
        const rect = (await olorin.nodeRects())[id];
        expect(rect.x).toBeCloseTo(diagram.x + 300, 0);
        expect(rect.y).toBeCloseTo(diagram.y + 250, 0);
    });

    test('dragging the background without the modifier still selects boxes', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);
        const id = await olorin.dragRule('andI', 400, 300);
        const box = await page.locator('#' + id).boundingBox();
        const selected = () => page.evaluate((id) => document.getElementById(id).classList.contains('jtk-drag-selected'), id);

        // A plain drag of the background rubber-bands a selection around the box...
        await page.mouse.move(box.x - 40, box.y - 40);
        await page.mouse.down();
        await page.mouse.move(box.x + box.width + 40, box.y + box.height + 40, { steps: 8 });
        await page.mouse.up();
        expect(await selected()).toBe(true);

        // ... while the same drag with Ctrl held pans the canvas instead.
        await olorin.panBackground(box.x - 40, box.y - 40, box.x - 240, box.y - 140);
        const after = await olorin.nodeRects();
        expect(after[id].x).toBeCloseTo(box.x - 200, 0);
    });
});

test.describe('Resuming a saved proof', () => {
    // Build a proof and pan it around, leaving it on screen but nowhere near where it started:
    // pushing it down and to the right slides the boxes (there being no scrolling to be had that
    // way), and bringing the view part of the way back over it scrolls.  So the saved proof has
    // both a shifted layout and a scrolled view for a resume to put back.
    async function buildPannedProof(page, olorin) {
        await olorin.selectLevel(LEVEL.name);
        const andId = await olorin.dragRule('andI', 400, 300);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: andId, sort: 'input', label: 'fst' });
        await olorin.panBackground(300, 300, 800, 600);
        await olorin.panBackground(800, 600, 500, 400);
        expect((await nodeMinimum(page)).left).toBeGreaterThan(0);
        expect((await geom(page)).scrollX).toBeGreaterThan(0);
        return andId;
    }

    test('looks at it just where it was left', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildPannedProof(page, olorin);
        const before = await screenRects(page);

        await olorin.selectLevel(ELSEWHERE.name);
        await olorin.selectLevel(LEVEL.name);
        await olorin.loadSaved();

        // Every box is back on the same pixel it was on, rather than the whole proof having slid
        // over because the view came back somewhere else.
        expect(await screenRects(page)).toEqual(before);
    });

    test('scrolling with nothing else changing is saved too', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildPannedProof(page, olorin);
        const before = (await olorin.savedProof()).view;

        // Scrolling changes no part of the proof, but it is where the player is looking: take the
        // view somewhere else (as far right as the canvas goes) and touch nothing else.
        const target = await page.evaluate(() => {
            const d = document.getElementById('diagram');
            d.scrollLeft = d.scrollWidth;
            return d.scrollLeft;
        });
        expect(target).not.toBe(before.x);
        await expect.poll(async () => (await olorin.savedProof()).view.x).toBe(target);
    });

    test('opening a level cannot scroll its empty diagram over the saved proof', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // A level with a proof saved on it, to come back to.
        await olorin.selectLevel(ONEWIRE.name);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        const saved = await olorin.savedProof();
        expect(saved).not.toBeNull();

        // Work somewhere else, leaving the view scrolled away from the origin...
        await buildPannedProof(page, olorin);

        // ... and come back.  Opening a level puts its view at the origin, which is a scroll like
        // any other -- but the diagram being scrolled is the empty one set up behind the "load
        // saved proof?" prompt, and it must not save itself over the proof being offered.
        await olorin.selectLevel(ONEWIRE.name);
        expect(await olorin.savedPromptVisible()).toBe(true);
        await page.waitForTimeout(700);
        expect(await olorin.savedProof()).toEqual(saved);
    });

    test('a proof saved with no view recorded is looked at where its boxes are', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildPannedProof(page, olorin);

        // Proofs saved before the view was recorded (and proofs imported from a window of another
        // size) have none, and are found by looking at the boxes themselves.
        const state = await olorin.serialize();
        delete state.view;
        await olorin.restore(state);
        expect(await offScreen(page)).toEqual([]);
    });
});
