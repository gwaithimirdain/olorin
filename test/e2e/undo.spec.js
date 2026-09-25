// The Undo and Redo buttons (and Ctrl+Z / Ctrl+Shift+Z).  Every change to the proof -- placing a
// block, drawing or deleting a wire, moving or deleting blocks, clearing it, arranging it -- can be
// undone, one at a time, back to how the level started, and redone again.  Panning isn't a change,
// and a change cancelled in its dialog was never made.  Opening another level starts afresh.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// P and Q as hypotheses, P∧Q to prove, with one ∧-introduction to do it.  (Saved as a custom level,
// so that the proof is saved as it changes.)
async function openLevel(page, difficulty) {
    const olorin = new Olorin(page);
    if (difficulty !== undefined) { await olorin.seed([['difficulty', String(difficulty)]]); }
    await olorin.open();
    await olorin.buildCustom({
        name: 'undo', parameters: 'P : Type\nQ : Type', variables: '',
        hypotheses: 'P\nQ', conclusion: 'P∧Q',
    });
    const nodes = await olorin.nodes();
    return {
        olorin,
        hyps: nodes.filter((n) => n.rule === 'hypothesis').map((n) => n.id),
        concl: nodes.find((n) => n.rule === 'conclusion').id,
    };
}

// Everything about the proof that undoing has to put back.
const proofState = async (olorin) => ({ nodes: await olorin.nodes(), connections: await olorin.connections() });

test.describe('Undo', () => {
    test('undoes each change in turn back to the start, and redoes them all', async ({ page }) => {
        const { olorin, hyps, concl } = await openLevel(page);
        const states = [await proofState(olorin)];
        const step = async (change) => {
            await change();
            await olorin.waitForTypecheck();
            states.push(await proofState(olorin));
            expect(await olorin.undoDepth()).toEqual({ undo: states.length - 1, redo: 0 });
        };
        let andI;
        await step(async () => { andI = await olorin.dragRule('andI', 400, 300); });
        await step(() => olorin.connect({ vertex: hyps[0], sort: 'output' }, { vertex: andI, sort: 'input', label: 'fst' }));
        await step(() => olorin.connect({ vertex: hyps[1], sort: 'output' }, { vertex: andI, sort: 'input', label: 'snd' }));
        await step(() => olorin.connect({ vertex: andI, sort: 'output' }, { vertex: concl, sort: 'input' }));
        expect(await olorin.isComplete()).toBe(true);
        await step(() => olorin.dragNode(andI, 60, 40));
        await step(() => olorin.deleteNode(andI));
        expect(await olorin.isComplete()).toBe(false);

        for (let i = states.length - 2; i >= 0; i--) {
            await olorin.undo();
            expect(await proofState(olorin)).toEqual(states[i]);
        }
        expect(await olorin.undoDepth()).toEqual({ undo: 0, redo: states.length - 1 });
        await expect(page.locator('#undo')).toBeDisabled();

        for (let i = 1; i < states.length; i++) {
            await olorin.redo();
            expect(await proofState(olorin)).toEqual(states[i]);
            // The proof put back is typechecked: it is complete once all its wires are back.
            if (i === 4) { expect(await olorin.isComplete()).toBe(true); }
        }
        await expect(page.locator('#redo')).toBeDisabled();
        expect(await olorin.isComplete()).toBe(false);
    });

    test('a block put back comes back with its wires, and is saved', async ({ page }) => {
        const { olorin, hyps, concl } = await openLevel(page);
        const andI = await olorin.dragRule('andI', 400, 300);
        await olorin.connect({ vertex: hyps[0], sort: 'output' }, { vertex: andI, sort: 'input', label: 'fst' });
        await olorin.connect({ vertex: hyps[1], sort: 'output' }, { vertex: andI, sort: 'input', label: 'snd' });
        await olorin.connect({ vertex: andI, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        const before = await proofState(olorin);
        await olorin.deleteNode(andI);
        await olorin.waitForTypecheck();
        await olorin.undo();
        expect(await proofState(olorin)).toEqual(before);
        expect(await olorin.isComplete()).toBe(true);
        expect((await olorin.savedProof()).connections.length).toBe(3);
        // The block is the one it was, as far as the diagram goes: it can be moved and deleted.
        await olorin.dragNode(andI, 30, 30);
        await olorin.deleteNode(andI);
        await olorin.waitForTypecheck();
        expect((await olorin.nodes()).some((n) => n.id === andI)).toBe(false);
        expect(await olorin.connections()).toEqual([]);
    });

    test('a new change after undoing leaves nothing to redo', async ({ page }) => {
        const { olorin } = await openLevel(page);
        await olorin.dragRule('andI', 400, 300);
        await olorin.waitForTypecheck();
        await olorin.undo();
        expect(await olorin.undoDepth()).toEqual({ undo: 0, redo: 1 });
        await olorin.dragRule('andE', 400, 300);
        await olorin.waitForTypecheck();
        expect(await olorin.undoDepth()).toEqual({ undo: 1, redo: 0 });
    });

    test('deleting several selected blocks at once is one change', async ({ page }) => {
        const { olorin } = await openLevel(page);
        await olorin.dragRule('andI', 400, 200);
        await olorin.dragRule('andI', 400, 400);
        await olorin.waitForTypecheck();
        const before = await proofState(olorin);
        // Rubber-band select the whole diagram.
        const d = await page.locator('#diagram').boundingBox();
        await page.mouse.move(d.x + 5, d.y + 5);
        await page.mouse.down();
        await page.mouse.move(d.x + d.width - 5, d.y + d.height - 5, { steps: 10 });
        await page.mouse.up();
        await page.keyboard.press('Delete');
        await olorin.waitForTypecheck();
        expect((await olorin.nodes()).filter((n) => n.rule === 'andI')).toEqual([]);
        expect(await olorin.undoDepth()).toEqual({ undo: 3, redo: 0 });
        await olorin.undo();
        expect(await proofState(olorin)).toEqual(before);
    });

    test('Clear can be undone', async ({ page }) => {
        const { olorin, hyps } = await openLevel(page);
        const andI = await olorin.dragRule('andI', 400, 300);
        await olorin.connect({ vertex: hyps[0], sort: 'output' }, { vertex: andI, sort: 'input', label: 'fst' });
        await olorin.waitForTypecheck();
        const before = await olorin.structuralState();
        await olorin.clear();
        await olorin.waitForTypecheck();
        expect((await olorin.nodes()).some((n) => n.rule === 'andI')).toBe(false);
        expect(await olorin.undoDepth()).toEqual({ undo: 3, redo: 0 });
        await olorin.undo();
        // (The hypotheses and conclusion were made afresh by clearing, so they have new ids.)
        expect(await olorin.structuralState()).toEqual(before);
        expect((await olorin.savedProof()).connections.length).toBe(1);
        await olorin.redo();
        expect(await olorin.connections()).toEqual([]);
    });

    test('panning is no change, and a move undone after panning goes back slid along with the rest', async ({ page }) => {
        const { olorin } = await openLevel(page);
        const andI = await olorin.dragRule('andI', 400, 300);
        await olorin.waitForTypecheck();
        const px = (v) => parseFloat(v);
        const placed = await olorin.nodes();
        await olorin.dragNode(andI, 80, 60);
        expect(await olorin.undoDepth()).toEqual({ undo: 2, redo: 0 });

        // Dragging the background down and to the right, with the view at the top left, has
        // nowhere to scroll to, so it slides the whole diagram along instead.
        const d = await page.locator('#diagram').boundingBox();
        await olorin.panBackground(d.x + 200, d.y + 5, d.x + 320, d.y + 85);
        expect(await olorin.undoDepth()).toEqual({ undo: 2, redo: 0 });
        const moved = await olorin.nodes();
        const shift = { x: px(moved[0].left) - px(placed[0].left), y: px(moved[0].top) - px(placed[0].top) };
        expect(shift.x).toBeGreaterThan(0);
        expect(shift.y).toBeGreaterThan(0);

        // (Panning leaves every block on a whole pixel, so they may be a fraction of one out.)
        await olorin.undo();
        const back = await olorin.nodes();
        expect(back.map((n) => n.id)).toEqual(placed.map((n) => n.id));
        back.forEach((n, i) => {
            expect(px(n.left)).toBeCloseTo(px(placed[i].left) + shift.x, 0);
            expect(px(n.top)).toBeCloseTo(px(placed[i].top) + shift.y, 0);
        });
        await olorin.redo();
        expect(await olorin.nodes()).toEqual(moved);
    });

    test('a wire cancelled in its label dialog is no change', async ({ page }) => {
        const { olorin } = await openLevel(page, 1);
        const andE = await olorin.dragRule('andE', 350, 250);
        const andI = await olorin.dragRule('andI', 650, 250);
        await olorin.waitForTypecheck();
        expect(await olorin.undoDepth()).toEqual({ undo: 2, redo: 0 });
        await olorin.connect({ vertex: andE, sort: 'output', label: 'fst' },
                             { vertex: andI, sort: 'input', label: 'fst' });
        await expect(page.locator('#wireBG')).toBeVisible();
        // Nothing is undone while the dialog is open, even by the keyboard.
        await page.evaluate(() => document.body.focus());
        await page.keyboard.press('Control+z');
        expect(await olorin.undoDepth()).toEqual({ undo: 2, redo: 0 });
        await page.click('#cancelWire');
        await olorin.waitForTypecheck();
        expect(await olorin.connections()).toEqual([]);
        expect(await olorin.undoDepth()).toEqual({ undo: 2, redo: 0 });
    });

    test('Ctrl+Z undoes and Ctrl+Shift+Z redoes, but not in a text field', async ({ page }) => {
        const { olorin } = await openLevel(page);
        await olorin.dragRule('andI', 400, 300);
        await olorin.waitForTypecheck();
        await page.keyboard.press('Control+z');
        await olorin.waitForTypecheck();
        expect((await olorin.nodes()).some((n) => n.rule === 'andI')).toBe(false);
        await page.keyboard.press('Control+Shift+z');
        await olorin.waitForTypecheck();
        expect((await olorin.nodes()).some((n) => n.rule === 'andI')).toBe(true);
        await page.keyboard.press('Control+z');
        await olorin.waitForTypecheck();
        await page.keyboard.press('Control+y');
        await olorin.waitForTypecheck();
        expect(await olorin.undoDepth()).toEqual({ undo: 1, redo: 0 });

        await page.click('#importProof');
        await page.locator('#importJson').press('Control+z');
        await page.click('#cancelImport');
        expect(await olorin.undoDepth()).toEqual({ undo: 1, redo: 0 });
    });

    test('opening another level starts the history afresh', async ({ page }) => {
        const { olorin } = await openLevel(page);
        await olorin.dragRule('andI', 400, 300);
        await olorin.waitForTypecheck();
        expect(await olorin.undoDepth()).toEqual({ undo: 1, redo: 0 });
        await olorin.buildCustom();
        expect(await olorin.undoDepth()).toEqual({ undo: 0, redo: 0 });
        await expect(page.locator('#undo')).toBeDisabled();
    });
});
