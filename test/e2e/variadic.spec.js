// The blocks that take any number of inputs -- an algebra block, whatever equations it reasons
// from, and an expression block, the values its expression uses -- give each wire a port of its
// own.  There is always exactly one empty port to wire the next input to: a new block has just
// that one, wiring it adds another, and deleting a wire takes its port away.  The box grows to fit.
// To the typechecker they are all still the block's one input, so none of this changes what a
// proof means or how it is saved.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// The input ports on a block, and how many of them have a wire.
async function inputs(page, id) {
    return page.evaluate((i) => {
        const ports = window.__olorin.ports().filter((p) => p.vertex === i && p.sort === 'input');
        const wired = window.__olorin.connections().filter((c) => c.target.vertex === i).length;
        return { ports: ports.length, wired };
    }, id);
}

const boxHeight = (page, id) =>
    page.evaluate((i) => document.getElementById(i).getBoundingClientRect().height, id);

// Delete the index'th wire through the X that hovering it shows.
async function deleteWire(olorin, page, index) {
    await olorin.hoverWire(0.5, index);
    await page.evaluate(() => Array.from(document.querySelectorAll('#canvas .closebutton'))
        .find((e) => !e.closest('.rule') && getComputedStyle(e).visibility === 'visible').click());
    await olorin.unhoverWire();
    await olorin.waitForTypecheck();
}

test.describe('Blocks with any number of inputs', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('an algebra block has a port per wire, and one spare', async ({ page }) => {
        await olorin.buildCustom({
            parameters: '',
            variables: 'x ∈ ℤ\ny ∈ ℤ\nz ∈ ℤ',
            hypotheses: 'x=1\ny=2\nz=3',
            conclusion: 'x+y+z=6',
        });
        const nodes = await olorin.nodes();
        const hyps = nodes.filter((n) => n.rule === 'hypothesis').map((n) => n.id);
        const concl = nodes.find((n) => n.rule === 'conclusion').id;
        const alg = await olorin.dragRule('algplus', 500, 200);
        expect(await inputs(page, alg)).toEqual({ ports: 1, wired: 0 });
        const small = await boxHeight(page, alg);

        for (let i = 0; i < hyps.length; i++) {
            await olorin.connect({ vertex: hyps[i], sort: 'output' }, { vertex: alg, sort: 'input' });
            await olorin.waitForTypecheck();
            expect(await inputs(page, alg)).toEqual({ ports: i + 2, wired: i + 1 });
        }
        // Four ports don't fit in a basic block's height.
        expect(await boxHeight(page, alg)).toBeGreaterThan(small);

        await olorin.connect({ vertex: alg, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);

        // Saved and restored, it comes back with the same ports, and still proves the goal.
        const saved = await page.evaluate(() => window.__olorin.serialize());
        await olorin.restore(saved);
        const restoredAlg = (await olorin.nodes()).find((n) => n.rule === 'algplus').id;
        expect(await inputs(page, restoredAlg)).toEqual({ ports: 4, wired: 3 });
        expect(await olorin.isComplete()).toBe(true);

        // Deleting a wire into it takes its port away, and the box shrinks back.
        await deleteWire(olorin, page, 0);
        expect(await inputs(page, restoredAlg)).toEqual({ ports: 3, wired: 2 });
        expect(await olorin.isComplete()).toBe(false);
        await deleteWire(olorin, page, 0);
        expect(await inputs(page, restoredAlg)).toEqual({ ports: 2, wired: 1 });
        expect(await boxHeight(page, restoredAlg)).toBe(small);
    });

    test('so does an expression block, and deleting what feeds it takes the port too', async ({ page }) => {
        await olorin.buildCustom({
            parameters: '',
            variables: 'x ∈ ℤ\ny ∈ ℤ',
            hypotheses: 'x=1',
            conclusion: 'x=1',
        });
        const nodes = await olorin.nodes();
        const vars = nodes.filter((n) => n.rule === 'variable').map((n) => n.id);
        const expr = await olorin.dragRule('expr', 400, 250);
        await page.waitForSelector('#expressionBG', { state: 'visible' });
        await page.fill('#expression', 'x+y');
        await page.click('#submitExpression');
        await olorin.waitForTypecheck();
        expect(await inputs(page, expr)).toEqual({ ports: 1, wired: 0 });

        for (const v of vars) {
            await olorin.connect({ vertex: v, sort: 'output' }, { vertex: expr, sort: 'input' });
        }
        await olorin.waitForTypecheck();
        expect(await inputs(page, expr)).toEqual({ ports: 3, wired: 2 });
        // Its ports carry values, like the one it started with.
        const ports = await page.evaluate((i) => window.__olorin.ports()
            .filter((p) => p.vertex === i && p.sort === 'input'), expr);
        expect(ports.every((p) => !p.hidden)).toBe(true);

        // A block wired into it, deleted, takes its wire and so that wire's port.
        const alg = await olorin.dragRule('algplus', 200, 400);
        await page.evaluate(({ s, t }) => window.__olorin.connect(s, t),
                            { s: { vertex: alg, sort: 'output' }, t: { vertex: expr, sort: 'input' } });
        await olorin.waitForTypecheck();
        expect(await inputs(page, expr)).toEqual({ ports: 4, wired: 3 });
        await olorin.deleteNode(alg);
        await olorin.waitForTypecheck();
        expect(await inputs(page, expr)).toEqual({ ports: 3, wired: 2 });
    });
});
