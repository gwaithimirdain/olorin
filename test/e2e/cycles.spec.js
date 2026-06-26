// A graphical proof must be acyclic.  The checker detects cycles and flags an offending wire red
// rather than looping forever trying to typecheck the impossible term.  Two projection (andE) nodes
// wired into each other used to freeze the browser; this guards that it no longer does.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

const out = (v, l) => ({ vertex: v, sort: 'output', label: l });
const inp = (v, l) => ({ vertex: v, sort: 'input', label: l });

// Close the final connection in a separate evaluate that we race against a timeout, so a
// regression (an infinite loop in the synchronous typecheck) surfaces as a failure, not a 30s hang.
async function connectRacingHang(page, s, t) {
    const evalP = page.evaluate(({ s, t }) => window.__olorin.connect(s, t), { s, t }).then(() => 'ok');
    const timeoutP = new Promise((res) => setTimeout(() => res('HANG'), 8000));
    return Promise.race([evalP, timeoutP]);
}

const redWireCount = (page) =>
    page.evaluate(() =>
        Array.from(document.querySelectorAll('#canvas svg path'))
            .filter((p) => p.getAttribute('stroke') === '#ff0000').length);

test.describe('Cyclic proofs', () => {
    test('two andE nodes wired into a cycle: no hang, an offending wire turns red', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel('1-2-1'); // rules andI + andE
        const a = await olorin.dragRule('andE', 300, 120);
        const b = await olorin.dragRule('andE', 600, 320);
        await olorin.connect(out(a, 'fst'), inp(b, undefined));
        expect(await connectRacingHang(page, out(b, 'fst'), inp(a, undefined))).toBe('ok');
        expect(await redWireCount(page)).toBeGreaterThan(0);
    });

    test('andI/andE cycle is also flagged without hanging', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel('1-2-1');
        const i = await olorin.dragRule('andI', 300, 120);
        const e = await olorin.dragRule('andE', 600, 320);
        await olorin.connect(out(e, 'fst'), inp(i, 'fst'));
        expect(await connectRacingHang(page, out(i, undefined), inp(e, undefined))).toBe('ok');
        expect(await redWireCount(page)).toBeGreaterThan(0);
    });

    test('breaking the cycle lets a normal proof still complete (synthesis still works)', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel('1-2-1'); // P, Q |- P/\Q
        // A straightforward andI proof of P/\Q from the two hypotheses.
        const andI = await olorin.dragRule('andI', 450, 200);
        await olorin.connect(out('hyp0', undefined), inp(andI, 'fst'));
        await olorin.connect(out('hyp1', undefined), inp(andI, 'snd'));
        await olorin.connect(out(andI, undefined), inp('concl0', undefined));
        expect(await olorin.isComplete()).toBe(true);
    });
});
