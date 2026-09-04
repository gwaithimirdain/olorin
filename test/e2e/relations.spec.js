// Writing a relation the other way round.
//
// "x < y" reads the number system off whichever side synthesizes.  When that is the right-hand
// side, the two have to be swapped so the synthesizing one comes first, and the relation is stated
// *reversed* to compensate: "0 < x" becomes "x > 0".  The reverse of = is =, and of ≠ is ≠; they
// used to be paired with each other instead, so "0 = x" quietly meant x ≠ 0 and "0 ≠ x" meant
// x = 0 -- in level statements, wire labels and ascriptions alike.
//
// Each pair below is the same statement written both ways round, so the two are the same type and
// one wire from the hypothesis to the conclusion proves it.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// The types Olorin ends up giving the statements on each wire, whitespace squashed.
const wireLabels = (page) => page.evaluate(() =>
    Array.from(document.querySelectorAll('.connLabel')).map((e) => (e.innerText || '').replace(/\s+/g, '')));

// A level asserting `hypothesis` and asking for `conclusion`, proved by a single wire between them
// -- which goes through exactly when the two elaborate to the same statement.
async function oneWireProves(olorin, hypothesis, conclusion) {
    await olorin.buildCustom({
        parameters: '',
        variables: 'x ∈ ℤ',
        hypotheses: hypothesis,
        conclusion,
    });
    const nodes = await olorin.nodes();
    await olorin.connect({ vertex: nodes.find((n) => n.rule === 'hypothesis').id, sort: 'output' },
                         { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

// Every relation, written with the variable on the left and then with it on the right.
const PAIRS = [
    ['x=0', '0=x'],
    ['x≠0', '0≠x'],
    ['x<0', '0>x'],
    ['x>0', '0<x'],
    ['x≤0', '0≥x'],
    ['x≥0', '0≤x'],
];

test.describe('A relation written with the numeral first', () => {
    for (const [plain, reversed] of PAIRS) {
        test(`"${reversed}" states the same thing as "${plain}"`, async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            expect(await oneWireProves(olorin, plain, reversed)).toBe(true);
            expect(await oneWireProves(olorin, reversed, plain)).toBe(true);
        });
    }

    test('and in particular is not read as its negation', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // The regression: "0=x" as ¬(x=0) and "0≠x" as x=0.  Read the type off the wire, so the
        // check doesn't depend on one-wire provability alone.
        await oneWireProves(olorin, '0=x', '0=x');
        expect(await wireLabels(page)).toEqual(['x=0']);
        await oneWireProves(olorin, '0≠x', '0≠x');
        expect(await wireLabels(page)).toEqual(['x≠0']);
    });
});
