// Writing a relation the other way round.
//
// An ordering names its number system in its own constant, and > is < with its sides exchanged, so
// "0<x" and "x>0" really are the same statement: one wire carries either to the other.
//
// Equality is not like that.  Its type argument is implicit, read off whichever side synthesizes
// one -- and the side it is read off has to come first, so the only way to state "0=x", whose left
// side is a numeral and synthesizes nothing, used to be the reversed "x=0".  That made the two
// spellings the same statement, which was an accident of where the implicit type came from rather
// than anything anyone asked for, and it didn't extend to "a=x" against "x=a", where both sides
// synthesize and the written order stands.  Now the number system is named outright instead, so
// every spelling keeps its own order and getting from one to the other takes an algebra block.
//
// What must not come back is the older bug behind this one: the reverse of = is =, and of ≠ is ≠,
// and those two were once paired with each other, so "0=x" quietly meant x≠0 and "0≠x" meant x=0.

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

// The same, with an algebra block in between, which is what it takes when the two statements are
// different ways of saying one thing rather than one statement.  A disequality goal is the "algneq"
// block's to prove, not the plain one's.
async function algebraProves(olorin, rule, hypothesis, conclusion) {
    await olorin.buildCustom({
        parameters: '',
        variables: 'x ∈ ℤ',
        hypotheses: hypothesis,
        conclusion,
    });
    const nodes = await olorin.nodes();
    const alg = await olorin.dragRule(rule, 500, 200);
    await olorin.connect({ vertex: nodes.find((n) => n.rule === 'hypothesis').id, sort: 'output' },
                         { vertex: alg, sort: 'input' });
    await olorin.connect({ vertex: alg, sort: 'output' },
                         { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

// Each ordering, written with the variable on the left and then with it on the right.
const ORDERINGS = [
    ['x<0', '0>x'],
    ['x>0', '0<x'],
    ['x≤0', '0≥x'],
    ['x≥0', '0≤x'],
];

const EQUALITIES = [
    ['x=0', '0=x', 'alg'],
    ['x≠0', '0≠x', 'algneq'],
];

test.describe('A relation written with the numeral first', () => {
    for (const [plain, reversed] of ORDERINGS) {
        test(`"${reversed}" states the same thing as "${plain}"`, async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            expect(await oneWireProves(olorin, plain, reversed)).toBe(true);
            expect(await oneWireProves(olorin, reversed, plain)).toBe(true);
        });
    }

    for (const [plain, reversed, rule] of EQUALITIES) {
        test(`"${reversed}" is its own statement, and algebra gets to "${plain}"`, async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            expect(await oneWireProves(olorin, plain, reversed)).toBe(false);
            expect(await algebraProves(olorin, rule, plain, reversed)).toBe(true);
            expect(await algebraProves(olorin, rule, reversed, plain)).toBe(true);
        });
    }

    test('and in particular is not read as its negation', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // The regression: "0=x" as ¬(x=0) and "0≠x" as x=0.  Read the type off the wire, so the
        // check doesn't depend on provability alone.
        await oneWireProves(olorin, '0=x', '0=x');
        expect(await wireLabels(page)).toEqual(['0=x']);
        await oneWireProves(olorin, '0≠x', '0≠x');
        expect(await wireLabels(page)).toEqual(['0≠x']);
        // And it says what it says: from "0=x" algebra gets x=0 and not x≠0, and the other way
        // about from "0≠x".
        expect(await algebraProves(olorin, 'algneq', '0=x', 'x≠0')).toBe(false);
        expect(await algebraProves(olorin, 'alg', '0≠x', 'x=0')).toBe(false);
    });
});
