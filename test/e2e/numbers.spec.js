// Facts about the number systems that the algebra block can't reach, and one it now can.
//
// The "=∨≠" and "≤∨>" blocks are disjunctions, which the algebra block doesn't prove: each is a
// "User" rule (bin/rules.ml) offering the ℤ/ℚ/ℝ/𝕊 versions of one axiom as an SFirst, so the
// number system is picked by whatever is wired to its inputs -- the same arrangement as the
// "?·?=0" (integral) block.
//
// A disequality the algebra block does still refuse, except between plain numbers: 0≠1 and its
// like are facts, while x≠y is for the student to prove by contradiction.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { find, firstLevel } = require('../lib/levels');

// State a level over two numbers x, y of the given set, prove it with a single two-input block
// (deceq or tord) fed by both variables, and report whether Olorin accepts the result.
async function twoNumberBlockProves(olorin, rule, { set, conclusion }) {
    await olorin.buildCustom({
        parameters: '',
        variables: `x ∈ ${set}\ny ∈ ${set}`,
        hypotheses: '',
        conclusion,
    });
    const box = await olorin.dragRule(rule, 400, 200);
    const nodes = await olorin.nodes();
    const varOf = (n) => nodes.find((v) => v.rule === 'variable' && v.name === n).id;
    await olorin.connect({ vertex: varOf('x'), sort: 'output' }, { vertex: box, sort: 'input', label: 'x' });
    await olorin.connect({ vertex: varOf('y'), sort: 'output' }, { vertex: box, sort: 'input', label: 'y' });
    const concl = nodes.find((n) => n.rule === 'conclusion');
    await olorin.connect({ vertex: box, sort: 'output' }, { vertex: concl.id, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

test.describe('The "=∨≠" block', () => {
    test('proves that two numbers are either equal or unequal', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await twoNumberBlockProves(olorin, 'deceq', {
            set: 'ℤ',
            conclusion: '(x=y)∨(x≠y)',
        })).toBe(true);
    });

    test('follows its inputs into the larger number systems', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await twoNumberBlockProves(olorin, 'deceq', {
            set: 'ℝ',
            conclusion: '(x=y)∨(x≠y)',
        })).toBe(true);
    });

    test('does not prove the ordering disjunction', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await twoNumberBlockProves(olorin, 'deceq', {
            set: 'ℤ',
            conclusion: '(x≤y)∨(x>y)',
        })).toBe(false);
    });
});

test.describe('The "≤∨>" block', () => {
    test('proves that of two numbers one is at most the other, or greater', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await twoNumberBlockProves(olorin, 'tord', {
            set: 'ℤ',
            conclusion: '(x≤y)∨(x>y)',
        })).toBe(true);
    });

    test('follows its inputs into the larger number systems', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await twoNumberBlockProves(olorin, 'tord', {
            set: '𝕊',
            conclusion: '(x≤y)∨(x>y)',
        })).toBe(true);
    });

    test('does not prove the equality disjunction', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await twoNumberBlockProves(olorin, 'tord', {
            set: 'ℤ',
            conclusion: '(x=y)∨(x≠y)',
        })).toBe(false);
    });
});

// State a level, prove it with a single algebra block fed by every hypothesis, and report whether
// Olorin accepts the result.
async function algebraProves(olorin, { variables = '', hypotheses = [], conclusion }) {
    await olorin.buildCustom({
        parameters: '',
        variables,
        hypotheses: hypotheses.join('\n'),
        conclusion,
    });
    const alg = await olorin.dragRule('alg', 500, 200);
    const nodes = await olorin.nodes();
    for (const n of nodes.filter((n) => n.rule === 'hypothesis')) {
        await olorin.connect({ vertex: n.id, sort: 'output' }, { vertex: alg, sort: 'input' });
    }
    await olorin.connect({ vertex: alg, sort: 'output' },
                         { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

test.describe('Disequalities and the algebra block', () => {
    // Neither side of a relation between two numerals says which number system it is about, so the
    // notation tries them in order and takes the first that works -- as the arithmetic operations
    // already do.  Without that, a statement like 0≠1 can't be written down at all.
    test('a relation between two numerals can be stated at all', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, { conclusion: '2=2' })).toBe(true);
        expect(await algebraProves(olorin, { conclusion: '0<1' })).toBe(true);
    });

    test('proves a disequality between plain numbers', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, { conclusion: '0≠1' })).toBe(true);
        expect(await algebraProves(olorin, { conclusion: '1/2≠1/3' })).toBe(true);
        expect(await algebraProves(olorin, { conclusion: '−1≠1' })).toBe(true);
    });

    test('and only a true one', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, { conclusion: '2≠2' })).toBe(false);
    });

    test('but still refuses one with a variable in it, however forced', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'x ∈ ℤ',
            hypotheses: ['x=1'],
            conclusion: 'x≠0',
        })).toBe(false);
        expect((await olorin.diagnostics()).map((d) => d.explanation).join(' '))
            .toContain('prove by contradiction');
    });

    // What the "0≠1" fact is for: contradicting an algebraic consequence of the hypotheses.  The
    // ascription block is what puts the statement where ¬-elimination can synthesize it.
    test('0≠1 contradicts a proof that 0=1', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '',
            variables: 'x ∈ ℤ',
            hypotheses: 'x=0\nx=1',
            conclusion: '⊥',
        });
        const zeroNeqOne = await olorin.dragRule('alg', 300, 100);
        const asc = await olorin.dragRule('asc', 500, 100);
        await page.waitForSelector('#ascribeBG', { state: 'visible' });
        await page.fill('#ascribe', '0≠1');
        await page.click('#submitAscribe');
        await olorin.waitForTypecheck();
        const zeroEqOne = await olorin.dragRule('alg', 300, 300);
        const negE = await olorin.dragRule('negE', 800, 200);
        const nodes = await olorin.nodes();
        for (const n of nodes.filter((n) => n.rule === 'hypothesis')) {
            await olorin.connect({ vertex: n.id, sort: 'output' }, { vertex: zeroEqOne, sort: 'input' });
        }
        await olorin.connect({ vertex: zeroNeqOne, sort: 'output' }, { vertex: asc, sort: 'input' });
        await olorin.connect({ vertex: asc, sort: 'output' }, { vertex: negE, sort: 'input', label: 'negation' });
        await olorin.connect({ vertex: zeroEqOne, sort: 'output' }, { vertex: negE, sort: 'input', label: 'statement' });
        await olorin.connect({ vertex: negE, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
    });
});
