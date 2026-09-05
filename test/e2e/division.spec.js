// Tests for the algebra block over rational functions.
//
// Division is handed to Z3 as division: Z3's real division is total with the value at a zero
// denominator left uninterpreted, so an identity is provable exactly when it holds for every
// value the quotient-by-zero might take.  On top of that we require the hypotheses to force
// every denominator nonzero, so writing a quotient that might not denote is an error rather
// than a question about an unspecified value.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// State a level, then prove it with a single algebra block fed by every hypothesis, and report
// whether Olorin accepts the result.
async function algebraProves(olorin, { variables = '', hypotheses = [], conclusion }) {
    await olorin.buildCustom({
        parameters: '',
        variables,
        hypotheses: hypotheses.join('\n'),
        conclusion,
    });
    const alg = await olorin.dragRule('alg', 400, 200);
    const nodes = await olorin.nodes();
    for (const n of nodes.filter((n) => n.rule === 'hypothesis')) {
        await olorin.connect({ vertex: n.id, sort: 'output' }, { vertex: alg, sort: 'input' });
    }
    const concl = nodes.find((n) => n.rule === 'conclusion');
    await olorin.connect({ vertex: alg, sort: 'output' }, { vertex: concl.id, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

test.describe('Algebra over rational functions', () => {
    test('a quotient of numerals is just a constant', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, { conclusion: '1/2+1/2=1' })).toBe(true);
    });

    test('x·(1/x)=1 needs x≠0, and follows from it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'x ∈ ℝ',
            conclusion: 'x·(1/x)=1',
        })).toBe(false);
        expect(await algebraProves(olorin, {
            variables: 'x ∈ ℝ',
            hypotheses: ['x≠0'],
            conclusion: 'x·(1/x)=1',
        })).toBe(true);
    });

    test('cancelling a common factor needs the factor nonzero', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'x ∈ ℝ',
            conclusion: '(x²−1)/(x−1)=x+1',
        })).toBe(false);
        expect(await algebraProves(olorin, {
            variables: 'x ∈ ℝ',
            hypotheses: ['x≠1'],
            conclusion: '(x²−1)/(x−1)=x+1',
        })).toBe(true);
    });

    test('adding fractions over a common denominator', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'x ∈ ℝ\ny ∈ ℝ',
            hypotheses: ['x≠0', 'y≠0'],
            conclusion: '1/x+1/y=(x+y)/(x·y)',
        })).toBe(true);
    });

    test('a nested quotient', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'x ∈ ℝ',
            hypotheses: ['x≠0'],
            conclusion: '1/(1/x)=x',
        })).toBe(true);
    });

    test('a denominator can be shown nonzero by an inequality', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'x ∈ ℝ',
            hypotheses: ['x>0'],
            conclusion: '1/x>0',
        })).toBe(true);
    });

    test('dividing integers lands in ℚ', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'a ∈ ℤ',
            hypotheses: ['a≠0'],
            conclusion: 'a/a=1',
        })).toBe(true);
    });

    test('the surreals are a field too', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'x ∈ 𝕊',
            hypotheses: ['x≠0'],
            conclusion: 'x·(1/x)=1',
        })).toBe(true);
    });

    // Spacing in the input is normalized away by Narya's printer, so a port showing the tight form
    // means the term really did round-trip through the divide notation.
    test('a quotient prints back as a quotient', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '',
            variables: 'x ∈ ℝ\ny ∈ ℝ',
            hypotheses: 'y≠0',
            conclusion: '(x+1)/y + 1/2 = x',
        });
        await olorin.waitForTypecheck();
        const types = (await page.evaluate(() => window.__olorin.ports())).map((p) => p.type);
        expect(types).toContain('(x+1)/y+1/2=x');
    });

    // Clearing denominators and then using the *cleared* hypotheses to discharge the side
    // conditions would turn this hypothesis into 1=0 and prove anything at all.  It is genuinely
    // satisfiable (at x=0, whatever 1/0 denotes), so nothing may follow from it.
    test('a hypothesis about a quotient by a possibly-zero denominator proves nothing', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'x ∈ ℝ',
            hypotheses: ['1/x=0'],
            conclusion: 'x=x+1',
        })).toBe(false);
    });
});
