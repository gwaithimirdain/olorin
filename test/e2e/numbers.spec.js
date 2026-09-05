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
async function algebraProves(olorin, { parameters = '', variables = '', hypotheses = [], conclusion }) {
    await olorin.buildCustom({
        parameters,
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
            .toContain('proof by contradiction');
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

// ℕ is a number system of the game's like any other, except that it isn't a ring: it has addition,
// multiplication, powers and an ordering, and no subtraction or negation.  Everything defined with
// those -- −, ∣ ∣, min, max, the squares, √ -- starts at ℤ instead, which naturals still reach,
// since ℕ ≤ ℤ.  The algebra block reads all of it as arithmetic over the reals, which ℕ embeds in,
// so its facts are the ones true of the naturals as a sub-semiring of ℝ, induction excepted.
test.describe('The natural numbers', () => {
    test('add, multiply and take powers', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nm ∈ ℕ',
            conclusion: 'n+m=m+n',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nm ∈ ℕ\nk ∈ ℕ',
            conclusion: 'n·(m+k)=n·m+n·k',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ',
            conclusion: 'n^2=n·n',
        })).toBe(true);
    });

    test('are ordered', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nm ∈ ℕ\nk ∈ ℕ',
            hypotheses: ['n<m', 'm<k'],
            conclusion: 'n<k',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nm ∈ ℕ',
            hypotheses: ['n≤m'],
            conclusion: 'n+1≤m+1',
        })).toBe(true);
    });

    // Subtraction is the whole reason ℕ isn't on the ring list: a difference of naturals is an
    // integer, and reads as one, so nothing here is the truncated subtraction of the naturals.
    test('subtract as integers, not by truncation', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nm ∈ ℕ',
            conclusion: 'n−m=−(m−n)',
        })).toBe(true);
        // 0−1 would be 0 if it were truncated, and the block would then refuse this.
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ',
            conclusion: '(n−(n+1))+1=0',
        })).toBe(true);
    });

    test('take sizes, the smaller and larger of two, and the small powers', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ',
            conclusion: 'n²·n=n³',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ',
            conclusion: 'n⁴=n²·n²',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nm ∈ ℕ',
            hypotheses: ['n≤m'],
            conclusion: 'min(n,m)+max(n,m)=n+m',
        })).toBe(true);
        // ∣n∣ needs the sign of n settled, and being a natural settles it: even the plain block,
        // which otherwise makes the student split into cases, takes this one.
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ',
            conclusion: '∣n∣=n',
        })).toBe(true);
    });

    // None of those takes you out of the naturals, and the results really are naturals: f accepts
    // nothing else, so these statements can't even be made unless min and ² land back in ℕ.
    test('and stay in ℕ when they do', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            parameters: 'f : ℕ → ℝ',
            variables: 'n ∈ ℕ',
            conclusion: 'f (n²) = f (n·n)',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            parameters: 'f : ℕ → ℝ',
            variables: 'n ∈ ℕ\nm ∈ ℕ',
            hypotheses: ['n≤m'],
            conclusion: 'f (min(n,m)) = f n',
        })).toBe(true);
    });

    // What does take you out of them: subtraction, division and square roots, which read as the
    // integer, rational or real ones, a natural being contained in all three.  √ needs its
    // argument nonnegative before it denotes anything, and a natural is.
    test('leave ℕ for the operations that have to', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ',
            conclusion: '√n·√n=n',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nm ∈ ℕ',
            hypotheses: ['n≠0'],
            conclusion: '(m·n)/n=m',
        })).toBe(true);
    });

    // Being a natural is a fact in itself: the block is told 0≤n for every natural it meets, since
    // to Z3 they are opaque reals and nothing else would say so.
    test('are known to be nonnegative for being naturals', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nm ∈ ℕ',
            conclusion: 'n≤n+m',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ',
            conclusion: '0≤n·n+n',
        })).toBe(true);
        // An integer that happens to be called m is not a natural, and gets no such fact.
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nm ∈ ℤ',
            conclusion: 'n≤n+m',
        })).toBe(false);
    });

    // The value of a function landing in ℕ is just as opaque, and just as nonnegative.
    test('are nonnegative wherever they turn up, not just as variables', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            parameters: 'f : ℝ → ℕ',
            variables: 'x ∈ ℝ',
            conclusion: '0≤f x',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            parameters: 'f : ℝ → ℤ',
            variables: 'x ∈ ℝ',
            conclusion: '0≤f x',
        })).toBe(false);
    });

    test('mix with the larger systems, being contained in them', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            variables: 'n ∈ ℕ\nx ∈ ℝ',
            hypotheses: ['n<3', 'x=n'],
            conclusion: 'x<3',
        })).toBe(true);
    });
});
