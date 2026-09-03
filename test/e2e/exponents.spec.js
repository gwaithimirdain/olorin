// Powers with a rational exponent, and so the roots that come with them: x^(1/2) is a square root,
// x^(1/3) a cube root.
//
// The exponent's type is whatever the base's number system is closed under -- ℤ under naturals, ℚ
// under integers, and only ℝ and 𝕊 under arbitrary rationals -- so writing a root of an integer
// promotes the statement to ℝ, through the same SFirst-and-subtyping that already sends x/2 out of
// ℤ and into ℚ.
//
// The oracle gives a root p/q a fresh variable s defined by s^q = base^p.  An even q leaves two
// candidates, so it also says s >= 0 and takes the principal root -- and then the base has to be
// shown nonnegative, since otherwise that definition has no solution at all and the algebra block
// would "prove" anything at all from it.  Odd roots are total on the reals and need neither.  A
// negative exponent is the reciprocal of the positive one, so it picks up the ordinary
// nonzero-denominator obligation.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// State a level, prove it with a single algebra block fed by every hypothesis, and report whether
// Olorin accepted it along with what it said if it didn't.
async function algebra(olorin, { variables = '', hypotheses = [], conclusion }) {
    await olorin.buildCustom({
        parameters: '',
        variables,
        hypotheses: hypotheses.join('\n'),
        conclusion,
    });
    const nodes = await olorin.nodes();
    const alg = await olorin.dragRule('alg', 600, 200);
    for (const n of nodes.filter((n) => n.rule === 'hypothesis')) {
        await olorin.connect({ vertex: n.id, sort: 'output' }, { vertex: alg, sort: 'input' });
    }
    await olorin.connect({ vertex: alg, sort: 'output' },
                         { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
    await olorin.waitForTypecheck();
    return {
        proved: await olorin.isComplete(),
        said: (await olorin.diagnostics()).map((d) => d.explanation || '').join(' '),
    };
}

const proves = async (olorin, level) => (await algebra(olorin, level)).proved;

test.describe('Integer exponents', () => {
    test('still mean what they did, and stay in the number system they started in', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, { variables: 'x ∈ ℤ', conclusion: 'x^2 = x·x' })).toBe(true);
        expect(await proves(olorin, { variables: 'x ∈ ℝ', conclusion: 'x^3 = x·x·x' })).toBe(true);
    });

    test('a negative one is a reciprocal, so the base has to be nonzero', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['x≠0'], conclusion: 'x^(-1)·x = 1',
        })).toBe(true);
        const without = await algebra(olorin, { variables: 'x ∈ ℝ', conclusion: 'x^(-1)·x = 1' });
        expect(without.proved).toBe(false);
        expect(without.said).toContain('is nonzero');
        // ℚ is closed under integer powers, so this one needn't leave it.
        expect(await proves(olorin, {
            variables: 'x ∈ ℚ', hypotheses: ['x≠0'], conclusion: 'x^(-1)·x = 1',
        })).toBe(true);
    });
});

test.describe('An even root', () => {
    test('needs its base shown nonnegative', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['0≤x'], conclusion: '(x^(1/2))^2 = x',
        })).toBe(true);
        const without = await algebra(olorin, { variables: 'x ∈ ℝ', conclusion: '(x^(1/2))^2 = x' });
        expect(without.proved).toBe(false);
        expect(without.said).toContain('is nonnegative');
    });

    // The reason that condition is an obligation and not just an assumption: "s >= 0 and s*s = x"
    // has no solution when x < 0, and a definition with no solution proves everything.
    test('and a base the hypotheses force negative proves nothing at all', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const r = await algebra(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['x<0'], conclusion: 'x^(1/2) = 5',
        });
        expect(r.proved).toBe(false);
        expect(r.said).toContain('is nonnegative');
    });

    test('is the nonnegative one of the two', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['0≤x'], conclusion: '0 ≤ x^(1/2)',
        })).toBe(true);
        // So (x²)^(1/2) is |x|, and is not provably x.
        expect(await proves(olorin, { variables: 'x ∈ ℝ', conclusion: '(x²)^(1/2) = x' })).toBe(false);
    });
});

test.describe('An odd root', () => {
    test('is total: no condition on the base, negatives included', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, { variables: 'x ∈ ℝ', conclusion: '(x^(1/3))^3 = x' })).toBe(true);
        expect(await proves(olorin, { conclusion: '(-8)^(1/3) = -2' })).toBe(true);
    });
});

test.describe('The laws of rational exponents', () => {
    test('hold where they should', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\ny ∈ ℝ', hypotheses: ['0≤x', '0≤y'],
            conclusion: '(x·y)^(1/2) = x^(1/2)·y^(1/2)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['0≤x'], conclusion: 'x^(1/2)·x^(1/3) = x^(5/6)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['0<x'], conclusion: 'x^(-1/2)·x^(1/2) = 1',
        })).toBe(true);
    });

    test('and hold of plain numbers too', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, { conclusion: '4^(1/2) = 2' })).toBe(true);
        expect(await proves(olorin, { conclusion: '2^(1/2) < 3/2' })).toBe(true);
        expect(await proves(olorin, { conclusion: '2^(1/2) < 7/5' })).toBe(false);
    });
});

test.describe('A rational exponent on an integer base', () => {
    test('promotes the statement to ℝ, and the hypotheses come with it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℤ', hypotheses: ['0≤x'], conclusion: '(x^(1/2))^2 = x',
        })).toBe(true);
    });
});
