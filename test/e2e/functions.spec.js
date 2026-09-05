// Functions the algebra block can't interpret -- anything that isn't one of the arithmetic
// operations, like an f from the level's parameters -- are given to Z3 as uninterpreted function
// symbols rather than folded into an opaque constant apiece.  Z3 assumes nothing about such a
// function beyond congruence: equal arguments give equal results.  So "x = y" proves "f(x) = f(y)"
// and nothing else about f comes with it -- in particular it is not assumed injective, monotone,
// or anything of the sort.
//
// Congruence only reaches arguments the block can talk about in the first place, since the
// hypotheses it takes have to be relations between numbers: "f(x) = f(y)" from "x = y" needs x and
// y to be numbers, not elements of some parameter type.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// State a level and prove it with a single algebra block fed by every hypothesis.
async function algebraProves(olorin, { parameters = 'f : ℝ → ℝ', variables = 'x ∈ ℝ\ny ∈ ℝ',
                                       hypotheses = [], conclusion }) {
    await olorin.buildCustom({
        parameters,
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
    return olorin.isComplete();
}

test.describe('Uninterpreted functions in the algebra block', () => {
    test('equal arguments give equal values', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            hypotheses: ['x = y'],
            conclusion: 'f x = f y',
        })).toBe(true);
    });

    test('but nothing else about f comes with that', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // Unequal arguments say nothing, so f(x)=f(y) on its own is unprovable...
        expect(await algebraProves(olorin, {
            conclusion: 'f x = f y',
        })).toBe(false);
        // ...and f is not assumed injective, so the converse doesn't hold either.
        expect(await algebraProves(olorin, {
            hypotheses: ['f x = f y'],
            conclusion: 'x = y',
        })).toBe(false);
        // Nor monotone.
        expect(await algebraProves(olorin, {
            hypotheses: ['x < y'],
            conclusion: 'f x < f y',
        })).toBe(false);
    });

    test('the arguments are compared as arithmetic, not as syntax', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            hypotheses: ['x = y + 1'],
            conclusion: 'f x = f (y + 1)',
        })).toBe(true);
        expect(await algebraProves(olorin, {
            hypotheses: ['x + x = 2 · y'],
            conclusion: 'f x = f y',
        })).toBe(true);
    });

    test('a value of f is a number like any other', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            conclusion: 'f x + f x = 2 · f x',
        })).toBe(true);
        // Congruence carries a hypothesis about f(x) over to f(y).
        expect(await algebraProves(olorin, {
            hypotheses: ['x = y', 'f x ≤ 3'],
            conclusion: 'f y ≤ 3',
        })).toBe(true);
    });

    test('a function of two arguments', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            parameters: 'g : ℝ → ℝ → ℝ',
            hypotheses: ['x = y'],
            conclusion: 'g x y = g y x',
        })).toBe(true);
        // One argument agreeing isn't enough.
        expect(await algebraProves(olorin, {
            parameters: 'g : ℝ → ℝ → ℝ',
            conclusion: 'g x y = g y x',
        })).toBe(false);
    });
});
