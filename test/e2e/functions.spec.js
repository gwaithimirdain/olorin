// Functions the algebra block can't interpret -- anything that isn't one of the arithmetic
// operations, like an f from the level's parameters -- are given to Z3 as uninterpreted function
// symbols rather than folded into an opaque constant apiece.  Z3 assumes nothing about such a
// function beyond congruence: equal arguments give equal results.  So "x = y" proves "f(x) = f(y)"
// and nothing else about f comes with it -- in particular it is not assumed injective, monotone,
// or anything of the sort.
//
// The statements wired into a block don't have to be about the same kind of number as its goal, or
// about numbers at all: an equation between elements of a parameter type is carried into the
// arguments of an uninterpreted function just the same.  There's no need to hold the orderings to
// the goal's number system either, because each number system has an ordering of its own and
// nothing else has one -- <, ≤, > and ≥ can't be written about anything but numbers.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { firstLevel } = require('../lib/levels');

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

test.describe('Equations about things that are not numbers', () => {
    // The point of allowing these: the equation is useless to the arithmetic itself, but it tells
    // Z3 that two arguments of an uninterpreted function agree, and congruence does the rest.
    test('carry into the arguments of a function that lands in the numbers', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            parameters: 'A : Type\nf : A → ℝ',
            variables: 'a ∈ A\nb ∈ A',
            hypotheses: ['a = b'],
            conclusion: 'f a = f b',
        })).toBe(true);
        // And they are still only equations: nothing about f comes with them.
        expect(await algebraProves(olorin, {
            parameters: 'A : Type\nf : A → ℝ',
            variables: 'a ∈ A\nb ∈ A',
            conclusion: 'f a = f b',
        })).toBe(false);
    });

    test('and can be the goal as well as a hypothesis', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            parameters: 'A : Type\ng : ℝ → A',
            variables: 'x ∈ ℝ\ny ∈ ℝ',
            hypotheses: ['x + 1 = y'],
            conclusion: 'g (x + 1) = g y',
        })).toBe(true);
    });

    test('mix with equations about numbers in one block', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            parameters: 'A : Type\nf : A → ℝ',
            variables: 'a ∈ A\nb ∈ A\nx ∈ ℝ',
            hypotheses: ['a = b', 'f a = 2 · x'],
            conclusion: 'f b = x + x',
        })).toBe(true);
    });

    test('and so does an inequality about a number system the goal has nothing to do with',
         async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await algebraProves(olorin, {
            parameters: 'A : Type\ng : ℝ → A',
            variables: 'x ∈ ℝ\ny ∈ ℝ',
            hypotheses: ['x ≤ y', 'y ≤ x'],
            conclusion: 'g x = g y',
        })).toBe(true);
    });

    test('while an ordering between them cannot be stated at all', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(firstLevel().name);
        // <, ≤, > and ≥ are relations on the number systems and nowhere else, so there is no
        // reading of "a < b" for a and b in a parameter type, and Olorin won't take the level.
        await olorin.buildCustom({
            parameters: 'A : Type',
            variables: 'a ∈ A\nb ∈ A',
            hypotheses: 'a < b',
            conclusion: 'a = b',
        });
        expect(await olorin.currentLevelName()).toBe(firstLevel().name);
    });
});
