// Powers with a rational exponent, and so the roots that come with them: x^(1/2) is a square root,
// written √x as well, and x^(1/3) a cube root.
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

// The types Olorin ends up giving the statements on each wire, whitespace squashed.
const wireLabels = (page) => page.evaluate(() =>
    Array.from(document.querySelectorAll('.connLabel')).map((e) => (e.innerText || '').replace(/\s+/g, '')));

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

test.describe('The √ symbol', () => {
    test('is the 1/2 power written another way, obligation and all', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['0≤x'], conclusion: '√x = x^(1/2)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['0≤x'], conclusion: '√x·√x = x',
        })).toBe(true);
        const without = await algebra(olorin, { variables: 'x ∈ ℝ', conclusion: '√x·√x = x' });
        expect(without.proved).toBe(false);
        expect(without.said).toContain('is nonnegative');
        const negative = await algebra(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['x<0'], conclusion: '√x = 5',
        });
        expect(negative.proved).toBe(false);
        expect(negative.said).toContain('is nonnegative');
    });

    test('lands in the reals whatever number system it started in', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℤ', hypotheses: ['0≤x'], conclusion: '√x·√x = x',
        })).toBe(true);
        expect(await proves(olorin, { conclusion: '√4 = 2' })).toBe(true);
        expect(await proves(olorin, { conclusion: '√2 < 3/2' })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\ny ∈ ℝ', hypotheses: ['0≤x', '0≤y'], conclusion: '√(x·y) = √x·√y',
        })).toBe(true);
    });

    test('binds tighter than the arithmetic, but reaches over a power', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // (√x)·2, not √(x·2) -- the latter is not 2√x.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['0≤x'], conclusion: '√x·2 = 2·√x',
        })).toBe(true);
        // √(x²), not (√x)²: it asks nothing of x, since x² is nonnegative by itself, and what it
        // gives back is |x| rather than x.
        const squared = await algebra(olorin, { variables: 'x ∈ ℝ', conclusion: '√x² = x' });
        expect(squared.proved).toBe(false);
        expect(squared.said).not.toContain('is nonnegative');
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ', hypotheses: ['0≤x'], conclusion: '√x² = x',
        })).toBe(true);
    });

    // It is the one symbol here with no ASCII spelling to fall back on -- · and − have * and - --
    // so as well as the \sqrt shortcut it gets a button, next to the other relations and before
    // the number systems.
    test('has a palette button, on every box that has a palette', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.openChooser();
        await page.click('#customLevel');
        await page.fill('#customName', '');
        await page.fill('#parameters', '');
        await page.fill('#variables', 'x ∈ ℝ');
        await page.fill('#hypotheses', '0≤x');
        await page.fill('#conclusion', '');
        for (const pal of ['paramPalette', 'varPalette', 'hypPalette', 'conclPalette', 'ascPalette', 'wirePalette']) {
            await expect(page.locator(`#${pal} .unicode-button`, { hasText: '√' })).toHaveCount(1);
        }
        // Click it, and it lands at the cursor and leaves the cursor after it.
        await page.click('#conclPalette .unicode-button:has-text("√")');
        await page.locator('#conclusion').pressSequentially('x·x^(1/2) = x');
        expect(await page.inputValue('#conclusion')).toBe('√x·x^(1/2) = x');

        // And what it typed is a statement the algebra block can prove.
        await page.click('#submitLevel');
        await olorin.dismissHints();
        const nodes = await olorin.nodes();
        const alg = await olorin.dragRule('alg', 600, 200);
        await olorin.connect({ vertex: nodes.find((n) => n.rule === 'hypothesis').id, sort: 'output' },
                             { vertex: alg, sort: 'input' });
        await olorin.connect({ vertex: alg, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
    });

    test('is what gets printed back, rather than the power it stands for', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℝ', hypotheses: '√(x+1) = 1', conclusion: '√(x+1) = 1',
        });
        const nodes = await olorin.nodes();
        await olorin.connect({ vertex: nodes.find((n) => n.rule === 'hypothesis').id, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await wireLabels(page)).toEqual(['√(x+1)=1']);
    });
});

// An exponent that isn't a literal at all: x^n, and x^(n+1) and x^(n+m) beside it.  The power
// itself stays an uninterpreted function of its base and its exponent, as it always was, but the
// translation now reads the exponent as a sum of terms with integer coefficients first, and writes
// the power as the matching product: x^(n+1) is x^n·x, x^(n+m) is x^n·x^m, x^(2·n) is x^n·x^n.  So
// the laws of exponents hold on the nose, both sides of one becoming the very same product.  What
// this needs is that each term of the exponent that stays a term is a whole number:
// b^(a+c) = b^a·b^c and b^(c·a) = (b^a)^c are true of every real b for natural a and c, and of a
// nonzero one for integers, but not of a negative base and a fractional exponent, where there is
// no real b^a to speak of.  A term that comes out a constant is no such worry, and folds into the
// offset -- which may then be a fraction, and a root of the base like any other.
test.describe('A variable exponent', () => {
    test('comes apart at a numeral, so the laws of exponents hold of it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: 'x^(n+1) = x^n·x',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: 'x^(n+2) = x^n·x²',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: 'x^(n+2) = x^(n+1)·x',
        })).toBe(true);
        // Nothing is assumed of the base: this is the one power law that holds at x = 0 too, the
        // translation reading x^0 as 1 there as everywhere else.
        expect(await proves(olorin, {
            variables: 'n ∈ ℕ', conclusion: '2^(n+1) = 2·2^n',
        })).toBe(true);
    });

    test('comes apart at a sum of terms, and at a coefficient', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ', conclusion: 'x^(n+m) = x^n·x^m',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ', conclusion: 'x^(n+m+1) = x^n·x^m·x',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: 'x^(2·n) = x^n·x^n',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: '(x^n)² = x^(2·n)',
        })).toBe(true);
        // The terms are compared as the translation writes them, so the same one twice is one
        // term with a coefficient of two.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: 'x^(n+n) = (x^n)²',
        })).toBe(true);
        // And terms that cancel leave a literal exponent, with nothing uninterpreted left in it.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ', conclusion: 'x^(n+m−n) = x^m',
        })).toBe(true);
    });

    // A fractional offset is a root of the base: the 1/2 in x^(n+1/2) folds into the offset like
    // any other constant, and x^(1/2) is then a root the problem never writes down, identified by
    // its base and its exponent as √x and x^(1/2) themselves are.
    test('may leave a fraction behind, which is a root of the base', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', hypotheses: ['0≤x'], conclusion: 'x^(n+1/2) = x^n·√x',
        })).toBe(true);
        // An even root carries its obligation here as it does anywhere else.
        const without = await algebra(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: 'x^(n+1/2) = x^n·√x',
        });
        expect(without.proved).toBe(false);
        expect(without.said).toContain('is nonnegative');
        // An odd one is total, and asks nothing.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: 'x^(n+1/3) = x^n·x^(1/3)',
        })).toBe(true);
    });

    test('takes its sign from its base, which a power of an opaque symbol would not', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', hypotheses: ['0<x'], conclusion: '0 < x^(n+1)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', hypotheses: ['0≤x'], conclusion: '0 ≤ x^n·x',
        })).toBe(true);
        // A literal base answers for itself, with nothing asked of the hypotheses.
        expect(await proves(olorin, { variables: 'n ∈ ℕ', conclusion: '0 < 2^n' })).toBe(true);
        // A power of ℕ is a natural like any other term of that type.
        expect(await proves(olorin, {
            variables: 'n ∈ ℕ\nk ∈ ℕ', conclusion: '0 ≤ n^(k+1)',
        })).toBe(true);
        // But a base whose sign nothing settles gives the power no sign either.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: '0 ≤ x^(n+1)',
        })).toBe(false);
    });

    // Which is the point of the whole thing: the step of an induction, with the inductive
    // hypothesis about x^n in hand and the goal about x^(n+1), is now one algebra block.
    test('lets the step of an induction be done by algebra', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', hypotheses: ['1≤x', '1≤x^n'], conclusion: '1 ≤ x^(n+1)',
        })).toBe(true);
    });

    test('is a reciprocal where it can go below zero, so the base must be nonzero', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // n−1 is an integer, not a natural, so this power may be a reciprocal.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', hypotheses: ['x≠0'], conclusion: 'x^(n−1)·x = x^n',
        })).toBe(true);
        const without = await algebra(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', conclusion: 'x^(n−1)·x = x^n',
        });
        expect(without.proved).toBe(false);
        expect(without.said).toContain('is nonzero');
        // Likewise a term with a negative coefficient, where the nonzero base is what makes the
        // power it divides by nonzero in its turn.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ', hypotheses: ['x≠0'],
            conclusion: 'x^(n−m)·x^m = x^n',
        })).toBe(true);
        const negcoeff = await algebra(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ', conclusion: 'x^(n−m)·x^m = x^n',
        });
        expect(negcoeff.proved).toBe(false);
        expect(negcoeff.said).toContain('is nonzero');
    });

    test('stays opaque when it need not be a whole number', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // q could be 1/2 and x could be negative, where there is no law to apply.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nq ∈ ℚ', conclusion: 'x^(q+1) = x^q·x',
        })).toBe(false);
        // Even a nonnegative base doesn't bring this one back: the split is refused outright
        // rather than carrying an obligation.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nq ∈ ℚ', hypotheses: ['0<x'], conclusion: 'x^(q+1) = x^q·x',
        })).toBe(false);
    });

    // Coming apart mustn't cost what congruence already gave.  A power whose exponent is written
    // as a product is a term of its own, and one written as a sum comes apart -- so the written
    // form is kept alongside the product, and said to equal it, or two ways of writing the same
    // power would no longer be the same power.
    test('is still the power any other way of writing that exponent is', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ', conclusion: 'x^((m+1)·(n+1)) = x^(m·n+m+n+1)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ', hypotheses: ['m=n'], conclusion: 'x^(m+1) = x^(n+1)',
        })).toBe(true);
    });

    // What comes apart is a sum with numerals in it and nothing else: a product of two terms is a
    // term of its own, there being no power of the base to raise to it.
    test('is only taken apart at a sum and a numeral', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ', conclusion: 'x^(n·m) = (x^n)^m',
        })).toBe(false);
        // Nor is a product multiplied out, so an exponent written as one doesn't come apart into
        // the powers of the sum it would expand to.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ',
            conclusion: 'x^((m+1)·(n+1)) = x^(m·n)·x^m·x^n·x',
        })).toBe(false);
        // A fractional coefficient is no coefficient either: (x^n)^(1/2) would need x^n shown
        // nonnegative, which is not something the split can ask for.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ', hypotheses: ['0<x'], conclusion: 'x^(n/2)·x^(n/2) = x^n',
        })).toBe(false);
        // Equal exponents do give equal powers, though, as they did before: that much is
        // congruence, which the uninterpreted symbol has always had.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ', hypotheses: ['n=m'], conclusion: 'x^n = x^m',
        })).toBe(true);
    });
});
