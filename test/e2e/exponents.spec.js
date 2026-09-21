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
async function algebraWith(rule, olorin, { variables = '', hypotheses = [], conclusion }) {
    await olorin.buildCustom({
        parameters: '',
        variables,
        hypotheses: hypotheses.join('\n'),
        conclusion,
    });
    const nodes = await olorin.nodes();
    const alg = await olorin.dragRule(rule, 600, 200);
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

const algebra = (olorin, level) => algebraWith('alg', olorin, level);
const proves = async (olorin, level) => (await algebra(olorin, level)).proved;
// An absolute value written into the statement is one the plain block asks the hypotheses to
// decide the sign of, so the goals below that write one are proved with the block that decides it
// itself.  The absolute value the translation introduces of its own accord is not such a case: it
// stands for a nonnegative quantity and there is no split in it for anyone to make.
const plusProves = async (olorin, level) => (await algebraWith('algplus', olorin, level)).proved;

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

// An exponent that isn't a literal at all: x^n, and x^(n+1) and x^(n+m) beside it.  A power is
// read as the product of powers it really is -- the exponent as a polynomial over ℚ, multiplied
// out, and the base taken down to the terms at the bottom of it -- so that x^(n+1) is x^n·x,
// x^(n+m) is x^n·x^m, (x·y)^n is x^n·y^n, (x^m)^n is x^(m·n), and x^((m+1)·(n+1)) is
// x^(m·n)·x^m·x^n·x.  What is left at the end of that is one uninterpreted power for each term,
// as the whole power was before, so the laws of exponents hold on the nose -- both sides of one
// becoming the very same product -- rather than by anything Z3 is asked to work out.
//
// Every step of it needs the exponent it distributes over to be a whole number: b^(a+c) is b^a·b^c
// and (b^a)^c is b^(a·c) for every real b when a and c are naturals, and for a nonzero one when
// they are integers, but neither is so of a negative base and a fractional exponent, where there
// is no real b^a to speak of.  A step that hasn't got that simply isn't taken, and the steps
// around it still are -- or it is taken of the absolute value, where an even exponent makes one
// available.  A fractional *coefficient* is another matter, being no obstacle at all: clearing its
// denominator is taking that root of the base, which is the module's own way of saying that
// x^(n/2) is (x^(1/2))^n.
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

    // A product of sums multiplies out, so an exponent written as one comes apart into the powers
    // of the sum it expands to, and is the same exponent as that sum written directly.
    test('multiplies out a product of sums', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ',
            conclusion: 'x^((m+1)·(n+1)) = x^(m·n)·x^m·x^n·x',
        })).toBe(true);
        // A small power in the exponent is the product it stands for.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nm ∈ ℕ', conclusion: 'x^((m+1)²) = x^(m·m)·x^m·x^m·x',
        })).toBe(true);
        // The monomials are compared as the translation writes them, and Z3 sees m·n and n·m are
        // the same number, so a monomial written both ways round is one power twice over.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ', conclusion: 'x^(m·n+n·m) = (x^(m·n))²',
        })).toBe(true);
    });

    // The base comes apart multiplicatively as the exponent comes apart additively: (u·v)^E is
    // u^E·v^E and (u/v)^E is u^E·v^(−E), so a power is a product of powers of the terms at the
    // bottom of it, with the exponents multiplied out along the way.
    test('takes a base apart at its products and quotients', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\ny ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ';
        expect(await proves(olorin, { variables: vars, conclusion: '(x·y)^n = x^n·y^n' })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, conclusion: '(x·y)^(n+1) = x^n·y^n·x·y',
        })).toBe(true);
        // A factor written twice is that power squared, the factors being collected like the
        // terms of the exponent are.
        expect(await proves(olorin, {
            variables: vars, conclusion: '(x·y·x)^n = (x^n)²·y^n',
        })).toBe(true);
        // And a base that is a product of powers gives both at once.
        expect(await proves(olorin, {
            variables: vars, conclusion: '((x·y)^m)^n = x^(m·n)·y^(m·n)',
        })).toBe(true);
        expect(await proves(olorin, { variables: vars, conclusion: '(2·x)^n = 2^n·x^n' })).toBe(true);
        // One to any power is one, which the uninterpreted symbol would not have said -- and
        // without which a quotient coming apart would leave a 1^n standing in the way.
        expect(await proves(olorin, { variables: vars, conclusion: '1^n = 1' })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['x≠0'], conclusion: '(1/x)^n = x^(−n)',
        })).toBe(true);
    });

    // With the same conditions as everywhere else, now asked of each factor: nothing for a natural
    // exponent, a nonzero factor where the exponent can go negative, and positive ones where it
    // isn't whole -- two negative factors having a positive product, which is why the product and
    // not the factors is what would otherwise be enough.
    test('and asks of each factor what it asks of any base', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\ny ∈ ℝ\nn ∈ ℕ';
        // A denominator is nonzero whatever the exponent does, as it was when it was written as a
        // division.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['y≠0'], conclusion: '(x/y)^n = x^n/y^n',
        })).toBe(true);
        const nodiv = await algebra(olorin, { variables: vars, conclusion: '(x/y)^n = x^n/y^n' });
        expect(nodiv.proved).toBe(false);
        expect(nodiv.said).toContain('is nonzero');
        // A negative exponent makes every factor a reciprocal.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['x≠0', 'y≠0'], conclusion: '(x·y)^(−n) = x^(−n)·y^(−n)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, conclusion: '(x·y)^(−n) = x^(−n)·y^(−n)',
        })).toBe(false);
        // An exponent that isn't whole needs them positive, one at a time.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['0<x', '0<y'],
            conclusion: '(x·y)^(n+1/2) = x^(n+1/2)·y^(n+1/2)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, conclusion: '(x·y)^(n+1/2) = x^(n+1/2)·y^(n+1/2)',
        })).toBe(false);
    });

    // A power whose exponent the hypotheses settle is that many copies of its base, which the
    // uninterpreted symbol does not say for itself: "x^0" is 1 only because the translation sees
    // the 0 and folds it, and there is no such 0 to see in "x^n" under a hypothesis that n is 0.
    // Which is the base case of an induction over powers, so it is worth having.
    test('is its base multiplied out where the hypotheses settle its exponent', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ';
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n=0'], conclusion: 'x^n = 1',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n=1'], conclusion: 'x^n = x',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n=2'], conclusion: 'x^n = x²',
        })).toBe(true);
        // And it is that inside a power that came apart, as anywhere else.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n=0'], conclusion: 'x^(n+1) = x',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n=2'], conclusion: 'x^(n+1) = x³',
        })).toBe(true);
        // Including where the problem writes no literal power at all, which is the one thing
        // congruence has nothing to work from.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n=2'], conclusion: 'x^n = x·x',
        })).toBe(true);
    });

    // They needn't say it outright, either.  The power is an uninterpreted symbol, so the symbol's
    // value is stated at the small exponents outright and at every other literal power the problem
    // writes, and congruence carries across whatever Z3 can work the exponent out to be -- which
    // is more than reading an equation off the hypotheses would give.
    test('and wherever Z3 can work that exponent out for itself', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ';
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['2·n=4'], conclusion: 'x^n = x²',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n+1=3'], conclusion: 'x^n = x²',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['2·n=m', 'm=4'], conclusion: 'x^n = x²',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n=5'], conclusion: 'x^n = x^5',
        })).toBe(true);
        // And none of it turns on how the other side is written, the small exponents being said
        // about whether or not the problem writes a power at them.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['2·n=4'], conclusion: 'x^n = x·x',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n+1=3'], conclusion: 'x^n = x·x',
        })).toBe(true);
        // Where nothing settles the exponent there is nothing to carry across.
        expect(await proves(olorin, { variables: vars, conclusion: 'x^n = x²' })).toBe(false);
    });

    // Past the small ones the power has to be written somewhere for congruence to have a term, or
    // the exponent said outright for it to be read: an exponent pinned indirectly to a large value
    // with no such power anywhere in the problem is where all of it runs out.
    test('past the exponents it says itself about, one or the other is needed', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\nn ∈ ℕ';
        // Written as a power, so there is a term saying what x^7 is.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['2·n=14'], conclusion: 'x^n = x^7',
        })).toBe(true);
        // Said outright, so the exponent is read off the hypotheses.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['n=7'], conclusion: 'x^n = x·x·x·x·x·x·x',
        })).toBe(true);
        // Neither.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['2·n=14'], conclusion: 'x^n = x·x·x·x·x·x·x',
        })).toBe(false);
    });

    // A negative one is a reciprocal, which is a definition to make and not a fact to state, and
    // there is no making one where these are said.
    test('but not to a negative exponent, which is a definition and not a fact', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nz ∈ ℤ', hypotheses: ['z=−1', 'x≠0'], conclusion: 'x^z = 1/x',
        })).toBe(false);
    });

    // A fractional coefficient is a coefficient like any other, the exponents being a module over
    // ℚ and not just over ℤ: clearing its denominator is taking that root of the base, x^(n/2)
    // being (x^(1/2))^n.  So the root becomes the base, and powers of it are tied back to powers
    // of what it is a root of, without which x^(n/2)·x^(n/2) and x^n would be unrelated terms.
    test('has a fractional coefficient where its base has a root', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\nn ∈ ℕ';
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['0≤x'], conclusion: 'x^(n/2)·x^(n/2) = x^n',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['0≤x'], conclusion: '(x^(1/2))^(2·n) = x^n',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['0≤x'], conclusion: '(x^(1/2))^(n+1) = x^(n/2+1/2)',
        })).toBe(true);
        // An even root asks of its base exactly what a written-out one does, and no more.
        const without = await algebra(olorin, {
            variables: vars, conclusion: 'x^(n/2)·x^(n/2) = x^n',
        });
        expect(without.proved).toBe(false);
        expect(without.said).toContain('is nonnegative');
        // An odd one is total, and asks nothing at all.
        expect(await proves(olorin, {
            variables: vars, conclusion: 'x^(n/3)·x^(n/3)·x^(n/3) = x^n',
        })).toBe(true);
    });

    // A step whose conditions don't hold isn't taken, and the steps around it still are: the base
    // it was going to come apart stays a base of its own.  So a power of a product of roots comes
    // apart at the product, and a root of a product doesn't come apart at all -- and the exponents
    // still multiply out through both.
    test('leaves untaken only the step whose conditions fail', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // The product comes apart, the root of x does not.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\ny ∈ ℝ\nn ∈ ℕ', hypotheses: ['0≤x'],
            conclusion: '(x^(1/2)·y)^n = (x^(1/2))^n·y^n',
        })).toBe(true);
        // And here nothing may be said of u or v apart, u·v being what has the root -- so the
        // product is left alone and the exponents multiplied out over it, which needs only what
        // the root already needed.
        expect(await proves(olorin, {
            variables: 'u ∈ ℝ\nv ∈ ℝ\nn ∈ ℕ', hypotheses: ['u<0', 'v<0'],
            conclusion: '((u·v)^(1/2))^(n+1) = (u·v)^(n/2+1/2)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'u ∈ ℝ\nv ∈ ℝ\nn ∈ ℕ',
            conclusion: '((u·v)^(1/2))^(n+1) = (u·v)^(n/2+1/2)',
        })).toBe(false);
    });

    // An even exponent makes a base nonnegative whatever the base was -- u^(2·k) is ∣u∣^(2·k) --
    // and ∣u∣ is nonnegative outright, so the exponents multiply out over it with nothing asked of
    // the hypotheses at all.  (x^6)^(n+1/2) is ∣x∣^(6·n+3) for every x, where it is x^(6·n+3) only
    // for a nonnegative one.
    test('takes an even power of a base for the absolute value it is', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\nn ∈ ℕ';
        expect(await plusProves(olorin, {
            variables: vars, conclusion: '(x^6)^(n+1/2) = ∣x∣^(6·n+3)',
        })).toBe(true);
        expect(await plusProves(olorin, {
            variables: vars, conclusion: '(x^2)^(n+1/2) = ∣x∣^(2·n+1)',
        })).toBe(true);
        // Which also makes a power of an absolute value the absolute value of the power, without
        // which ∣x∣^(2·n) and (x²)^n would be unrelated symbols.
        expect(await plusProves(olorin, { variables: vars, conclusion: '(x²)^n = ∣x∣^(2·n)' })).toBe(true);
        expect(await plusProves(olorin, { variables: vars, conclusion: '∣x^n∣ = ∣x∣^n' })).toBe(true);
        expect(await plusProves(olorin, { variables: vars, conclusion: '∣x∣^(2·n) = x^(2·n)' })).toBe(true);
        // Dropping the bars is then exactly as true as the base is nonnegative.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['0≤x'], conclusion: '(x^2)^(n+1/2) = x^(2·n+1)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['x<0'], conclusion: '(x^2)^(n+1/2) = x^(2·n+1)',
        })).toBe(false);
        expect(await proves(olorin, {
            variables: vars, conclusion: '(x^2)^(n+1/2) = x^(2·n+1)',
        })).toBe(false);
        // An odd exponent says nothing of the sort, a negative base staying negative under it.
        expect(await plusProves(olorin, {
            variables: vars, conclusion: '(x^3)^(n+1/2) = ∣x∣^(3·n+3/2)',
        })).toBe(false);
    });

    // A base that is itself a power comes into the exponent: (u^e)^M is u^(e·M), so a tower of
    // powers is one power of the base at the bottom of it.  The named small powers are powers
    // like any other here, "(x²)^n" being the tower "(x^2)^n".
    test('takes in the exponents of a base that is a power itself', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ';
        expect(await proves(olorin, { variables: vars, conclusion: 'x^(m·n) = (x^m)^n' })).toBe(true);
        expect(await proves(olorin, { variables: vars, conclusion: '(x^m)^n = (x^n)^m' })).toBe(true);
        expect(await proves(olorin, { variables: vars, conclusion: '((x^m)^n)² = x^(2·m·n)' })).toBe(true);
        expect(await proves(olorin, { variables: vars, conclusion: '(x²)^n = (x^n)²' })).toBe(true);
        // Which is the last of the iterated cases: the exponents multiply, and then the sum they
        // multiply out to comes apart as any other does.
        expect(await proves(olorin, {
            variables: vars, conclusion: '(x^(m+1))^(n+1) = x^(m·n)·x^m·x^n·x',
        })).toBe(true);
    });

    // Both exponents have to be whole numbers for that to hold of every base, and not merely the
    // product of the two: (u^6)^(n+1/2)
    // is u^(6·n)·∣u∣³, which is not u^(6·n+3) for a negative u, though the exponents 6 and n+1/2
    // multiply out to a whole number between them.
    test('but only where both of the exponents are whole numbers', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ';
        expect(await proves(olorin, {
            variables: vars, conclusion: '(x^6)^(n+1/2) = x^(6·n+3)',
        })).toBe(false);
        // Which is not merely unproved but false, the hypotheses here being where it fails.
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['x<0'], conclusion: '(x^6)^(n+1/2) = x^(6·n+3)',
        })).toBe(false);
        // A root of the base is the same thing the other way up: (x^(1/2))^(2·n) is not x^n, the
        // one being ∣x∣^n and the other not.
        expect(await proves(olorin, {
            variables: vars, conclusion: '(x^(1/2))^(2·n) = x^n',
        })).toBe(false);
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nq ∈ ℚ', conclusion: '(x^q)^n = x^(q·n)',
        })).toBe(false);
    });

    // Unless the base is positive, where (u^e)^M is u^(e·M) for every real e and M and nothing
    // need be whole at all.  Whether the hypotheses make it positive is not something the
    // translation can ask -- they have not been translated when it runs -- so the tower is
    // translated as it stands, and what it would have come to is said beside it, conditional on
    // that positivity.  Where the hypotheses give it, the equation is there to be used.
    test('or the base is positive, which asks nothing of the exponents', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const vars = 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ';
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['0<x'], conclusion: '(x^6)^(n+1/2) = x^(6·n+3)',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['0<x'], conclusion: '(x^(1/2))^(2·n) = x^n',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: vars, hypotheses: ['0<x'], conclusion: '(x²)^(n+1/2) = x^(2·n+1)',
        })).toBe(true);
        // Including an exponent that is no product of powers at all: the tower is then the one
        // power of the base that it is, with the exponents multiplied out as arithmetic.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nq ∈ ℚ', hypotheses: ['0<x'], conclusion: '(x^q)^n = x^(q·n)',
        })).toBe(true);
        // Positive, not merely nonnegative: a zero base has no negative powers to speak of, and a
        // rational exponent may well be one.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nq ∈ ℚ', hypotheses: ['0≤x'], conclusion: '(x^q)^n = x^(q·n)',
        })).toBe(false);
    });

    // And nothing is refused for want of that positivity that wasn't refused before it: what the
    // tower would come to is a fact to be had where it holds, never a condition to be met.
    test('and a tower nothing is known about is the term it always was', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nq ∈ ℚ', hypotheses: ['(x^q)^n = 5'],
            conclusion: '(x^q)^n+1 = 6',
        })).toBe(true);
    });

    // And where an inner exponent can be negative, the base has to be nonzero: two negative
    // exponents cancel in the product, which would otherwise lose what each of them needed.
    test('and asks for a nonzero base where an inner exponent can be negative', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ', hypotheses: ['x≠0'],
            conclusion: '(x^(−m))^(−n) = x^(m·n)',
        })).toBe(true);
    });

    test('and refuses it where the hypotheses leave the base able to be zero', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const without = await algebra(olorin, {
            variables: 'x ∈ ℝ\nm ∈ ℕ\nn ∈ ℕ', conclusion: '(x^(−m))^(−n) = x^(m·n)',
        });
        expect(without.proved).toBe(false);
        expect(without.said).toContain('is nonzero');
    });

    // Where it stops: a monomial is a term the base is raised to, and a base is taken apart only
    // where it is a power itself, so nothing here relates x^(m·n) to anything else's n-th power.
    test('is only taken apart into powers of the base', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ', conclusion: 'x^(n·m) = (x·x)^(n·m)',
        })).toBe(false);
        // Equal exponents do give equal powers, though, as they did before: that much is
        // congruence, which the uninterpreted symbol has always had.
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\nn ∈ ℕ\nm ∈ ℕ', hypotheses: ['n=m'], conclusion: 'x^n = x^m',
        })).toBe(true);
    });
});
