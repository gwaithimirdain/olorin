// Absolute value, written ∣x∣, and the smaller and larger of two numbers, written min(x,y) and
// max(x,y).  All three make sense in every one of the number systems, since all of them are
// ordered, and all three are definable in a real closed field by a case split: each is handed to
// Z3 as a conditional between two polynomials.
//
// Z3 decides such a conditional on its own, and the "alg+" block lets it -- so alg+ proves things
// about ∣ ∣, min and max with no help.  The plain "alg" block does not: it first requires the
// hypotheses wired into it to settle which way each of those comparisons goes, so that the
// conditional simplifies away and the student has done the case split themselves.
//
// ∣x∣ borrows the ∣ of divisibility.  An infix notation that is an initial segment of an outfix one
// is allowed to be ambiguous with it, and the parse resolves in favour of the infix -- the reading
// that couldn't otherwise be recovered, since the outfix one can always be parenthesized.  So "a ∣
// b" still divides and "∣a∣" is still a size, including when they are written next to each other.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// The types Olorin ends up giving the statements on each wire, whitespace squashed.
const wireLabels = (page) => page.evaluate(() =>
    Array.from(document.querySelectorAll('.connLabel')).map((e) => (e.innerText || '').replace(/\s+/g, '')));

// State a level and prove it with a single algebra block -- "algplus" unless told otherwise --
// fed by every hypothesis.
async function provesWith(rule, olorin, { variables = 'x ∈ ℝ\ny ∈ ℝ', hypotheses = [], conclusion }) {
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
    return olorin.isComplete();
}

const proves = (olorin, level) => provesWith('algplus', olorin, level);
const plainProves = (olorin, level) => provesWith('alg', olorin, level);

// State something and wire it straight through, to read back the statement Olorin understood.
async function readsAs(olorin, page, statement, variables = 'a ∈ ℤ\nb ∈ ℤ') {
    await olorin.buildCustom({
        parameters: '', variables, hypotheses: statement, conclusion: statement,
    });
    const nodes = await olorin.nodes();
    await olorin.connect({ vertex: nodes.find((n) => n.rule === 'hypothesis').id, sort: 'output' },
                         { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
    await olorin.waitForTypecheck();
    return (await wireLabels(page))[0];
}

test.describe('Absolute value, given to the alg+ block', () => {
    test('is nonnegative and multiplicative, and obeys the triangle inequality', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, { conclusion: '0 ≤ ∣x∣' })).toBe(true);
        expect(await proves(olorin, { conclusion: '∣x·y∣ = ∣x∣·∣y∣' })).toBe(true);
        expect(await proves(olorin, { conclusion: '∣x+y∣ ≤ ∣x∣+∣y∣' })).toBe(true);
        expect(await proves(olorin, { conclusion: '∣x∣·∣x∣ = x·x' })).toBe(true);
    });

    test('is x exactly when x is nonnegative', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, { conclusion: '∣x∣ = x' })).toBe(false);
        expect(await proves(olorin, { hypotheses: ['0≤x'], conclusion: '∣x∣ = x' })).toBe(true);
        expect(await proves(olorin, { hypotheses: ['∣x∣=0'], conclusion: 'x=0' })).toBe(true);
    });

    test('agrees with the square root of the square', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, { conclusion: '∣x∣ = √(x²)' })).toBe(true);
    });

    test('makes sense in every number system, not just the reals', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℤ\ny ∈ ℤ', conclusion: '∣x+y∣ ≤ ∣x∣+∣y∣',
        })).toBe(true);
        expect(await proves(olorin, {
            variables: 'x ∈ 𝕊\ny ∈ 𝕊', conclusion: '∣x·y∣ = ∣x∣·∣y∣',
        })).toBe(true);
    });
});

test.describe('min and max, given to the alg+ block', () => {
    test('are the smaller and the larger', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, { conclusion: 'min(x,y) ≤ x' })).toBe(true);
        expect(await proves(olorin, { conclusion: 'x ≤ max(x,y)' })).toBe(true);
        expect(await proves(olorin, { conclusion: 'min(x,y)+max(x,y) = x+y' })).toBe(true);
        expect(await proves(olorin, { conclusion: 'max(x,min(x,y)) = x' })).toBe(true);
        expect(await proves(olorin, { conclusion: 'max(x,y) = (x+y+∣x−y∣)/2' })).toBe(true);
    });

    test('and are not the same thing as each other', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, { conclusion: 'min(x,y) = max(x,y)' })).toBe(false);
    });

    test('nest, and take any expression', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await proves(olorin, {
            variables: 'x ∈ ℝ\ny ∈ ℝ\nz ∈ ℝ',
            conclusion: 'min(x,min(y,z)) = min(min(x,y),z)',
        })).toBe(true);
        expect(await proves(olorin, { conclusion: 'min(∣x∣,∣y∣) = ∣x∣' , hypotheses: ['∣x∣≤∣y∣'] })).toBe(true);
    });
});

// The plain block asks for the case split first.  The messages it gives when it doesn't get one
// are Explain.Oracle.undecided_sign and undecided_order in bin/explain.ml.
const complaint = async (olorin) =>
    (await olorin.diagnostics()).map((d) => d.explanation).join(' ');

test.describe('The plain alg block', () => {
    test('refuses an absolute value whose sign nothing settles', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // Something alg+ proves outright, and with no hypotheses at all.
        expect(await plainProves(olorin, { conclusion: '0 ≤ ∣x∣' })).toBe(false);
        expect(await complaint(olorin)).toContain('know which way that goes');
        // A hypothesis that says something about x, but not which way it goes, is no better.
        expect(await plainProves(olorin, { hypotheses: ['x·x = 4'], conclusion: '0 ≤ ∣x∣' })).toBe(false);
    });

    test('takes an absolute value once a hypothesis settles the sign, either way', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await plainProves(olorin, { hypotheses: ['0≤x'], conclusion: '∣x∣ = x' })).toBe(true);
        expect(await plainProves(olorin, { hypotheses: ['x≤0'], conclusion: '∣x∣ = −x' })).toBe(true);
        // The two branches of the "≤∨>" block are "x ≤ 0" and "0 < x", so each of those has to be
        // enough on its own: that block is how a student is meant to do the split.
        expect(await plainProves(olorin, { hypotheses: ['0<x'], conclusion: '∣x∣ = x' })).toBe(true);
        // And a hypothesis that forces the sign without saying so does just as well.
        expect(await plainProves(olorin, { hypotheses: ['x = y·y'], conclusion: '∣x∣ = x' })).toBe(true);
    });

    test('refuses a min or max whose order nothing settles, and takes one that is settled', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await plainProves(olorin, { conclusion: 'min(x,y) ≤ x' })).toBe(false);
        expect(await complaint(olorin)).toContain('which of those two numbers is the smaller');
        expect(await plainProves(olorin, { hypotheses: ['x≤y'], conclusion: 'min(x,y) = x' })).toBe(true);
        expect(await plainProves(olorin, { hypotheses: ['y<x'], conclusion: 'min(x,y) = y' })).toBe(true);
        expect(await plainProves(olorin, { hypotheses: ['x≤y'], conclusion: 'max(x,y) = y' })).toBe(true);
    });

    test('asks separately about every case in the statement', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // Both absolute values are settled, and then min's own comparison still isn't.
        expect(await plainProves(olorin, {
            hypotheses: ['0≤x', '0≤y'], conclusion: 'min(∣x∣,∣y∣) ≤ x',
        })).toBe(false);
        expect(await complaint(olorin)).toContain('which of those two numbers is the smaller');
        // Settling the absolute values settles the comparison between them too.
        expect(await plainProves(olorin, {
            hypotheses: ['0≤x', '0≤y', 'x≤y'], conclusion: 'min(∣x∣,∣y∣) = x',
        })).toBe(true);
        // The other way round: the order of the two is given, but not the sign of either.
        expect(await plainProves(olorin, {
            hypotheses: ['∣x∣≤∣y∣'], conclusion: 'min(∣x∣,∣y∣) = ∣x∣',
        })).toBe(false);
        expect(await complaint(olorin)).toContain('know which way that goes');
    });

    test('is otherwise the block it always was', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // A statement with no case split in it is proved exactly as before.
        expect(await plainProves(olorin, { conclusion: '(x+y)·(x−y) = x·x−y·y' })).toBe(true);
        expect(await plainProves(olorin, { hypotheses: ['x+y=1'], conclusion: 'x = 1−y' })).toBe(true);
    });
});

test.describe('The ∣ of absolute value and the ∣ of divisibility', () => {
    // Divisibility is an ∃ under the hood, so a statement that reads back as one was parsed as
    // divisibility; one that reads back with bars around it was parsed as an absolute value.
    test('coexist, and each is read where it belongs', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await readsAs(olorin, page, 'a ∣ b')).toContain('∃k∈ℤ');
        expect(await readsAs(olorin, page, '∣a∣ = 1')).toBe('∣a∣=1');
        // And where both meanings meet, on either side of the divides.
        expect(await readsAs(olorin, page, 'a ∣ ∣b∣')).toBe('∃k∈ℤ,(∣b∣=k·a)');
        expect(await readsAs(olorin, page, '∣a∣ ∣ b')).toBe('∃k∈ℤ,(b=k·∣a∣)');
        expect(await readsAs(olorin, page, '∣a∣ ∣ ∣b∣')).toBe('∃k∈ℤ,(∣b∣=k·∣a∣)');
    });

    test('and the algebra block still refuses a divisibility, as it always did', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'a ∈ ℤ\nb ∈ ℤ', hypotheses: '', conclusion: '2 ∣ 4',
        });
        const nodes = await olorin.nodes();
        const alg = await olorin.dragRule('algebra', 600, 200);
        await olorin.connect({ vertex: alg, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(false);
        expect((await olorin.diagnostics()).map((d) => d.explanation).join(' '))
            .toContain('only proves equations and inequalities');
    });
});

test.describe('All three', () => {
    test('print back the way they were written', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const R = 'x ∈ ℝ\ny ∈ ℝ';
        expect(await readsAs(olorin, page, '∣x+y∣ = 1', R)).toBe('∣x+y∣=1');
        expect(await readsAs(olorin, page, 'min(x,y) = 1', R)).toBe('min(x,y)=1');
        expect(await readsAs(olorin, page, 'max(x,y) = 1', R)).toBe('max(x,y)=1');
        expect(await readsAs(olorin, page, 'min(∣x∣,y) = 1', R)).toBe('min(∣x∣,y)=1');
    });

    test('have a way to be typed: the ordinary bar key becomes ∣', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.openChooser();
        await page.click('#customLevel');
        const typed = async (text) => {
            await page.fill('#conclusion', '');
            await page.locator('#conclusion').pressSequentially(text);
            return page.inputValue('#conclusion');
        };
        expect(await typed('|x|')).toBe('∣x∣');
        expect(await typed('|a| | |b|')).toBe('∣a∣ ∣ ∣b∣');
        expect(await typed('min(|x|,|y|)')).toBe('min(∣x∣,∣y∣)');
        // The bar is also the first character of ↦, whose rule has to keep getting there first --
        // and to recognize what is left after the bar and the hyphen have been converted.
        expect(await typed('x|->y')).toBe('x↦y');
        // The palette button and the \mid shortcut still work as well.
        await expect(page.locator('#conclPalette .unicode-button', { hasText: '∣' })).toHaveCount(1);
        await page.fill('#conclusion', '');
        await page.click('#conclPalette .unicode-button:has-text("∣")');
        await page.locator('#conclusion').pressSequentially('x');
        await page.locator('#conclusion').pressSequentially('\\mid ');
        expect(await page.inputValue('#conclusion')).toBe('∣x∣');
    });
});
