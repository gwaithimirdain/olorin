// The blocks that assert how one number system sits inside another: "Arch", "ℤ→ℕ" and "ℝ<ω".
//
// Each is a "User" rule (bin/rules.ml) applying one axiom, and all of those axioms live in the
// secondary startup code, since each one relates two number systems and so needs the subtyping
// between them.  Arch and ℤ→ℕ conclude an ∃, which their block destructs itself: instead of a
// single output carrying ∃n∈ℕ,…, each hands out the natural number on a value port and the
// statement about it on another, exactly as ∃-elimination does.  ℝ<ω concludes a relation, so it
// has the ordinary single output.
//
// Unlike "=∨≠" and "≤∨>", none of them follows its input into a number system: each axiom is about
// one.  A rational or integer input to Arch is coerced into ℝ and the block still applies, but
// then what it proves is stated in ℝ, so a goal written about ℚ isn't what comes out of it.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// Drop a rule that binds a variable, naming it in the dialog it pops.
async function dragBinder(olorin, rule, x, y, name) {
    const id = await olorin.dragRule(rule, x, y);
    await olorin.page.waitForSelector('#variableBG', { state: 'visible' });
    await olorin.page.fill('#newvar', name);
    await olorin.page.click('#submitVariable');
    await olorin.dismissHints();
    return id;
}

// The type labels currently shown on unconnected output ports.
function portLabels(olorin) {
    return olorin.page.evaluate(() => Array.from(document.querySelectorAll(
        '#canvas .upperOutputLabel, #canvas .middleOutputLabel, #canvas .lowerOutputLabel'))
        .map((e) => e.innerText));
}

// State ∃n∈ℕ,(x<n) over a variable x of the given set, prove it by feeding x to an Arch block and
// passing the block's two outputs straight to ∃-introduction, and report whether Olorin accepts it.
async function archProves(olorin, set) {
    await olorin.buildCustom({
        parameters: '',
        variables: `x ∈ ${set}`,
        hypotheses: '',
        conclusion: '∃n∈ℕ,(x<n)',
    });
    const arch = await dragBinder(olorin, 'arch', 400, 150, 'm');
    const intro = await olorin.dragRule('exI', 650, 350);
    const nodes = await olorin.nodes();
    const varx = nodes.find((v) => v.rule === 'variable' && v.name === 'x').id;
    const concl = nodes.find((n) => n.rule === 'conclusion').id;
    await olorin.connect({ vertex: varx, sort: 'output' }, { vertex: arch, sort: 'input', label: 'x' });
    for (const port of ['element', 'property']) {
        await olorin.connect({ vertex: arch, sort: 'output', label: port },
                             { vertex: intro, sort: 'input', label: port });
    }
    await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: concl, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

test.describe('The "Arch" block', () => {
    test('produces a natural number above a real one', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await archProves(olorin, 'ℝ')).toBe(true);
    });

    // The superreals are exactly the number system where the Archimedean property fails, and the
    // axiom is stated about ℝ, so there is no coercion to carry an 𝕊 into the block.
    test('does not apply to a superreal', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await archProves(olorin, '𝕊')).toBe(false);
    });

    test('labels its outputs with the number it binds and the inequality it proves',
        async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.buildCustom({
                parameters: '',
                variables: 'x ∈ ℝ',
                hypotheses: '',
                conclusion: '∃n∈ℕ,(x<n)',
            });
            const arch = await dragBinder(olorin, 'arch', 400, 150, 'm');
            const varx = (await olorin.nodes()).find((v) => v.rule === 'variable' && v.name === 'x').id;
            await olorin.connect({ vertex: varx, sort: 'output' },
                                 { vertex: arch, sort: 'input', label: 'x' });
            await olorin.waitForTypecheck();
            expect(await portLabels(olorin)).toEqual(
                expect.arrayContaining(['m ∈ ℕ', 'x<m']));
        });
});

// State ∃n∈ℕ,(x=n) over an integer x that a hypothesis says is nonnegative, prove it by feeding
// both to a ℤ→ℕ block and passing that block's two outputs to ∃-introduction, and report whether
// Olorin accepts it.  With `nonneg` false the hypothesis is left unwired, so the block is missing
// the very thing that makes its axiom apply.
async function ztonProves(olorin, { set = 'ℤ', hypothesis = 'x≥0', nonneg = true } = {}) {
    await olorin.buildCustom({
        parameters: '',
        variables: `x ∈ ${set}`,
        hypotheses: hypothesis,
        conclusion: '∃n∈ℕ,(x=n)',
    });
    const zton = await dragBinder(olorin, 'zton', 400, 150, 'm');
    const intro = await olorin.dragRule('exI', 650, 350);
    const nodes = await olorin.nodes();
    const varx = nodes.find((v) => v.rule === 'variable' && v.name === 'x').id;
    const hyp = nodes.find((n) => n.rule === 'hypothesis').id;
    const concl = nodes.find((n) => n.rule === 'conclusion').id;
    await olorin.connect({ vertex: varx, sort: 'output' }, { vertex: zton, sort: 'input', label: 'x' });
    if (nonneg) {
        await olorin.connect({ vertex: hyp, sort: 'output' },
                             { vertex: zton, sort: 'input', label: 'nonneg' });
    }
    for (const port of ['element', 'property']) {
        await olorin.connect({ vertex: zton, sort: 'output', label: port },
                             { vertex: intro, sort: 'input', label: port });
    }
    await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: concl, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

test.describe('The "ℤ→ℕ" block', () => {
    test('turns a nonnegative integer into the natural number it is equal to', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await ztonProves(olorin)).toBe(true);
    });

    // The proof that x is nonnegative is an input, not something the block assumes: without it the
    // proof is unfinished, exactly as any block with an empty port is.
    test('needs the proof that its input is nonnegative', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await ztonProves(olorin, { nonneg: false })).toBe(false);
    });

    // The hypothesis has to say the input is nonnegative, not something else about it.
    test('does not take just any statement on that port', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await ztonProves(olorin, { hypothesis: 'x≤0' })).toBe(false);
    });

    test('labels its outputs with the number it binds and the equation it proves',
        async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.buildCustom({
                parameters: '', variables: 'x ∈ ℤ', hypotheses: 'x≥0', conclusion: '∃n∈ℕ,(x=n)',
            });
            const zton = await dragBinder(olorin, 'zton', 400, 150, 'm');
            const nodes = await olorin.nodes();
            const varx = nodes.find((v) => v.rule === 'variable' && v.name === 'x').id;
            await olorin.connect({ vertex: varx, sort: 'output' },
                                 { vertex: zton, sort: 'input', label: 'x' });
            await olorin.connect({ vertex: nodes.find((n) => n.rule === 'hypothesis').id, sort: 'output' },
                                 { vertex: zton, sort: 'input', label: 'nonneg' });
            await olorin.waitForTypecheck();
            expect(await portLabels(olorin)).toEqual(
                expect.arrayContaining(['m ∈ ℕ', 'x=m']));
        });
});

// What frac says about the numerator it hands out: there is a denominator b of at least 1 making x
// the fraction a/b, with no common factor of the two but 1.  Divisibility is an ∃ under the hood
// and prints as one, so this is written the way a player would write it and read back the long way.
const LOWEST_TERMS = (a) => `∃b∈ℤ,((b≥1)∧((x=${a}/b)∧(∀c∈ℕ,(((c∣${a})∧(c∣b))⇒(c=1)))))`;

// State ∃a∈ℤ,(that), over a variable x of the given set, and prove it by feeding x to a frac block
// and passing its two outputs straight to ∃-introduction.  The block gives out the numerator and
// the ∃ over the denominator, so this is the whole proof: the player only has to name a.
async function fracProves(olorin, set) {
    await olorin.buildCustom({
        parameters: '',
        variables: `x ∈ ${set}`,
        hypotheses: '',
        conclusion: `∃a∈ℤ,${LOWEST_TERMS('a')}`,
    });
    const frac = await dragBinder(olorin, 'frac', 400, 150, 'p');
    const intro = await olorin.dragRule('exI', 650, 350);
    const nodes = await olorin.nodes();
    const varx = nodes.find((v) => v.rule === 'variable' && v.name === 'x').id;
    await olorin.connect({ vertex: varx, sort: 'output' }, { vertex: frac, sort: 'input', label: 'x' });
    for (const port of ['element', 'property']) {
        await olorin.connect({ vertex: frac, sort: 'output', label: port },
                             { vertex: intro, sort: 'input', label: port });
    }
    await olorin.connect({ vertex: intro, sort: 'output' },
                         { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

test.describe('The "frac" block', () => {
    test('writes a rational as a fraction in lowest terms', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await fracProves(olorin, 'ℚ')).toBe(true);
    });

    // The axiom is about ℚ, and a real has nowhere to be coerced to.
    test('does not apply to a real number', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await fracProves(olorin, 'ℝ')).toBe(false);
    });

    // The block binds one variable, the numerator; the denominator is inside the ∃ it hands out,
    // and the player names it with an ∃-elimination of their own.  Here that yields b≥1.
    test('leaves the denominator to an ∃-elimination, which names it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℚ', hypotheses: '', conclusion: '∃b∈ℤ,(b≥1)',
        });
        const frac = await dragBinder(olorin, 'frac', 300, 100, 'p');
        const elim = await dragBinder(olorin, 'exE', 500, 200, 'q');
        const and = await olorin.dragRule('andE', 700, 300);
        const intro = await olorin.dragRule('exI', 900, 400);
        const nodes = await olorin.nodes();
        const varx = nodes.find((v) => v.rule === 'variable' && v.name === 'x').id;
        await olorin.connect({ vertex: varx, sort: 'output' }, { vertex: frac, sort: 'input', label: 'x' });
        await olorin.connect({ vertex: frac, sort: 'output', label: 'property' },
                             { vertex: elim, sort: 'input' });
        await olorin.connect({ vertex: elim, sort: 'output', label: 'property' },
                             { vertex: and, sort: 'input' });
        await olorin.connect({ vertex: elim, sort: 'output', label: 'element' },
                             { vertex: intro, sort: 'input', label: 'element' });
        await olorin.connect({ vertex: and, sort: 'output', label: 'fst' },
                             { vertex: intro, sort: 'input', label: 'property' });
        await olorin.connect({ vertex: intro, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
    });

    test('labels its outputs with the numerator and what holds of it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℚ', hypotheses: '', conclusion: '⊤',
        });
        const frac = await dragBinder(olorin, 'frac', 400, 150, 'p');
        const varx = (await olorin.nodes()).find((v) => v.rule === 'variable' && v.name === 'x').id;
        await olorin.connect({ vertex: varx, sort: 'output' },
                             { vertex: frac, sort: 'input', label: 'x' });
        await olorin.waitForTypecheck();
        const labels = await portLabels(olorin);
        expect(labels).toEqual(expect.arrayContaining(['p ∈ ℤ']));
        // The statement about it, read back with divisibility spelled out as the ∃ it is.
        expect(labels.join(' ')).toContain('∃b∈ℤ,((1≤b)∧((x=p/b)∧');
    });
});

// State the given conclusion about a variable x of the given set, prove it with a single ℝ<ω block
// fed by x, and report whether Olorin accepts it.
async function omegaProves(olorin, { set = 'ℝ', conclusion = 'x<ω' } = {}) {
    await olorin.buildCustom({ parameters: '', variables: `x ∈ ${set}`, hypotheses: '', conclusion });
    const om = await olorin.dragRule('omega', 400, 200);
    const nodes = await olorin.nodes();
    const varx = nodes.find((v) => v.rule === 'variable' && v.name === 'x').id;
    await olorin.connect({ vertex: varx, sort: 'output' }, { vertex: om, sort: 'input', label: 'x' });
    await olorin.connect({ vertex: om, sort: 'output' },
                         { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

test.describe('The "ℝ<ω" block', () => {
    test('puts a real number below ω', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await omegaProves(olorin)).toBe(true);
    });

    // ω is a superreal, so what the block proves is a statement about 𝕊 -- but its input is a real,
    // and a superreal has nowhere to be coerced to.
    test('does not apply to a superreal', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await omegaProves(olorin, { set: '𝕊' })).toBe(false);
    });

    test('proves that x is below ω, not that it is above it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await omegaProves(olorin, { conclusion: 'ω<x' })).toBe(false);
    });
});
