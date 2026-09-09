// The blocks that assert how one number system sits inside another: "Arch", "ℤ→ℕ", "frac" and
// "ℝ<ω".
//
// Each is a "User" rule (bin/rules.ml) applying one axiom, and all of those axioms live in the
// secondary startup code, since each one relates two number systems and so needs the subtyping
// between them.  Arch, ℤ→ℕ and frac conclude an ∃, which their block takes apart itself: instead
// of a single output carrying ∃n∈ℕ,…, each hands out the number on a value port and the statement
// about it on another, exactly as ∃-elimination does.  frac's axiom concludes two nested ∃s and
// then a ∧ of three statements, and its block takes all of that apart: it binds two variables
// rather than one -- the only block that does -- and hands out each half of the ∧ on a port of its
// own, so nothing after it has to take anything apart.  ℝ<ω concludes a relation, so it has the
// ordinary single output.
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

    // The surreals are exactly the number system where the Archimedean property fails, and the
    // axiom is stated about ℝ, so there is no coercion to carry an 𝕊 into the block.
    test('does not apply to a surreal', async ({ page }) => {
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

// Drop a block that binds several variables, naming them in the dialogs it pops one after another.
async function dragMultiBinder(olorin, rule, x, y, names) {
    const id = await olorin.dragRule(rule, x, y);
    for (const name of names) {
        await olorin.page.waitForSelector('#variableBG', { state: 'visible' });
        await olorin.page.fill('#newvar', name);
        await olorin.page.click('#submitVariable');
    }
    await olorin.dismissHints();
    return id;
}

// What frac says about the two numbers it hands out: the denominator is at least 1, it makes x the
// fraction a/b, and the two have no common factor but 1.  Divisibility is an ∃ under the hood and
// prints as one, so this is written the way a player would write it and read back the long way.
const LOWEST_TERMS = (a, b) => `((${b}≥1)∧((x=${a}/${b})∧(∀c∈ℕ,(((c∣${a})∧(c∣${b}))⇒(c=1)))))`;

// State ∃a∈ℤ,∃b∈ℤ,(that), over a variable x of the given set, and prove it by feeding x to a frac
// block and putting what comes out of it back together: the three statements into two ∧s, and the
// two numbers into two ∃s.  Nothing takes anything apart here -- the block did all of that.
async function fracProves(olorin, set) {
    await olorin.buildCustom({
        parameters: '',
        variables: `x ∈ ${set}`,
        hypotheses: '',
        conclusion: `∃a∈ℤ,∃b∈ℤ,${LOWEST_TERMS('a', 'b')}`,
    });
    const frac = await dragMultiBinder(olorin, 'frac', 300, 100, ['p', 'q']);
    const andInner = await olorin.dragRule('andI', 500, 250);
    const andOuter = await olorin.dragRule('andI', 650, 350);
    const inner = await olorin.dragRule('exI', 800, 450);
    const outer = await olorin.dragRule('exI', 950, 550);
    const nodes = await olorin.nodes();
    const varx = nodes.find((v) => v.rule === 'variable' && v.name === 'x').id;
    await olorin.connect({ vertex: varx, sort: 'output' }, { vertex: frac, sort: 'input', label: 'x' });
    // (x=a/b) ∧ (∀c∈ℕ,…), and then (b≥1) ∧ that.
    await olorin.connect({ vertex: frac, sort: 'output', label: 'fraction' },
                         { vertex: andInner, sort: 'input', label: 'fst' });
    await olorin.connect({ vertex: frac, sort: 'output', label: 'lowest' },
                         { vertex: andInner, sort: 'input', label: 'snd' });
    await olorin.connect({ vertex: frac, sort: 'output', label: 'atleastone' },
                         { vertex: andOuter, sort: 'input', label: 'fst' });
    await olorin.connect({ vertex: andInner, sort: 'output' },
                         { vertex: andOuter, sort: 'input', label: 'snd' });
    // The inner ∃ is over the denominator, the outer one over the numerator.
    await olorin.connect({ vertex: frac, sort: 'output', label: 'denominator' },
                         { vertex: inner, sort: 'input', label: 'element' });
    await olorin.connect({ vertex: andOuter, sort: 'output' },
                         { vertex: inner, sort: 'input', label: 'property' });
    await olorin.connect({ vertex: frac, sort: 'output', label: 'numerator' },
                         { vertex: outer, sort: 'input', label: 'element' });
    await olorin.connect({ vertex: inner, sort: 'output' },
                         { vertex: outer, sort: 'input', label: 'property' });
    await olorin.connect({ vertex: outer, sort: 'output' },
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

    test('asks for both names in turn, and binds them both', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℚ', hypotheses: '', conclusion: '⊤',
        });
        const id = await olorin.dragRule('frac', 400, 150);
        // The first dialog asks for the numerator, and stays open for the denominator.
        await expect(page.locator('#variableBG')).toBeVisible();
        expect(await page.textContent('#variableHeading')).toContain('numerator');
        await page.fill('#newvar', 'p');
        await page.click('#submitVariable');
        await expect(page.locator('#variableBG')).toBeVisible();
        expect(await page.textContent('#variableHeading')).toContain('denominator');
        // The name just given is taken, so the second one can't repeat it.
        expect(await page.textContent('#variableList')).toContain('p');
        await page.fill('#newvar', 'q');
        await page.click('#submitVariable');

        expect(await page.isVisible('#variableBG')).toBe(false);
        expect((await olorin.nodes()).find((n) => n.id === id).names).toEqual(['p', 'q']);
        expect(await olorin.varnames()).toEqual(expect.arrayContaining(['p', 'q']));

        // And deleting the block gives both names back.
        await olorin.deleteNode(id);
        const left = await olorin.varnames();
        expect(left).not.toContain('p');
        expect(left).not.toContain('q');
    });

    test('renames both, one dialog after the other', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℚ', hypotheses: '', conclusion: '⊤',
        });
        const id = await dragMultiBinder(olorin, 'frac', 400, 150, ['p', 'q']);
        await page.dblclick('#' + id);
        // Each is pre-filled with the name it binds now, which is therefore not taken.
        await expect(page.locator('#variableBG')).toBeVisible();
        expect(await page.inputValue('#newvar')).toBe('p');
        expect(await page.textContent('#variableList')).not.toContain('p');
        await page.fill('#newvar', 'u');
        await page.click('#submitVariable');
        expect(await page.inputValue('#newvar')).toBe('q');
        await page.fill('#newvar', 'v');
        await page.click('#submitVariable');

        expect((await olorin.nodes()).find((n) => n.id === id).names).toEqual(['u', 'v']);
        const names = await olorin.varnames();
        expect(names).toEqual(expect.arrayContaining(['u', 'v']));
        expect(names).not.toContain('p');
        expect(names).not.toContain('q');
    });

    // Cancelling any of the dialogs a new block pops takes the block away, as cancelling the one
    // dialog always has -- and the name already given goes back into circulation with it.
    test('is taken away, names and all, by cancelling the second dialog', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℚ', hypotheses: '', conclusion: '⊤',
        });
        await olorin.dragRule('frac', 400, 150);
        await page.fill('#newvar', 'p');
        await page.click('#submitVariable');
        await expect(page.locator('#variableBG')).toBeVisible();
        await page.click('#cancelVariable');

        expect((await olorin.nodes()).some((n) => n.rule === 'frac')).toBe(false);
        expect(await olorin.varnames()).not.toContain('p');
    });

    // Both names have to survive a save: a block that binds two writes them as a list, where one
    // that binds a single variable has always written it on its own.
    test('keeps both names through an export and import', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℚ', hypotheses: '', conclusion: '⊤',
        });
        const frac = await dragMultiBinder(olorin, 'frac', 400, 150, ['p', 'q']);
        const varx = (await olorin.nodes()).find((v) => v.rule === 'variable' && v.name === 'x').id;
        await olorin.connect({ vertex: varx, sort: 'output' },
                             { vertex: frac, sort: 'input', label: 'x' });
        const before = await olorin.structuralState();
        const json = await olorin.exportText();
        expect(JSON.parse(json).nodes.find((n) => n.rule === 'frac').names).toEqual(['p', 'q']);

        await olorin.clear();
        await olorin.importText(json);
        expect(await olorin.structuralState()).toEqual(before);
        expect(await olorin.varnames()).toEqual(expect.arrayContaining(['p', 'q']));
    });

    test('labels its outputs with both numbers and each statement about them', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℚ', hypotheses: '', conclusion: '⊤',
        });
        const frac = await dragMultiBinder(olorin, 'frac', 400, 150, ['p', 'q']);
        const varx = (await olorin.nodes()).find((v) => v.rule === 'variable' && v.name === 'x').id;
        await olorin.connect({ vertex: varx, sort: 'output' },
                             { vertex: frac, sort: 'input', label: 'x' });
        await olorin.waitForTypecheck();
        const labels = await portLabels(olorin);
        // Five ports: the two numbers, and each half of the ∧ separately -- no conjunction is left
        // on any of them.  Coprimality reads back with divisibility spelled out as the ∃ it is.
        expect(labels).toEqual(expect.arrayContaining(['p ∈ ℤ', 'q ∈ ℤ', '1≤q', 'x=p/q']));
        expect(labels.join(' ')).toContain('∀c∈ℕ,');
        expect(labels.join(' ')).not.toContain('∧((x=p/q)');
    });

    // Each of the three statements comes out on a wire of its own, so a proof that needs just one
    // of them takes it straight from the block -- where before that took an ∧-elimination too.
    test('hands out one half of its ∧ without the others', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℚ', hypotheses: '', conclusion: '∃b∈ℤ,(b≥1)',
        });
        const frac = await dragMultiBinder(olorin, 'frac', 400, 150, ['p', 'q']);
        const intro = await olorin.dragRule('exI', 700, 300);
        const nodes = await olorin.nodes();
        const varx = nodes.find((v) => v.rule === 'variable' && v.name === 'x').id;
        await olorin.connect({ vertex: varx, sort: 'output' },
                             { vertex: frac, sort: 'input', label: 'x' });
        await olorin.connect({ vertex: frac, sort: 'output', label: 'denominator' },
                             { vertex: intro, sort: 'input', label: 'element' });
        await olorin.connect({ vertex: frac, sort: 'output', label: 'atleastone' },
                             { vertex: intro, sort: 'input', label: 'property' });
        await olorin.connect({ vertex: intro, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
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

    // ω is a surreal, so what the block proves is a statement about 𝕊 -- but its input is a real,
    // and a surreal has nowhere to be coerced to.
    test('does not apply to a surreal', async ({ page }) => {
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
