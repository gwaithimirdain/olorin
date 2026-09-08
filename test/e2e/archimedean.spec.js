// The Archimedean property, as the "Arch" block.
//
// It is a "User" rule (bin/rules.ml) applying the axiom ℝ.archimedean, which lives in the
// secondary startup code because it compares a real to a natural number and so needs ℕ≤ℝ.  Its
// conclusion is an ∃, which the block destructs itself: instead of a single output carrying
// ∃n∈ℕ,(x<n), it hands out the natural number on a value port and the proof that x is below it on
// another, exactly as ∃-elimination does.
//
// Unlike "=∨≠" and "≤∨>", it doesn't follow its input into a number system: the one axiom is about
// ℝ.  A rational or integer input is coerced into ℝ and the block still applies, but then what it
// proves is stated in ℝ, so a goal written about ℚ isn't what comes out of it.

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
