// The "natInd" block: strong induction on the natural numbers.  It is a "User" rule
// (bin/rules.ml) applying the axiom ℕ.induction, whose first argument is the predicate P of the
// goal ∀n∈ℕ,P(n) -- the axiom takes it implicitly from the goal, as the second argument of the
// "forall" that goal is an application of -- and whose step is a bracket on the side of the block,
// binding a natural number n on a value port and assuming the inductive hypothesis ∀k∈[n],P(k).

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

// The type labels currently shown on unconnected output and assumption ports.
function portLabels(olorin) {
    return olorin.page.evaluate(() => Array.from(document.querySelectorAll(
        '#canvas .upperOutputLabel, #canvas .middleOutputLabel, #canvas .lowerOutputLabel'))
        .map((e) => e.innerText));
}

// State the given conclusion and wire an induction block into it, returning the block's id.
async function induct(olorin, conclusion) {
    await olorin.buildCustom({ parameters: '', variables: '', hypotheses: '', conclusion });
    const ind = await dragBinder(olorin, 'natInd', 250, 100, 'j');
    const nodes = await olorin.nodes();
    const concl = nodes.find((n) => n.rule === 'conclusion').id;
    await olorin.connect({ vertex: ind, sort: 'output' }, { vertex: concl, sort: 'input' });
    return ind;
}

// Prove the conclusion by induction, proving the step by algebra alone.
async function inductionProves(olorin, conclusion) {
    const ind = await induct(olorin, conclusion);
    const alg = await olorin.dragRule('algplus', 450, 100);
    await olorin.connect({ vertex: alg, sort: 'output' },
                         { vertex: ind, sort: 'subgoal', label: 'step' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

test.describe('The "natInd" block', () => {
    test('proves a statement about every natural number', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await inductionProves(olorin, '∀n∈ℕ,(n≥0)')).toBe(true);
    });

    // The predicate it takes from the goal must be one on the natural numbers.
    test("doesn't prove a statement about every integer", async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await inductionProves(olorin, '∀n∈ℤ,(n=n)')).toBe(false);
    });

    test('labels its assumptions with the variable it binds and the inductive hypothesis',
        async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await induct(olorin, '∀n∈ℕ,(n≥0)');
            await olorin.waitForTypecheck();
            expect(await portLabels(olorin)).toEqual(
                expect.arrayContaining(['j ∈ ℕ', '∀k∈[j],(0≤k)']));
        });
});
