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

// Wire an induction block into a label block saying something that isn't a ∀ over ℕ at all, with
// a nested ∀-introduction inside the induction, one of whose own assumptions is wired onward.  The
// induction can't get the predicate it proves out of that goal, so nothing inside it is elaborated
// and none of its inner wires can be placed either.
async function inductToWrongGoal(olorin, page) {
    await olorin.buildCustom({
        parameters: '', variables: '', hypotheses: '∀n∈ℕ,(n≥0)', conclusion: '∀n∈ℕ,(n≥0)',
    });
    const ind = await dragBinder(olorin, 'natInd', 200, 400, 'j');
    const all = await dragBinder(olorin, 'allI', 500, 300, 'k');
    const use = await olorin.dragRule('allE', 800, 200);
    const label = await olorin.dragRule('asc', 1100, 500);
    await page.waitForSelector('#ascribeBG', { state: 'visible' });
    await page.fill('#ascribe', '0=1');
    await page.click('#submitAscribe');
    const hyp = (await olorin.nodes()).find((n) => n.rule === 'hypothesis').id;
    await olorin.connect({ vertex: hyp, sort: 'output' },
                         { vertex: use, sort: 'input', label: 'universal' });
    await olorin.connect({ vertex: all, sort: 'assumption' },
                         { vertex: use, sort: 'input', label: 'element' });
    await olorin.connect({ vertex: use, sort: 'output' }, { vertex: all, sort: 'subgoal' });
    await olorin.connect({ vertex: all, sort: 'output' },
                         { vertex: ind, sort: 'subgoal', label: 'step' });
    await olorin.connect({ vertex: ind, sort: 'output' }, { vertex: label, sort: 'input' });
    await olorin.waitForTypecheck();
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

    // The goal has to be a ∀ over ℕ for the block to get the predicate it proves out of it.
    test("names the shape of goal it proves when it's wired to another one",
        async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await inductToWrongGoal(olorin, page);
            const d = (await olorin.diagnostics()).find((x) => x.code === 'E1602');
            expect(d, 'no diagnostic with code E1602').toBeTruthy();
            expect(d.explanation).toContain('(∀n∈ℕ,…)');
            expect(d.explanation).toContain('0=1');
            expect(d.explanation).toContain("isn't of that form");
        });

    // And that one error is the only thing marked: the wires inside the block are perfectly good,
    // and are unplaceable only because the block they are inside of never got elaborated.
    test("doesn't mark the wires inside it when it can't be elaborated", async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await inductToWrongGoal(olorin, page);
        const errors = await olorin.wireErrors();
        expect(errors).toHaveLength(1);
        expect(errors[0]).toContain("isn't of that form");
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
