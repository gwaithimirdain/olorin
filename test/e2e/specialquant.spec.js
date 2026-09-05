// The quantifiers over a set that isn't a type of its own: ∀x∈ℝ₊ / ∃x∈ℝ₊ over the positive reals,
// and ∀x∈[n] / ∃x∈[n] over the whole numbers below n.  Their blocks carry the condition defining
// the set -- 0<x, or (0≤x)∧(x<n) -- on a port of its own alongside the value port for x.  No
// built-in level offers them yet, so these drive them on custom levels, whose palette holds every
// rule.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

const FAMILIES = [
    {
        set: 'ℝ₊',
        parameters: 'P : ℝ → Type',
        variables: '',
        elementSet: 'ℝ',
        condition: 'positive',
        conditionOn: (v) => `0<${v}`,
        rules: { allI: 'allposI', allE: 'allposE', exI: 'exposI', exE: 'exposE' },
        // A goal the algebra block can reach from the condition alone, to pin that the bound
        // variable is a number you can compute with.  `split` says the condition is a conjunction,
        // so it needs ∧-elimination before the algebra block, which takes only relations.
        arithmetic: { conclusion: '∀x∈ℝ₊,(0<x·2)', split: false },
        // A statement that nests both quantifiers of the family, with the bodies parenthesized as
        // ∀ and the relations have no relative precedence (as for the ordinary quantifiers).
        nested: '∀ε∈ℝ₊,∃δ∈ℝ₊,∀x∈ℝ,((∣x∣<δ)⇒(∣f x∣<ε))',
        nestedParameters: 'f : ℝ → ℝ',
        nestedVariables: '',
        nestedPrinted: '∀ε∈ℝ₊,∃δ∈ℝ₊,∀x∈ℝ,((∣x∣<δ)⇒(∣f(x)∣<ε))',
    },
    {
        set: '[n]',
        parameters: 'P : ℤ → Type',
        variables: 'n ∈ ℤ',
        elementSet: 'ℤ',
        condition: 'below',
        conditionOn: (v) => `(0≤${v})∧(${v}<n)`,
        rules: { allI: 'allbelowI', allE: 'allbelowE', exI: 'exbelowI', exE: 'exbelowE' },
        // 0 ≤ x < n forces 0 < n, using both halves of the condition.
        arithmetic: { conclusion: '∀x∈[n],(0<n)', split: true },
        nested: '∀i∈[n],∃j∈[n],(i<j)',
        nestedParameters: '',
        nestedVariables: 'n ∈ ℤ',
        nestedPrinted: '∀i∈[n],∃j∈[n],(i<j)',
    },
];

// Drop a rule that binds a variable, naming it in the dialog it pops.
async function dragBinder(olorin, rule, x, y, name) {
    const id = await olorin.dragRule(rule, x, y);
    await olorin.page.waitForSelector('#variableBG', { state: 'visible' });
    await olorin.page.fill('#newvar', name);
    await olorin.page.click('#submitVariable');
    await olorin.dismissHints();
    return id;
}

// The type labels currently shown on unconnected output/assumption ports.
function portLabels(olorin) {
    return olorin.page.evaluate(() => Array.from(document.querySelectorAll(
        '#canvas .upperOutputLabel, #canvas .middleOutputLabel, #canvas .lowerOutputLabel'))
        .map((e) => e.innerText));
}

for (const f of FAMILIES) {
    const { allI, allE, exI, exE } = f.rules;

    test.describe(`Quantifiers over ${f.set}`, () => {
        // ∀x∈S,P x ⊢ ∀y∈S,P y, the long way round: introduce the quantifier and eliminate the
        // hypothesis at the very variable (and condition) the introduction just bound.
        async function universalLevel(olorin) {
            await olorin.buildCustom({
                parameters: f.parameters,
                variables: f.variables,
                hypotheses: `∀x∈${f.set},P x`,
                conclusion: `∀y∈${f.set},P y`,
            });
            const intro = await dragBinder(olorin, allI, 500, 120, 'z');
            const elim = await olorin.dragRule(allE, 250, 350);
            await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
            await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: elim, sort: 'input', label: 'universal' });
            return { intro, elim };
        }

        async function wireUniversal(olorin, { intro, elim }) {
            await olorin.connect({ vertex: intro, sort: 'assumption' }, { vertex: elim, sort: 'input', label: 'element' });
            await olorin.connect({ vertex: intro, sort: 'assumption', label: f.condition }, { vertex: elim, sort: 'input', label: f.condition });
            await olorin.connect({ vertex: elim, sort: 'output' }, { vertex: intro, sort: 'subgoal' });
        }

        test('∀-introduction assumes an element and the condition, and ∀-elimination supplies both',
            async ({ page }) => {
                const olorin = new Olorin(page);
                await olorin.open();
                const boxes = await universalLevel(olorin);
                // The variable the block binds, and separately the condition putting it in the set.
                expect(await portLabels(olorin)).toEqual(
                    expect.arrayContaining([`z ∈ ${f.elementSet}`, f.conditionOn('z')]));

                await wireUniversal(olorin, boxes);
                expect(await olorin.isComplete()).toBe(true);
            });

        test('∃-elimination yields an element and the condition, and ∃-introduction takes both',
            async ({ page }) => {
                const olorin = new Olorin(page);
                await olorin.open();
                await olorin.buildCustom({
                    parameters: f.parameters,
                    variables: f.variables,
                    hypotheses: `∀x∈${f.set},P x\n∃x∈${f.set},⊤`,
                    conclusion: `∃x∈${f.set},P x`,
                });
                const ex = await dragBinder(olorin, exE, 250, 100, 'e');
                const all = await olorin.dragRule(allE, 450, 250);
                const intro = await olorin.dragRule(exI, 650, 400);
                await olorin.connect({ vertex: 'hyp1', sort: 'output' }, { vertex: ex, sort: 'input' });
                expect(await portLabels(olorin)).toEqual(
                    expect.arrayContaining([`e ∈ ${f.elementSet}`, f.conditionOn('e')]));

                await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: all, sort: 'input', label: 'universal' });
                for (const [port, target] of [['element', all], [f.condition, all], ['element', intro], [f.condition, intro]]) {
                    await olorin.connect({ vertex: ex, sort: 'output', label: port }, { vertex: target, sort: 'input', label: port });
                }
                await olorin.connect({ vertex: all, sort: 'output' }, { vertex: intro, sort: 'input', label: 'property' });
                await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
                expect(await olorin.isComplete()).toBe(true);
            });

        test('nest, and print back the way they were written', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.buildCustom({
                parameters: f.nestedParameters,
                variables: f.nestedVariables,
                hypotheses: f.nested,
                conclusion: f.nested,
            });
            expect(await olorin.currentLevelName()).toBe('Custom');
            await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
            expect(await page.evaluate(() =>
                Array.from(document.querySelectorAll('#canvas .connLabel')).map((e) => e.innerText)))
                .toEqual([f.nestedPrinted]);
            expect(await olorin.isComplete()).toBe(true);
        });

        test('let the algebra block work with the variable they bind', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.buildCustom({
                parameters: '',
                variables: f.variables,
                hypotheses: '',
                conclusion: f.arithmetic.conclusion,
            });
            const intro = await dragBinder(olorin, allI, 450, 60, 'z');
            await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
            const alg = await olorin.dragRule('alg', 520, 300);
            const condition = { vertex: intro, sort: 'assumption', label: f.condition };
            if (f.arithmetic.split) {
                const and = await olorin.dragRule('andE', 260, 300);
                await olorin.connect(condition, { vertex: and, sort: 'input' });
                for (const half of ['fst', 'snd']) {
                    await olorin.connect({ vertex: and, sort: 'output', label: half }, { vertex: alg, sort: 'input' });
                }
            } else {
                await olorin.connect(condition, { vertex: alg, sort: 'input' });
            }
            await olorin.connect({ vertex: alg, sort: 'output' }, { vertex: intro, sort: 'subgoal' });
            // Anything the algebra block asks Z3 comes back asynchronously.
            await olorin.waitForTypecheck();
            expect(await olorin.isComplete()).toBe(true);
        });

        test('survive a save and restore, keeping the variable each block binds', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            const boxes = await universalLevel(olorin);
            await wireUniversal(olorin, boxes);
            const before = await olorin.structuralState();

            const json = await olorin.exportText();
            await olorin.clear();
            expect(await olorin.isComplete()).toBe(false);
            await olorin.importText(json);
            expect(await olorin.structuralState()).toEqual(before);
            expect(await olorin.isComplete()).toBe(true);
        });
    });
}

test('ℝ₊ is reserved, so no bound variable can be named it', async ({ page }) => {
    const olorin = new Olorin(page);
    await olorin.open();
    await olorin.buildCustom(); // P |- P, enough to initialize the checker
    expect(await page.evaluate(() => window.Narya.checkVariable('ℝ₊').complete)).toBe(false);
    expect(await page.evaluate(() => window.Narya.checkVariable('ℝ').complete)).toBe(true);
});
