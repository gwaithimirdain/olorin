// The quantifiers over a set that isn't a type of its own: ∀x∈ℝ₊ / ∃x∈ℝ₊ over the positive reals,
// and ∀x∈[n] / ∃x∈[n] over the whole numbers below n.  They use the same blocks as the plain
// quantifiers, which carry the condition defining the set -- 0<x, or x<n -- on a port of its own
// alongside the value port for x, shown only when the quantifier has such a condition.  [n]'s
// elements are naturals, so being at least 0 comes with the element rather than with the
// condition.  These drive them on custom levels, whose palette holds every rule.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

const FAMILIES = [
    {
        set: 'ℝ₊',
        parameters: 'P : ℝ → Type',
        variables: '',
        elementSet: 'ℝ',
        condition: 'condition',
        conditionOn: (v) => `0<${v}`,
        rules: { allI: 'allI', allE: 'allE', exI: 'exI', exE: 'exE' },
        // A goal the algebra block can reach from the condition alone, to pin that the bound
        // variable is a number you can compute with.  `split` says the condition is a conjunction,
        // so it needs ∧-elimination before the algebra block, which takes only relations.
        arithmetic: { conclusion: '∀x∈ℝ₊,(0<x·2)' },
        // Supplying that condition to an elimination from a hypothesis, rather than from a binder.
        elimVariables: 'k ∈ ℝ',
        elimCondition: '0<k',
        // A statement that nests both quantifiers of the family, with the bodies parenthesized as
        // ∀ and the relations have no relative precedence (as for the ordinary quantifiers).
        nested: '∀ε∈ℝ₊,∃δ∈ℝ₊,∀x∈ℝ,((∣x∣<δ)⇒(∣f x∣<ε))',
        nestedParameters: 'f : ℝ → ℝ',
        nestedVariables: '',
        nestedPrinted: '∀ε∈ℝ₊,∃δ∈ℝ₊,∀x∈ℝ,((∣x∣<δ)⇒(∣f(x)∣<ε))',
    },
    {
        set: '[n]',
        parameters: 'P : ℕ → Type',
        variables: 'n ∈ ℕ',
        elementSet: 'ℕ',
        condition: 'condition',
        conditionOn: (v) => `${v}<n`,
        rules: { allI: 'allI', allE: 'allE', exI: 'exI', exE: 'exE' },
        // x < n forces 0 < n, using the condition and the 0 ≤ x that comes of x being a natural --
        // which the block is told, and which used to have to be half of the condition.
        arithmetic: { conclusion: '∀x∈[n],(0<n)' },
        elimVariables: 'n ∈ ℕ\nk ∈ ℕ',
        elimCondition: 'k<n',
        nested: '∀i∈[n],∃j∈[n],(i<j)',
        nestedParameters: '',
        nestedVariables: 'n ∈ ℕ',
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

// The condition port of a block, as the diagram currently has it.
async function conditionPort(olorin, vertex) {
    await olorin.waitForTypecheck();
    return (await olorin.page.evaluate(() => window.__olorin.ports()))
        .find((p) => p.vertex === vertex && p.label === 'condition');
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
            await olorin.connect({ vertex: intro, sort: 'assumption', label: f.condition },
                                 { vertex: alg, sort: 'input' });
            await olorin.connect({ vertex: alg, sort: 'output' }, { vertex: intro, sort: 'subgoal' });
            // Anything the algebra block asks Z3 comes back asynchronously.
            await olorin.waitForTypecheck();
            expect(await olorin.isComplete()).toBe(true);
        });

        test('and can be handed the condition an elimination asks for', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.buildCustom({
                parameters: f.parameters,
                variables: f.elimVariables,
                hypotheses: `∀x∈${f.set},P x\n${f.elimCondition}`,
                conclusion: 'P k',
            });
            const nodes = await olorin.nodes();
            const k = nodes.find((n) => n.name === 'k').id;
            const [universal, condition] = nodes.filter((n) => n.rule === 'hypothesis').map((n) => n.id);
            const elim = await olorin.dragRule(allE, 450, 200);
            const alg = await olorin.dragRule('alg', 250, 420);
            await olorin.connect({ vertex: universal, sort: 'output' }, { vertex: elim, sort: 'input', label: 'universal' });
            await olorin.connect({ vertex: k, sort: 'output' }, { vertex: elim, sort: 'input', label: 'element' });
            await olorin.connect({ vertex: condition, sort: 'output' }, { vertex: alg, sort: 'input' });
            await olorin.connect({ vertex: alg, sort: 'output' }, { vertex: elim, sort: 'input', label: f.condition });
            await olorin.connect({ vertex: elim, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
            await olorin.waitForTypecheck();
            expect(await olorin.isComplete()).toBe(true);
        });

        test('show the condition port of a ∀ block once it is wired to such a goal', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.buildCustom({
                parameters: f.parameters,
                variables: f.variables,
                hypotheses: '',
                conclusion: `∀y∈${f.set},P y`,
            });
            const intro = await dragBinder(olorin, allI, 500, 120, 'z');
            // Until then, nothing says what the block quantifies over.
            expect(await conditionPort(olorin, intro)).toMatchObject({ hidden: true });
            await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
            expect(await conditionPort(olorin, intro)).toMatchObject({ hidden: false, type: f.conditionOn('z') });
        });

        test('and leaving the condition of an elimination empty is an unfinished proof', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            const { intro, elim } = await universalLevel(olorin);
            await olorin.connect({ vertex: intro, sort: 'assumption' }, { vertex: elim, sort: 'input', label: 'element' });
            await olorin.connect({ vertex: elim, sort: 'output' }, { vertex: intro, sort: 'subgoal' });
            expect(await olorin.isComplete()).toBe(false);
            expect(await conditionPort(olorin, elim)).toMatchObject({ hidden: false });
            // The empty port is what's said to be missing.
            const holes = (await olorin.diagnostics()).flatMap((d) => d.locs)
                .filter((l) => !l.isEdge && l.id === elim && l.label === 'condition');
            expect(holes.length).toBeGreaterThan(0);
        });

        test('load a proof saved when they had blocks of their own', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            const boxes = await universalLevel(olorin);
            await wireUniversal(olorin, boxes);
            const state = await olorin.serialize();
            // What the proof looked like then: blocks named for the set, with the condition port
            // named for what it said.
            const old = f.set === 'ℝ₊'
                ? { rules: { allI: 'allposI', allE: 'allposE' }, label: 'positive' }
                : { rules: { allI: 'allbelowI', allE: 'allbelowE' }, label: 'below' };
            state.nodes.forEach((n) => { n.rule = old.rules[n.rule] || n.rule; });
            state.connections.forEach((c) => {
                for (const end of [c.source, c.target]) {
                    if (end.label === 'condition') { end.label = old.label; }
                }
            });
            await olorin.restore(state);
            expect(await olorin.isComplete()).toBe(true);
            expect((await olorin.nodes()).map((n) => n.rule)).toEqual(expect.arrayContaining(['allI', 'allE']));
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

// The lexer skips whatever space surrounds a name, so the checks that a name isn't reserved, and
// doesn't start with a numeral, have to be made against the name the lexer found rather than the
// string as typed: against the latter, padding waved anything at all through.
test('and padding it does not smuggle it past that check', async ({ page }) => {
    const olorin = new Olorin(page);
    await olorin.open();
    await olorin.buildCustom();
    const check = (v) => page.evaluate((s) => window.Narya.checkVariable(s).complete, v);
    for (const padded of [' ℝ₊', 'ℝ₊ ', '  ℝ₊  ']) {
        expect(await check(padded), padded).toBe(false);
    }
    // Nor may a variable begin with a numeral, however it's padded.
    expect(await check('0x')).toBe(false);
    expect(await check(' 0x')).toBe(false);
    expect(await check(' 9')).toBe(false);
    // Padding an ordinary name is just padding, though: the name it spells is a fine one.
    expect(await check(' z ')).toBe(true);
});

// A plain quantifier ranges over a whole type, so its condition is the trivial ⊤: the blocks never
// show the port for it, and the proof goes through without it.
test.describe('Quantifiers over a type', () => {
    test('∀ needs no condition, and its blocks show no port for one', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: 'P : ℝ → Type',
            variables: '',
            hypotheses: '∀x∈ℝ,P x',
            conclusion: '∀y∈ℝ,P y',
        });
        const intro = await dragBinder(olorin, 'allI', 500, 120, 'z');
        const elim = await olorin.dragRule('allE', 250, 350);
        await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: elim, sort: 'input', label: 'universal' });
        await olorin.connect({ vertex: intro, sort: 'assumption' }, { vertex: elim, sort: 'input', label: 'element' });
        await olorin.connect({ vertex: elim, sort: 'output' }, { vertex: intro, sort: 'subgoal' });
        expect(await olorin.isComplete()).toBe(true);
        expect(await conditionPort(olorin, intro)).toMatchObject({ hidden: true });
        expect(await conditionPort(olorin, elim)).toMatchObject({ hidden: true });
    });

    test('nor does ∃', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: 'P : ℝ → Type',
            variables: '',
            hypotheses: '∃x∈ℝ,P x',
            conclusion: '∃y∈ℝ,P y',
        });
        const elim = await dragBinder(olorin, 'exE', 250, 100, 'e');
        const intro = await olorin.dragRule('exI', 550, 300);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: elim, sort: 'input' });
        await olorin.connect({ vertex: elim, sort: 'output', label: 'element' }, { vertex: intro, sort: 'input', label: 'element' });
        await olorin.connect({ vertex: elim, sort: 'output', label: 'property' }, { vertex: intro, sort: 'input', label: 'property' });
        await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.isComplete()).toBe(true);
        expect(await conditionPort(olorin, elim)).toMatchObject({ hidden: true });
        expect(await conditionPort(olorin, intro)).toMatchObject({ hidden: true });
    });

    test('and a ∀-introduction wired straight into a ∀-elimination needs none either', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: 'P : ℝ → Type',
            variables: 'a ∈ ℝ',
            hypotheses: '∀x∈ℝ,P x',
            conclusion: 'P a',
        });
        const nodes = await olorin.nodes();
        const a = nodes.find((n) => n.name === 'a').id;
        const intro = await dragBinder(olorin, 'allI', 500, 120, 'z');
        const inner = await olorin.dragRule('allE', 300, 350);
        const outer = await olorin.dragRule('allE', 700, 350);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: inner, sort: 'input', label: 'universal' });
        await olorin.connect({ vertex: intro, sort: 'assumption' }, { vertex: inner, sort: 'input', label: 'element' });
        await olorin.connect({ vertex: inner, sort: 'output' }, { vertex: intro, sort: 'subgoal' });
        await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: outer, sort: 'input', label: 'universal' });
        await olorin.connect({ vertex: a, sort: 'output' }, { vertex: outer, sort: 'input', label: 'element' });
        await olorin.connect({ vertex: outer, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.isComplete()).toBe(true);
    });
});
