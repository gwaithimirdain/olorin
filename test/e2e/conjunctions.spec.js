// Conjunctions through the "alg+" algebra block, which takes and proves them as well as bare
// relations: a hypothesis that is a conjunction contributes both of its parts, and a goal that is
// one is decided part by part against all the hypotheses.  The plain "alg" block still insists on
// a bare equation or inequality at both ends.
//
// The motivating case is the ∀x∈[n] and ∃x∈[n] blocks, whose condition port carries the single
// statement (0≤x)∧(x<n): alg+ consumes and produces it directly, with no ∧-elimination or
// ∧-introduction in between.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// State a level and prove it with a single algebra block, fed by every hypothesis.
async function provesWith(rule, olorin, { variables = 'x ∈ ℤ\nn ∈ ℤ', hypotheses = [], conclusion }) {
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

const proves = (olorin, level) => provesWith('algebraplus', olorin, level);
const plainProves = (olorin, level) => provesWith('algebra', olorin, level);

// What the block complained about, as the player is shown it.
const complaints = async (olorin) =>
    (await olorin.diagnostics()).map((d) => (d.explanation || d.text).replace(/\s+/g, ' '));

test.describe('alg+ and conjunctions', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('proves a conjunctive goal part by part', async () => {
        expect(await proves(olorin, {
            hypotheses: ['0≤x', 'x<n'],
            conclusion: '(0≤x·2)∧(x·2<n·2)',
        })).toBe(true);
    });

    test('needs every part of a conjunctive goal to follow, not just one', async () => {
        expect(await proves(olorin, {
            hypotheses: ['0≤x'],
            conclusion: '(0≤x)∧(x<n)',
        })).toBe(false);
    });

    test('takes a conjunctive hypothesis as both of its parts', async () => {
        expect(await proves(olorin, {
            hypotheses: ['(0≤x)∧(x<n)'],
            conclusion: '0<n',
        })).toBe(true);
    });

    test('nests, on either side', async () => {
        expect(await proves(olorin, {
            hypotheses: ['((0≤x)∧(x<n))∧(n<9)'],
            conclusion: '(0<n)∧(x<9)',
        })).toBe(true);
    });

    test('still proves a bare relation', async () => {
        expect(await proves(olorin, { hypotheses: ['0<x'], conclusion: '0<x·2' })).toBe(true);
    });

    test('holds each part of a goal to the rule about ≠', async () => {
        // A disequality is only proved outright between literals, whether or not it is conjoined.
        expect(await proves(olorin, { hypotheses: ['0<x'], conclusion: '(0<x)∧(x≠1)' })).toBe(false);
        expect(await complaints(olorin)).toEqual(
            [expect.stringContaining("won't prove a ≠ statement outright")]);
        expect(await proves(olorin, { hypotheses: ['0<x'], conclusion: '(0<x)∧(0≠1)' })).toBe(true);
    });

    test('wants the parts of a conjunctive goal to be about the same numbers', async () => {
        expect(await proves(olorin, {
            variables: 'x ∈ ℤ\ny ∈ ℝ',
            hypotheses: ['0≤x', '0≤y'],
            conclusion: '(0≤x)∧(0≤y)',
        })).toBe(false);
        expect(await complaints(olorin)).toEqual(
            [expect.stringContaining('have to be about the same kind of number')]);
    });

    test("won't take a conjunction that isn't one of relations", async () => {
        expect(await proves(olorin, { hypotheses: ['0<x'], conclusion: '(0<x)∧⊤' })).toBe(false);
        // The whole goal is named, not just the part that isn't a relation.
        expect(await complaints(olorin)).toEqual([expect.stringContaining('(0<x)∧⊤')]);
    });

    test("won't split a negated conjunction, which is really a disjunction", async () => {
        expect(await proves(olorin, {
            hypotheses: ['¬((0≤x)∧(x<n))'],
            conclusion: '0<n',
        })).toBe(false);
    });
});

test.describe('the plain alg block', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('refuses a conjunctive goal, and says which block does take one', async () => {
        expect(await plainProves(olorin, {
            hypotheses: ['0≤x', 'x<n'],
            conclusion: '(0≤x)∧(x<n)',
        })).toBe(false);
        expect(await complaints(olorin)).toEqual([expect.stringContaining(
            'the alg+ block conjunctions (∧) of those. The goal it\'s wired to is (0≤x)∧(x<n)')]);
    });

    test('refuses a conjunctive hypothesis, blaming the wire rather than the goal', async () => {
        expect(await plainProves(olorin, {
            hypotheses: ['(0≤x)∧(x<n)'],
            conclusion: '0<n',
        })).toBe(false);
        expect(await complaints(olorin)).toEqual([expect.stringContaining(
            'Everything wired into the algebra block has to be')]);
    });
});

test.describe('the [n] quantifiers with alg+', () => {
    // Their condition port carries (0≤x)∧(x<n), which alg+ now handles at both ends.
    test('consumes the condition ∀x∈[n] binds', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'n ∈ ℤ', hypotheses: '', conclusion: '∀x∈[n],(0<n)',
        });
        const intro = await olorin.dragRule('allbelowI', 450, 60);
        await page.waitForSelector('#variableBG', { state: 'visible' });
        await page.fill('#newvar', 'z');
        await page.click('#submitVariable');
        await olorin.dismissHints();
        const alg = await olorin.dragRule('algebraplus', 500, 300);
        await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.connect({ vertex: intro, sort: 'assumption', label: 'below' }, { vertex: alg, sort: 'input' });
        await olorin.connect({ vertex: alg, sort: 'output' }, { vertex: intro, sort: 'subgoal' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
    });

    test('and produces the condition ∀x∈[n]-elimination asks for', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: 'P : ℤ → Type',
            variables: 'n ∈ ℤ\nk ∈ ℤ',
            hypotheses: '∀x∈[n],P x\n0≤k\nk<n',
            conclusion: 'P k',
        });
        const nodes = await olorin.nodes();
        const k = nodes.find((n) => n.name === 'k').id;
        const [universal, low, high] = nodes.filter((n) => n.rule === 'hypothesis').map((n) => n.id);
        const elim = await olorin.dragRule('allbelowE', 450, 200);
        const alg = await olorin.dragRule('algebraplus', 250, 420);
        await olorin.connect({ vertex: universal, sort: 'output' }, { vertex: elim, sort: 'input', label: 'universal' });
        await olorin.connect({ vertex: k, sort: 'output' }, { vertex: elim, sort: 'input', label: 'element' });
        await olorin.connect({ vertex: low, sort: 'output' }, { vertex: alg, sort: 'input' });
        await olorin.connect({ vertex: high, sort: 'output' }, { vertex: alg, sort: 'input' });
        await olorin.connect({ vertex: alg, sort: 'output' }, { vertex: elim, sort: 'input', label: 'below' });
        await olorin.connect({ vertex: elim, sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
    });
});
