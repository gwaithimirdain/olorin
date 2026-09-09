// Conjunctions and disjunctions through the "alg+" algebra block, which takes and proves them as
// well as bare relations: a hypothesis that is a conjunction contributes both of its parts, a goal
// that is one is decided part by part against all the hypotheses, and a goal that is a disjunction
// is decided by ruling out every one of its sides at once.  The plain "alg" block still insists on
// a bare equation or inequality at both ends.

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

const proves = (olorin, level) => provesWith('algplus', olorin, level);
const plainProves = (olorin, level) => provesWith('alg', olorin, level);

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
            [expect.stringContaining("won't prove a ≠ statement by algebra")]);
        expect(await proves(olorin, { hypotheses: ['0<x'], conclusion: '(0<x)∧(0≠1)' })).toBe(true);
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

// A disjunctive goal is proved by contradicting all of its sides at once; which side actually
// holds the block never says, and needn't, since the disjunction is what it proves.
test.describe('alg+ and disjunctive goals', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('proves a disjunction when the hypotheses rule out every other side', async () => {
        expect(await proves(olorin, {
            hypotheses: ['x·x=1'],
            conclusion: '(x=1)∨(x=−1)',
        })).toBe(true);
    });

    test('proves one whose sides no hypothesis decides between', async () => {
        // Nothing here says which of the two holds; that they can't both fail is the whole proof.
        expect(await proves(olorin, { conclusion: '(x≤n)∨(n<x)' })).toBe(true);
    });

    test('nests, and to the left as well as the right', async () => {
        expect(await proves(olorin, {
            hypotheses: ['x·x·x=x'],
            conclusion: '((x=0)∨(x=1))∨(x=−1)',
        })).toBe(true);
    });

    test("won't prove one whose sides can all fail", async () => {
        expect(await proves(olorin, { hypotheses: ['0<x'], conclusion: '(x=1)∨(x=2)' })).toBe(false);
    });

    test('takes a conjunction of disjunctions, proving each conjunct on its own', async () => {
        expect(await proves(olorin, {
            hypotheses: ['x·x=1'],
            conclusion: '((x=1)∨(x=−1))∧((0<x)∨(x<0))',
        })).toBe(true);
    });

    test('distributes a conjunction inside a disjunction, rather than giving up on it', async () => {
        // "a ∨ (b ∧ c)" needs "a ∨ b" and "a ∨ c" separately: x=1 gives the first side, and
        // 0<x gives both halves of the second.
        expect(await proves(olorin, {
            hypotheses: ['x·x=1', '0<x'],
            conclusion: '(x=−1)∨((x=1)∧(0<x·2))',
        })).toBe(true);
    });

    test('holds a disjunct to the rule about ≠, as it holds a conjunct', async () => {
        expect(await proves(olorin, { hypotheses: ['0<x'], conclusion: '(x=0)∨(x≠1)' })).toBe(false);
        expect(await complaints(olorin)).toEqual(
            [expect.stringContaining("won't prove a ≠ statement by algebra")]);
    });

    test("won't take a disjunction that isn't one of relations", async () => {
        expect(await proves(olorin, { hypotheses: ['0<x'], conclusion: '(0<x)∨⊤' })).toBe(false);
        expect(await complaints(olorin)).toEqual([expect.stringContaining('(0<x)∨⊤')]);
    });
});

test.describe('the plain alg block', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('refuses a conjunctive goal, quoting the goal it wouldn\'t take', async () => {
        expect(await plainProves(olorin, {
            hypotheses: ['0≤x', 'x<n'],
            conclusion: '(0≤x)∧(x<n)',
        })).toBe(false);
        expect(await complaints(olorin)).toEqual([expect.stringContaining(
            'only proves equations and inequalities (=, ≠, <, ≤, >, ≥), unless its inputs are '
            + 'contradictory. The goal it\'s wired to here is (0≤x)∧(x<n)')]);
    });

    test('refuses a disjunctive goal too', async () => {
        expect(await plainProves(olorin, {
            hypotheses: ['x·x=1'],
            conclusion: '(x=1)∨(x=−1)',
        })).toBe(false);
        expect(await complaints(olorin)).toEqual([expect.stringContaining(
            'only proves equations and inequalities')]);
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

