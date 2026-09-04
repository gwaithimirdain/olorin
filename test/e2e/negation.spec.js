// Which of its two inputs a ¬-elimination block reads as the negation.
//
// The block takes them in either order, so that a player who wires the negation to the "statement"
// port still gets a proof: whichever input synthesizes is tried both as the negation applied to the
// other, and as the statement the other implicitly contradicts.
//
// Both readings are tried whatever is on the ports; what matters is whose failure is reported when
// neither works.  When the negation port holds something whose type really is a negation, that is
// the reading the two ports describe, and its failure is the one to report.  Reporting the other
// one meant that a subproof still being built under the statement port -- which fails to check for
// a reason of its own -- got a demand for a doubly negated statement on its wire instead, on a port
// that had shown the un-negated one a moment before, while the wire went red.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// The types Olorin shows for every port, keyed by "vertex:label".
async function portTypes(page) {
    const ports = await page.evaluate(() => window.__olorin.ports());
    return Object.fromEntries(ports.map((p) => [p.vertex + ':' + (p.label || p.sort), p.type]));
}

// The two ¬-elimination boxes of the proof below, told apart by which has anything wired into it.
// Restoring a proof renumbers its boxes, so they have to be found rather than named.
async function negEliminations(olorin) {
    const nodes = await olorin.nodes();
    const connections = await olorin.connections();
    const fed = (id) => connections.some((c) => c.target.vertex === id);
    const negEs = nodes.filter((n) => n.rule === 'negE').map((n) => n.id);
    return { wired: negEs.find(fed), bare: negEs.find((id) => !fed(id)) };
}

// ¬∀x∈A,P(x) ⊢ ∃x∈A,¬P(x), part-way through: the ∀-introduction feeding the ¬-elimination is
// itself proved by a second ¬-elimination that has nothing wired into it yet.
const LEVEL = {
    parameters: [{ name: 'A', ty: 'Type' }, { name: 'P', ty: 'A→Type' }],
    variables: [],
    hypotheses: [{ ty: '¬∀x∈A,P(x)' }],
    conclusion: { ty: '∃x∈A,¬P(x)' },
};

// The hypothesis goes to one port of the ¬-elimination and the ∀-introduction to the other; the
// player may have picked either way round, and the block takes both.
const stateWith = (hypPort) => ({
    level: LEVEL,
    complete: false,
    difficulty: 0,
    nodes: [
        { id: 'hyp16', rule: 'hypothesis', left: '50px', top: '489px', value: '¬∀x∈A,P(x)' },
        { id: 'concl23', rule: 'conclusion', left: '1593px', top: '464px', value: '∃x∈A,¬P(x)' },
        { id: 'rule142', rule: 'cnegI', left: '180px', top: '898px', width: '1442px', height: '50px' },
        { id: 'rule145', rule: 'negE', left: '678px', top: '364px' },
        { id: 'rule146', rule: 'allI', left: '265px', top: '594px', name: 'cam', width: '200px', height: '50px', variable: 'cam' },
        // The one with nothing wired into it.
        { id: 'rule153', rule: 'negE', left: '330px', top: '689px' },
    ],
    connections: [
        { source: { vertex: 'rule142', sort: 'output' }, target: { vertex: 'concl23', sort: 'input' } },
        { source: { vertex: 'hyp16', sort: 'output' },
          target: { vertex: 'rule145', sort: 'input', label: hypPort } },
        { source: { vertex: 'rule146', sort: 'output' },
          target: { vertex: 'rule145', sort: 'input', label: hypPort === 'negation' ? 'statement' : 'negation' } },
        { source: { vertex: 'rule145', sort: 'output' }, target: { vertex: 'rule142', sort: 'subgoal' } },
        { source: { vertex: 'rule153', sort: 'output' }, target: { vertex: 'rule146', sort: 'subgoal' } },
    ],
});

const buildLevel = (olorin) => olorin.buildCustom({
    parameters: LEVEL.parameters.map((p) => p.name + ' : ' + p.ty).join('\n'),
    variables: '',
    hypotheses: LEVEL.hypotheses.map((h) => h.ty).join('\n'),
    conclusion: LEVEL.conclusion.ty,
});

// Whichever port the hypothesis went to.  Both orders had the same trouble, on the port the
// ∀-introduction was wired to.
for (const hypPort of ['negation', 'statement']) {
    const otherPort = hypPort === 'negation' ? 'statement' : 'negation';

    test.describe(`A subproof still being built, with the hypothesis on the ${hypPort} port`, () => {
        test('does not turn its wire red, or ask for a doubly negated statement', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await buildLevel(olorin);
            await olorin.restore(stateWith(hypPort));
            await olorin.waitForTypecheck();

            expect(await olorin.wireErrors()).toEqual([]);
            const { wired } = await negEliminations(olorin);
            const types = await portTypes(page);
            expect(types[wired + ':' + hypPort]).toBe('¬∀x∈A,P(x)');
            expect(types[wired + ':' + otherPort]).toBe('∀x∈A,P(x)');
        });

        test('leaves the trouble reported where it is: the ports nothing is wired to', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await buildLevel(olorin);
            await olorin.restore(stateWith(hypPort));
            await olorin.waitForTypecheck();

            const { bare } = await negEliminations(olorin);
            const errors = (await olorin.diagnostics()).filter((d) => d.code.startsWith('E'));
            expect(errors.length).toBeGreaterThan(0);
            for (const d of errors) {
                for (const loc of d.locs) {
                    expect(loc.id).toBe(bare);
                }
            }
        });
    });
}

test.describe('The two inputs of a ¬-elimination', () => {
    // Both of these have a non-synthesizing box output on one port and a hypothesis on the other,
    // which is the case that has to choose a reading without being able to see both types.
    test('work with the negation on the negation port', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: 'P : Type\nQ : Type', variables: '',
            hypotheses: '¬(P∧Q)\nP\nQ', conclusion: '⊥',
        });
        const nodes = await olorin.nodes();
        const hyps = nodes.filter((n) => n.rule === 'hypothesis');
        const andI = await olorin.dragRule('andI', 350, 300);
        const negE = await olorin.dragRule('negE', 650, 200);
        await olorin.connect({ vertex: hyps[1].id, sort: 'output' }, { vertex: andI, sort: 'input', label: 'fst' });
        await olorin.connect({ vertex: hyps[2].id, sort: 'output' }, { vertex: andI, sort: 'input', label: 'snd' });
        await olorin.connect({ vertex: hyps[0].id, sort: 'output' }, { vertex: negE, sort: 'input', label: 'negation' });
        await olorin.connect({ vertex: andI, sort: 'output' }, { vertex: negE, sort: 'input', label: 'statement' });
        await olorin.connect({ vertex: negE, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
    });

    test('and the other way round, when what is on the negation port is not one', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: 'P : Type\nQ : Type', variables: '',
            hypotheses: 'P\n¬Q\nQ', conclusion: '⊥',
        });
        const nodes = await olorin.nodes();
        const hyps = nodes.filter((n) => n.rule === 'hypothesis');
        // A ¬-introduction proving ¬P, which is a box output and so doesn't synthesize.
        const negI = await olorin.dragRule('negI', 350, 380);
        const inner = await olorin.dragRule('negE', 380, 200);
        const outer = await olorin.dragRule('negE', 750, 300);
        await olorin.connect({ vertex: hyps[1].id, sort: 'output' }, { vertex: inner, sort: 'input', label: 'negation' });
        await olorin.connect({ vertex: hyps[2].id, sort: 'output' }, { vertex: inner, sort: 'input', label: 'statement' });
        await olorin.connect({ vertex: inner, sort: 'output' }, { vertex: negI, sort: 'subgoal' });
        // P on the negation port and ¬P on the statement port: the wrong way round, and taken anyway.
        await olorin.connect({ vertex: hyps[0].id, sort: 'output' }, { vertex: outer, sort: 'input', label: 'negation' });
        await olorin.connect({ vertex: negI, sort: 'output' }, { vertex: outer, sort: 'input', label: 'statement' });
        await olorin.connect({ vertex: outer, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.wireErrors()).toEqual([]);
    });

    // Both of them negations and the wrong way round is the one case the ports can't settle, and
    // where the reversed reading has to get its chance before the direct one commits.
    test('and the other way round when both of them are negations', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: 'P : Type', variables: '', hypotheses: '¬P\nP', conclusion: '⊥',
        });
        const nodes = await olorin.nodes();
        const hyps = nodes.filter((n) => n.rule === 'hypothesis');   // 0: ¬P   1: P
        // A ¬-introduction proving ¬¬P, from its assumption ¬P and the hypothesis P.
        const negI = await olorin.dragRule('negI', 300, 380);
        const inner = await olorin.dragRule('negE', 420, 250);
        const outer = await olorin.dragRule('negE', 800, 320);
        await olorin.connect({ vertex: negI, sort: 'assumption' }, { vertex: inner, sort: 'input', label: 'negation' });
        await olorin.connect({ vertex: hyps[1].id, sort: 'output' }, { vertex: inner, sort: 'input', label: 'statement' });
        await olorin.connect({ vertex: inner, sort: 'output' }, { vertex: negI, sort: 'subgoal' });
        // ¬P on the negation port and ¬¬P on the statement port: both negations, and swapped.
        await olorin.connect({ vertex: hyps[0].id, sort: 'output' }, { vertex: outer, sort: 'input', label: 'negation' });
        await olorin.connect({ vertex: negI, sort: 'output' }, { vertex: outer, sort: 'input', label: 'statement' });
        await olorin.connect({ vertex: outer, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.wireErrors()).toEqual([]);
    });
});

// A ¬-elimination with one port wired and the other still empty.  A hole checks against anything,
// so both readings of the block are available and the one preferred has to be the one that wins:
// the empty port wants the statement the negation negates, not a negation of the negation.
test.describe('A ¬-elimination with one port still empty', () => {
    for (const hypPort of ['negation', 'statement']) {
        const otherPort = hypPort === 'negation' ? 'statement' : 'negation';

        test(`labels the empty port with the un-negated statement (¬ on the ${hypPort} port)`, async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.buildCustom({
                parameters: 'P : Type\nQ : Type', variables: '',
                hypotheses: '¬(P∧Q)', conclusion: '⊥',
            });
            const nodes = await olorin.nodes();
            const negE = await olorin.dragRule('negE', 600, 250);
            await olorin.connect({ vertex: nodes.find((n) => n.rule === 'hypothesis').id, sort: 'output' },
                                 { vertex: negE, sort: 'input', label: hypPort });
            await olorin.connect({ vertex: negE, sort: 'output' },
                                 { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
            await olorin.waitForTypecheck();

            const types = await portTypes(page);
            expect(types[negE + ':' + hypPort]).toBe('¬(P∧Q)');
            expect(types[negE + ':' + otherPort]).toBe('P∧Q');
        });
    }
});

