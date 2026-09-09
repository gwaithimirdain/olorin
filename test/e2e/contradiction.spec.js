// What the algebra blocks do with a goal that isn't algebraic at all.
//
// Their inputs still have to be equations or inequalities (or, for alg+, conjunctions of those),
// but the goal no longer does: anything whatsoever follows from hypotheses that contradict each
// other, so a non-algebraic goal is proved exactly when the inputs are inconsistent on their own.
// Where they aren't, the block says so as part of the "not a relation" complaint, rather than
// leaving the player to think the goal was of the wrong shape and nothing else.  Each block
// describes itself there: what the plain one takes, or what alg+ takes on top of that.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// State a level, wire every hypothesis into one algebra block and that block into the conclusion,
// and report whether Olorin accepts the result.
async function algebraProves(olorin, rule, { parameters = '', variables = '', hypotheses = [], conclusion }) {
    await olorin.buildCustom({
        parameters,
        variables,
        hypotheses: hypotheses.join('\n'),
        conclusion,
    });
    const alg = await olorin.dragRule(rule, 500, 200);
    const nodes = await olorin.nodes();
    for (const n of nodes.filter((n) => n.rule === 'hypothesis')) {
        await olorin.connect({ vertex: n.id, sort: 'output' }, { vertex: alg, sort: 'input' });
    }
    await olorin.connect({ vertex: alg, sort: 'output' },
                         { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

// What the block complained about, whether or not it complained at all.
async function complaint(olorin) {
    return (await olorin.diagnostics()).map((d) => d.explanation).join(' ');
}

// What each block says of itself: what it proves, in the complaint about a goal it wouldn't take,
// and what it takes, in the complaint about a wire.  Each describes itself alone.
const SAYS = {
    alg: {
        goal: 'The algebra block only proves equations and inequalities',
        input: 'Everything wired into the algebra block',
    },
    algplus: {
        goal: 'The alg+ block only proves equations and inequalities (=, ≠, <, ≤, >, ≥), and '
            + 'conjunctions (∧) and disjunctions (∨) of them',
        input: 'Everything wired into the alg+ block',
    },
};

for (const rule of ['alg', 'algplus']) {
    test.describe(`A goal that isn't a relation, and the "${rule}" block`, () => {
        test('is proved when the inputs contradict each other', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            expect(await algebraProves(olorin, rule, {
                parameters: 'P : Type',
                variables: 'x ∈ ℝ',
                hypotheses: ['x<0', '0<x'],
                conclusion: 'P',
            })).toBe(true);
        });

        test('includes ⊥, which is what a contradiction is usually wired to', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            expect(await algebraProves(olorin, rule, {
                variables: 'x ∈ ℝ',
                hypotheses: ['x<0', '0<x'],
                conclusion: '⊥',
            })).toBe(true);
        });

        // The contradiction has to be one the arithmetic can see, not merely a goal nobody could
        // prove: consistent hypotheses leave the goal exactly as unreachable as it was before.
        test('is not proved when the inputs are consistent', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            expect(await algebraProves(olorin, rule, {
                parameters: 'P : Type',
                variables: 'x ∈ ℝ',
                hypotheses: ['0<x'],
                conclusion: 'P',
            })).toBe(false);
            const said = await complaint(olorin);
            expect(said.replace(/\s+/g, ' ')).toContain(SAYS[rule].goal);
            expect(said).toContain('its inputs are not contradictory');
            // The plain block describes itself, and doesn't send the player to the other one.
            if (rule === 'alg') expect(said).not.toContain('alg+');
        });

        test('says the same thing when there are no inputs at all to be inconsistent',
            async ({ page }) => {
                const olorin = new Olorin(page);
                await olorin.open();
                expect(await algebraProves(olorin, rule, {
                    parameters: 'P : Type',
                    conclusion: 'P',
                })).toBe(false);
                const said = await complaint(olorin);
                expect(said.replace(/\s+/g, ' ')).toContain(SAYS[rule].goal);
                expect(said).toContain('its inputs are not contradictory');
                if (rule === 'alg') expect(said).not.toContain('alg+');
            });

        // Only the goal was generalized.  A wire carrying something that isn't a relation is still
        // refused outright, with the message about inputs rather than the one about goals.
        test('does not extend to its inputs', async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            expect(await algebraProves(olorin, rule, {
                parameters: 'P : Type',
                variables: 'x ∈ ℝ',
                hypotheses: ['P', '0<x'],
                conclusion: 'x·x≥0',
            })).toBe(false);
            const said = await complaint(olorin);
            expect(said).toContain(SAYS[rule].input);
            if (rule === 'alg') expect(said).not.toContain('alg+');
        });
    });
}

test.describe('The alg+ block on a non-algebraic goal', () => {
    // Its extra power over alg is conjunctions, and that applies to the hypotheses it reads the
    // contradiction out of just as it does anywhere else.
    test('reads a contradiction out of a conjunction, where alg cannot', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const level = {
            parameters: 'P : Type',
            variables: 'x ∈ ℝ',
            hypotheses: ['(x<0)∧(0<x)'],
            conclusion: 'P',
        };
        expect(await algebraProves(olorin, 'algplus', level)).toBe(true);
        expect(await algebraProves(olorin, 'alg', level)).toBe(false);
    });

    // A conjunction with a non-relation in it isn't split into a provable half and an unprovable
    // one: the goal as a whole isn't algebraic, so it takes the same contradiction as any other.
    test('treats a conjunction with a non-relation in it as non-algebraic throughout',
        async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            expect(await algebraProves(olorin, 'algplus', {
                parameters: 'P : Type',
                variables: 'x ∈ ℝ',
                hypotheses: ['0<x'],
                conclusion: '(0≤x)∧P',
            })).toBe(false);
            expect(await algebraProves(olorin, 'algplus', {
                parameters: 'P : Type',
                variables: 'x ∈ ℝ',
                hypotheses: ['x<0', '0<x'],
                conclusion: '(0≤x)∧P',
            })).toBe(true);
        });
});
