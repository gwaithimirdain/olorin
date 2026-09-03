// Tests for the explanations Olorin gives when a proof doesn't typecheck.
//
// Narya's own message for each error is written for someone who knows Narya -- it talks about
// tuples, records, constructors and fields.  bin/explain.ml restates the ones a player can
// actually provoke in terms of blocks, wires and goals, and a wire marked red carries that text
// as a tooltip while the pointer is over it.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// State a level, build a (deliberately wrong) proof in it, and settle the typecheck.
async function mistake(olorin, level, build) {
    await olorin.buildCustom(Object.assign(
        { parameters: '', variables: '', hypotheses: '', conclusion: 'P' }, level));
    const nodes = await olorin.nodes();
    await build(olorin,
        nodes.filter((n) => n.rule === 'hypothesis').map((n) => n.id),
        nodes.find((n) => n.rule === 'conclusion').id);
    await olorin.waitForTypecheck();
}

// The explanation given for the first error with the given code.
async function explanationFor(olorin, code) {
    const d = (await olorin.diagnostics()).find((x) => x.code === code);
    expect(d, 'no diagnostic with code ' + code).toBeTruthy();
    return d.explanation;
}

// Wire a block's single output into the conclusion.
const toConclusion = (rule) => async (o, hyps, concl) => {
    const r = await o.dragRule(rule, 300, 150);
    await o.connect({ vertex: r, sort: 'output' }, { vertex: concl, sort: 'input' });
};

test.describe('Error explanations', () => {
    test('a wire between mismatched statements names both of them', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await mistake(olorin, { parameters: 'P : Type\nQ : Type', hypotheses: 'P', conclusion: 'Q' },
            async (o, hyps, concl) =>
                o.connect({ vertex: hyps[0], sort: 'output' }, { vertex: concl, sort: 'input' }));
        const e = await explanationFor(olorin, 'E0401');
        expect(e).toContain('This wire carries a proof of');
        expect(e).toContain('\n    P\n');
        expect(e).toContain('\n    Q\n');
    });

    test('an introduction block at a goal of the wrong shape says so', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // ∧-introduction: Narya sees the connectives-as-records, so this is "tuple at non-record".
        await mistake(olorin, { parameters: 'P : Type' }, toConclusion('andI'));
        expect(await explanationFor(olorin, 'E0900')).toContain('compound statement');
        // ∨-introduction: ∨ is a datatype, so this one is "no such constructor" instead.
        await mistake(olorin, { parameters: 'P : Type' }, toConclusion('orI1'));
        const e = await explanationFor(olorin, 'E1000');
        expect(e).toContain('a disjunction (A∨B)');
        expect(e).toContain('\n    P\n');
    });

    test('an elimination block fed the wrong shape names the shape it wanted', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await mistake(olorin, { parameters: 'P : Type', hypotheses: 'P' },
            async (o, hyps, concl) => {
                const r = await o.dragRule('andE', 300, 150);
                await o.connect({ vertex: hyps[0], sort: 'output' }, { vertex: r, sort: 'input' });
                await o.connect({ vertex: r, sort: 'output', label: 'fst' }, { vertex: concl, sort: 'input' });
            });
        expect(await explanationFor(olorin, 'E0800')).toContain('takes apart a conjunction (A∧B)');
    });

    test('case-splitting on something with no cases says so', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await mistake(olorin, { parameters: 'P : Type', hypotheses: 'P' },
            async (o, hyps, concl) => {
                const r = await o.dragRule('orE', 300, 150);
                await o.connect({ vertex: hyps[0], sort: 'output' }, { vertex: r, sort: 'input' });
                await o.connect({ vertex: r, sort: 'output' }, { vertex: concl, sort: 'input' });
            });
        expect(await explanationFor(olorin, 'E1200')).toContain('no cases to split on');
    });

    test('an assumption used outside its own block says so', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await mistake(olorin, { parameters: 'P : Type' }, async (o, hyps, concl) => {
            const r = await o.dragRule('impI', 300, 150);
            await o.connect({ vertex: r, sort: 'assumption' }, { vertex: concl, sort: 'input' });
        });
        expect(await explanationFor(olorin, 'E0303')).toContain('out of the block that introduced it');
    });

    // A loop is easy to draw by accident, and every wire in it is marked, so each one explains it.
    test('wires that run in a circle say so', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await mistake(olorin, { parameters: 'P : Type', hypotheses: 'P' }, async (o, hyps, concl) => {
            const r = await o.dragRule('alg', 300, 150);
            await o.connect({ vertex: r, sort: 'output' }, { vertex: r, sort: 'input' });
            await o.connect({ vertex: r, sort: 'output' }, { vertex: concl, sort: 'input' });
        });
        expect(await explanationFor(olorin, 'E0280')).toContain('run in a circle');
        expect((await olorin.wireErrors()).join('')).toContain('run in a circle');
    });

    test('an unfinished proof says it is unfinished', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await mistake(olorin, { parameters: 'P : Type' }, async () => {});
        expect(await explanationFor(olorin, 'E2002')).toContain("isn't finished");
    });

    test('the algebra block explains each way it can fail', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();

        await mistake(olorin, { variables: 'x ∈ ℝ', conclusion: 'x·x=x' }, toConclusion('alg'));
        expect(await explanationFor(olorin, 'E3000')).toContain("couldn't prove this");

        await mistake(olorin, { variables: 'x ∈ ℝ', conclusion: 'x·(1/x)=1' }, toConclusion('alg'));
        const denom = await explanationFor(olorin, 'E3000');
        expect(denom).toContain("can't tell that");
        expect(denom).toContain('\n    x\n');
        expect(denom).toContain('is nonzero');

        await mistake(olorin, { parameters: 'P : Type' }, toConclusion('alg'));
        expect(await explanationFor(olorin, 'E3000')).toContain('only proves equations and inequalities');
    });

    test('every red wire has something to say', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await mistake(olorin, { parameters: 'P : Type\nQ : Type', hypotheses: 'P', conclusion: 'Q' },
            async (o, hyps, concl) =>
                o.connect({ vertex: hyps[0], sort: 'output' }, { vertex: concl, sort: 'input' }));
        const errors = await olorin.wireErrors();
        expect(errors.length).toBe(1);
        expect(errors[0].length).toBeGreaterThan(0);
    });
});

test.describe('The wire-error tooltip', () => {
    // Set up the mismatched-wire level used by every test here, and return its Olorin.
    async function mismatchedWire(page) {
        const olorin = new Olorin(page);
        await olorin.open();
        await mistake(olorin, { parameters: 'P : Type\nQ : Type', hypotheses: 'P', conclusion: 'Q' },
            async (o, hyps, concl) =>
                o.connect({ vertex: hyps[0], sort: 'output' }, { vertex: concl, sort: 'input' }));
        return olorin;
    }

    test('appears over the wire and goes away again', async ({ page }) => {
        const olorin = await mismatchedWire(page);
        expect(await olorin.wireTooltip()).toBeNull();
        await olorin.hoverWire(0.25);
        expect(await olorin.wireTooltip()).toContain('This wire carries a proof of');
        await olorin.unhoverWire();
        expect(await olorin.wireTooltip()).toBeNull();
    });

    // The wire's type label sits at its midpoint, right where you'd aim, so it has to let the
    // pointer through to the wire underneath.
    test('appears at the middle of the wire, where the label is', async ({ page }) => {
        const olorin = await mismatchedWire(page);
        await olorin.hoverWire(0.5);
        expect(await olorin.wireTooltip()).toContain('This wire carries a proof of');
    });

    test('a wire that is not in error has no tooltip', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // P |- P, correctly wired: the proof is complete, so nothing is red.
        await mistake(olorin, { parameters: 'P : Type', hypotheses: 'P', conclusion: 'P' },
            async (o, hyps, concl) =>
                o.connect({ vertex: hyps[0], sort: 'output' }, { vertex: concl, sort: 'input' }));
        expect(await olorin.isComplete()).toBe(true);
        await olorin.hoverWire(0.5);
        expect(await olorin.wireTooltip()).toBeNull();
    });

    test('the explanation is replaced when the error changes', async ({ page }) => {
        const olorin = await mismatchedWire(page);
        await olorin.hoverWire(0.25);
        expect(await olorin.wireTooltip()).toContain('This wire carries a proof of');
        await olorin.unhoverWire();
        // Re-state the level so the same wiring is now an algebra failure instead.
        await mistake(olorin, { variables: 'x ∈ ℝ', conclusion: 'x·x=x' }, toConclusion('alg'));
        await olorin.hoverWire(0.25);
        expect(await olorin.wireTooltip()).toContain('algebra block');
    });
});
