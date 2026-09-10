// The introduction block for a connective wired straight into the elimination block for the same
// one: "prove ⇒" into "use ⇒", "prove and" into "use and".
//
// Root cause of the bug this covers: ⇒ and ∧ are records for Narya's internals, so those pairs of
// blocks build a *record redex* -- (implies ≔ x ↦ M) .implies N -- and Narya can't typecheck one,
// since projecting a field needs the record to synthesize and a tuple never does.  The wire between
// them came out red, and the proof only went through with a label block in between.  Olorin now
// takes that projection itself, leaving the plain redex (x ↦ M) N that Narya does synthesize.
//
// Nothing determines the record type P⇒Q the wire carries, though, so Narya still gives that one
// wire no label of its own.  It takes its port's label instead, when the port has one -- which it
// does exactly when the same output is also wired somewhere that checks it.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

test.describe('A connective introduced and immediately eliminated', () => {
    test('"prove ⇒" into "use ⇒" needs no label block', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // P |- P, proved the long way round: build the identity P⇒P and apply it to the hypothesis.
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: 'P', conclusion: 'P' });
        const impI = await olorin.dragRule('impI', 300, 200);
        const impE = await olorin.dragRule('impE', 650, 250);
        await olorin.connect({ vertex: impI, sort: 'assumption' }, { vertex: impI, sort: 'subgoal' });
        await olorin.connect({ vertex: impI, sort: 'output' }, { vertex: impE, sort: 'input', label: 'implication' });
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: impE, sort: 'input', label: 'antecedent' });
        await olorin.connect({ vertex: impE, sort: 'output' }, { vertex: 'concl0', sort: 'input' });

        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.wireErrors()).toEqual([]);
        // The redex wire is the one wire with no label: nothing here determines the record type
        // P⇒P it carries, and its port has no label of its own to lend it either.
        expect((await olorin.labelRects()).map((l) => l.text)).toEqual(['P', 'P', 'P']);
    });

    test('...and the wire takes its label from its port when the port has one', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // The same identity P⇒P, used twice: once as the argument of a "use ⇒" -- a checking
        // position, which is what gives its port the label P⇒P -- and once as the implication of
        // another, which is the redex.
        await olorin.buildCustom({
            parameters: 'P : Type\nQ : Type',
            hypotheses: 'P\n(P⇒P)⇒Q',
            conclusion: 'Q∧P',
        });
        const impI = await olorin.dragRule('impI', 300, 150);
        const useQ = await olorin.dragRule('impE', 620, 120);
        const useP = await olorin.dragRule('impE', 620, 400);
        const andI = await olorin.dragRule('andI', 900, 250);
        await olorin.connect({ vertex: impI, sort: 'assumption' }, { vertex: impI, sort: 'subgoal' });
        await olorin.connect({ vertex: 'hyp1', sort: 'output' }, { vertex: useQ, sort: 'input', label: 'implication' });
        await olorin.connect({ vertex: impI, sort: 'output' }, { vertex: useQ, sort: 'input', label: 'antecedent' });
        await olorin.connect({ vertex: impI, sort: 'output' }, { vertex: useP, sort: 'input', label: 'implication' });
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: useP, sort: 'input', label: 'antecedent' });
        await olorin.connect({ vertex: useQ, sort: 'output' }, { vertex: andI, sort: 'input', label: 'fst' });
        await olorin.connect({ vertex: useP, sort: 'output' }, { vertex: andI, sort: 'input', label: 'snd' });
        await olorin.connect({ vertex: andI, sort: 'output' }, { vertex: 'concl0', sort: 'input' });

        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.wireErrors()).toEqual([]);
        // All eight wires are labeled, the redex one included: both wires out of the "prove ⇒"
        // block say P⇒P, the second of them by taking it from the port.
        const labels = (await olorin.labelRects()).map((l) => l.text);
        expect(labels).toHaveLength(8);
        expect(labels.filter((l) => l === 'P⇒P')).toHaveLength(2);
    });

    test('"prove and" into "use and" needs no label block either', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({ parameters: 'P : Type\nQ : Type', hypotheses: 'P\nQ', conclusion: 'P' });
        const andI = await olorin.dragRule('andI', 350, 250);
        const andE = await olorin.dragRule('andE', 650, 250);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: andI, sort: 'input', label: 'fst' });
        await olorin.connect({ vertex: 'hyp1', sort: 'output' }, { vertex: andI, sort: 'input', label: 'snd' });
        await olorin.connect({ vertex: andI, sort: 'output' }, { vertex: andE, sort: 'input' });
        await olorin.connect({ vertex: andE, sort: 'output', label: 'fst' }, { vertex: 'concl0', sort: 'input' });

        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.wireErrors()).toEqual([]);
    });
});
