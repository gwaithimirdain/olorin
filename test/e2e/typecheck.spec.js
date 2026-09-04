// Wiring faster than Z3 answers.
//
// A typecheck that needs the algebra block suspends in an OCaml continuation while it waits for
// Z3, and the answer comes back through a JavaScript promise.  Starting another typecheck in the
// meantime discontinues that suspended round, so the answer the promise eventually delivers
// belongs to nobody -- feeding it back in resumed the *new* round with the old round's answer,
// and left two chains driving one continuation, which ended in Continuation_already_resumed
// escaping into the connection handler and the "Typechecking..." overlay never coming down.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

test.describe('Wires connected faster than Z3 answers', () => {
    test('still settle on the right answer', async ({ page }) => {
        test.setTimeout(60000);
        const errors = [];
        page.on('console', (m) => { if (/fire failed/.test(m.text())) errors.push(m.text()); });
        const olorin = new Olorin(page);
        await olorin.open();
        // ⊥ from ¬(x=1) and an algebra proof of x=1: every wire added changes what the algebra
        // block is asked, so each one starts a Z3 query the next one interrupts.
        await olorin.buildCustom({
            parameters: '',
            variables: 'x ∈ ℤ',
            hypotheses: '¬(x=1)\nx+0=1',
            conclusion: '⊥',
        });
        const alg = await olorin.dragRule('algebra', 300, 300);
        const negE = await olorin.dragRule('negE', 600, 200);
        const nodes = await olorin.nodes();
        const hyps = nodes.filter((n) => n.rule === 'hypothesis');
        // No waiting between these on purpose: that is the race.
        await olorin.connect({ vertex: hyps[1].id, sort: 'output' }, { vertex: alg, sort: 'input' });
        await olorin.connect({ vertex: hyps[0].id, sort: 'output' }, { vertex: negE, sort: 'input', label: 'negation' });
        await olorin.connect({ vertex: alg, sort: 'output' }, { vertex: negE, sort: 'input', label: 'statement' });
        await olorin.connect({ vertex: negE, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });

        await olorin.waitForTypecheck();
        expect(errors).toEqual([]);
        expect(await olorin.isComplete()).toBe(true);
    });
});
