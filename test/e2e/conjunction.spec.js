// The two inputs of an ∧-introduction block.
//
// A conjunction's two halves are proved the same way whichever order they are written in, so the
// block takes its inputs in either order: a player who wires the proof of B to the "fst" port and
// the proof of A to the "snd" port, proving A∧B, still gets a proof.
//
// The natural reading is tried first, so it is the one that wins wherever both would work -- which
// includes any port still empty, since a hole checks against anything, and such a port has to go
// on showing the half it normally carries.  When neither reading works, it is the natural one's
// complaint that is reported, so the ports aren't asked for each other's halves.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// The types Olorin shows for every port, keyed by "vertex:label".
async function portTypes(page) {
    const ports = await page.evaluate(() => window.__olorin.ports());
    return Object.fromEntries(ports.map((p) => [p.vertex + ':' + (p.label || p.sort), p.type]));
}

// P and Q as hypotheses, P∧Q to prove: the one ∧-introduction has a hypothesis on each port, so
// which port each goes to is entirely the player's choice.
const buildLevel = (olorin) => olorin.buildCustom({
    parameters: 'P : Type\nQ : Type', variables: '',
    hypotheses: 'P\nQ', conclusion: 'P∧Q',
});

for (const [name, fstHyp, sndHyp] of [
    ['the way round the ports read', 0, 1],
    ['the other way round', 1, 0],
]) {
    test(`An ∧-introduction proves P∧Q with its inputs ${name}`, async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildLevel(olorin);
        const nodes = await olorin.nodes();
        const hyps = nodes.filter((n) => n.rule === 'hypothesis');   // 0: P   1: Q
        const andI = await olorin.dragRule('andI', 400, 300);
        await olorin.connect({ vertex: hyps[fstHyp].id, sort: 'output' },
                             { vertex: andI, sort: 'input', label: 'fst' });
        await olorin.connect({ vertex: hyps[sndHyp].id, sort: 'output' },
                             { vertex: andI, sort: 'input', label: 'snd' });
        await olorin.connect({ vertex: andI, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.wireErrors()).toEqual([]);
    });
}

test.describe('An ∧-introduction with one port still empty', () => {
    for (const [port, wanted, other, otherWanted] of [
        ['fst', 'P', 'snd', 'Q'],
        ['snd', 'Q', 'fst', 'P'],
    ]) {
        test(`labels the empty ${other} port with the half it carries (${port} wired)`, async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await buildLevel(olorin);
            const nodes = await olorin.nodes();
            const hyps = nodes.filter((n) => n.rule === 'hypothesis');
            const andI = await olorin.dragRule('andI', 400, 300);
            // The half that port normally carries, so the natural reading works and must win.
            await olorin.connect({ vertex: hyps[wanted === 'P' ? 0 : 1].id, sort: 'output' },
                                 { vertex: andI, sort: 'input', label: port });
            await olorin.connect({ vertex: andI, sort: 'output' },
                                 { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
            await olorin.waitForTypecheck();

            expect(await olorin.wireErrors()).toEqual([]);
            const types = await portTypes(page);
            expect(types[andI + ':' + port]).toBe(wanted);
            expect(types[andI + ':' + other]).toBe(otherWanted);
        });
    }
});

// Neither reading works: the natural one is run once more, committing, so the ports keep the
// halves they normally carry rather than being asked for each other's.
test('An ∧-introduction that proves neither way round keeps its own halves on its ports', async ({ page }) => {
    const olorin = new Olorin(page);
    await olorin.open();
    await olorin.buildCustom({
        parameters: 'P : Type\nQ : Type\nR : Type', variables: '',
        hypotheses: 'R', conclusion: 'P∧Q',
    });
    const nodes = await olorin.nodes();
    const hyp = nodes.find((n) => n.rule === 'hypothesis');
    const andI = await olorin.dragRule('andI', 400, 300);
    // R proves neither half, so neither reading works; the snd port is left empty, and a hole
    // checks against anything, so it is the reading that commits that labels it.
    await olorin.connect({ vertex: hyp.id, sort: 'output' }, { vertex: andI, sort: 'input', label: 'fst' });
    await olorin.connect({ vertex: andI, sort: 'output' },
                         { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
    await olorin.waitForTypecheck();

    expect(await olorin.isComplete()).toBe(false);
    expect((await olorin.diagnostics()).filter((d) => d.code.startsWith('E')).length).toBeGreaterThan(0);
    // The empty port is asked for the second half, not the first.
    expect((await portTypes(page))[andI + ':snd']).toBe('Q');
});
