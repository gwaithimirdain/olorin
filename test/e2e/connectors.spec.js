// A saved proof should remember each wire's connector style (angled vs curved), not just apply
// the current global default on restore.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { conjunctionLevel } = require('../lib/levels');

// P, Q |- P∧Q, in a stage with the ∧ rules: two hypotheses, one conclusion, and both
// andI and andE in the palette.  Selected from levels.js so a renumbering can't break it.
const LEVEL = conjunctionLevel();

// Map each connection to its connector type, keyed by its target port (label, or sort).
const styles = (state) => Object.fromEntries(
    state.connections.map((c) => [c.target.label || c.target.sort, c.connector]),
);

test.describe('Connector styles', () => {
    test('saved proofs remember angled vs curved wires', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);
        const andId = await olorin.dragRule('andI', 500, 250);

        // First wire angled, the other two curved.
        await olorin.setConnectorStyle('angle');
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: andId, sort: 'input', label: 'fst' });
        await olorin.setConnectorStyle('curved');
        await olorin.connect({ vertex: 'hyp1', sort: 'output' }, { vertex: andId, sort: 'input', label: 'snd' });
        await olorin.connect({ vertex: andId, sort: 'output' }, { vertex: 'concl0', sort: 'input' });

        const state = await olorin.serialize();
        expect(styles(state)).toEqual({ fst: 'Flowchart', snd: 'Bezier', input: 'Bezier' });

        // Restore: the per-wire styles survive even though the global default is now curved.
        await olorin.restore(state);
        expect(styles(await olorin.serialize())).toEqual({ fst: 'Flowchart', snd: 'Bezier', input: 'Bezier' });
    });
});
