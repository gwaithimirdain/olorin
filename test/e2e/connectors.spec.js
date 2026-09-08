// A saved proof should remember each wire's connector style (angled vs curved), not just apply
// the current global default on restore.  A wire that runs from a block's own assumption to its
// own subgoal is drawn straight instead, whatever that default is, since the flowchart connector
// takes such a wire out around the block.

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

// Which connector each wire got, as [source label or sort] -> connector.  A subgoal port takes a
// single wire, so each block below carries just the one being asked about.
const connectors = (state) => state.connections.map((c) => c.connector);

test.describe('A wire from an assumption to its own block\'s subgoal', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
        // A custom level, whose palette holds every rule.
        await olorin.buildCustom({ parameters: 'P : Type', variables: '', hypotheses: 'P', conclusion: 'P' });
    });

    // Drop a block that binds a variable, naming it in the dialog it pops.
    async function dragBinder(page, rule, x, y, name) {
        const id = await olorin.dragRule(rule, x, y);
        await page.waitForSelector('#variableBG', { state: 'visible' });
        await page.fill('#newvar', name);
        await page.click('#submitVariable');
        await olorin.dismissHints();
        return id;
    }

    test('is drawn straight when the block has a single, unlabelled subgoal', async () => {
        const impI = await olorin.dragRule('impI', 300, 100);
        await olorin.connect({ vertex: impI, sort: 'assumption' }, { vertex: impI, sort: 'subgoal' });
        expect(connectors(await olorin.serialize())).toEqual(['Straight']);
    });

    test('is drawn straight from the condition port of a ∀x∈[n] block too', async ({ page }) => {
        // That port has a label of its own ("below"), while the subgoal it reaches has none, so
        // matching the two labels isn't what says they belong together.
        const allI = await dragBinder(page, 'allbelowI', 300, 100, 'z');
        await olorin.connect({ vertex: allI, sort: 'assumption', label: 'below' }, { vertex: allI, sort: 'subgoal' });
        expect(connectors(await olorin.serialize())).toEqual(['Straight']);
    });

    test('and from the condition port of a ∀x∈ℝ₊ block', async ({ page }) => {
        const allI = await dragBinder(page, 'allposI', 300, 100, 'z');
        await olorin.connect({ vertex: allI, sort: 'assumption', label: 'positive' }, { vertex: allI, sort: 'subgoal' });
        expect(connectors(await olorin.serialize())).toEqual(['Straight']);
    });

    test('but not when it reaches the subgoal of another branch', async () => {
        // ∨-elimination has a subgoal per branch, each labelled, and an assumption only belongs to
        // its own; a wire across to the other one is ill-typed and stays a flowchart wire.
        const orE = await olorin.dragRule('orE', 300, 100);
        await olorin.connect({ vertex: orE, sort: 'assumption', label: 'left' }, { vertex: orE, sort: 'subgoal', label: 'right' });
        expect(connectors(await olorin.serialize())).toEqual(['Flowchart']);
    });

    test('and its own branch\'s subgoal still is', async () => {
        const orE = await olorin.dragRule('orE', 300, 100);
        await olorin.connect({ vertex: orE, sort: 'assumption', label: 'left' }, { vertex: orE, sort: 'subgoal', label: 'left' });
        expect(connectors(await olorin.serialize())).toEqual(['Straight']);
    });
});
