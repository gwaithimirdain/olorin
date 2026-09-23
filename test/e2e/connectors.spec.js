// A saved proof should remember each wire's connector style (angled vs curved), not just apply
// the current global default on restore.  A wire that runs from a block's own assumption to its
// own subgoal is drawn straight instead, whatever that default is, since the flowchart connector
// takes such a wire out around the block.  A wire from a block back to itself is forced angled
// only when it runs backwards -- to a port left of the one it started at -- since that is the
// shape a curved connector can't draw without looping over the block.

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

// The shape the one wire on screen is really drawn in: how wide its SVG is, and how far apart the
// two ports it joins are.  jsPlumb's loopback circle is a fixed 50px across wherever the ports
// are, while a wire drawn between them covers the distance from one to the other.
const drawnShape = (page) => page.evaluate(() => {
    const svg = Array.from(document.querySelectorAll('.jtk-connector')).find((s) => s.jtk && s.jtk.connector);
    const conn = svg.jtk.connector.connection;
    const x = (i) => conn.instance.router.getEndpointLocation(conn.endpoints[i]).curX;
    return { drawnWidth: svg.getBoundingClientRect().width, portGap: Math.abs(x(1) - x(0)) };
});

// Whether that wire spans its ports rather than curling up at one of them.
function expectDrawnBetweenPorts(drawn) {
    expect(drawn.portGap).toBeGreaterThan(100);
    expect(drawn.drawnWidth).toBeGreaterThan(drawn.portGap * 0.8);
}

test.describe('A wire from a block back to itself', () => {
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

    test('is drawn straight from the condition port of a ∀ block too', async ({ page }) => {
        // That port has a label of its own ("condition"), while the subgoal it reaches has none, so
        // matching the two labels isn't what says they belong together.
        const allI = await dragBinder(page, 'allI', 300, 100, 'z');
        await olorin.connect({ vertex: allI, sort: 'assumption', label: 'condition' }, { vertex: allI, sort: 'subgoal' });
        expect(connectors(await olorin.serialize())).toEqual(['Straight']);
    });

    test('but not when it reaches the subgoal of another branch', async () => {
        // ∨-elimination has a subgoal per branch, each labelled, and an assumption only belongs to
        // its own; a wire across to the other one is ill-typed, so it isn't straightened.  It still
        // runs forwards across the block, though, so it is drawn in whichever style is selected.
        const orE = await olorin.dragRule('orE', 300, 100);
        await olorin.connect({ vertex: orE, sort: 'assumption', label: 'left' }, { vertex: orE, sort: 'subgoal', label: 'right' });
        expect(connectors(await olorin.serialize())).toEqual(['Flowchart']);

        await olorin.setConnectorStyle('curved');
        const orE2 = await olorin.dragRule('orE', 300, 400);
        await olorin.connect({ vertex: orE2, sort: 'assumption', label: 'left' }, { vertex: orE2, sort: 'subgoal', label: 'right' });
        expect(connectors(await olorin.serialize())).toEqual(['Flowchart', 'Bezier']);
    });

    // Left to itself, jsPlumb draws a curved wire that begins and ends on the same block as a
    // circle sitting on its source port: the loopback case reads only where the wire starts, so
    // the wire lands nowhere near the port it actually joins.  The connector is configured out of
    // that, and the wire's own type doesn't record it, so check the shape it is really drawn in.
    test('and the curved one is drawn between its two ports, not as a loopback circle', async ({ page }) => {
        await olorin.setConnectorStyle('curved');
        const orE = await olorin.dragRule('orE', 300, 100);
        await olorin.connect({ vertex: orE, sort: 'assumption', label: 'left' }, { vertex: orE, sort: 'subgoal', label: 'right' });
        expect(connectors(await olorin.serialize())).toEqual(['Bezier']);

        expectDrawnBetweenPorts(await drawnShape(page));
    });

    test('and its own branch\'s subgoal still is', async () => {
        const orE = await olorin.dragRule('orE', 300, 100);
        await olorin.connect({ vertex: orE, sort: 'assumption', label: 'left' }, { vertex: orE, sort: 'subgoal', label: 'left' });
        expect(connectors(await olorin.serialize())).toEqual(['Straight']);
    });

    // A saved proof records only a wire's connector *type*, and the bare Bezier type draws a wire
    // that begins and ends on the same block as a loopback circle sitting on its source port.  So
    // the shape such a wire needs wins over the style it was saved in: a proof saved before the
    // wire was drawn that way -- or saved after a load that lost it, which would otherwise keep the
    // loop for good -- comes back drawn across the block, not curled up at its own port.
    test('is drawn in the shape it needs even when the saved proof says otherwise', async ({ page }) => {
        const impI = await olorin.dragRule('impI', 300, 100);
        await olorin.connect({ vertex: impI, sort: 'assumption' }, { vertex: impI, sort: 'subgoal' });
        const state = await olorin.serialize();
        state.connections.forEach((c) => { c.connector = 'Bezier'; });

        await olorin.restore(state);
        expect(connectors(await olorin.serialize())).toEqual(['Straight']);
        expectDrawnBetweenPorts(await drawnShape(page));
    });

    // The one whose style *is* the player's choice keeps it, and keeps being drawn between its two
    // ports, even when the wires being drawn now are angled ones.
    test('keeps a saved curved one curved, and still not a loopback circle', async ({ page }) => {
        await olorin.setConnectorStyle('curved');
        const orE = await olorin.dragRule('orE', 300, 100);
        await olorin.connect({ vertex: orE, sort: 'assumption', label: 'left' }, { vertex: orE, sort: 'subgoal', label: 'right' });
        const state = await olorin.serialize();
        expect(connectors(state)).toEqual(['Bezier']);

        await olorin.setConnectorStyle('angle');
        await olorin.restore(state);
        expect(connectors(await olorin.serialize())).toEqual(['Bezier']);
        expectDrawnBetweenPorts(await drawnShape(page));
    });

    test('while one that runs backwards stays angled even when curved wires are selected', async () => {
        // ∧-elimination takes its input on the left and gives its outputs on the right, so wiring
        // one of those outputs back into its own input doubles the wire back over the block.
        await olorin.setConnectorStyle('curved');
        const andE = await olorin.dragRule('andE', 300, 100);
        await olorin.connect({ vertex: andE, sort: 'output', label: 'fst' }, { vertex: andE, sort: 'input' });
        expect(connectors(await olorin.serialize())).toEqual(['Flowchart']);
    });
});
