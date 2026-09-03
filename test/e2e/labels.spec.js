// Regression test for wire labels disappearing from the rest of the diagram as soon as an
// incomplete box is wired to the conclusion.
//
// Root cause: checking the term connected to the conclusion and synthesizing the disconnected
// fragments shared one Reporter handler, so a fatal error from the conclusion's term (here an orE
// box with nothing connected to its input: "non-synthesizing term in synthesizing position") jumped
// straight out of the check, before the pass that labels everything not connected to the goal.
// Checking the conclusion now catches its own fatal, so the labeling pass still runs.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// A partial proof: an integral/alg/expr fragment on the left, feeding nothing, plus an empty orE
// box wired to the conclusion.
const STATE = {
    level: {
        parameters: [],
        variables: [{ name: 'x', ty: 'ℚ' }, { name: 'y', ty: 'ℚ' }],
        hypotheses: [{ ty: '(x=3*y)∧(1−x=4*y)' }],
        conclusion: { ty: '(x=3/7) ∧ (y=1/7)' },
    },
    complete: false,
    difficulty: 0,
    nodes: [
        { id: 'var2', rule: 'variable', left: '50px', top: '10px', name: 'x', value: 'ℚ' },
        { id: 'var3', rule: 'variable', left: '50px', top: '62px', name: 'y', value: 'ℚ' },
        { id: 'hyp1', rule: 'hypothesis', left: '50px', top: '526px', value: '(x=3*y)∧(1−x=4*y)' },
        { id: 'concl1', rule: 'conclusion', left: '1383px', top: '449px', value: '(x=3/7) ∧ (y=1/7)' },
        { id: 'rule0', rule: 'integral', left: '515px', top: '385px' },
        { id: 'rule1', rule: 'alg', left: '359px', top: '590px' },
        { id: 'rule2', rule: 'expr', left: '274px', top: '392px', value: 'x−1', width: 'fit-content' },
        { id: 'rule3', rule: 'orE', left: '689px', top: '476px', width: '276px', height: '80px' },
    ],
    connections: [
        { source: { vertex: 'var2', sort: 'output' }, target: { vertex: 'rule0', sort: 'input', label: 'x' } },
        { source: { vertex: 'rule2', sort: 'output' }, target: { vertex: 'rule0', sort: 'input', label: 'y' } },
        { source: { vertex: 'var2', sort: 'output' }, target: { vertex: 'rule2', sort: 'input' } },
        { source: { vertex: 'rule1', sort: 'output' }, target: { vertex: 'rule0', sort: 'input', label: 'xy0' } },
        { source: { vertex: 'hyp1', sort: 'output' }, target: { vertex: 'rule1', sort: 'input' } },
        { source: { vertex: 'rule3', sort: 'output' }, target: { vertex: 'concl1', sort: 'input' } },
    ],
};

// The wire labels currently drawn, with whitespace squashed so they're easy to match.
function wireLabels(page) {
    return page.evaluate(() =>
        Array.from(document.querySelectorAll('.connLabel')).map((e) => (e.innerText || '').replace(/\s+/g, '')));
}

test.describe('Wire labels', () => {
    test('an incomplete box wired to the conclusion still leaves the rest labeled', async ({ page }) => {
        test.setTimeout(60000);
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            variables: 'x ∈ ℚ\ny ∈ ℚ',
            hypotheses: '(x=3*y)∧(1−x=4*y)',
            conclusion: '(x=3/7) ∧ (y=1/7)',
        });
        await olorin.restore(STATE);

        // The wires of the disconnected fragment keep their labels, alongside the goal's own wire.
        await expect.poll(() => wireLabels(page), { timeout: 20000 }).toEqual(
            expect.arrayContaining(['x∈ℚ', '(x=3*y)∧(1−x=4*y)', 'x−1∈ℚ', 'x*(x−1)=0', '(x=3/7)∧(y=1/7)']));

        // Removing the wire into the conclusion leaves the fragment labeled just the same.
        const detached = JSON.parse(JSON.stringify(STATE));
        detached.connections = detached.connections.filter((c) => c.target.vertex !== 'concl1');
        await olorin.restore(detached);
        await expect.poll(() => wireLabels(page), { timeout: 20000 }).toEqual(
            expect.arrayContaining(['x∈ℚ', '(x=3*y)∧(1−x=4*y)', 'x−1∈ℚ', 'x*(x−1)=0']));
    });
});

// Wire labels are drawn in the middle of their wire, so wires that run close together used to end
// up with their labels stacked on top of each other, unreadable.  Colliding labels now slide along
// their own wire until they're clear.
test.describe('Overlapping labels', () => {
    test('a port fanning out to two nearby inputs keeps its labels apart', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        // P |- P∧P, proved by wiring the one hypothesis into both inputs of an andI box: two wires
        // a couple of dozen pixels apart, whose midpoints (and labels) all but coincide.
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: 'P', conclusion: 'P∧P' });
        const andI = await olorin.dragRule('andI', 450, 250);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: andI, sort: 'input', label: 'fst' });
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: andI, sort: 'input', label: 'snd' });
        await olorin.connect({ vertex: andI, sort: 'output' }, { vertex: 'concl0', sort: 'input' });

        expect(await olorin.labelRects()).toHaveLength(3); // both wires are still labeled
        expect(await olorin.overlappingLabels()).toEqual([]);
        // The boxes and the port labels can't move, so labels keep off them too.
        expect(await olorin.overlappingObstacles()).toEqual([]);

        // ...and they stay apart when the box moves.
        await olorin.dragNode(andI, -120, 90);
        expect(await olorin.overlappingLabels()).toEqual([]);

        // ...and with curved wires, whose midpoints sit elsewhere again.
        await olorin.setConnectorStyle('curved');
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: andI, sort: 'input', label: 'fst' });
        expect(await olorin.overlappingLabels()).toEqual([]);
    });

    test('a box dropped where a label sits pushes the label off it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: 'P', conclusion: 'P' });
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        const before = (await olorin.labelRects())[0];

        // Drop an unrelated box right on top of that label.
        const origin = await page.evaluate(() => {
            const r = document.getElementById('diagram').getBoundingClientRect();
            return { x: r.x, y: r.y };
        });
        await olorin.dragRule('andI', before.x - origin.x - 10, before.y - origin.y - 10);

        // The box can't move, so the label slid along its wire to somewhere clear of it.
        expect(await olorin.overlappingObstacles()).toEqual([]);
        expect((await olorin.labelRects())[0].x).not.toBeCloseTo(before.x, 0);
    });

    test('the labels of a cluttered proof do not collide', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            variables: 'x ∈ ℚ\ny ∈ ℚ',
            hypotheses: '(x=3*y)∧(1−x=4*y)',
            conclusion: '(x=3/7) ∧ (y=1/7)',
        });
        await olorin.restore(STATE);
        // Six wires carry a type, and one of them is a type mismatch showing both of its types.
        await expect.poll(() => wireLabels(page), { timeout: 20000 })
            .toEqual(expect.arrayContaining(['x∈ℚ', '(x=3*y)∧(1−x=4*y)', 'x−1∈ℚ', 'x*(x−1)=0']));
        expect((await olorin.labelRects()).length).toBeGreaterThanOrEqual(6);
        expect(await olorin.overlappingLabels()).toEqual([]);
        expect(await olorin.overlappingObstacles()).toEqual([]);
    });
});

// A wire whose ends disagree about the type is drawn red; at novice it also says what the two
// types are, each written at its own end of the wire.
// A value port shows "? ∈ <set>" while it's empty.  For the ∧-elimination-style boxes the set
// comes from the goal and is real, but the "integral" box picks its number system with an SFirst
// over ℤ, ℚ, ℝ and 𝕊, and with these ports empty that resolves to whichever goes through first --
// never the set the player is actually working in.  So it says the set is unknown as well.
test.describe('A value port whose set is not yet determined', () => {
    async function integralPorts(page, conclusion) {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'a ∈ ℝ\nb ∈ ℝ', hypotheses: 'a*b=0', conclusion,
        });
        const nodes = await olorin.nodes();
        const concl = nodes.find((n) => n.rule === 'conclusion').id;
        const box = await olorin.dragRule('integral', 300, 150);
        await olorin.connect({ vertex: box, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        const ports = await page.evaluate(() => window.__olorin.ports());
        return ['x', 'y'].map((l) =>
            (ports.find((p) => p.vertex === box && p.sort === 'input' && p.label === l) || {}).type);
    }

    test('the integral box leaves the set open on its empty value inputs', async ({ page }) => {
        expect(await integralPorts(page, '(a=0)∨(b=0)')).toEqual(['? ∈ ?', '? ∈ ?']);
    });
});

test.describe('Type-mismatch labels', () => {
    // How many wires are drawn in the error color.
    const redWires = (page) => page.evaluate(() =>
        Array.from(document.querySelectorAll('#canvas svg path'))
            .filter((p) => p.getAttribute('stroke') === '#ff0000').length);

    async function mismatchLevel(olorin) {
        // P∧Q, Q |- P: wiring either hypothesis straight to the goal is a type error.
        await olorin.buildCustom({ parameters: 'P : Type\nQ : Type', hypotheses: 'P∧Q\nQ', conclusion: 'P' });
    }

    test('a red wire is labeled with both types, one at each end', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await mismatchLevel(olorin);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });

        await expect.poll(() => redWires(page)).toBeGreaterThan(0);
        const labels = await olorin.labelRects();
        expect(labels.map((l) => l.text).sort()).toEqual(['P', 'P∧Q']);
        expect(labels.every((l) => l.mismatch)).toBe(true);
        // The type coming out of the hypothesis is written nearer the hypothesis, the one the goal
        // wanted nearer the goal (the hypothesis is on the left, the conclusion on the right).
        const got = labels.find((l) => l.text === 'P∧Q');
        const expected = labels.find((l) => l.text === 'P');
        expect(got.x).toBeLessThan(expected.x);
    });

    test('the labels go away once the wire typechecks', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await mismatchLevel(olorin);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await expect.poll(async () => (await olorin.labelRects()).length).toBe(2);

        // Take the P out of the P∧Q with an andE box, which is the proof the level wants.
        // (Clearing rebuilds the level's fixed nodes, so their ids are fresh.)
        await olorin.clear();
        const fixed = await olorin.nodes();
        const hyp = fixed.find((n) => n.rule === 'hypothesis').id;
        const concl = fixed.find((n) => n.rule === 'conclusion').id;
        const andE = await olorin.dragRule('andE', 450, 250);
        await olorin.connect({ vertex: hyp, sort: 'output' }, { vertex: andE, sort: 'input' });
        await olorin.connect({ vertex: andE, sort: 'output', label: 'fst' }, { vertex: concl, sort: 'input' });

        expect(await olorin.isComplete()).toBe(true);
        expect(await redWires(page)).toBe(0);
        expect((await olorin.labelRects()).some((l) => l.mismatch)).toBe(false);
    });

    test('above novice the wire is red but the types are not spelled out', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed([['difficulty', '1']]); // adept
        await olorin.open();
        await mismatchLevel(olorin);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });

        await expect.poll(() => redWires(page)).toBeGreaterThan(0);
        expect((await olorin.labelRects()).some((l) => l.mismatch)).toBe(false);
    });
});
