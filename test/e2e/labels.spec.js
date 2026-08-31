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
