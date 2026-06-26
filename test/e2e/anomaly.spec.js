// Regression test for an "anomaly: undefined metavariable" reported in the console (and a
// fragment's ports/wire left unlabeled) when a proof has two independent disconnected fragments
// that each introduce a variable via existential elimination (exE).
//
// Root cause: each speculative typecheck of a disconnected port ran in its own History.do_command,
// whose failure path deletes the holes that attempt created -- but a sibling fragment already
// depended on one of those holes, so it became a dangling metavariable reference.  The fix runs the
// whole check under a single do_command so a caught fatal no longer prunes shared holes.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// A partial proof with two parallel allE -> exE chains, both disconnected from the conclusion.
const STATE = {
    level: {
        parameters: [
            { name: 'A', ty: 'Type' }, { name: 'B', ty: 'Type' }, { name: 'C', ty: 'Type' },
            { name: 'P', ty: 'A×B→Type' }, { name: 'Q', ty: 'B×C→Type' }, { name: 'R', ty: 'A×C→Type' },
        ],
        variables: [],
        hypotheses: [
            { ty: '∀x∈A,∃y∈B,P(x,y)' }, { ty: '∀y∈B,∃z∈C,Q(y,z)' },
            { ty: '∀x∈A,∀y∈B,∀z∈C,((P(x,y)∧Q(y,z))⇒R(x,z))' },
        ],
        conclusion: { ty: '∀x∈A,∃z∈C,R(x,z)' },
    },
    complete: false,
    difficulty: 0,
    nodes: [
        { id: 'hyp7', rule: 'hypothesis', left: '42px', top: '58px', value: '∀x∈A,∃y∈B,P(x,y)' },
        { id: 'hyp8', rule: 'hypothesis', left: '59px', top: '289px', value: '∀y∈B,∃z∈C,Q(y,z)' },
        { id: 'hyp9', rule: 'hypothesis', left: '43px', top: '502px', value: '∀x∈A,∀y∈B,∀z∈C,((P(x,y)∧Q(y,z))⇒R(x,z))' },
        { id: 'concl7', rule: 'conclusion', left: '1286px', top: '458px', value: '∀x∈A,∃z∈C,R(x,z)' },
        { id: 'rule10', rule: 'allE', left: '508px', top: '64px' },
        { id: 'rule11', rule: 'exE', left: '785px', top: '63px', name: 'a', variable: 'a' },
        { id: 'rule12', rule: 'allE', left: '487px', top: '312px' },
        { id: 'rule13', rule: 'exE', left: '754px', top: '349px', name: 'x', variable: 'x' },
    ],
    connections: [
        { source: { vertex: 'hyp7', sort: 'output' }, target: { vertex: 'rule10', sort: 'input', label: 'universal' } },
        { source: { vertex: 'rule10', sort: 'output' }, target: { vertex: 'rule11', sort: 'input' } },
        { source: { vertex: 'hyp8', sort: 'output' }, target: { vertex: 'rule12', sort: 'input', label: 'universal' } },
        { source: { vertex: 'rule12', sort: 'output' }, target: { vertex: 'rule13', sort: 'input' } },
    ],
};

test('two disconnected exE fragments: no anomaly, and both get labeled', async ({ page }) => {
    test.setTimeout(60000);
    const errors = [];
    page.on('console', (m) => { if (/anomaly|undefined metavariable/i.test(m.text())) errors.push(m.text()); });

    const olorin = new Olorin(page);
    await olorin.open();

    // Build (and name, so it becomes a current level) a custom level matching the proof's context.
    await page.evaluate(() => {
        document.getElementById('selectLevel').click();
        document.getElementById('customLevel').click();
    });
    await page.fill('#customName', 'Anomaly');
    await page.fill('#parameters', 'A : Type\nB : Type\nC : Type\nP : A×B→Type\nQ : B×C→Type\nR : A×C→Type');
    await page.fill('#hypotheses', '∀x∈A,∃y∈B,P(x,y)\n∀y∈B,∃z∈C,Q(y,z)\n∀x∈A,∀y∈B,∀z∈C,((P(x,y)∧Q(y,z))⇒R(x,z))');
    await page.fill('#conclusion', '∀x∈A,∃z∈C,R(x,z)');
    await page.click('#submitLevel');
    await olorin.dismissHints();

    await page.evaluate((s) => window.__olorin.restore(s), STATE);
    await page.waitForTimeout(300);

    expect(errors).toEqual([]);

    // Both fragments should be labeled.  The witness of each exE labels its property output with the
    // existential body instantiated at that witness: P(?,a) for the "a" fragment, Q(?,x) for "x".
    const labels = await page.evaluate(() =>
        Array.from(document.querySelectorAll('#canvas .connLabel, #canvas .jtk-overlay'))
            .map((e) => (e.innerText || '').replace(/\s+/g, '')));
    expect(labels.some((t) => t.includes('P(?,a)'))).toBe(true);
    expect(labels.some((t) => t.includes('Q(?,x)'))).toBe(true);
});
