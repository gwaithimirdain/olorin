// The "natE" block: proof by cases on a natural number n.  It is a "Match" rule (bin/rules.ml), so
// rather than handing out an equation to wire up, it refines the goal and the context of each
// branch: where the discriminee is a variable, the upper case proves the goal with 0 written in
// place of n, and the lower one binds a natural number k on a value port and proves the goal with
// k+1 written there.  The equations that refinement stands for are written on the block itself
// (the ".caselabel" divs), since that is the only place they appear.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// Drop a rule that binds a variable, naming it in the dialog it pops.
async function dragBinder(olorin, rule, x, y, name) {
    const id = await olorin.dragRule(rule, x, y);
    await olorin.page.waitForSelector('#variableBG', { state: 'visible' });
    await olorin.page.fill('#newvar', name);
    await olorin.page.click('#submitVariable');
    await olorin.dismissHints();
    return id;
}

// The type labels currently shown on unconnected output and assumption ports.
function portLabels(olorin) {
    return olorin.page.evaluate(() => Array.from(document.querySelectorAll(
        '#canvas .upperOutputLabel, #canvas .middleOutputLabel, #canvas .lowerOutputLabel'))
        .map((e) => e.innerText));
}

// The equations written on the cases of the blocks on the canvas.
function caseLabels(olorin) {
    return olorin.page.evaluate(() => Array.from(document.querySelectorAll('#canvas .caselabel'))
        .map((e) => e.innerText).filter((t) => t !== ''));
}

// State that n is 0 or a successor, and prove it by cases on n.  Each case's goal is the
// disjunction with the case's own value of n written into it: the upper case proves 0=0 and the
// lower one produces j as the k it needs, so each is a different half of the disjunction.  With
// `swapped`, each case's proof is wired into the other case's subgoal instead.  Report whether
// Olorin accepted it.
async function casesProves(olorin, { swapped = false } = {}) {
    await olorin.buildCustom({
        parameters: '',
        variables: 'n ∈ ℕ',
        hypotheses: '',
        conclusion: '(n=0)∨(∃k∈ℕ,(n=k+1))',
    });
    const cases = await dragBinder(olorin, 'natE', 250, 100, 'j');
    const zeroalg = await olorin.dragRule('alg', 700, 60);
    const left = await olorin.dragRule('orI1', 500, 60);
    const sucalg = await olorin.dragRule('alg', 700, 300);
    const intro = await olorin.dragRule('exI', 450, 300);
    const right = await olorin.dragRule('orI2', 550, 300);
    const nodes = await olorin.nodes();
    const varn = nodes.find((v) => v.rule === 'variable' && v.name === 'n').id;
    const concl = nodes.find((n) => n.rule === 'conclusion').id;
    await olorin.connect({ vertex: varn, sort: 'output' }, { vertex: cases, sort: 'input' });
    // The 0 case: 0=0, which is the left half.
    await olorin.connect({ vertex: zeroalg, sort: 'output' }, { vertex: left, sort: 'input', label: 'left' });
    // The successor case: j is the k that j+1 is one more than, and j+1=j+1 is what it takes.
    await olorin.connect({ vertex: cases, sort: 'assumption', label: 'pred' },
                         { vertex: intro, sort: 'input', label: 'element' });
    await olorin.connect({ vertex: sucalg, sort: 'output' }, { vertex: intro, sort: 'input', label: 'property' });
    await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: right, sort: 'input', label: 'right' });
    await olorin.connect({ vertex: left, sort: 'output' },
                         { vertex: cases, sort: 'subgoal', label: swapped ? 'suc' : 'zero' });
    await olorin.connect({ vertex: right, sort: 'output' },
                         { vertex: cases, sort: 'subgoal', label: swapped ? 'zero' : 'suc' });
    await olorin.connect({ vertex: cases, sort: 'output' }, { vertex: concl, sort: 'input' });
    await olorin.waitForTypecheck();
    return olorin.isComplete();
}

test.describe('The "natE" block', () => {
    test('proves the goal by proving it for 0 and for a successor', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await casesProves(olorin)).toBe(true);
    });

    // Each case proves its own refinement of the goal, and the successor case's proof uses a
    // variable the 0 case doesn't have, so neither proof is any good for the other case.
    test('keeps each case to its own goal and assumptions', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await casesProves(olorin, { swapped: true })).toBe(false);
    });

    // What the refinement writes into a branch is the "suc" constructor, and the arithmetic has to
    // read it as the number it is wherever it lands -- including inside an exponent, where a power
    // of it is only a power of m+1 if the exponent normalizes to m+1 (see poly_form in
    // bin/oracle.ml).  Without that, 2^n refined to 2^(m+1) is a power of something opaque, with
    // nothing to do with the 2^m the same branch is talking about.
    test('refines an exponent into arithmetic the algebra block can use', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'n ∈ ℕ', hypotheses: '',
            conclusion: '(n=0)∨(∃k∈ℕ,(2^n=2·2^k))',
        });
        const cases = await dragBinder(olorin, 'natE', 250, 100, 'm');
        const zeroalg = await olorin.dragRule('alg', 700, 60);
        const left = await olorin.dragRule('orI1', 500, 60);
        const sucalg = await olorin.dragRule('alg', 700, 300);
        const intro = await olorin.dragRule('exI', 450, 300);
        const right = await olorin.dragRule('orI2', 550, 300);
        const nodes = await olorin.nodes();
        const varn = nodes.find((v) => v.rule === 'variable' && v.name === 'n').id;
        const concl = nodes.find((n) => n.rule === 'conclusion').id;
        await olorin.connect({ vertex: varn, sort: 'output' }, { vertex: cases, sort: 'input' });
        await olorin.connect({ vertex: zeroalg, sort: 'output' }, { vertex: left, sort: 'input', label: 'left' });
        await olorin.connect({ vertex: left, sort: 'output' }, { vertex: cases, sort: 'subgoal', label: 'zero' });
        await olorin.connect({ vertex: cases, sort: 'assumption', label: 'pred' },
                             { vertex: intro, sort: 'input', label: 'element' });
        // 2^(m+1) = 2·2^m, which is the whole point: both sides are powers of the same base at
        // exponents the arithmetic can tell apart by one.
        await olorin.connect({ vertex: sucalg, sort: 'output' }, { vertex: intro, sort: 'input', label: 'property' });
        await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: right, sort: 'input', label: 'right' });
        await olorin.connect({ vertex: right, sort: 'output' }, { vertex: cases, sort: 'subgoal', label: 'suc' });
        await olorin.connect({ vertex: cases, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
    });

    test('writes the equation each case stands for on the block', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: '', variables: 'n ∈ ℕ', hypotheses: '', conclusion: 'n≥0',
        });
        const cases = await dragBinder(olorin, 'natE', 250, 100, 'j');
        const nodes = await olorin.nodes();
        const varn = nodes.find((v) => v.rule === 'variable' && v.name === 'n').id;
        const concl = nodes.find((n) => n.rule === 'conclusion').id;
        await olorin.connect({ vertex: varn, sort: 'output' }, { vertex: cases, sort: 'input' });
        await olorin.connect({ vertex: cases, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await caseLabels(olorin)).toEqual(['n=0', 'n=j+1']);
        expect(await portLabels(olorin)).toEqual(expect.arrayContaining(['j ∈ ℕ']));
    });
});
