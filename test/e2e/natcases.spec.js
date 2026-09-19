// The "natE" block: proof by cases on a natural number n.  It is a "User" rule (bin/rules.ml)
// applying the axiom ℕ.cases, whose conclusion is whatever the goal is -- the axiom takes that as
// an implicit first argument -- and whose two cases are brackets on the side of the block, like
// those of ∨-elimination: the upper one assumes n=0, and the lower one binds a natural number k on
// a value port and assumes n=k+1.  Each proves the same goal as the block itself.

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

// State that n is 0 or a successor, and prove it by cases on n: the n=0 case is the left half of
// the disjunction, and the other case is its right half, with the k and the n=k+1 that the block
// hands out going straight into an ∃-introduction.  With `swapped`, each case's proof is wired into
// the other case's subgoal instead.  Report whether Olorin accepts it.
async function casesProves(olorin, { swapped = false } = {}) {
    await olorin.buildCustom({
        parameters: '',
        variables: 'n ∈ ℕ',
        hypotheses: '',
        conclusion: '(n=0)∨(∃k∈ℕ,(n=k+1))',
    });
    const cases = await dragBinder(olorin, 'natE', 250, 100, 'j');
    const left = await olorin.dragRule('orI1', 500, 60);
    const intro = await olorin.dragRule('exI', 450, 300);
    const right = await olorin.dragRule('orI2', 550, 300);
    const nodes = await olorin.nodes();
    const varn = nodes.find((v) => v.rule === 'variable' && v.name === 'n').id;
    const concl = nodes.find((n) => n.rule === 'conclusion').id;
    await olorin.connect({ vertex: varn, sort: 'output' }, { vertex: cases, sort: 'input', label: 'n' });
    await olorin.connect({ vertex: cases, sort: 'assumption', label: 'zero' },
                         { vertex: left, sort: 'input', label: 'left' });
    await olorin.connect({ vertex: cases, sort: 'assumption', label: 'pred' },
                         { vertex: intro, sort: 'input', label: 'element' });
    await olorin.connect({ vertex: cases, sort: 'assumption', label: 'succ' },
                         { vertex: intro, sort: 'input', label: 'property' });
    await olorin.connect({ vertex: intro, sort: 'output' }, { vertex: right, sort: 'input', label: 'right' });
    await olorin.connect({ vertex: left, sort: 'output' },
                         { vertex: cases, sort: 'subgoal', label: swapped ? 'succ' : 'zero' });
    await olorin.connect({ vertex: right, sort: 'output' },
                         { vertex: cases, sort: 'subgoal', label: swapped ? 'zero' : 'succ' });
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

    // Each case has its own assumptions, which aren't in scope in the other one.
    test('keeps each case to its own assumptions', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await casesProves(olorin, { swapped: true })).toBe(false);
    });

    test('labels its assumptions with the variable it binds and the equations for n',
        async ({ page }) => {
            const olorin = new Olorin(page);
            await olorin.open();
            await olorin.buildCustom({
                parameters: '', variables: 'n ∈ ℕ', hypotheses: '', conclusion: 'n≥0',
            });
            const cases = await dragBinder(olorin, 'natE', 250, 100, 'j');
            const nodes = await olorin.nodes();
            const varn = nodes.find((v) => v.rule === 'variable' && v.name === 'n').id;
            const concl = nodes.find((n) => n.rule === 'conclusion').id;
            await olorin.connect({ vertex: varn, sort: 'output' },
                                 { vertex: cases, sort: 'input', label: 'n' });
            await olorin.connect({ vertex: cases, sort: 'output' }, { vertex: concl, sort: 'input' });
            await olorin.waitForTypecheck();
            expect(await portLabels(olorin)).toEqual(
                expect.arrayContaining(['n=0', 'j ∈ ℕ', 'n=j+1']));
        });
});
