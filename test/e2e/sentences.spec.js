// Tests for the sentences a block on the diagram shows when hovered or tapped: what it says in an
// English proof, from the templates in client/sentences.js, filled in with the statements on its
// own ports.  And for the whole proof in English that a completed level offers, put together from
// those sentences.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { fixtureLevels } = require('../lib/levels');
const { hasFixture, readFixture, proofRules } = require('../lib/fixtures');

const IMPLICATION = { parameters: 'P : Type\nQ : Type', hypotheses: 'P ⇒ Q\nP', conclusion: 'Q' };

// The wording of the real templates is for editing freely, so all but the first test below install
// these instead: what they test is how a template gets filled in and shown.
const TEMPLATES = {
    hypothesis: 'By hypothesis, {output}.',
    variable: 'Let {output}∈{output.type} be given.',
    conclusion: 'We want to prove {input}.',
    impE: 'Since {input:implication} and {input:antecedent}, we have {output}.',
    impI: 'Assume {assumption}; we will prove {subgoal}.\n{proof}',
    allI: 'Let {assumption}∈{assumption.type}[ with {assumption:condition}] be arbitrary; we will prove {subgoal}.',
    alg: 'By algebra[ from {input}], we have {output}.',
    zton: 'Choose {output:element}∈{output:element.type} such that {output:property}.',
    natInd: 'Assume {assumption:IH}.',
    natE: 'Cases on {input}.',
    'natE in natInd': 'Induction on {input}.',
};

// Open the app, with those templates in place of the real ones.
async function openWithTemplates(olorin, page, options) {
    await olorin.open(options);
    await page.evaluate((t) => Object.assign(window.__olorin.sentences(), t), TEMPLATES);
}

const sentenceOf = (page, id) => page.evaluate((i) => window.__olorin.sentence(i), id);
const writtenProof = (page) => page.evaluate(() => window.__olorin.writtenProof());
const tooltip = (page) => page.locator('#blockTooltip');

// The ids of a level's given blocks and its goal.
async function givens(olorin) {
    const nodes = await olorin.nodes();
    return {
        hyps: nodes.filter((n) => n.rule === 'hypothesis').map((n) => n.id),
        concl: nodes.find((n) => n.rule === 'conclusion').id,
    };
}

// The P⇒Q, P ⊢ Q level, proved with a ⇒-elimination; the id of that block.
async function provedByImpE(olorin) {
    await olorin.buildCustom(IMPLICATION);
    const { hyps, concl } = await givens(olorin);
    const impE = await olorin.dragRule('impE', 300, 150);
    await olorin.connect({ vertex: hyps[0], sort: 'output' }, { vertex: impE, sort: 'input', label: 'implication' });
    await olorin.connect({ vertex: hyps[1], sort: 'output' }, { vertex: impE, sort: 'input', label: 'antecedent' });
    await olorin.connect({ vertex: impE, sort: 'output' }, { vertex: concl, sort: 'input' });
    await olorin.waitForTypecheck();
    return impE;
}

// Answer the dialog a binding block opens with the name of its variable.
async function nameVariable(page, name) {
    await page.fill('#newvar', name);
    await page.click('#submitVariable');
}

// The middle of a block's box on the screen.
async function centre(page, id) {
    const box = await page.locator('#' + id).boundingBox();
    return { x: box.x + box.width / 2, y: box.y + box.height / 2 };
}

test.describe('Sentence templates', () => {
    test('name only ports that their blocks have, and have a hole for each subgoal', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({ parameters: 'P : Type', variables: 'x ∈ ℝ', hypotheses: 'P', conclusion: 'P' });
        const problems = await page.evaluate(() => {
            const { sentences, nodes, ports } = window.__olorin;
            const found = [];
            const given = (rule) => nodes().find((n) => n.rule === rule).id;
            const placed = (rule) => {
                if (['hypothesis', 'variable', 'conclusion'].includes(rule)) { return given(rule); }
                const src = document.getElementById(rule);
                if (!src) { return null; }
                const dt = new DataTransfer();
                dt.setData('text/plain', rule);
                document.getElementById('diagram').dispatchEvent(new DragEvent('drop', {
                    bubbles: true, cancelable: true, dataTransfer: dt, clientX: 400, clientY: 300,
                }));
                const all = nodes();
                return all[all.length - 1].id;
            };
            for (const [name, template] of Object.entries(sentences())) {
                // "natE in natInd" is another sentence for the first block it names.
                const rule = name.split(' ')[0];
                const id = placed(rule);
                if (id === null) { found.push(rule + ': no such block'); continue; }
                const have = ports().filter((p) => p.vertex === id).map((p) => p.sort + ':' + (p.label || ''));
                const holes = [];
                for (const line of template.split('\n')) {
                    const hole = line.match(/^\{proof(?::(\w+))?\}$/);
                    if (hole) { holes.push('subgoal:' + (hole[1] || '')); continue; }
                    for (const m of line.matchAll(/\{(\w+)(?::(\w+))?(\.type)?\}/g)) {
                        const name = m[1] + ':' + (m[2] || '');
                        if (!have.includes(name)) { found.push(rule + ': ' + m[0]); }
                    }
                }
                const subgoals = have.filter((p) => p.startsWith('subgoal:'));
                if (holes.slice().sort().join() !== subgoals.slice().sort().join()) {
                    found.push(rule + ': holes for ' + holes.join(', ') + ' but subgoals ' + subgoals.join(', '));
                }
            }
            return found;
        });
        expect(problems).toEqual([]);
    });
});

test.describe('A block\'s sentence', () => {
    let olorin;
    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await openWithTemplates(olorin, page);
    });

    test('is filled in from the statements on its ports', async ({ page }) => {
        const impE = await provedByImpE(olorin);
        expect(await sentenceOf(page, impE)).toBe('Since P⇒Q and P, we have Q.');
    });

    test('leaves a blank for what is not known yet', async ({ page }) => {
        await olorin.buildCustom(IMPLICATION);
        const { hyps } = await givens(olorin);
        const impE = await olorin.dragRule('impE', 300, 150);
        await olorin.connect({ vertex: hyps[1], sort: 'output' }, { vertex: impE, sort: 'input', label: 'antecedent' });
        await olorin.waitForTypecheck();
        expect(await sentenceOf(page, impE)).toBe('Since ___ and P, we have ___.');
    });

    test('is said for the givens and the goal too', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type', variables: 'x ∈ ℝ', hypotheses: 'P', conclusion: 'P' });
        await olorin.waitForTypecheck();
        const nodes = await olorin.nodes();
        const says = (rule) => sentenceOf(page, nodes.find((n) => n.rule === rule).id);
        expect(await says('hypothesis')).toBe('By hypothesis, P.');
        expect(await says('variable')).toBe('Let x∈ℝ be given.');
        expect(await says('conclusion')).toBe('We want to prove P.');
    });

    test('names the variable, the set, and the goal of a ∀', async ({ page }) => {
        await olorin.buildCustom({
            parameters: 'B : Type\nP : B→Type\nQ : B→Type',
            hypotheses: '',
            conclusion: '∀x∈B,(P(x)∧Q(x))',
        });
        const { concl } = await givens(olorin);
        const allI = await olorin.dragRule('allI', 300, 150);
        await nameVariable(page, 'b');
        await olorin.waitForTypecheck();
        await olorin.connect({ vertex: allI, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await sentenceOf(page, allI)).toBe('Let b∈B be arbitrary; we will prove P(b)∧Q(b).');
    });

    test('mentions the condition of a ∀ only when it has one', async ({ page }) => {
        await olorin.buildCustom({ parameters: '', hypotheses: '', conclusion: '∀x∈ℝ₊,(0<x)' });
        const { concl } = await givens(olorin);
        const allI = await olorin.dragRule('allI', 300, 150);
        await nameVariable(page, 'y');
        await olorin.waitForTypecheck();
        await olorin.connect({ vertex: allI, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await sentenceOf(page, allI)).toBe('Let y∈ℝ with 0<y be arbitrary; we will prove 0<y.');
    });

    test('lists exactly the inputs wired into an algebra block', async ({ page }) => {
        await olorin.buildCustom({
            parameters: '', variables: 'x ∈ ℝ\ny ∈ ℝ', hypotheses: 'x = 1\ny = 2', conclusion: 'x + y = 3',
        });
        const { hyps, concl } = await givens(olorin);
        const alg = await olorin.dragRule('alg', 300, 150);
        await olorin.connect({ vertex: alg, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await sentenceOf(page, alg)).toBe('By algebra, we have x+y=3.');
        await olorin.connect({ vertex: hyps[0], sort: 'output' }, { vertex: alg, sort: 'input' });
        await olorin.waitForTypecheck();
        await olorin.connect({ vertex: hyps[1], sort: 'output' }, { vertex: alg, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await sentenceOf(page, alg)).toBe('By algebra from x=1 and y=2, we have x+y=3.');
    });

    test('states an assumption as it is made, not as a later case refines it', async ({ page }) => {
        // A strong induction that goes on to split into cases on its own variable: there, the
        // inductive hypothesis's wire reads "∀k<m+1", about the m of the second case.
        const level = fixtureLevels().filter(hasFixture).find((l) => {
            const rules = proofRules(readFixture(l));
            return rules.includes('natInd') && rules.includes('natE');
        });
        expect(level, 'no proof by strong induction that splits into cases').toBeTruthy();
        await openWithTemplates(olorin, page, { code: level.code });
        await olorin.selectLevel(level.name);
        await olorin.restore(readFixture(level));
        const natInd = (await olorin.nodes()).find((n) => n.rule === 'natInd');
        const name = natInd.names[0];
        expect(await sentenceOf(page, natInd.id)).toMatch(new RegExp(`Assume ∀\\S+<${name},`));
    });

    test('states what a block hands out as it is handed out, not as a later case refines it', async ({ page }) => {
        // ℤ→ℕ hands out a natural number and that x equals it; splitting into cases on that number
        // makes the equation's wire read "x=n+1", about the n of the second case.
        const level = fixtureLevels().filter(hasFixture).find((l) => {
            const rules = proofRules(readFixture(l));
            return rules.includes('zton') && rules.includes('natE');
        });
        expect(level, 'no proof that splits into cases on the result of a ℤ→ℕ').toBeTruthy();
        await openWithTemplates(olorin, page, { code: level.code });
        await olorin.selectLevel(level.name);
        await olorin.restore(readFixture(level));
        const blocks = (await olorin.nodes()).filter((n) => n.rule === 'zton');
        expect(blocks.length).toBeGreaterThan(0);
        for (const b of blocks) {
            expect(await sentenceOf(page, b.id)).toMatch(/Choose (\S+)∈ℕ such that \S+=\1\.$/);
        }
    });

    // An induction on n, with a natE wired straight into its step.  Returns the natE, whose input
    // is left for the test to wire, and the natInd.
    async function inductionWithCases(page, variables) {
        await olorin.buildCustom({ parameters: '', variables, hypotheses: '', conclusion: '∀n∈ℕ,(n=n)' });
        const { concl } = await givens(olorin);
        const natInd = await olorin.dragRule('natInd', 200, 100);
        await nameVariable(page, 'n');
        await olorin.waitForTypecheck();
        const natE = await olorin.dragRule('natE', 300, 150);
        await nameVariable(page, 'm');
        await olorin.waitForTypecheck();
        await olorin.connect({ vertex: natInd, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        return { natE, natInd };
    }

    test('calls the cases of a natE on the induction variable the base case and step', async ({ page }) => {
        const { natE, natInd } = await inductionWithCases(page, '');
        await olorin.connect({ vertex: natInd, sort: 'assumption', label: 'n' }, { vertex: natE, sort: 'input' });
        await olorin.waitForTypecheck();
        // Not yet wired into the induction's step, this is still just a proof by cases.
        expect(await sentenceOf(page, natE)).toBe('Cases on n.');
        await olorin.connect({ vertex: natE, sort: 'output' }, { vertex: natInd, sort: 'subgoal', label: 'step' });
        await olorin.waitForTypecheck();
        expect(await sentenceOf(page, natE)).toBe('Induction on n.');
    });

    test('leaves a natE on some other number an ordinary proof by cases', async ({ page }) => {
        const { natE, natInd } = await inductionWithCases(page, 'x ∈ ℕ');
        const x = (await olorin.nodes()).find((n) => n.rule === 'variable').id;
        await olorin.connect({ vertex: x, sort: 'output' }, { vertex: natE, sort: 'input' });
        await olorin.waitForTypecheck();
        await olorin.connect({ vertex: natE, sort: 'output' }, { vertex: natInd, sort: 'subgoal', label: 'step' });
        await olorin.waitForTypecheck();
        expect(await sentenceOf(page, natE)).toBe('Cases on x.');
    });

    for (const level of [1, 2]) {
        test(`is not shown above novice (difficulty ${level})`, async ({ page }) => {
            await olorin.seed([['difficulty', String(level)]]);
            await openWithTemplates(olorin, page);
            const impE = await provedByImpE(olorin);
            expect(await page.evaluate(() => window.__olorin.difficulty())).toBe(level);
            const c = await centre(page, impE);
            await page.mouse.move(c.x, c.y);
            await page.waitForTimeout(600);
            await expect(tooltip(page)).toBeHidden();
        });
    }
});

test.describe('The proof in English', () => {
    let olorin;
    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await openWithTemplates(olorin, page);
    });

    test('says the givens, the goal, and then each block in order', async ({ page }) => {
        await provedByImpE(olorin);
        expect(await writtenProof(page)).toEqual([
            { text: 'By hypothesis, P⇒Q.', depth: 0 },
            { text: 'By hypothesis, P.', depth: 0 },
            { text: 'We want to prove Q.', depth: 0 },
            { text: 'Since P⇒Q and P, we have Q.', depth: 0 },
        ]);
    });

    test('puts the proof of a bracket\'s subgoal in its hole, indented', async ({ page }) => {
        await olorin.buildCustom({
            parameters: 'P : Type\nQ : Type\nR : Type', hypotheses: 'P ⇒ Q\nQ ⇒ R', conclusion: 'P ⇒ R',
        });
        const { hyps, concl } = await givens(olorin);
        const impI = await olorin.dragRule('impI', 250, 100);
        // The second step is the further left, but it can't come first.
        const second = await olorin.dragRule('impE', 300, 300);
        const first = await olorin.dragRule('impE', 500, 300);
        await olorin.connect({ vertex: hyps[0], sort: 'output' }, { vertex: first, sort: 'input', label: 'implication' });
        await olorin.connect({ vertex: impI, sort: 'assumption' }, { vertex: first, sort: 'input', label: 'antecedent' });
        await olorin.connect({ vertex: hyps[1], sort: 'output' }, { vertex: second, sort: 'input', label: 'implication' });
        await olorin.connect({ vertex: first, sort: 'output' }, { vertex: second, sort: 'input', label: 'antecedent' });
        await olorin.connect({ vertex: second, sort: 'output' }, { vertex: impI, sort: 'subgoal' });
        await olorin.connect({ vertex: impI, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
        expect((await writtenProof(page)).slice(3)).toEqual([
            { text: 'Assume P; we will prove R.', depth: 0 },
            { text: 'Since P⇒Q and P, we have Q.', depth: 1 },
            { text: 'Since Q⇒R and Q, we have R.', depth: 1 },
        ]);
    });

    test('puts a block in the subproof that uses it, even if it uses nothing assumed there', async ({ page }) => {
        await olorin.buildCustom({
            parameters: 'P : Type\nQ : Type\nR : Type', hypotheses: 'P ⇒ Q\nP', conclusion: 'R ⇒ Q',
        });
        const { hyps, concl } = await givens(olorin);
        const impE = await olorin.dragRule('impE', 250, 150);
        const impI = await olorin.dragRule('impI', 450, 100);
        await olorin.connect({ vertex: hyps[0], sort: 'output' }, { vertex: impE, sort: 'input', label: 'implication' });
        await olorin.connect({ vertex: hyps[1], sort: 'output' }, { vertex: impE, sort: 'input', label: 'antecedent' });
        await olorin.connect({ vertex: impE, sort: 'output' }, { vertex: impI, sort: 'subgoal' });
        await olorin.connect({ vertex: impI, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
        expect((await writtenProof(page)).slice(3)).toEqual([
            { text: 'Assume R; we will prove Q.', depth: 0 },
            { text: 'Since P⇒Q and P, we have Q.', depth: 1 },
        ]);
    });

    test('says a subgoal with nothing to prove is trivial', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: '', conclusion: 'P ⇒ P' });
        const { concl } = await givens(olorin);
        const impI = await olorin.dragRule('impI', 300, 150);
        await olorin.connect({ vertex: impI, sort: 'assumption' }, { vertex: impI, sort: 'subgoal' });
        await olorin.connect({ vertex: impI, sort: 'output' }, { vertex: concl, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
        const trivial = await page.evaluate(() => window.__olorin.trivial());
        expect(await writtenProof(page)).toEqual([
            { text: 'We want to prove P⇒P.', depth: 0 },
            { text: 'Assume P; we will prove P.', depth: 0 },
            { text: trivial, depth: 1 },
        ]);
    });

    test('is shown by a button on completing a level', async ({ page }) => {
        await provedByImpE(olorin);
        await page.click('#showWrittenProof');
        await expect(page.locator('#writtenProof .writtenProofLine')).toHaveText([
            'By hypothesis, P⇒Q.', 'By hypothesis, P.', 'We want to prove Q.', 'Since P⇒Q and P, we have Q.',
        ]);
        await page.click('#doneWrittenProof');
        await expect(page.locator('#writtenProofBG')).toBeHidden();
    });

    test('is not offered above novice', async ({ page }) => {
        await olorin.seed([['difficulty', '1']]);
        await openWithTemplates(olorin, page);
        await provedByImpE(olorin);
        expect(await olorin.completeBannerVisible()).toBe(true);
        await expect(page.locator('#showWrittenProof')).toBeHidden();
    });

    // With the real templates: every case of a proof that splits into them has its own proof.
    test('fills in every hole of a real proof by cases', async ({ page }) => {
        const level = fixtureLevels().filter(hasFixture).find((l) => proofRules(readFixture(l)).includes('orE'));
        expect(level, 'no proof by cases on an ∨').toBeTruthy();
        await olorin.open({ code: level.code });
        await olorin.selectLevel(level.name);
        await olorin.restore(readFixture(level));
        expect(await olorin.isComplete()).toBe(true);
        const lines = await writtenProof(page);
        const cases = lines.map((l, i) => [l, i]).filter(([l]) => /^Case \d/.test(l.text));
        expect(cases.length).toBeGreaterThanOrEqual(2);
        for (const [c, i] of cases) {
            expect(lines[i + 1].depth, 'the case after "' + c.text + '" has no proof').toBe(c.depth + 1);
        }
        expect(lines.map((l) => l.text).join('\n')).not.toMatch(/___|\{|\.\.\./);
    });
});

test.describe('Hovering a block', () => {
    let olorin;
    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await openWithTemplates(olorin, page);
    });

    test('shows its sentence, until the pointer leaves it', async ({ page }) => {
        const impE = await provedByImpE(olorin);
        const c = await centre(page, impE);
        await page.mouse.move(c.x, c.y);
        await expect(tooltip(page)).toHaveText('Since P⇒Q and P, we have Q.');
        await page.mouse.move(5, 5);
        await expect(tooltip(page)).toBeHidden();
    });

    test('shows the sentence instead of the palette description', async ({ page }) => {
        const impE = await provedByImpE(olorin);
        expect(await page.locator('#' + impE).getAttribute('title')).toBeNull();
        expect(await page.locator('#impE').getAttribute('title')).toBeTruthy();
    });

    test('shows no description on a block that has no sentence', async ({ page }) => {
        await olorin.buildCustom({ parameters: '', variables: 'x ∈ ℝ', hypotheses: '', conclusion: 'x = x' });
        const expr = await olorin.dragRule('expr', 300, 150);
        expect(await page.locator('#' + expr).getAttribute('title')).toBeNull();
        expect(await page.locator('#expr').getAttribute('title')).toBeTruthy();
    });

    test('puts the sentence away when the block is pressed', async ({ page }) => {
        const impE = await provedByImpE(olorin);
        const c = await centre(page, impE);
        await page.mouse.move(c.x, c.y);
        await expect(tooltip(page)).toBeVisible();
        await page.mouse.down();
        await expect(tooltip(page)).toBeHidden();
        await page.mouse.up();
    });

    test('says nothing over the empty middle of a bracket, only over its frame', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: '', conclusion: 'P ⇒ P' });
        const impI = await olorin.dragRule('impI', 300, 150);
        await olorin.waitForTypecheck();
        const box = await page.locator('#' + impI).boundingBox();
        await page.mouse.move(box.x + box.width / 2, box.y + 8);
        await page.waitForTimeout(600);
        await expect(tooltip(page)).toBeHidden();
        await page.mouse.move(box.x + box.width / 2, box.y + box.height - 8);
        await expect(tooltip(page)).toHaveText(/we will prove/);
    });
});

test.describe('On a touchscreen', () => {
    test.use({ hasTouch: true });

    test('tapping a block shows its sentence, and tapping again puts it away', async ({ page }) => {
        const olorin = new Olorin(page);
        await openWithTemplates(olorin, page);
        const impE = await provedByImpE(olorin);
        const c = await centre(page, impE);
        await page.touchscreen.tap(c.x, c.y);
        await expect(tooltip(page)).toHaveText('Since P⇒Q and P, we have Q.');
        await page.waitForTimeout(500);
        await page.touchscreen.tap(c.x, c.y);
        await expect(tooltip(page)).toBeHidden();
    });

    test('tapping a block above novice shows nothing', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed([['difficulty', '1']]);
        await openWithTemplates(olorin, page);
        const impE = await provedByImpE(olorin);
        const c = await centre(page, impE);
        await page.touchscreen.tap(c.x, c.y);
        await page.waitForTimeout(500);
        await expect(tooltip(page)).toBeHidden();
    });

    test('tapping the background puts it away', async ({ page }) => {
        const olorin = new Olorin(page);
        await openWithTemplates(olorin, page);
        const impE = await provedByImpE(olorin);
        const c = await centre(page, impE);
        await page.touchscreen.tap(c.x, c.y);
        await expect(tooltip(page)).toBeVisible();
        const d = await page.locator('#diagram').boundingBox();
        await page.waitForTimeout(500);
        await page.touchscreen.tap(d.x + d.width - 30, d.y + d.height - 30);
        await expect(tooltip(page)).toBeHidden();
    });
});
