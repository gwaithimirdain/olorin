// Tests for the sentences a block on the diagram shows when hovered or tapped: what it says in an
// English proof, from the templates in client/sentences.js, filled in with the statements on its
// own ports.

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
    impI: 'Assume {assumption}; we will prove {subgoal}.',
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
    test('name only ports that their blocks have', async ({ page }) => {
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
                for (const m of template.matchAll(/\{(\w+)(?::(\w+))?(\.type)?\}/g)) {
                    const name = m[1] + ':' + (m[2] || '');
                    if (!have.includes(name)) { found.push(rule + ': ' + m[0]); }
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
