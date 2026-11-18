// The law of excluded middle block, lem.  Dropping it asks for a statement P, in the same dialog an
// ascription uses, and its one output is then P∨¬P, by an axiom: it has no inputs at all.  The
// statement is parsed and typechecked along with the rest of the proof, so it can mention any
// variable in scope where its output is used, and one that doesn't make sense is an error.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// The text a box shows (without its close button).
const boxText = (page, id) =>
    page.evaluate((i) => document.getElementById(i).childNodes[0].textContent.trim(), id);

// The type shown on the block's output port.
async function outputType(page, id) {
    const ports = await page.evaluate(() => window.__olorin.ports());
    const out = ports.find((p) => p.vertex === id && p.sort === 'output');
    return out && out.type;
}

async function conclusionId(olorin) {
    return (await olorin.nodes()).find((n) => n.rule === 'conclusion').id;
}

// Drop a lem block and give it the statement.
async function dropLem(olorin, page, statement, x = 300, y = 200) {
    const id = await olorin.dragRule('lem', x, y);
    await page.waitForSelector('#ascribeBG', { state: 'visible' });
    await page.fill('#ascribe', statement);
    await page.click('#submitAscribe');
    await olorin.waitForTypecheck();
    return id;
}

test.describe('Excluded middle', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('asks for a statement P, and proves P∨¬P from nothing', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: '', conclusion: 'P∨¬P' });
        const id = await olorin.dragRule('lem', 300, 200);
        // The dialog says what it is asking for, rather than talking about labeling a wire.
        await page.waitForSelector('#ascribeBG', { state: 'visible' });
        expect(await page.textContent('#ascribeTitle')).toBe('Excluded middle');
        await page.fill('#ascribe', 'P');
        await page.click('#submitAscribe');
        await olorin.waitForTypecheck();

        expect(await boxText(page, id)).toBe('lem P');
        expect((await olorin.nodes()).find((n) => n.id === id).value).toBe('P');
        // It has no inputs: its only port is its output.
        const ports = (await page.evaluate(() => window.__olorin.ports())).filter((p) => p.vertex === id);
        expect(ports.map((p) => p.sort)).toEqual(['output']);
        expect(await outputType(page, id)).toBe('P∨¬P');

        await olorin.connect({ vertex: id, sort: 'output' }, { vertex: await conclusionId(olorin), sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
        expect(await page.evaluate((i) => window.__olorin.sentence(i), id))
            .toBe('By the law of excluded middle, P∨¬P.');
    });

    // An ascription box still says what it does, after the dialog has been used for excluded middle.
    test('the ascription dialog keeps its own wording', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: '', conclusion: 'P∨¬P' });
        await dropLem(olorin, page, 'P');
        await olorin.dragRule('asc', 300, 300);
        await page.waitForSelector('#ascribeBG', { state: 'visible' });
        expect(await page.textContent('#ascribeTitle')).toBe('Label a wire');
        await page.click('#cancelAscribe');
    });

    test('the statement is typechecked: excluded middle for the wrong one proves nothing', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type\nQ : Type', hypotheses: '', conclusion: 'P∨¬P' });
        const id = await dropLem(olorin, page, 'Q');
        expect(await outputType(page, id)).toBe('Q∨¬Q');
        await olorin.connect({ vertex: id, sort: 'output' }, { vertex: await conclusionId(olorin), sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(false);
        expect((await olorin.diagnostics()).length).toBeGreaterThan(0);
    });

    test('a statement that names no variable in scope is an error', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: '', conclusion: 'P∨¬P' });
        const id = await dropLem(olorin, page, 'R');
        await olorin.connect({ vertex: id, sort: 'output' }, { vertex: await conclusionId(olorin), sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(false);
        expect((await olorin.diagnostics()).length).toBeGreaterThan(0);
    });

    test('a statement that does not parse is refused, and the dialog stays open', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: '', conclusion: 'P∨¬P' });
        let alerted = null;
        page.on('dialog', (d) => { alerted = d.message(); });
        await olorin.dragRule('lem', 300, 200);
        await page.waitForSelector('#ascribeBG', { state: 'visible' });
        await page.fill('#ascribe', 'P∨');
        await page.click('#submitAscribe');
        expect(alerted).toBe('Invalid statement');
        expect(await page.isVisible('#ascribeBG')).toBe(true);
    });

    test('cancelling the dialog for a new block removes it', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: '', conclusion: 'P∨¬P' });
        const id = await olorin.dragRule('lem', 300, 200);
        await page.waitForSelector('#ascribeBG', { state: 'visible' });
        await page.click('#cancelAscribe');
        expect((await olorin.nodes()).some((n) => n.id === id)).toBe(false);
    });

    test('double-clicking the block changes its statement in place', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type\nQ : Type', hypotheses: '', conclusion: 'P∨¬P' });
        const id = await dropLem(olorin, page, 'Q');
        await olorin.connect({ vertex: id, sort: 'output' }, { vertex: await conclusionId(olorin), sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(false);

        await page.dblclick('#' + id);
        await page.waitForSelector('#ascribeBG', { state: 'visible' });
        expect(await page.inputValue('#ascribe')).toBe('Q');
        await page.fill('#ascribe', 'P');
        await page.click('#submitAscribe');
        await olorin.waitForTypecheck();
        expect(await boxText(page, id)).toBe('lem P');
        expect(await olorin.isComplete()).toBe(true);
    });

    // Inside a ∀-introduction, the statement can mention the variable it binds.
    test('the statement can use a bound variable', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'A : Type\nP : A→Type', hypotheses: '', conclusion: '∀x∈A,(P(x)∨¬P(x))' });
        const all = await olorin.dragRule('allI', 200, 150);
        await page.waitForSelector('#variableBG', { state: 'visible' });
        await page.fill('#newvar', 'x');
        await page.click('#submitVariable');
        await olorin.waitForTypecheck();
        const lem = await dropLem(olorin, page, 'P(x)', 300, 300);
        await olorin.connect({ vertex: lem, sort: 'output' }, { vertex: all, sort: 'subgoal' });
        await olorin.connect({ vertex: all, sort: 'output' }, { vertex: await conclusionId(olorin), sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
    });

    test('the statement is saved with the proof and restored', async ({ page }) => {
        await olorin.buildCustom({ parameters: 'P : Type', hypotheses: '', conclusion: 'P∨¬P' });
        const id = await dropLem(olorin, page, 'P');
        await olorin.connect({ vertex: id, sort: 'output' }, { vertex: await conclusionId(olorin), sort: 'input' });
        await olorin.waitForTypecheck();
        const saved = await page.evaluate(() => window.__olorin.serialize());

        await olorin.clear();
        expect(await olorin.isComplete()).toBe(false);
        await olorin.restore(saved);
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
        const restored = (await olorin.nodes()).find((n) => n.rule === 'lem');
        expect(restored.value).toBe('P');
        expect(await boxText(page, restored.id)).toBe('lem P');
    });
});
