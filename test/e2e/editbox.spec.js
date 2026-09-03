// Three kinds of box carry something the player writes: an expression (x−1, say), the type an
// ascription forces, and the variable a ∀-introduction or ∃-elimination binds.  Each asks for it
// when the box is dropped, and double-clicking the box re-opens that dialog to edit it in place --
// the box keeps its id, its position, and its wires.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// A level with an integer variable, where expression boxes are in the palette and make sense.
const LEVEL = { variables: 'x ∈ ℤ', hypotheses: 'x=1', conclusion: 'x=1' };

// Fill in the expression dialog and submit it.
async function enterExpression(page, text) {
    await page.waitForSelector('#expressionBG', { state: 'visible' });
    await page.fill('#expression', text);
    await page.click('#submitExpression');
}

// The text an expression box shows (without its close button).
const boxText = (page, id) =>
    page.evaluate((i) => document.getElementById(i).childNodes[0].textContent.trim(), id);

// The value the app has recorded for a node, which is what gets typechecked and saved.
const nodeValue = async (olorin, id) => (await olorin.nodes()).find((n) => n.id === id).value;

test.describe('Expression boxes', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom(LEVEL);
    });

    // An expression is arithmetic, so its dialog gets a shorter palette than the statement boxes do
    // -- no connectives or quantifiers, just the symbols an expression needs and a keyboard hasn't
    // got.  Most have a typed spelling too (- for −, * for ·, | for ∣, ^2 for ²); √ has only \sqrt.
    test('the dialog offers a palette of the symbols an expression is written out of', async ({ page }) => {
        await olorin.dragRule('expr', 420, 240);
        await page.waitForSelector('#expressionBG', { state: 'visible' });
        const buttons = () => page.evaluate(() =>
            Array.from(document.querySelectorAll('#exprPalette .unicode-button')).map((b) => b.textContent));
        expect(await buttons()).toEqual(['−', '·', '∣', '√', '²', '³', '⁴', 'shortcuts']);

        // The buttons type into the expression, at the cursor.
        await page.fill('#expression', '');
        for (const sym of ['∣', '√']) {
            await page.click(`#exprPalette .unicode-button:has-text("${sym}")`);
        }
        await page.locator('#expression').pressSequentially('x');
        await page.click('#exprPalette .unicode-button:has-text("∣")');
        expect(await page.inputValue('#expression')).toBe('∣√x∣');

        // And the shortcuts, which the dialog had before it had a palette, still work in it.
        await page.fill('#expression', '');
        await page.locator('#expression').pressSequentially('|x*2|');
        expect(await page.inputValue('#expression')).toBe('∣x·2∣');
    });

    test('double-clicking one re-opens the dialog, pre-filled, and edits it in place', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');
        expect(await boxText(page, id)).toBe('x−1');

        await page.dblclick('#' + id);

        // The dialog comes back with the expression that's there now, ready to be corrected.
        await expect(page.locator('#expressionBG')).toBeVisible();
        expect(await page.inputValue('#expression')).toBe('x−1');

        await page.fill('#expression', 'x+2');
        await page.click('#submitExpression');

        expect(await page.isVisible('#expressionBG')).toBe(false);
        expect(await boxText(page, id)).toBe('x+2');
        expect(await nodeValue(olorin, id)).toBe('x+2');
        // Same box: it wasn't deleted and re-made, and re-rendering it left exactly one close button.
        expect((await olorin.nodes()).filter((n) => n.rule === 'expr')).toHaveLength(1);
        expect(await page.locator(`#${id} .closebutton`).count()).toBe(1);
    });

    test('an edit keeps the box wired up as it was', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');
        await olorin.connect({ vertex: 'var0', sort: 'output' }, { vertex: id, sort: 'input' });
        const before = await olorin.connections();
        expect(before).toHaveLength(1);

        await page.dblclick('#' + id);
        await page.fill('#expression', 'x+2');
        await page.click('#submitExpression');

        expect(await olorin.connections()).toEqual(before);
    });

    test('cancelling an edit leaves the box and its expression alone', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');

        await page.dblclick('#' + id);
        await page.fill('#expression', 'x+2');
        await page.click('#cancelExpression');

        expect(await page.isVisible('#expressionBG')).toBe(false);
        expect(await boxText(page, id)).toBe('x−1');
        expect(await nodeValue(olorin, id)).toBe('x−1');
    });

    test('cancelling the prompt for a NEW box still removes it', async ({ page }) => {
        await olorin.dragRule('expr', 420, 240);
        await page.waitForSelector('#expressionBG', { state: 'visible' });
        await page.click('#cancelExpression');

        expect((await olorin.nodes()).some((n) => n.rule === 'expr')).toBe(false);
    });

    test('an invalid expression is refused and the box keeps the old one', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');

        await page.dblclick('#' + id);
        await page.fill('#expression', 'x +');
        await page.click('#submitExpression'); // the alert is auto-accepted by open()

        // The dialog stays open on a bad expression, and the box still says what it said.
        await expect(page.locator('#expressionBG')).toBeVisible();
        await page.click('#cancelExpression');
        expect(await boxText(page, id)).toBe('x−1');
    });

    test('a restored expression box can be edited too', async ({ page }) => {
        const id = await olorin.dragRule('expr', 420, 240);
        await enterExpression(page, 'x−1');
        const state = await olorin.serialize();

        await olorin.restore(state);
        const restored = (await olorin.nodes()).find((n) => n.rule === 'expr').id;
        await page.dblclick('#' + restored);

        await expect(page.locator('#expressionBG')).toBeVisible();
        expect(await page.inputValue('#expression')).toBe('x−1');
        await page.fill('#expression', 'x+2');
        await page.click('#submitExpression');
        expect(await boxText(page, restored)).toBe('x+2');
    });
});

test.describe('Ascription boxes', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom(LEVEL);
    });

    // Fill in the ascription dialog and submit it.
    async function enterAscription(page, text) {
        await page.waitForSelector('#ascribeBG', { state: 'visible' });
        await page.fill('#ascribe', text);
        await page.click('#submitAscribe');
    }

    test('double-clicking one re-opens the dialog, pre-filled, and edits it in place', async ({ page }) => {
        const id = await olorin.dragRule('asc', 420, 240);
        await enterAscription(page, 'x=1');
        expect(await boxText(page, id)).toContain('x=1');

        await page.dblclick('#' + id);

        await expect(page.locator('#ascribeBG')).toBeVisible();
        expect(await page.inputValue('#ascribe')).toBe('x=1');
        await page.fill('#ascribe', '1=x');
        await page.click('#submitAscribe');

        expect(await boxText(page, id)).toContain('1=x');
        expect(await nodeValue(olorin, id)).toBe('1=x');
        expect(await page.locator(`#${id} .closebutton`).count()).toBe(1);
    });

    test('cancelling an edit leaves the box and its type alone', async ({ page }) => {
        const id = await olorin.dragRule('asc', 420, 240);
        await enterAscription(page, 'x=1');

        await page.dblclick('#' + id);
        await page.fill('#ascribe', '1=x');
        await page.click('#cancelAscribe');

        expect(await boxText(page, id)).toContain('x=1');
        expect(await nodeValue(olorin, id)).toBe('x=1');
    });

    test('cancelling the prompt for a NEW box still removes it', async ({ page }) => {
        await olorin.dragRule('asc', 420, 240);
        await page.waitForSelector('#ascribeBG', { state: 'visible' });
        await page.click('#cancelAscribe');

        expect((await olorin.nodes()).some((n) => n.rule === 'asc')).toBe(false);
    });
});

test.describe('Boxes that bind a variable', () => {
    let olorin;

    test.beforeEach(async ({ page }, testInfo) => {
        olorin = new Olorin(page);
        // One test is about the types typed on wires, which only happens above novice.
        if (testInfo.title.includes('above novice')) await olorin.seed([['difficulty', '1']]);
        await olorin.open();
        // ∀-introduction needs a goal worth introducing into; the level's own x is already taken.
        await olorin.buildCustom({ parameters: 'A : Type\nP : A→Type', variables: 'x ∈ ℤ',
                                   hypotheses: '∀z∈A,P(z)', conclusion: '∀z∈A,P(z)' });
    });

    // Fill in the bound-variable dialog and submit it.
    async function enterVariable(page, name) {
        await page.waitForSelector('#variableBG', { state: 'visible' });
        await page.fill('#newvar', name);
        await page.click('#submitVariable');
    }

    const boundName = (page, id) => page.evaluate((i) => document.getElementById(i).dataset.variable, id);

    test('double-clicking one re-opens the dialog, pre-filled, and renames the variable', async ({ page }) => {
        const id = await olorin.dragRule('allI', 420, 240);
        await enterVariable(page, 'y');
        expect(await boundName(page, id)).toBe('y');

        await page.dblclick('#' + id);

        await expect(page.locator('#variableBG')).toBeVisible();
        expect(await page.inputValue('#newvar')).toBe('y');
        // The name it binds now isn't listed as taken -- it's the one being replaced.
        expect(await page.textContent('#variableList')).not.toContain('y');

        await page.fill('#newvar', 'w');
        await page.click('#submitVariable');

        expect(await page.isVisible('#variableBG')).toBe(false);
        expect(await boundName(page, id)).toBe('w');
        expect((await olorin.nodes()).find((n) => n.id === id).name).toBe('w');
        // The old name is no longer in use, and the new one is.
        const names = await olorin.varnames();
        expect(names).toContain('w');
        expect(names).not.toContain('y');
    });

    test('re-submitting the same name is accepted', async ({ page }) => {
        const id = await olorin.dragRule('allI', 420, 240);
        await enterVariable(page, 'y');

        await page.dblclick('#' + id);
        await page.click('#submitVariable'); // unchanged

        expect(await page.isVisible('#variableBG')).toBe(false);
        expect(await boundName(page, id)).toBe('y');
        expect((await olorin.varnames()).filter((v) => v === 'y')).toHaveLength(1);
    });

    test('a name already in use is still refused', async ({ page }) => {
        const id = await olorin.dragRule('allI', 420, 240);
        await enterVariable(page, 'y');

        await page.dblclick('#' + id);
        await page.fill('#newvar', 'x'); // the level's own variable
        await page.click('#submitVariable'); // the alert is auto-accepted by open()

        await expect(page.locator('#variableBG')).toBeVisible();
        await page.click('#cancelVariable');
        expect(await boundName(page, id)).toBe('y');
    });

    // Renaming can't reach into text the player wrote by hand, so the dialog says so when the
    // proof has anywhere that could contain it.
    const warning = (page) => page.evaluate(() => {
        const w = document.getElementById('renameWarning');
        return w.classList.contains('shown') ? w.innerText : null;
    });

    test('renaming warns about hand-written names when a box could hold one', async ({ page }) => {
        const id = await olorin.dragRule('allI', 420, 240);
        await enterVariable(page, 'y');

        // Nothing written by hand yet, and novice types no wires: no warning.
        await page.dblclick('#' + id);
        expect(await warning(page)).toBeNull();
        await page.click('#cancelVariable');

        // Add an expression box, and the rename dialog cautions about it.
        await olorin.dragRule('expr', 600, 400);
        await page.waitForSelector('#expressionBG', { state: 'visible' });
        await page.fill('#expression', 'x+1');
        await page.click('#submitExpression');

        await page.dblclick('#' + id);
        expect(await warning(page)).toContain('expression and ascription boxes');
        expect(await warning(page)).not.toContain('wires');
    });

    test('the warning covers typed wire labels above novice', async ({ page }) => {
        const id = await olorin.dragRule('allI', 420, 240);
        await enterVariable(page, 'y');
        await page.dblclick('#' + id);

        expect(await warning(page)).toContain("types you've written on wires");
    });

    test('a brand-new variable is not warned about', async ({ page }) => {
        // An expression box is present, but naming a *new* binder leaves nothing behind.
        await olorin.dragRule('expr', 600, 400);
        await page.waitForSelector('#expressionBG', { state: 'visible' });
        await page.fill('#expression', 'x+1');
        await page.click('#submitExpression');

        await olorin.dragRule('allI', 420, 240);
        await page.waitForSelector('#variableBG', { state: 'visible' });
        expect(await warning(page)).toBeNull();
    });

    test('cancelling a rename leaves the box alone, but cancelling a new box removes it', async ({ page }) => {
        const id = await olorin.dragRule('allI', 420, 240);
        await enterVariable(page, 'y');

        await page.dblclick('#' + id);
        await page.fill('#newvar', 'w');
        await page.click('#cancelVariable');
        expect(await boundName(page, id)).toBe('y');
        expect((await olorin.nodes()).some((n) => n.id === id)).toBe(true);

        await olorin.dragRule('exE', 420, 400);
        await page.waitForSelector('#variableBG', { state: 'visible' });
        await page.click('#cancelVariable');
        expect((await olorin.nodes()).some((n) => n.rule === 'exE')).toBe(false);
    });
});

// Shortcut sequences are replaced as they are typed, by rewriting the box's whole contents.  That
// drops the cursor at the end of the box unless it is put back, which used to lose the player's
// place -- and worse, broke every shortcut of more than one keystroke typed anywhere but the end,
// since the second keystroke landed at the end rather than beside the first: "**2" in the middle
// of "ab" gave "a·b·2" rather than "a²b".
test.describe('Shortcut sequences', () => {
    // Type `keys` into the conclusion box of the custom-level dialog, starting from `initial` with
    // the cursor `at` characters in, and report what the box says and where the cursor ended up.
    async function typeAt(page, initial, at, keys) {
        const box = page.locator('#conclusion');
        await box.fill(initial);
        await page.evaluate((n) => document.getElementById('conclusion').setSelectionRange(n, n), at);
        await box.pressSequentially(keys);
        return {
            text: await box.inputValue(),
            cursor: await page.evaluate(() => document.getElementById('conclusion').selectionStart),
        };
    }

    test.beforeEach(async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.openChooser();
        await page.click('#customLevel');
    });

    test('leave the cursor after what they inserted, not at the end of the box', async ({ page }) => {
        for (const [keys, text] of [['*', 'x·y'], ['-', 'x−y'], ['|', 'x∣y'],
                                    ['\\land ', 'x∧y'], ['<=>', 'x⇔y']]) {
            expect(await typeAt(page, 'xy', 1, keys)).toEqual({ text, cursor: 2 });
        }
    });

    test('of more than one keystroke work in the middle of a box', async ({ page }) => {
        expect(await typeAt(page, 'ab', 1, '**2')).toEqual({ text: 'a²b', cursor: 2 });
        expect(await typeAt(page, 'ab', 1, '--')).toEqual({ text: 'a∸b', cursor: 2 });
        expect(await typeAt(page, 'ab', 1, '|->')).toEqual({ text: 'a↦b', cursor: 2 });
    });

    test('still work at either end', async ({ page }) => {
        expect(await typeAt(page, 'xy', 2, '*')).toEqual({ text: 'xy·', cursor: 3 });
        expect(await typeAt(page, 'xy', 0, '*')).toEqual({ text: '·xy', cursor: 1 });
    });
});

