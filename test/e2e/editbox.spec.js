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
    // got, plus the Greek dropdown for whatever the variables in it are called.  Most have a typed
    // spelling too (- for −, * for ·, | for ∣, ^2 for ²); √ has only \sqrt.
    //
    // Nothing here reads on the palette's exact contents, so that adding a symbol to it can't
    // break this: what is asserted is that the symbols an expression needs are offered, that the
    // ones belonging to statements are not, and that whatever is offered works.
    test('the dialog offers a palette of the symbols an expression is written out of', async ({ page }) => {
        await olorin.dragRule('expr', 420, 240);
        await page.waitForSelector('#expressionBG', { state: 'visible' });
        const buttons = (await page.evaluate(() =>
            Array.from(document.querySelectorAll('#exprPalette .unicode-button')).map((b) => b.textContent)))
              .filter((b) => b !== 'shortcuts');

        expect(buttons).toEqual(expect.arrayContaining(['−', '·', '∣', '√', '²', '³', '⁴']));
        // The one assertion a new palette entry could disturb, and only by offering a connective
        // or a quantifier in a box where an expression is what's wanted.
        for (const logical of ['∧', '∨', '⇒', '⇔', '¬', '⊤', '⊥', '∀', '∃', '∈']) {
            expect(buttons).not.toContain(logical);
        }

        // Whatever is on offer types itself into the box.
        for (const sym of buttons) {
            await page.fill('#expression', '');
            await page.click(`#exprPalette .unicode-button:has-text("${sym}")`);
            expect(await page.inputValue('#expression')).toBe(sym);
        }

        // And they go in at the cursor, rather than at the end.
        await page.fill('#expression', '');
        await page.click('#exprPalette .unicode-button:has-text("∣")');
        await page.click('#exprPalette .unicode-button:has-text("√")');
        await page.locator('#expression').pressSequentially('x');
        await page.click('#exprPalette .unicode-button:has-text("∣")');
        expect(await page.inputValue('#expression')).toBe('∣√x∣');

        // And the shortcuts, which the dialog had before it had a palette, still work in it.
        await page.fill('#expression', '');
        await page.locator('#expression').pressSequentially('|x*2|');
        expect(await page.inputValue('#expression')).toBe('∣x·2∣');
    });

    // The Greek letters are a dropdown here as they are in a statement box, rather than the button
    // each that ε and δ used to have: a level can name a variable with any of them, and an
    // expression has to be able to write the name it was given.
    test('the dialog offers the Greek alphabet in a dropdown, not just ε and δ', async ({ page }) => {
        await olorin.dragRule('expr', 420, 240);
        await page.waitForSelector('#expressionBG', { state: 'visible' });
        const menus = await page.evaluate(() => Array.from(document.querySelectorAll('#exprPalette select'))
            .map((s) => Array.from(s.options).map((o) => o.textContent)));
        expect(menus).toHaveLength(1);
        const [label, ...letters] = menus[0];
        expect(label).toBe('Greek');
        expect(letters).toEqual(expect.arrayContaining(['α', 'δ', 'ε', 'λ', 'π', 'ω']));

        // What the dropdown holds is no longer a button of its own.
        const buttons = await page.evaluate(() => Array.from(
            document.querySelectorAll('#exprPalette .unicode-button')).map((b) => b.textContent));
        for (const letter of letters) {
            expect(buttons).not.toContain(letter);
        }

        // And picking one types it into the box, at the cursor.
        await page.fill('#expression', 'x2');
        await page.evaluate(() => document.getElementById('expression').setSelectionRange(1, 1));
        await page.selectOption('#exprPalette select', 'ε');
        expect(await page.inputValue('#expression')).toBe('xε2');
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

    // The names a block binds live on its node entry, in the order its value ports hand them out.
    const boundName = async (page, id) =>
          (await page.evaluate((i) => (window.__olorin.nodes().find((n) => n.id === i) || {}).names, id) || [])[0];

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
        expect((await olorin.nodes()).find((n) => n.id === id).names).toEqual(['w']);
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

    // Narya reads a name the same however it's padded, so a padded copy of a name already in use
    // is that same variable, and must be refused rather than bound a second time.
    test('and so is one that differs only by surrounding space', async ({ page }) => {
        const id = await olorin.dragRule('allI', 420, 240);
        await enterVariable(page, 'y');

        for (const padded of [' x', 'x ', '  x  ']) {
            await page.dblclick('#' + id);
            await page.fill('#newvar', padded); // the level's own variable, padded
            await page.click('#submitVariable');
            await expect(page.locator('#variableBG')).toBeVisible();
            await page.click('#cancelVariable');
            expect(await boundName(page, id)).toBe('y');
        }
        expect(await olorin.varnames()).toEqual(expect.arrayContaining(['x', 'y']));
    });

    // Almost nothing in the usual palette can go in a name, so this box offers the same Greek
    // dropdown a statement box has, and nothing else.  Nothing here reads on its exact contents:
    // what is asserted is that ε and δ are offered, that the symbols belonging to statements are
    // not, and that every letter offered both types itself in and names a variable the checker will
    // actually take -- offering a name it would refuse would be a trap.
    test('the dialog offers the Greek dropdown, and shortcuts reach it', async ({ page }) => {
        await olorin.dragRule('allI', 420, 240);
        await page.waitForSelector('#variableBG', { state: 'visible' });
        const menus = await page.evaluate(() => Array.from(document.querySelectorAll('#varnamePalette select'))
            .map((s) => Array.from(s.options).map((o) => o.textContent)));
        expect(menus).toHaveLength(1);
        const [label, ...letters] = menus[0];

        expect(label).toBe('Greek');
        expect(letters).toEqual(expect.arrayContaining(['ε', 'δ']));
        for (const logical of ['∧', '∨', '⇒', '⇔', '¬', '⊤', '⊥', '∀', '∃', '∈']) {
            expect(letters).not.toContain(logical);
        }

        for (const letter of letters) {
            await page.fill('#newvar', '');
            await page.selectOption('#varnamePalette select', letter);
            expect(await page.inputValue('#newvar')).toBe(letter);
            expect(await page.evaluate((s) => window.Narya.checkVariable(s).complete, letter), letter).toBe(true);
        }

        // The backslash shortcuts reach this box too, and the name they spell is accepted.
        await page.fill('#newvar', '');
        await page.locator('#newvar').pressSequentially('\\lambda ');
        expect(await page.inputValue('#newvar')).toBe('λ');
        await page.click('#submitVariable');
        expect(await page.isVisible('#variableBG')).toBe(false);
        expect(await olorin.varnames()).toContain('λ');
    });

    test('a padded name that is free is accepted, and kept without the padding', async ({ page }) => {
        const id = await olorin.dragRule('allI', 420, 240);
        await enterVariable(page, '  w  ');

        expect(await page.isVisible('#variableBG')).toBe(false);
        expect(await boundName(page, id)).toBe('w');
        expect((await olorin.nodes()).find((n) => n.id === id).names).toEqual(['w']);
        expect(await olorin.varnames()).toContain('w');
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
        expect(await typeAt(page, 'ab', 1, '><')).toEqual({ text: 'a×b', cursor: 2 });
        // These two are the ones that have to recognize what an earlier substitution left behind:
        // ** leaves ·· and |- leaves ∣−, each character having been converted on the way past.
        expect(await typeAt(page, 'ab', 1, '**2')).toEqual({ text: 'a²b', cursor: 2 });
        expect(await typeAt(page, 'ab', 1, '|->')).toEqual({ text: 'a↦b', cursor: 2 });
    });

    test('still work at either end', async ({ page }) => {
        expect(await typeAt(page, 'xy', 2, '*')).toEqual({ text: 'xy·', cursor: 3 });
        expect(await typeAt(page, 'xy', 0, '*')).toEqual({ text: '·xy', cursor: 1 });
    });

    // The substitutions are plain string replacements applied in order, so a sequence that spelled
    // another one as a substring -- in either direction -- would quietly swallow it.  The Greek
    // letters come close to several of the older sequences (\alpha to \all, \lambda to \land and
    // \le, \gamma to \ge, \sigma to \sim, \tau to \to, \nu to \neg, \mu to \mid, \xi to \x, \iota
    // to \in), so check that each of those still spells only what it should.
    test('of Greek letters do not swallow, or get swallowed by, the older ones', async ({ page }) => {
        const sequences = [
            ['\\alpha ', 'α'], ['\\beta ', 'β'], ['\\gamma ', 'γ'], ['\\delta ', 'δ'],
            ['\\eps ', 'ε'], ['\\epsilon ', 'ε'], ['\\zeta ', 'ζ'], ['\\eta ', 'η'],
            ['\\theta ', 'θ'], ['\\iota ', 'ι'], ['\\kappa ', 'κ'], ['\\lambda ', 'λ'],
            ['\\mu ', 'μ'], ['\\nu ', 'ν'], ['\\xi ', 'ξ'], ['\\pi ', 'π'], ['\\rho ', 'ρ'],
            ['\\sigma ', 'σ'], ['\\tau ', 'τ'], ['\\upsilon ', 'υ'], ['\\phi ', 'φ'],
            ['\\chi ', 'χ'], ['\\psi ', 'ψ'], ['\\omega ', 'ω'],
            // And the older sequences those come closest to.
            ['\\all ', '∀'], ['\\land ', '∧'], ['\\le', '≤'], ['\\ge', '≥'], ['\\sim', '∼'],
            ['\\to ', '→'], ['\\top ', '⊤'], ['\\neg ', '¬'], ['\\neq', '≠'], ['\\mid ', '∣'],
            ['\\x ', '×'], ['\\in ', '∈'], ['\\ex ', '∃'], ['\\sqrt ', '√'], ['\\R ', 'ℝ'],
        ];
        for (const [keys, symbol] of sequences) {
            expect(await typeAt(page, '', 0, keys), keys).toEqual({ text: symbol, cursor: 1 });
        }
    });
});


// The palette below a statement box holds a button per symbol, and the row has to stay one line
// long: the number systems and the Greek alphabet are folded into dropdowns rather than taking a
// button each, and ∼ and ∣ have none at all, since ~ and | already type them.
test.describe('The symbol palette', () => {
    test.beforeEach(async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.openChooser();
        await page.click('#customLevel');
    });

    // What the row is for: it wrapped onto a second line before the dropdowns took the bulk of it.
    test('fits on a single line', async ({ page }) => {
        const row = await page.evaluate(() => {
            const pal = document.getElementById('conclPalette');
            return {
                height: pal.getBoundingClientRect().height,
                tallest: Math.max(...Array.from(pal.children).map((k) => k.getBoundingClientRect().height)),
            };
        });
        // A second line would take the row to twice the height of the tallest thing on it.
        expect(row.height).toBeLessThan(row.tallest * 2);
    });

    test('offers the number systems and the Greek alphabet in dropdowns', async ({ page }) => {
        const menus = await page.evaluate(() => Array.from(document.querySelectorAll('#conclPalette select'))
            .map((s) => Array.from(s.options).map((o) => o.textContent)));
        const [numbers, greek] = menus;

        expect(numbers[0]).toBe('sets');
        expect(numbers).toEqual(expect.arrayContaining(['ℕ', 'ℤ', 'ℚ', 'ℝ', 'ℝ₊', 'ℂ', '𝕊']));
        expect(greek[0]).toBe('Greek');
        expect(greek).toEqual(expect.arrayContaining(['α', 'δ', 'ε', 'λ', 'π', 'ω']));
        // Whatever they hold is no longer a button, and the connectives are still buttons.
        const buttons = await page.evaluate(() => Array.from(
            document.querySelectorAll('#conclPalette .unicode-button')).map((b) => b.textContent));
        expect(buttons).toEqual(expect.arrayContaining(['∧', '∨', '⇒', '⇔', '¬', '∀', '∃', '∈']));
        for (const grouped of ['ℕ', 'ℝ₊', '𝕊', 'ε', 'δ']) {
            expect(buttons).not.toContain(grouped);
        }
    });

    test('types what is picked out of a dropdown at the cursor', async ({ page }) => {
        await page.fill('#conclusion', 'xy');
        await page.evaluate(() => document.getElementById('conclusion').setSelectionRange(1, 1));

        // ℝ₊ is two characters and 𝕊 one that takes two units to write, so both put the cursor
        // somewhere a plain "one along" would miss.
        await page.selectOption('#conclPalette select >> nth=0', 'ℝ₊');
        expect(await page.inputValue('#conclusion')).toBe('xℝ₊y');
        expect(await page.evaluate(() => document.getElementById('conclusion').selectionStart)).toBe(3);

        await page.selectOption('#conclPalette select >> nth=1', 'λ');
        expect(await page.inputValue('#conclusion')).toBe('xℝ₊λy');
        // Picking the same symbol again still types it, rather than counting as no change.
        await page.selectOption('#conclPalette select >> nth=1', 'λ');
        expect(await page.inputValue('#conclusion')).toBe('xℝ₊λλy');

        await page.fill('#conclusion', '');
        await page.selectOption('#conclPalette select >> nth=0', '𝕊');
        expect(await page.evaluate(() => document.getElementById('conclusion').selectionStart)).toBe(2);
    });

    test('leaves ∼ and ∣ to the keyboard keys that look like them', async ({ page }) => {
        const buttons = await page.evaluate(() => Array.from(
            document.querySelectorAll('#conclPalette .unicode-button')).map((b) => b.textContent));
        expect(buttons).not.toContain('∼');
        expect(buttons).not.toContain('∣');
        // Which is only reasonable because typing the plain keys still produces them.
        await page.fill('#conclusion', '');
        await page.locator('#conclusion').pressSequentially('x~y|z');
        expect(await page.inputValue('#conclusion')).toBe('x∼y∣z');
    });
});
