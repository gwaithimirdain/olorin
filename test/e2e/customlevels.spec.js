// Tests for saving, listing, opening, and deleting player-made custom levels, which live in a
// "Custom" world at the bottom of the chooser as named rows.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { firstLevel } = require('../lib/levels');

// Build a custom level via the custom-level dialog (P |- P by default).
const buildCustom = (olorin, opts) => olorin.buildCustom(opts);
const openChooser = (olorin) => olorin.openChooser();
const customNames = (olorin) => olorin.customLevelNames();

// The lock state of a custom row's three difficulty marks (true = locked).
function rowLocks(olorin) {
    return olorin.page.evaluate(() => {
        const m = document.querySelectorAll('#customRows .custom-marks .lvmark');
        return [0, 1, 2].map((i) => m[i].classList.contains('locked'));
    });
}

test.describe('Custom levels', () => {
    test('the Save button shows only on a custom level', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.selectLevel(firstLevel().name);
        expect(await page.isVisible('#saveLevel')).toBe(false); // built-in
        await buildCustom(olorin);
        expect(await olorin.currentLevelName()).toBe('Custom');
        expect(await page.isVisible('#saveLevel')).toBe(true);
    });

    test('saving lists it in the Custom world; completing a difficulty unlocks the next', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildCustom(olorin); // P |- P, novice (default difficulty)
        olorin.setPromptText('My Lemma');
        await page.click('#saveLevel');
        expect(await olorin.currentLevelName()).toBe('My Lemma');

        await openChooser(olorin);
        expect(await customNames(olorin)).toEqual(['My Lemma']);
        // Saved at novice: novice unlocked, adept + master locked.
        expect(await rowLocks(olorin)).toEqual([false, true, true]);

        // Solve it at novice.
        await page.evaluate(() => (document.getElementById('levelChooseBG').style.display = 'none'));
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.completeBannerVisible()).toBe(true);

        // Novice now shows a star, and adept has unlocked.
        await openChooser(olorin);
        expect(await page.evaluate(() => {
            const m = document.querySelectorAll('#customRows .custom-marks .lvmark');
            return { novice: m[0].innerText, adeptLocked: m[1].classList.contains('locked') };
        })).toEqual({ novice: '★', adeptLocked: false });

        // Re-opening lands on the highest unlocked difficulty (Adept).
        await page.evaluate(() => document.querySelector('#customRows .custom-row').click());
        await olorin.dismissHints();
        expect(await page.textContent('#currentDifficulty')).toContain('Adept');
    });

    test('a saved custom level can be deleted', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildCustom(olorin);
        olorin.setPromptText('Trash Me');
        await page.click('#saveLevel');

        await openChooser(olorin);
        expect(await customNames(olorin)).toEqual(['Trash Me']);
        // The delete ✕ confirms (auto-accepted) then removes the row.
        await page.evaluate(() => document.querySelector('#customRows .custom-delete').click());
        expect(await customNames(olorin)).toEqual([]);
    });

    test('naming the level in the dialog saves it on submit (no separate Save needed)', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await page.evaluate(() => {
            document.getElementById('selectLevel').click();
            document.getElementById('customLevel').click();
        });
        await page.fill('#customName', 'Quick Save');
        await page.fill('#parameters', 'P : Type');
        await page.fill('#hypotheses', 'P');
        await page.fill('#conclusion', 'P');
        await page.click('#submitLevel');
        await olorin.dismissHints();
        expect(await olorin.currentLevelName()).toBe('Quick Save');
        await openChooser(olorin);
        expect(await customNames(olorin)).toEqual(['Quick Save']);
    });

    test('an unnamed custom level is not auto-saved', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildCustom(olorin); // leaves the name box empty
        expect(await olorin.currentLevelName()).toBe('Custom');
        await openChooser(olorin);
        expect(await customNames(olorin)).toEqual([]);
    });

    test('Clear resets the proof on a saved custom level', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildCustom(olorin, { parameters: 'P : Type\nQ : Type', hypotheses: 'P\nQ', conclusion: 'P∧Q' });
        olorin.setPromptText('Clearable');
        await page.click('#saveLevel');
        await olorin.dragRule('andI', 450, 250);
        expect((await olorin.nodes()).some((n) => n.rule === 'andI')).toBe(true);

        await olorin.clear(); // confirm auto-accepted

        // The level stays open (with its own fixed nodes), and the added rule and autosave are gone.
        expect(await olorin.currentLevelName()).toBe('Clearable');
        expect((await olorin.nodes()).some((n) => n.rule === 'andI')).toBe(false);
        expect(await olorin.nodes()).toHaveLength(3); // two hypotheses and the conclusion
        expect(await olorin.savedProof()).toBeNull();
    });

    test('Clear resets the proof on an unsaved custom level', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildCustom(olorin, { parameters: 'P : Type\nQ : Type', hypotheses: 'P\nQ', conclusion: 'P∧Q' });
        await olorin.dragRule('andI', 450, 250);

        await olorin.clear();

        expect(await olorin.currentLevelName()).toBe('Custom');
        expect((await olorin.nodes()).some((n) => n.rule === 'andI')).toBe(false);
        expect(await olorin.nodes()).toHaveLength(3);
    });

    test('Clear keeps a reduced difficulty on a custom level', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildCustom(olorin);
        olorin.setPromptText('Reducible');
        await page.click('#saveLevel');
        // Solve it at novice so adept unlocks, then re-open at adept and reduce back to novice.
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        // (No saved-proof prompt: the novice proof is saved under the novice key, not adept's.)
        await olorin.openCustomLevel('Reducible');
        expect(await page.textContent('#currentDifficulty')).toContain('Adept');
        await page.click('#reduceDifficulty');
        // Reducing offers the proof saved at novice; keep the (empty) current one.
        await page.click('#keepCurrentDowngrade');
        expect(await page.textContent('#currentDifficulty')).toContain('Novice');

        await olorin.clear();

        // Clearing re-opens the level where we are, not back at the highest unlocked difficulty.
        expect(await page.textContent('#currentDifficulty')).toContain('Novice');
    });

    test('a saved custom level remembers an in-progress proof', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await buildCustom(olorin, { parameters: 'P : Type\nQ : Type', hypotheses: 'P\nQ', conclusion: 'P∧Q' });
        olorin.setPromptText('Conj');
        await page.click('#saveLevel');

        // Drop a rule box (partial progress), which autosaves under the custom level's key.
        await olorin.dragRule('andI', 450, 250);
        expect(await olorin.savedProof()).not.toBeNull();

        // Re-open from the Custom world: the saved-proof prompt should appear.
        await openChooser(olorin);
        await page.evaluate(() => document.querySelector('#customRows .custom-row').click());
        await page.waitForTimeout(200);
        expect(await page.isVisible('#savedProofBG')).toBe(true);
    });
});

// A statement Narya can't parse is reported and the dialog stays open to be corrected.  The report
// used to be the end of the session: Narya answers a bad statement by raising, out of a handler
// installed outside its coroutine, so the coroutine was unwound on the way and its saved
// continuation left spent -- and every later call died with "Continuation_already_resumed", the
// dialog refusing every statement after the first bad one, good ones included.
test.describe('A custom level that does not parse', () => {
    // Drive the dialog directly rather than through buildCustom, which assumes the level is taken.
    async function submit(page, conclusion) {
        await page.evaluate(() => {
            const bg = document.getElementById('levelChooseBG');
            if (getComputedStyle(bg).display === 'none') document.getElementById('selectLevel').click();
            document.getElementById('customLevel').click();
        });
        await page.fill('#customName', '');
        await page.fill('#parameters', '');
        await page.fill('#variables', 'x ∈ ℝ');
        await page.fill('#hypotheses', '');
        await page.fill('#conclusion', conclusion);
        await page.click('#submitLevel');
    }

    test('is refused, and the next one is still accepted', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        const alerts = [];
        page.on('dialog', (d) => { alerts.push(d.message()); });
        const crashes = [];
        page.on('pageerror', (e) => crashes.push(String(e)));

        // Several in a row, since the wedge showed up on the attempt after the first failure.
        for (const bad of ['x +', '∀', '((x', 'x ∈ ∈']) {
            await submit(page, bad);
            expect(await olorin.nodes()).toEqual([]);
        }
        expect(alerts).toHaveLength(4);
        expect(alerts[0]).toContain('parse error');

        // And now a good one, which has to be taken and to typecheck.
        await submit(page, 'x·x = x²');
        await olorin.dismissHints();
        expect(await olorin.currentLevelName()).toBe('Custom');
        const nodes = await olorin.nodes();
        const alg = await olorin.dragRule('alg', 500, 200);
        await olorin.connect({ vertex: alg, sort: 'output' },
                             { vertex: nodes.find((n) => n.rule === 'conclusion').id, sort: 'input' });
        await olorin.waitForTypecheck();
        expect(await olorin.isComplete()).toBe(true);
        expect(crashes).toEqual([]);
    });

    test('leaves the level you were on exactly as it was', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        page.on('dialog', (d) => {});
        await olorin.selectLevel(firstLevel().name);
        const was = await olorin.nodes();

        await submit(page, 'x +');

        // The label used to say "Custom" for a level that never opened.
        expect(await olorin.currentLevelName()).toBe(firstLevel().name);
        expect(await olorin.nodes()).toEqual(was);
    });
});
