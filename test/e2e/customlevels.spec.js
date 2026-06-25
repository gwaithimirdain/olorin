// Tests for saving, listing, opening, and deleting player-made custom levels, which live in a
// "Custom" world at the bottom of the chooser as named rows.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// Build a custom level via the custom-level dialog (P |- P by default).
async function buildCustom(olorin, opts = {}) {
    const { parameters = 'P : Type', variables = '', hypotheses = 'P', conclusion = 'P' } = opts;
    await olorin.page.evaluate(() => {
        document.getElementById('selectLevel').click();
        document.getElementById('customLevel').click();
    });
    await olorin.page.fill('#parameters', parameters);
    await olorin.page.fill('#variables', variables);
    await olorin.page.fill('#hypotheses', hypotheses);
    await olorin.page.fill('#conclusion', conclusion);
    await olorin.page.click('#submitLevel');
    await olorin.dismissHints();
}

async function openChooser(olorin) {
    await olorin.page.evaluate(() => {
        const bg = document.getElementById('levelChooseBG');
        if (getComputedStyle(bg).display === 'none') document.getElementById('selectLevel').click();
    });
}

function customNames(olorin) {
    return olorin.page.evaluate(() =>
        Array.from(document.querySelectorAll('#customRows .custom-name')).map((e) => e.innerText));
}

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
        await olorin.selectLevel('1-1-1');
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
