// A level's hint should pop up automatically only the first time the player visits it, and in
// particular should not reappear when returning to the level or loading its saved proof.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// Open the chooser if needed and click a level, WITHOUT auto-dismissing its hint (so the test
// can observe whether the hint popped up).
async function selectLevelKeepingHint(page, name) {
    await page.evaluate(() => {
        const bg = document.getElementById('levelChooseBG');
        if (getComputedStyle(bg).display === 'none') document.getElementById('selectLevel').click();
    });
    await page.click(`#worlds .level[data-name="${name}"]`);
    await page.waitForFunction((n) => document.getElementById('currentLevel').innerText.includes(n), name);
}

test.describe('Hints', () => {
    test('a hint shows only on the first visit, not on return or on loading a saved proof', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();

        // First visit to 1-1-1 (which has a hint): it pops up automatically.
        await selectLevelKeepingHint(page, '1-1-1');
        expect(await olorin.hintVisible()).toBe(true);
        await olorin.dismissHints();

        // Make a partial proof so the level has a saved proof to come back to.
        const andId = await olorin.dragRule('andI', 420, 230);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: andId, sort: 'input', label: 'fst' });

        // Leave and come back: the hint must NOT pop up again (it's been seen)...
        await olorin.selectLevel('1-1-2');
        await selectLevelKeepingHint(page, '1-1-1');
        expect(await olorin.hintVisible()).toBe(false);

        // ...and loading the saved proof must not pop it up either.
        expect(await olorin.savedPromptVisible()).toBe(true);
        await olorin.loadSaved();
        expect(await olorin.hintVisible()).toBe(false);
    });
});
