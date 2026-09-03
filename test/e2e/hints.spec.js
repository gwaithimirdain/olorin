// A level's hint should pop up automatically only the first time the player visits it, and in
// particular should not reappear when returning to the level or loading its saved proof.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels, hintedLevel, otherLevel } = require('../lib/levels');

// A level that pops a hint on its first visit and has a hypothesis to wire a partial proof from,
// plus any other level to leave for; taken from levels.js rather than named, since ids shift.
const HINTED = hintedLevel((l) => l.hypotheses.length > 0);
const ELSEWHERE = otherLevel(HINTED);

// Open the chooser if needed and click a level, WITHOUT auto-dismissing its hint (so the test
// can observe whether the hint popped up).
async function selectLevelKeepingHint(page, name) {
    await page.evaluate(() => {
        const bg = document.getElementById('levelChooseBG');
        if (getComputedStyle(bg).display === 'none') document.getElementById('selectLevel').click();
    });
    await page.click(`#worlds .level[data-name="${name}"] .level-number`);
    await page.waitForFunction((n) => document.getElementById('currentLevel').innerText.includes(n), name);
}

test.describe('Hints', () => {
    test('a hint shows only on the first visit, not on return or on loading a saved proof', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();

        // First visit to a level with a hint: it pops up automatically.
        await selectLevelKeepingHint(page, HINTED.name);
        expect(await olorin.hintVisible()).toBe(true);
        await olorin.dismissHints();

        // Make a partial proof so the level has a saved proof to come back to.
        const andId = await olorin.dragRule('andI', 420, 230);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: andId, sort: 'input', label: 'fst' });

        // Leave and come back: the hint must NOT pop up again (it's been seen)...
        await olorin.selectLevel(ELSEWHERE.name);
        await selectLevelKeepingHint(page, HINTED.name);
        expect(await olorin.hintVisible()).toBe(false);

        // ...and loading the saved proof must not pop it up either.
        expect(await olorin.savedPromptVisible()).toBe(true);
        await olorin.loadSaved();
        expect(await olorin.hintVisible()).toBe(false);
    });
});

// In the chooser, a level that has a hint carries an "i" in its top-right corner: blue and
// clickable once the level is open, grey while it's locked.
test.describe('Hint markers in the level chooser', () => {
    const HINTED = allLevels().filter((l) => l.hint);
    if (HINTED.length < 2) {
        throw new Error('This suite assumes at least two levels have hints; update it.');
    }

    // Every level button in the chooser, mapped to 'open', 'locked' or null (no marker at all).
    function markers(page) {
        return page.evaluate(() => Object.fromEntries(
            Array.from(document.querySelectorAll('#worlds .level'))
                .filter((el) => el.dataset.name)
                .map((el) => {
                    const b = el.querySelector('.hintbubble');
                    return [el.dataset.name, b ? (b.classList.contains('locked') ? 'locked' : 'open') : null];
                })));
    }

    // A hinted level that's open for a fresh player, and one that isn't.
    async function openAndLocked(olorin) {
        const states = {};
        for (const l of HINTED) { states[l.name] = (await olorin.levelStates(l.name))[0]; }
        const open = HINTED.find((l) => states[l.name] !== 'locked');
        const locked = HINTED.find((l) => states[l.name] === 'locked');
        expect(open && locked, 'a fresh player needs one hinted level open and one locked').toBeTruthy();
        return { open, locked };
    }

    test('exactly the levels with hints are marked, and locked ones are marked grey', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.openChooser();
        const shown = await markers(page);

        const marked = Object.entries(shown).filter(([, v]) => v !== null).map(([k]) => k);
        expect(marked.sort()).toEqual(HINTED.map((l) => l.name).sort());
        // ...and each marker's colour follows that level's own novice state.
        for (const l of HINTED) {
            const state = (await olorin.levelStates(l.name))[0];
            expect(shown[l.name], l.name).toBe(state === 'locked' ? 'locked' : 'open');
        }
    });

    test("clicking an open level's marker shows that hint, without opening the level", async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.openChooser();
        const { open } = await openAndLocked(olorin);

        await page.click(`#worlds .level[data-name="${open.name}"] .hintbubble`);
        expect(await olorin.hintVisible()).toBe(true);
        expect(await page.isVisible('#' + open.hint)).toBe(true);   // that level's hint, not just any
        expect(await page.isVisible('#levelChooseBG')).toBe(true);  // still choosing, not playing

        // Dismissing it leaves the chooser where it was.
        await olorin.dismissHints();
        expect(await olorin.hintVisible()).toBe(false);
        expect(await page.isVisible('#levelChooseBG')).toBe(true);
    });

    test("a locked level's marker shows nothing and doesn't open the level", async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.openChooser();
        const { locked } = await openAndLocked(olorin);

        await page.click(`#worlds .level[data-name="${locked.name}"] .hintbubble`);
        expect(await olorin.hintVisible()).toBe(false);
        expect(await page.isVisible('#levelChooseBG')).toBe(true);
    });

    // Reading a hint from the chooser is browsing, not playing, so it doesn't count as having seen
    // it: the level still greets the player with it the first time they open it.
    test('a hint read from the chooser still pops up on the first visit to the level', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.openChooser();
        const { open } = await openAndLocked(olorin);

        await page.click(`#worlds .level[data-name="${open.name}"] .hintbubble`);
        expect(await olorin.hintVisible()).toBe(true);
        await olorin.dismissHints();

        await selectLevelKeepingHint(page, open.name);
        expect(await olorin.hintVisible()).toBe(true);
        // And now that it has been seen on the level, it stays down.
        await olorin.dismissHints();
        await olorin.selectLevel(ELSEWHERE.name);
        await selectLevelKeepingHint(page, open.name);
        expect(await olorin.hintVisible()).toBe(false);
    });
});
