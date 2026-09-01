// Tests for the non-modal "level complete" pop-up: completing a level shows a pop-up at the
// top with Next / Select Level (without blocking the proof or the other buttons), Next advances
// to the next level, and the pop-up hides again when the level is no longer complete.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { oneWireLevel, nextLevel, completions } = require('../lib/levels');

// A level proved by a single wire, and the level that follows it in play order.  Both come from
// levels.js rather than being named, since inserting a level renumbers the ones after it.
const LEVEL = oneWireLevel();
const SECOND = nextLevel(LEVEL);

test.describe('Level complete', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('shows a pop-up on completion whose Next advances to the next level', async () => {
        await olorin.selectLevel(LEVEL.name);
        expect(await olorin.completeBannerVisible()).toBe(false);

        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.completeBannerVisible()).toBe(true);
        // The next level in sequence is active (unlocked and unsolved), so one Next button suffices.
        expect(await olorin.levelActive(SECOND.name)).toBe(true);
        expect(await olorin.page.isVisible('#nextUnsolved')).toBe(false);

        // The pop-up is tinted to the current difficulty's color, like the conclusion box.
        const colors = await olorin.page.evaluate(() => {
            const conclId = window.__olorin.nodes().find((n) => n.rule === 'conclusion').id;
            return {
                banner: getComputedStyle(document.getElementById('levelCompleteBanner')).backgroundColor,
                conclusion: getComputedStyle(document.getElementById(conclId)).backgroundColor,
            };
        });
        expect(colors.banner).toBe(colors.conclusion);

        await olorin.next();
        expect(await olorin.currentLevelName()).toBe(SECOND.name);
        // The fresh (incomplete) level hides the pop-up again.
        expect(await olorin.completeBannerVisible()).toBe(false);
    });

    test('the pop-up is not modal: other buttons and the proof stay usable', async () => {
        await olorin.selectLevel(LEVEL.name);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.completeBannerVisible()).toBe(true);

        // No full-screen backdrop: Export still opens and Clear still works while complete.
        await olorin.page.click('#exportProof');
        expect(await olorin.isVisible('#exportBG')).toBe(true);
        await olorin.page.click('#doneExport');

        await olorin.clear();
        expect(await olorin.connections()).toHaveLength(0);
        expect(await olorin.isComplete()).toBe(false);
        expect(await olorin.completeBannerVisible()).toBe(false);
    });

    test('Select Level in the pop-up opens the level chooser', async () => {
        await olorin.selectLevel(LEVEL.name);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.completeBannerVisible()).toBe(true);

        await olorin.page.click('#selectLevelAfterComplete');
        expect(await olorin.isVisible('#levelChooseBG')).toBe(true);
    });

    test('a custom level still shows the pop-up, with only Select Level (no Next)', async () => {
        // Build a custom level (P |- P) via the dialog; custom levels have no currentLevel.
        await olorin.page.evaluate(() => {
            document.getElementById('selectLevel').click();
            document.getElementById('customLevel').click();
        });
        await olorin.page.fill('#parameters', 'P : Type');
        await olorin.page.fill('#hypotheses', 'P');
        await olorin.page.fill('#conclusion', 'P');
        await olorin.page.click('#submitLevel');
        await olorin.dismissHints();
        expect(await olorin.currentLevelName()).toBe('Custom');

        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.completeBannerVisible()).toBe(true);
        // No "Next" target for a custom level, so only the Select Level button shows.
        expect(await olorin.page.isVisible('#nextLevel')).toBe(false);
        expect(await olorin.page.isVisible('#nextUnsolved')).toBe(false);
        expect(await olorin.page.isVisible('#selectLevelAfterComplete')).toBe(true);
    });
});

test.describe('Level complete: Next vs Next Unsolved', () => {
    test('splits into two buttons when the next level in sequence is already solved', async ({ page }) => {
        const olorin = new Olorin(page);
        // The next level in sequence is fully completed, so after finishing this one it isn't
        // "active"; the next active level is a different one, so both buttons appear.
        await olorin.seed(completions([SECOND], 2));
        await olorin.open();
        await olorin.selectLevel(LEVEL.name);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });

        expect(await page.isVisible('#nextLevel')).toBe(true);
        expect(await page.isVisible('#nextUnsolved')).toBe(true);

        // "Next Unsolved" skips the solved next-in-sequence level for one that's still active.
        await olorin.nextUnsolved();
        const landed = await olorin.currentLevelName();
        expect(landed).not.toBe(SECOND.name);
        expect(await olorin.levelActive(landed)).toBe(true);
    });
});
