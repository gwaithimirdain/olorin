// Tests for the non-modal "level complete" pop-up: completing a level shows a pop-up at the
// top with Next / Select Level (without blocking the proof or the other buttons), Next advances
// to the next level, and the pop-up hides again when the level is no longer complete.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels } = require('../lib/levels');

const completionKey = (name) => JSON.stringify(allLevels().find((l) => l.name === name).saveable);

test.describe('Level complete', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('shows a pop-up on completion whose Next advances to the next level', async () => {
        await olorin.selectLevel('1-1-1');
        expect(await olorin.completeBannerVisible()).toBe(false);

        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.completeBannerVisible()).toBe(true);
        // The next level in sequence (1-1-2) is active, so a single Next button suffices.
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
        expect(await olorin.currentLevelName()).toBe('1-1-2');
        // The fresh (incomplete) level hides the pop-up again.
        expect(await olorin.completeBannerVisible()).toBe(false);
    });

    test('the pop-up is not modal: other buttons and the proof stay usable', async () => {
        await olorin.selectLevel('1-1-1');
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
        await olorin.selectLevel('1-1-1');
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.completeBannerVisible()).toBe(true);

        await olorin.page.click('#selectLevelAfterComplete');
        expect(await olorin.isVisible('#levelChooseBG')).toBe(true);
    });
});

test.describe('Level complete: Next vs Next Unsolved', () => {
    test('splits into two buttons when the next level in sequence is already solved', async ({ page }) => {
        const olorin = new Olorin(page);
        // 1-1-2 is fully completed, so after finishing 1-1-1 the next-in-sequence level isn't
        // "active"; the next active level (1-2-1) differs, so both buttons appear.
        await olorin.seed([[completionKey('1-1-2'), JSON.stringify({ complete: true, difficulty: 2 })]]);
        await olorin.open();
        await olorin.selectLevel('1-1-1');
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });

        expect(await page.isVisible('#nextLevel')).toBe(true);
        expect(await page.isVisible('#nextUnsolved')).toBe(true);

        // "Next Unsolved" skips the solved 1-1-2 and jumps to the next active level.
        await olorin.nextUnsolved();
        expect(await olorin.currentLevelName()).toBe('1-2-1');
    });
});
