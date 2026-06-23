// Tests for the non-modal "level complete" pop-up: completing a level shows a pop-up at the
// top with Next / Select Level (without blocking the proof or the other buttons), Next advances
// to the next level, and the pop-up hides again when the level is no longer complete.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

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
