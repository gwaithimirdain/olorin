// Tests for the non-blocking "level complete" behaviour: completing a level tints the diagram
// (it doesn't pop a modal), the corner "Next" button is disabled until the level is complete
// and then advances, and the other corner buttons stay usable while a level is complete.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

test.describe('Level complete', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('Next is disabled until complete, then advances to the next level', async () => {
        await olorin.selectLevel('1-1-1');
        expect(await olorin.nextEnabled()).toBe(false);

        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.isComplete()).toBe(true);
        expect(await olorin.nextEnabled()).toBe(true);

        await olorin.next();
        expect(await olorin.currentLevelName()).toBe('1-1-2');
        // A freshly selected (incomplete) level disables Next again.
        expect(await olorin.nextEnabled()).toBe(false);
    });

    test('completing a level does not block the other buttons', async () => {
        await olorin.selectLevel('1-1-1');
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.isComplete()).toBe(true);

        // No modal is covering the screen: Export still opens, and Clear still works.
        await olorin.page.click('#exportProof');
        expect(await olorin.isVisible('#exportBG')).toBe(true);
        await olorin.page.click('#doneExport');

        await olorin.clear();
        expect(await olorin.connections()).toHaveLength(0);
        expect(await olorin.isComplete()).toBe(false);
        expect(await olorin.nextEnabled()).toBe(false);
    });
});
