// End-to-end tests for "Export Progress" / "Import Progress" on the level chooser: everything kept in
// localStorage goes out to a file, and comes back from it in place of whatever is there now.

const fs = require('fs');
const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { oneWireLevel } = require('../lib/levels');

// A level proved by a single wire, picked from levels.js rather than named, since ids shift.
const LEVEL = oneWireLevel();

// All of localStorage, as an object.
function storage(page) {
    return page.evaluate(() => Object.fromEntries(
        Array.from({ length: localStorage.length }, (_, i) => localStorage.key(i))
            .map((k) => [k, localStorage.getItem(k)])));
}

// Export progress from the chooser, returning the path of the downloaded file.
async function exportProgress(olorin) {
    await olorin.openChooser();
    const [download] = await Promise.all([
        olorin.page.waitForEvent('download'),
        olorin.page.click('#exportProgress'),
    ]);
    expect(download.suggestedFilename()).toMatch(/^olorin-progress-.*\.json$/);
    return download.path();
}

// Import a progress file through the chooser's hidden file input, waiting for the reload it does.
async function importProgress(olorin, file) {
    await olorin.openChooser();
    await Promise.all([
        olorin.page.waitForEvent('load'),
        olorin.page.setInputFiles('#importProgressFile', file),
    ]);
    await olorin.page.waitForFunction(() => typeof window.__olorin !== 'undefined');
}

test.describe('Progress export / import', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('exports progress to a file and imports it back after clearing', async () => {
        await olorin.selectLevel(LEVEL.name);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.isComplete()).toBe(true);
        const record = await olorin.completionRecord(LEVEL.name);
        expect(record.complete).toBe(true);
        const before = await storage(olorin.page);

        const file = await exportProgress(olorin);
        const exported = JSON.parse(fs.readFileSync(file, 'utf8'));
        expect(exported.format).toBe('olorin-progress');
        expect(exported.data).toEqual(before);

        // Forget everything, then restore it from the file.
        await olorin.openChooser();
        await olorin.page.click('#clearHistory');
        expect(await olorin.completionRecord(LEVEL.name)).toBeNull();

        await importProgress(olorin, file);
        expect(await olorin.completionRecord(LEVEL.name)).toEqual(record);
        expect(await olorin.levelStates(LEVEL.name)).toContain('completed');
        expect(await storage(olorin.page)).toEqual(before);
    });

    test('importing replaces the current progress', async () => {
        const file = await exportProgress(olorin);

        await olorin.selectLevel(LEVEL.name);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.completionRecord(LEVEL.name)).not.toBeNull();

        await importProgress(olorin, file);
        expect(await olorin.completionRecord(LEVEL.name)).toBeNull();
    });

    test('declining the confirmation leaves progress alone', async () => {
        const file = await exportProgress(olorin);

        await olorin.selectLevel(LEVEL.name);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        const before = await storage(olorin.page);

        olorin.setDialogAction('dismiss');
        const dialog = olorin.page.waitForEvent('dialog');
        await olorin.openChooser();
        await olorin.page.setInputFiles('#importProgressFile', file);
        expect((await dialog).message()).toContain('replace all your current progress');
        expect(await storage(olorin.page)).toEqual(before);
    });

    test('rejects a file that is not exported progress', async ({}, testInfo) => {
        const before = await storage(olorin.page);
        const bogus = testInfo.outputPath('bogus.json');
        fs.writeFileSync(bogus, JSON.stringify({ nodes: [] }));

        const dialog = olorin.page.waitForEvent('dialog');
        await olorin.openChooser();
        await olorin.page.setInputFiles('#importProgressFile', bogus);
        expect((await dialog).message()).toContain("isn't an exported Olorin progress file");
        expect(await storage(olorin.page)).toEqual(before);
    });
});

// Completing a level warns the player to export, when the browser might delete their progress --
// once a day or once a week at most, depending on the danger.
test.describe('Storage warning', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    // Complete LEVEL afresh: open it, or if it's already open, clear its proof to start over.
    async function complete() {
        if ((await olorin.currentLevelName()) === LEVEL.name) {
            await olorin.clear();
        } else {
            await olorin.selectLevel(LEVEL.name);
        }
        // Reopening a level numbers its boxes afresh, so find them rather than naming them.
        const nodes = await olorin.nodes();
        const hyp = nodes.find((n) => n.rule === 'hypothesis').id;
        const concl = nodes.find((n) => n.rule === 'conclusion').id;
        await olorin.connect({ vertex: hyp, sort: 'output' }, { vertex: concl, sort: 'input' });
        expect(await olorin.isComplete()).toBe(true);
    }

    const shown = (page) => page.isVisible('#storageWarningBG');

    test('is not shown when storage is safe', async () => {
        await complete();
        await olorin.page.waitForTimeout(200);
        expect(await shown(olorin.page)).toBe(false);
    });

    // Pretend the last warning was `days` days ago.
    function warnedDaysAgo(days) {
        return olorin.page.evaluate((days) => {
            const then = new Date();
            then.setDate(then.getDate() - days);
            localStorage.setItem('storageWarned', then.setHours(0, 0, 0, 0).toString());
        }, days);
    }

    test('is shown with the reason, once a day', async () => {
        await olorin.page.evaluate(() => window.__olorin.setStorageRisk('Because of reasons.', 1));
        await complete();
        await olorin.page.waitForSelector('#storageWarningBG', { state: 'visible' });
        expect(await olorin.page.innerText('#storageWarningReason')).toBe('Because of reasons.');
        await olorin.page.click('#storageWarningOK');
        expect(await shown(olorin.page)).toBe(false);

        // Not again today.
        await complete();
        await olorin.page.waitForTimeout(200);
        expect(await shown(olorin.page)).toBe(false);

        // But again the next day.
        await warnedDaysAgo(1);
        await complete();
        await olorin.page.waitForSelector('#storageWarningBG', { state: 'visible' });
    });

    test('can be shown only once a week', async () => {
        await olorin.page.evaluate(() => window.__olorin.setStorageRisk('Because of reasons.', 7));
        await complete();
        await olorin.page.waitForSelector('#storageWarningBG', { state: 'visible' });
        await olorin.page.click('#storageWarningOK');

        await warnedDaysAgo(6);
        await complete();
        await olorin.page.waitForTimeout(200);
        expect(await shown(olorin.page)).toBe(false);

        await warnedDaysAgo(7);
        await complete();
        await olorin.page.waitForSelector('#storageWarningBG', { state: 'visible' });
    });

    test('its button exports progress', async () => {
        await olorin.page.evaluate(() => window.__olorin.setStorageRisk('Because of reasons.', 1));
        await complete();
        await olorin.page.waitForSelector('#storageWarningBG', { state: 'visible' });
        const [download] = await Promise.all([
            olorin.page.waitForEvent('download'),
            olorin.page.click('#storageWarningExport'),
        ]);
        expect(download.suggestedFilename()).toMatch(/^olorin-progress-.*\.json$/);
        expect(await shown(olorin.page)).toBe(false);
    });
});
