// End-to-end tests for the Export / Import feature: showing the current proof as JSON for
// copying, and restoring a proof from pasted JSON.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

test.describe('Export / Import', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('exports the proof as JSON and imports it back', async () => {
        await olorin.selectLevel('1-1-1');
        const andId = await olorin.dragRule('andI', 420, 230);
        await olorin.connect(
            { vertex: 'hyp0', sort: 'output' },
            { vertex: andId, sort: 'input', label: 'fst' },
        );

        const before = await olorin.structuralState();
        const json = await olorin.exportText();

        // The exported text is valid JSON describing the proof.
        const parsed = JSON.parse(json);
        expect(Array.isArray(parsed.nodes)).toBe(true);
        expect(parsed.nodes.some((n) => n.rule === 'andI')).toBe(true);
        expect(Array.isArray(parsed.connections)).toBe(true);

        // Wipe the proof, then import the exported JSON and confirm it round-trips.
        await olorin.clear();
        expect(await olorin.connections()).toHaveLength(0);

        await olorin.importText(json);
        expect(await olorin.structuralState()).toEqual(before);
    });

    test('rejects invalid JSON without changing the proof', async () => {
        await olorin.selectLevel('1-1-1');
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.dismissCompletion();
        const before = await olorin.structuralState();

        // The alert() raised for bad input is auto-accepted by the dialog handler in open().
        await olorin.importText('{ this is not json');

        // The import modal stays open on error, and the proof is untouched.
        expect(await olorin.isVisible('#importBG')).toBe(true);
        await olorin.page.click('#cancelImport');
        expect(await olorin.structuralState()).toEqual(before);
    });
});
