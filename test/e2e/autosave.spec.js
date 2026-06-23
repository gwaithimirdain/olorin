// End-to-end tests for autosave: the proof is saved automatically on every change, and when
// returning to a level with a saved proof the user is prompted to load it or start fresh.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

test.describe('Autosave', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('saves on change and offers to reload it on return', async () => {
        await olorin.selectLevel('1-1-1');
        // A freshly selected level with no saved progress does not prompt.
        expect(await olorin.savedPromptVisible()).toBe(false);

        const andId = await olorin.dragRule('andI', 420, 230);
        await olorin.connect(
            { vertex: 'hyp0', sort: 'output' },
            { vertex: andId, sort: 'input', label: 'fst' },
        );
        const before = await olorin.structuralState();

        // Switch away and back: the autosaved proof should be offered.
        await olorin.selectLevel('1-1-2');
        await olorin.selectLevel('1-1-1');
        expect(await olorin.savedPromptVisible()).toBe(true);

        await olorin.loadSaved();
        expect(await olorin.structuralState()).toEqual(before);
    });

    test('discarding the prompt starts fresh and forgets the save', async () => {
        await olorin.selectLevel('1-1-1');
        const andId = await olorin.dragRule('andI', 420, 230);
        await olorin.connect(
            { vertex: 'hyp0', sort: 'output' },
            { vertex: andId, sort: 'input', label: 'fst' },
        );

        await olorin.selectLevel('1-1-2');
        await olorin.selectLevel('1-1-1');
        expect(await olorin.savedPromptVisible()).toBe(true);

        await olorin.discardSaved();
        expect(await olorin.connections()).toHaveLength(0);
        expect((await olorin.nodes()).every((n) => n.rule !== 'andI')).toBe(true);

        // The save was discarded, so returning again does not prompt.
        await olorin.selectLevel('1-1-2');
        await olorin.selectLevel('1-1-1');
        expect(await olorin.savedPromptVisible()).toBe(false);
    });

    test('a completed proof is autosaved and restores as complete', async () => {
        await olorin.selectLevel('1-1-1');
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        expect(await olorin.isComplete()).toBe(true);

        await olorin.selectLevel('1-1-2');
        await olorin.selectLevel('1-1-1');
        expect(await olorin.savedPromptVisible()).toBe(true);

        await olorin.loadSaved();
        expect(await olorin.isComplete()).toBe(true);
    });

    test('Clear discards the autosave so it is not offered again', async () => {
        await olorin.selectLevel('1-1-1');
        const andId = await olorin.dragRule('andI', 420, 230);
        await olorin.connect(
            { vertex: 'hyp0', sort: 'output' },
            { vertex: andId, sort: 'input', label: 'fst' },
        );

        await olorin.clear();
        expect(await olorin.connections()).toHaveLength(0);

        await olorin.selectLevel('1-1-2');
        await olorin.selectLevel('1-1-1');
        expect(await olorin.savedPromptVisible()).toBe(false);
    });

    test('autosaves are scoped per level', async () => {
        await olorin.selectLevel('1-1-1');
        await olorin.dragRule('andI', 420, 230);

        // 1-1-2 has its own (empty) state and must not show 1-1-1's saved proof.
        await olorin.selectLevel('1-1-2');
        expect(await olorin.savedPromptVisible()).toBe(false);
    });
});
