// End-to-end tests for the Save / Load feature.
//
// These drive the real built app in a browser: selecting a level, dragging rules from the
// palette, wiring ports, then exercising the Save, Clear, and Load buttons and asserting
// the proof state round-trips faithfully.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

test.describe('Save / Load', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
    });

    test('round-trips a partial proof (added node, position, connection)', async () => {
        await olorin.selectLevel('1-1-1'); // P ⊢ P

        // Build a work-in-progress proof: drop an ∧-introduction box and wire the
        // hypothesis P into its first input, without finishing the proof.
        const andId = await olorin.dragRule('andI', 420, 230);
        await olorin.connect(
            { vertex: 'hyp0', sort: 'output' },
            { vertex: andId, sort: 'input', label: 'fst' },
        );

        const before = await olorin.structuralState();
        expect(before.nodes.some((n) => n.rule === 'andI' && n.left === '420px' && n.top === '230px')).toBe(true);
        expect(before.connections).toHaveLength(1);
        expect(await olorin.isComplete()).toBe(false);

        await olorin.save();
        await olorin.clear();

        // After clearing, only the fixed level nodes remain and there are no connections.
        expect(await olorin.connections()).toHaveLength(0);
        expect((await olorin.nodes()).every((n) => n.rule !== 'andI')).toBe(true);

        await olorin.load();

        const after = await olorin.structuralState();
        expect(after).toEqual(before);
        expect(await olorin.isComplete()).toBe(false);
    });

    test('round-trips a completed proof and reports completion', async () => {
        await olorin.selectLevel('1-1-1');

        // The whole proof: connect the hypothesis directly to the conclusion.
        await olorin.connect(
            { vertex: 'hyp0', sort: 'output' },
            { vertex: 'concl0', sort: 'input' },
        );
        expect(await olorin.isComplete()).toBe(true);

        const before = await olorin.structuralState();

        await olorin.dismissCompletion(); // the "Level Complete!" modal would block the buttons
        await olorin.save();
        await olorin.clear();
        expect(await olorin.isComplete()).toBe(false);

        await olorin.load();
        await olorin.dismissCompletion();

        expect(await olorin.structuralState()).toEqual(before);
        expect(await olorin.isComplete()).toBe(true);
    });

    test('Load with no saved proof leaves the level untouched', async () => {
        await olorin.selectLevel('1-1-1');

        // No Save has happened, so Load should be a no-op (an alert, auto-dismissed) and
        // must not add stray nodes or connections.
        const before = await olorin.structuralState();
        await olorin.load();
        expect(await olorin.structuralState()).toEqual(before);
        expect(await olorin.connections()).toHaveLength(0);
    });

    test('save is scoped per level', async () => {
        // Saving on one level must not surface on a different level.
        await olorin.selectLevel('1-1-1');
        const keyA = await olorin.savedKey();
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.dismissCompletion();
        await olorin.save();

        await olorin.selectLevel('1-1-2');
        const keyB = await olorin.savedKey();
        expect(keyB).not.toEqual(keyA);

        // Loading on a level with nothing saved for it is a no-op.
        const before = await olorin.structuralState();
        await olorin.load();
        expect(await olorin.structuralState()).toEqual(before);
    });
});
