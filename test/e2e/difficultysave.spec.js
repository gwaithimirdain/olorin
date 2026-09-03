// Tests for per-difficulty saved proofs: a level opened at a difficulty with no saved proof
// starts blank (no prompt), and reducing the difficulty offers to restore the lower difficulty's
// saved proof, keep the current one, or start fresh.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { find, completionKey, prereqSeeds } = require('../lib/levels');
const { hasFixture, readFixture, readFixtureText } = require('../lib/fixtures');

// Levels are picked out of levels.js by what these tests need of them -- never by id, which shifts
// whenever a level is inserted -- among those with a captured proof in test/fixtures/proofs.

// A level proved by a single wire, for the plain saved-proof tests.
const SIMPLE = find((l) => hasFixture(l) && l.variables.length === 0
                        && l.hypotheses.length === 1 && l.conclusion === l.hypotheses[0],
    'proved by one wire and backed by a fixture proof');
// A level with a rule-to-rule (internal) wire, so it is NOT auto-completed -- used for the re-lock
// tests (the easy levels auto-complete at adept and can't be downgraded-from).  Wherever it sits,
// prereqSeeds below opens its world and its own stage for it.
const MANUAL = find((l) => hasFixture(l) && !l.autoComplete,
    'a non-auto-completing level backed by a fixture proof');
const simpleProof = readFixtureText(SIMPLE);
const manualProofRaw = readFixtureText(MANUAL);
const manualProof = readFixture(MANUAL);

test.describe('Per-difficulty saved proofs', () => {
    test('a level opens blank with no prompt at a difficulty that has no saved proof', async ({ page }) => {
        const olorin = new Olorin(page);
        // Load at Adept, with a saved NOVICE proof for the level (but nothing saved at Adept).
        await olorin.seed([['difficulty', '1'], ['proof:0:' + completionKey(SIMPLE), simpleProof]]);
        await olorin.open();
        await olorin.selectLevel(SIMPLE.name);
        expect(await olorin.savedPromptVisible()).toBe(false);
        expect(await olorin.connections()).toHaveLength(0); // the novice proof is NOT loaded
    });

    test('reducing difficulty offers to restore the lower difficulty\'s saved proof', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed([['difficulty', '1'], ['proof:0:' + completionKey(SIMPLE), simpleProof]]);
        await olorin.open();
        await olorin.selectLevel(SIMPLE.name); // opens at Adept, blank

        await page.click('#reduceDifficulty'); // -> Novice; a saved novice proof exists
        expect(await page.isVisible('#downgradeBG')).toBe(true);

        await page.click('#restoreSavedDowngrade');
        await olorin.dismissHints();
        expect(await olorin.connections()).toHaveLength(1);
        expect(await olorin.isComplete()).toBe(true);
    });

    test('reducing difficulty can keep the current proof instead', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed([['difficulty', '1'], ['proof:0:' + completionKey(SIMPLE), simpleProof]]);
        await olorin.open();
        await olorin.selectLevel(SIMPLE.name);
        // Build a partial proof at Adept (a dropped box), then reduce.
        await olorin.dragRule('andI', 450, 250);
        await page.click('#reduceDifficulty');
        expect(await page.isVisible('#downgradeBG')).toBe(true);

        await page.click('#keepCurrentDowngrade');
        // The current (partial) proof is kept: the andI box is still there, and it's not complete.
        expect((await olorin.nodes()).some((n) => n.rule === 'andI')).toBe(true);
        expect(await olorin.isComplete()).toBe(false);
    });

    // Make MANUAL reachable at Adept: the next world >= 50% novice (rule 2), the earlier stages of
    // its own world complete at adept (rule 4), and its stage predecessors complete at adept (rule 5).
    const reachAdept = () => prereqSeeds(MANUAL, 1);

    test('reducing difficulty and re-solving re-locks the higher difficulty for a while', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed([['difficulty', '1'], ...reachAdept()]);
        await olorin.open();
        await olorin.selectLevel(MANUAL.name); // opens at Adept
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('unlocked');

        await page.click('#reduceDifficulty'); // -> Novice (no saved novice proof, so no prompt)
        await olorin.restore(manualProof); // solve novice
        expect(await olorin.isComplete()).toBe(true);

        // Adept is re-locked now that this level's novice was just completed (rule 7).
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('locked');
    });

    test('downgrading and loading the saved lower-difficulty proof also re-locks the higher one', async ({ page }) => {
        const olorin = new Olorin(page);
        // Its novice was completed long ago (time 5 of 30), so Adept is unlocked; a saved novice
        // proof exists to restore.
        await olorin.seed([
            ['difficulty', '1'],
            ['time', '30'],
            [completionKey(MANUAL), JSON.stringify({ complete: true, difficulty: 0, times: { 0: 5 } })],
            ['proof:0:' + completionKey(MANUAL), manualProofRaw],
            ...reachAdept(),
        ]);
        await olorin.open();
        await olorin.selectLevel(MANUAL.name); // opens at Adept
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('unlocked');

        await page.click('#reduceDifficulty'); // -> Novice, with a saved novice proof
        await page.click('#restoreSavedDowngrade'); // load the complete novice proof
        await olorin.dismissHints();
        expect(await olorin.isComplete()).toBe(true);

        // Loading the saved complete novice proof counts as a fresh solve -> Adept re-locked.
        expect((await olorin.levelStates(MANUAL.name))[1]).toBe('locked');
        // But a re-load doesn't advance the global completion counter (still 30).
        expect(await page.evaluate(() => localStorage.getItem('time'))).toBe('30');
    });
});
