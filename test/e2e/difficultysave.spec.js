// Tests for per-difficulty saved proofs: a level opened at a difficulty with no saved proof
// starts blank (no prompt), and reducing the difficulty offers to restore the lower difficulty's
// saved proof, keep the current one, or start fresh.

const fs = require('fs');
const path = require('path');
const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels } = require('../lib/levels');

const LV = allLevels();
const sav = (name) => JSON.stringify(LV.find((l) => l.name === name).saveable);
const fixture111 = fs.readFileSync(path.join(__dirname, '..', 'fixtures', 'proofs', '1-1-1.json'), 'utf8');
// 1-2-5 ((P∧Q) ⊢ Q∧P) has a rule-to-rule (internal) wire, so it is NOT auto-completed -- used for
// the re-lock tests (the easy levels now auto-complete at adept and can't be downgraded-from).
const fixture125raw = fs.readFileSync(path.join(__dirname, '..', 'fixtures', 'proofs', '1-2-5.json'), 'utf8');
const fixture125 = JSON.parse(fixture125raw);

test.describe('Per-difficulty saved proofs', () => {
    test('a level opens blank with no prompt at a difficulty that has no saved proof', async ({ page }) => {
        const olorin = new Olorin(page);
        // Load at Adept, with a saved NOVICE proof for 1-1-1 (but nothing saved at Adept).
        await olorin.seed([['difficulty', '1'], ['proof:0:' + sav('1-1-1'), fixture111]]);
        await olorin.open();
        await olorin.selectLevel('1-1-1');
        expect(await olorin.savedPromptVisible()).toBe(false);
        expect(await olorin.connections()).toHaveLength(0); // the novice proof is NOT loaded
    });

    test('reducing difficulty offers to restore the lower difficulty\'s saved proof', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed([['difficulty', '1'], ['proof:0:' + sav('1-1-1'), fixture111]]);
        await olorin.open();
        await olorin.selectLevel('1-1-1'); // opens at Adept, blank

        await page.click('#reduceDifficulty'); // -> Novice; a saved novice proof exists
        expect(await page.isVisible('#downgradeBG')).toBe(true);

        await page.click('#restoreSavedDowngrade');
        await olorin.dismissHints();
        expect(await olorin.connections()).toHaveLength(1);
        expect(await olorin.isComplete()).toBe(true);
    });

    test('reducing difficulty can keep the current proof instead', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed([['difficulty', '1'], ['proof:0:' + sav('1-1-1'), fixture111]]);
        await olorin.open();
        await olorin.selectLevel('1-1-1');
        // Build a partial proof at Adept (a dropped box), then reduce.
        await olorin.dragRule('andI', 450, 250);
        await page.click('#reduceDifficulty');
        expect(await page.isVisible('#downgradeBG')).toBe(true);

        await page.click('#keepCurrentDowngrade');
        // The current (partial) proof is kept: the andI box is still there, and it's not complete.
        expect((await olorin.nodes()).some((n) => n.rule === 'andI')).toBe(true);
        expect(await olorin.isComplete()).toBe(false);
    });

    // Make 1-2-5 reachable at Adept: world 2 >= 50% novice (rule 2), stage 1-1 complete at adept
    // (rule 4), and its stage-1-2 predecessors complete at adept (rule 5).  1-2-5 has a rule-to-rule
    // wire of its own, so it is NOT auto-completed.
    const reachAdept = () => LV.filter((l) => l.name.startsWith('2-')).slice(0, 14)
        .map((l) => [sav(l.name), JSON.stringify({ complete: true, difficulty: 0 })])
        .concat(['1-1-1', '1-1-2', '1-2-1', '1-2-2', '1-2-3', '1-2-4']
            .map((n) => [sav(n), JSON.stringify({ complete: true, difficulty: 1 })]));

    test('reducing difficulty and re-solving re-locks the higher difficulty for a while', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed([['difficulty', '1'], ...reachAdept()]);
        await olorin.open();
        await olorin.selectLevel('1-2-5'); // opens at Adept
        expect((await olorin.levelStates('1-2-5'))[1]).toBe('unlocked');

        await page.click('#reduceDifficulty'); // -> Novice (no saved novice proof, so no prompt)
        await olorin.restore(fixture125); // solve novice
        expect(await olorin.isComplete()).toBe(true);

        // Adept is re-locked now that this level's novice was just completed (rule 7).
        expect((await olorin.levelStates('1-2-5'))[1]).toBe('locked');
    });

    test('downgrading and loading the saved lower-difficulty proof also re-locks the higher one', async ({ page }) => {
        const olorin = new Olorin(page);
        // 1-2-5's novice was completed long ago (time 5 of 30), so Adept is unlocked; a saved novice
        // proof exists to restore.
        await olorin.seed([
            ['difficulty', '1'],
            ['time', '30'],
            [sav('1-2-5'), JSON.stringify({ complete: true, difficulty: 0, times: { 0: 5 } })],
            ['proof:0:' + sav('1-2-5'), fixture125raw],
            ...reachAdept(),
        ]);
        await olorin.open();
        await olorin.selectLevel('1-2-5'); // opens at Adept
        expect((await olorin.levelStates('1-2-5'))[1]).toBe('unlocked');

        await page.click('#reduceDifficulty'); // -> Novice, with a saved novice proof
        await page.click('#restoreSavedDowngrade'); // load the complete novice proof
        await olorin.dismissHints();
        expect(await olorin.isComplete()).toBe(true);

        // Loading the saved complete novice proof counts as a fresh solve -> Adept re-locked.
        expect((await olorin.levelStates('1-2-5'))[1]).toBe('locked');
        // But a re-load doesn't advance the global completion counter (still 30).
        expect(await page.evaluate(() => localStorage.getItem('time'))).toBe('30');
    });
});
