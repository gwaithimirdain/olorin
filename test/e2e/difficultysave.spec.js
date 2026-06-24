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

    test('reducing difficulty and re-solving re-locks the higher difficulty for a while', async ({ page }) => {
        const olorin = new Olorin(page);
        // World 2 >= 50% novice makes 1-1-1 reachable at Adept; load there.
        const w2 = LV.filter((l) => l.name.startsWith('2-')).slice(0, 14)
            .map((l) => [sav(l.name), JSON.stringify({ complete: true, difficulty: 0 })]);
        await olorin.seed([['difficulty', '1'], ...w2]);
        await olorin.open();
        await olorin.selectLevel('1-1-1'); // opens at Adept
        expect((await olorin.levelStates('1-1-1'))[1]).toBe('unlocked');

        await page.click('#reduceDifficulty'); // -> Novice (no saved novice proof, so no prompt)
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' }); // solve novice

        // Adept is re-locked now that this level's novice was just completed (rule 7).
        expect((await olorin.levelStates('1-1-1'))[1]).toBe('locked');
    });
});
