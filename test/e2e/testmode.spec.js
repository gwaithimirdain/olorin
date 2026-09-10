// The "?test" URL parameter turns on a mode for experimenting with (and testing) the game: every
// level is playable regardless of the unlock rules, and double-clicking one of a level's three
// difficulty marks toggles whether it counts as completed at that difficulty, which feeds straight
// back into the unlock rules.
//
// It takes a password, which client/main.js declares and lib/testmode reads back, so that the game
// a student is given doesn't hand them all of it for typing "?test" on the end of the URL.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { firstLevel, inStage } = require('../lib/levels');
const { testPassword } = require('../lib/testmode');

const FIRST = firstLevel();
const AFTER_FIRST = inStage(FIRST.world, FIRST.stage)[1]; // gated on FIRST at novice (rule 6)

// Double-click the mark for difficulty d (0 novice, 1 adept, 2 master) of a level's button.
const toggle = (olorin, level, d) =>
    olorin.page.dblclick(`#worlds .level[data-name="${level.name}"] .level-marks .lvmark >> nth=${d}`);

test.describe('Test mode', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
        await olorin.open();
        await olorin.openChooser();
    });

    test('every level shows all three marks, even a fully locked one', async () => {
        // A level locked at novice normally collapses to a single padlock; in test mode it keeps
        // its three marks, so each difficulty can be toggled.
        expect((await olorin.levelStates(AFTER_FIRST.name))[0]).toBe('locked');
        const marks = olorin.page.locator(`#worlds .level[data-name="${AFTER_FIRST.name}"] .level-marks .lvmark`);
        expect(await marks.count()).toBe(3);
    });

    test('double-clicking a mark completes that difficulty, and feeds the unlock rules', async () => {
        expect(await olorin.levelStates(FIRST.name)).toEqual(['unlocked', 'locked', 'locked']);

        await toggle(olorin, FIRST, 0);

        expect((await olorin.levelStates(FIRST.name))[0]).toBe('completed');
        // Rule 6: completing the hinted first level unlocks the next one in the stage.
        expect((await olorin.levelStates(AFTER_FIRST.name))[0]).toBe('unlocked');
        // The completion is recorded the same way solving the level would record it.
        expect(await olorin.completionRecord(FIRST.name)).toMatchObject({ complete: true, difficulty: 0 });
    });

    test('double-clicking the same mark again clears the completion', async () => {
        await toggle(olorin, FIRST, 0);
        expect((await olorin.levelStates(FIRST.name))[0]).toBe('completed');

        await toggle(olorin, FIRST, 0);

        expect(await olorin.levelStates(FIRST.name)).toEqual(['unlocked', 'locked', 'locked']);
        expect((await olorin.levelStates(AFTER_FIRST.name))[0]).toBe('locked'); // re-locked (rule 6)
        expect(await olorin.completionRecord(FIRST.name)).toBeNull();
    });

    test('a higher difficulty completes the lower ones with it, and untoggles back to them', async () => {
        // Completion is stored as the highest difficulty done, so toggling adept marks novice too.
        await toggle(olorin, FIRST, 1);
        expect(await olorin.levelStates(FIRST.name)).toEqual(['completed', 'completed', 'locked']);

        // Toggling adept off leaves the level completed at novice.
        await toggle(olorin, FIRST, 1);
        expect((await olorin.levelStates(FIRST.name))[0]).toBe('completed');
        expect((await olorin.levelStates(FIRST.name))[1]).not.toBe('completed');
    });

    test('clicking a mark does not open the level', async () => {
        await olorin.page.click(`#worlds .level[data-name="${FIRST.name}"] .level-marks .lvmark >> nth=0`);
        // The chooser stays open and no level was loaded.
        expect(await olorin.isVisible('#levelChooseBG')).toBe(true);
        expect(await olorin.currentLevelName()).not.toBe(FIRST.name);
        // A single click is not a toggle either.
        expect((await olorin.levelStates(FIRST.name))[0]).toBe('unlocked');
    });

    test('the level button itself still opens the level', async () => {
        await olorin.selectLevel(FIRST.name);
        expect(await olorin.currentLevelName()).toBe(FIRST.name);
    });
});

// Anything but the password leaves the game exactly as a player has it.
test.describe('Without the password', () => {
    // Open the app at a query of our own, rather than through the page object (which knows the
    // password), and wait for it to be interactive.
    async function openAt(page, query) {
        await page.addInitScript(() => localStorage.setItem('visited', 'true'));
        await page.goto(query, { waitUntil: 'load' });
        await page.waitForFunction(() => typeof window.Narya !== 'undefined', null, { timeout: 30000 });
        // The chooser is already up for a fresh player; open it only if it isn't.
        await page.evaluate(() => {
            const bg = document.getElementById('levelChooseBG');
            if (getComputedStyle(bg).display === 'none') document.getElementById('selectLevel').click();
        });
    }
    // A locked level keeps its three marks in test mode and collapses to one padlock outside it.
    const marks = (page, level) =>
        page.locator(`#worlds .level[data-name="${level.name}"] .lvmark`).count();

    for (const [what, query] of [
        ['the bare parameter', '/?test'],
        ['an empty one', '/?test='],
        ['a wrong password', '/?test=notthepassword'],
        ['no parameter at all', '/'],
    ]) {
        test(`${what} leaves the seam away and the unlock rules on`, async ({ page }) => {
            await openAt(page, query);
            expect(await page.evaluate(() => typeof window.__olorin)).toBe('undefined');
            expect(await marks(page, AFTER_FIRST)).toBe(1);
        });
    }

    test('while the password itself turns it on', async ({ page }) => {
        await openAt(page, `/?test=${testPassword()}`);
        expect(await page.evaluate(() => typeof window.__olorin)).toBe('object');
        expect(await marks(page, AFTER_FIRST)).toBe(3);
    });
});
