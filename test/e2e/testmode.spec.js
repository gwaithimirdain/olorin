// The "?test" URL parameter turns on a mode for experimenting with (and testing) the game: every
// level is playable regardless of the unlock rules, and double-clicking one of a level's three
// difficulty marks toggles whether it counts as completed at that difficulty, which feeds straight
// back into the unlock rules.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { firstLevel, inStage } = require('../lib/levels');

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
