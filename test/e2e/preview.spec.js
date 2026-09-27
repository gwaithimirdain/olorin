// The level chooser's preview panel: what's under the pointer, without opening it.
//
// A level under the pointer shows its statement -- its parameters and variables, its hypotheses over
// a line, and its conclusion under it -- and how it stands at each difficulty; so does a saved custom
// level, and a world's box on the map shows how that world stands.  Clicking still opens a level.
// With nothing under the pointer the panel is blank, but a level counts as under the pointer out to
// halfway across the gap to the next, so moving from one to the next doesn't blank it in between.
// On a touchscreen, pressing and holding does what hovering does, and lifting the finger then opens
// nothing.

const { test, expect } = require('@playwright/test');
const { Olorin, worldNodeOf } = require('../helpers/olorin');
const { allLevels, worlds, inStage } = require('../lib/levels');

function pick(pred, what) {
    const l = allLevels().find(pred);
    if (!l) throw new Error(`This suite needs a level ${what}; update it.`);
    return l;
}
// A level with something in every part of its statement.
const FULL = pick((l) => l.hypotheses.length >= 2 && l.variables.length >= 1 && l.parameters.length >= 1,
                  'with parameters, variables and at least two hypotheses');
// A level with a level after it in its stage, to cross the gap between them.
const PAIR = pick((l) => inStage(l.world, l.stage).length >= 2, 'in a stage of two or more');
const NEXT = inStage(PAIR.world, PAIR.stage)[1];
const FIRST_OF_PAIR = inStage(PAIR.world, PAIR.stage)[0];
// A world that follows another, so that a new player has it locked.
const LATER = worlds().find((w) => w.previous.length > 0);

async function open(page, seeds = []) {
    const olorin = new Olorin(page);
    await olorin.seed(seeds);
    await olorin.open();
    await olorin.openChooser();
    return olorin;
}

// What the panel shows: its title, and the text of each part of a statement in it.
function panel(page) {
    return page.evaluate(() => {
        const p = document.getElementById('levelPreview');
        const texts = (sel) => Array.from(p.querySelectorAll(sel)).map((e) => e.innerText);
        return {
            blank: p.innerHTML === '',
            title: texts('.preview-title')[0],
            context: texts('.preview-context')[0],
            hypotheses: texts('.preview-hypothesis'),
            conclusion: texts('.preview-conclusion')[0],
            follows: texts('.preview-follows')[0],
            states: Array.from(p.querySelectorAll('.preview-difficulty')).map((d) => d.dataset.state),
            blockers: texts('.preview-blockers'),
        };
    });
}

const box = (page, sel) => page.locator(sel).boundingBox();

test.describe('The preview panel', () => {
    test('is blank until something is under the pointer', async ({ page }) => {
        await open(page);
        expect((await panel(page)).blank).toBe(true);
    });

    test("shows the statement of the level under the pointer, and how it stands", async ({ page }) => {
        const olorin = await open(page);
        await olorin.previewLevel(FULL.name);
        const p = await panel(page);
        expect(p.title).toBe('Level ' + FULL.name);
        expect(p.hypotheses).toEqual(FULL.hypotheses);
        expect(p.conclusion).toBe(FULL.conclusion);
        FULL.parameters.concat(FULL.variables).forEach((x) => expect(p.context).toContain(x));
        expect(p.states).toEqual(await olorin.levelStates(FULL.name));
    });

    test("shows a locked level's statement too, and what it waits on", async ({ page }) => {
        const olorin = await open(page);
        const locked = LATER.levels[0];
        expect((await olorin.levelStates(locked.name))[0]).toBe('locked');
        await olorin.previewLevel(locked.name);
        const p = await panel(page);
        expect(p.conclusion).toBe(locked.conclusion);
        expect(p.states[0]).toBe('locked');
        expect(p.blockers.length).toBeGreaterThan(0);
    });

    test('goes blank once nothing is under the pointer', async ({ page }) => {
        const olorin = await open(page);
        await olorin.previewLevel(FULL.name);
        const header = await box(page, '#worlds .world:not([style*="none"]) .world-header');
        await page.mouse.move(header.x + 5, header.y + header.height / 2);
        await expect.poll(async () => (await panel(page)).blank).toBe(true);
    });

    test('keeps showing a level while the pointer crosses the gap to the next', async ({ page }) => {
        const olorin = await open(page);
        await olorin.previewLevel(FIRST_OF_PAIR.name);
        const a = await box(page, `#worlds .level[data-name="${FIRST_OF_PAIR.name}"]`);
        const b = await box(page, `#worlds .level[data-name="${NEXT.name}"]`);
        const y = a.y + a.height / 2;
        // Step across the gap between them a pixel at a time, never leaving the panel blank.
        for (let x = a.x + a.width - 1; x <= b.x + 1; x++) {
            await page.mouse.move(x, y);
            expect((await panel(page)).blank, `blank at x = ${x}`).toBe(false);
        }
        expect((await panel(page)).title).toBe('Level ' + NEXT.name);
        // ...and that's not just the moment's grace before it blanks: in the gap, it stays.
        await page.mouse.move((a.x + a.width + b.x) / 2, y);
        await page.waitForTimeout(400);
        expect((await panel(page)).blank).toBe(false);
    });

    test('leaves clicking to open the level', async ({ page }) => {
        const olorin = await open(page);
        const first = allLevels()[0];
        await olorin.previewLevel(first.name);
        await page.click(`#worlds .level[data-name="${first.name}"] .level-number`);
        await page.waitForFunction((n) => document.getElementById('currentLevel').innerText.includes(n), first.name);
        await olorin.dismissHints();
        // And the chooser, reopened, starts blank again.
        await olorin.openChooser();
        expect((await panel(page)).blank).toBe(true);
    });

    test("shows how a world stands, for its box on the map", async ({ page }) => {
        await open(page);
        await page.hover(`#worldMap .world-node[data-world="${LATER.number}"]`);
        await expect.poll(async () => (await panel(page)).title).toBe(LATER.name);
        const p = await panel(page);
        LATER.previous.forEach((n) => expect(p.follows).toContain(worlds().find((w) => w.number === n).name));
        expect(p.states[0]).toBe('locked');
        expect(p.blockers.length).toBeGreaterThan(0);
    });

    test("shows a saved custom level's statement", async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({ name: 'Mine', parameters: 'P : Type\nQ : Type', hypotheses: 'P∧Q', conclusion: 'Q∧P' });
        await olorin.openChooser();
        await page.click('#worldMap .world-node[data-world="custom"]');
        await page.hover('#customRows .custom-row');
        await expect.poll(async () => (await panel(page)).title).toBe('Mine');
        const p = await panel(page);
        expect(p.hypotheses).toEqual(['P∧Q']);
        expect(p.conclusion).toBe('Q∧P');
    });

    test('updates when what it shows changes', async ({ page }) => {
        // In test mode, double-clicking a level's novice mark completes it there.
        const olorin = await open(page);
        const first = allLevels()[0];
        await olorin.previewLevel(first.name);
        expect((await panel(page)).states[0]).toBe('unlocked');
        await page.dblclick(`#worlds .level[data-name="${first.name}"] .level-marks .lvmark >> nth=0`);
        await expect.poll(async () => (await panel(page)).states[0]).toBe('completed');
    });
});

test.describe('The preview panel, placed', () => {
    const where = async (page) => ({ preview: await box(page, '#levelPreview'), levels: await box(page, '#worlds') });

    test('beside the levels, where the window has room', async ({ page }) => {
        await page.setViewportSize({ width: 1400, height: 900 });
        await open(page);
        const { preview, levels } = await where(page);
        expect(preview.x).toBeGreaterThanOrEqual(levels.x + levels.width);
    });

    test("over the levels, where it hasn't", async ({ page }) => {
        await page.setViewportSize({ width: 1024, height: 768 });
        await open(page);
        const { preview, levels } = await where(page);
        expect(preview.y + preview.height).toBeLessThanOrEqual(levels.y);
    });
});

test.describe('On a touchscreen', () => {
    test.use({ hasTouch: true });

    // Touch the screen, move and lift the finger, through the browser's own touch events.
    async function finger(page) {
        const cdp = await page.context().newCDPSession(page);
        const send = (type, p) => cdp.send('Input.dispatchTouchEvent', { type, touchPoints: p ? [p] : [] });
        return {
            down: (p) => send('touchStart', p),
            move: (p) => send('touchMove', p),
            up: () => send('touchEnd'),
        };
    }
    const middle = async (page, sel) => {
        const b = await box(page, sel);
        return { x: b.x + b.width / 2, y: b.y + b.height / 2 };
    };

    test('holding a press shows the level, sliding shows the next, and lifting opens nothing', async ({ page }) => {
        const olorin = await open(page);
        await page.tap(worldNodeOf(PAIR.name));
        const f = await finger(page);
        const a = await middle(page, `#worlds .level[data-name="${FIRST_OF_PAIR.name}"]`);
        const b = await middle(page, `#worlds .level[data-name="${NEXT.name}"]`);
        await f.down(a);
        await page.waitForTimeout(100);
        expect((await panel(page)).blank).toBe(true); // not held long enough yet
        await expect.poll(async () => (await panel(page)).title).toBe('Level ' + FIRST_OF_PAIR.name);
        await f.move({ x: (a.x + b.x) / 2, y: a.y });
        await f.move(b);
        await expect.poll(async () => (await panel(page)).title).toBe('Level ' + NEXT.name);
        await f.up();
        await expect.poll(async () => (await panel(page)).blank).toBe(true);
        await page.waitForTimeout(300);
        expect(await olorin.isVisible('#levelChooseBG')).toBe(true);
        expect(await olorin.currentLevelName()).toBe('');
    });

    test('a tap still opens the level, with nothing shown', async ({ page }) => {
        // Outside test mode: there, a level's difficulty marks are buttons of their own (see
        // testmode.spec.js), and the browser takes a tap near one for a tap on it.
        await page.addInitScript(() => localStorage.setItem('visited', 'true'));
        await page.goto('/', { waitUntil: 'load' });
        await page.waitForFunction(() => typeof window.Narya !== 'undefined', null, { timeout: 30000 });
        const first = allLevels()[0];
        await page.tap(worldNodeOf(first.name));
        await page.tap(`#worlds .level[data-name="${first.name}"] .level-number`);
        await page.waitForFunction((n) => document.getElementById('currentLevel').innerText.includes(n), first.name);
        expect((await panel(page)).blank).toBe(true);
    });

    test('a drag that starts on a level scrolls, rather than showing it', async ({ page }) => {
        await open(page);
        const first = allLevels()[0];
        await page.tap(worldNodeOf(first.name));
        const f = await finger(page);
        const a = await middle(page, `#worlds .level[data-name="${first.name}"]`);
        await f.down(a);
        await f.move({ x: a.x, y: a.y - 40 });
        await page.waitForTimeout(700);
        expect((await panel(page)).blank).toBe(true);
        await f.up();
    });
});
