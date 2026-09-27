// The map of worlds at the top of the level chooser.
//
// Each world has a box on the map, laid out from which worlds it follows (its `previous` list in
// levels.js): a line from each world it follows, or, where several worlds all follow the same set of
// worlds, a line from each of those into a junction and one out of it to each of these.  Clicking a
// box shows that world's levels, and only those.  A course's worlds, and Custom, come after the
// whole game, joined to none of it.
//
// Everything here is read from levels.js through lib/levels, and the map is also tried on relations
// levels.js doesn't declare (set through test mode's setWorldOption), since it has to lay out
// whatever the worlds come to.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { worlds, courseWorlds, courseCodes, inWorld, completions, worldGateSeeds } = require('../lib/levels');

const COURSE = courseWorlds()[0];
const CODE = COURSE && courseCodes().find((c) => COURSE.courses.includes(c.course));

async function open(page, { seeds = [], code } = {}) {
    const olorin = new Olorin(page);
    await olorin.seed(seeds);
    await olorin.open({ code });
    await olorin.openChooser();
    return olorin;
}

// Every box on the map, as { world, left, top, right, bottom, locked, selected }, where `world` is
// its data-world: the world's number in levels.js, or "custom".  Positions are within the map.
function boxes(page) {
    return page.evaluate(() => Array.from(document.querySelectorAll('#worldMap .world-node')).map((n) => ({
        world: n.dataset.world,
        left: n.offsetLeft,
        top: n.offsetTop,
        right: n.offsetLeft + n.offsetWidth,
        bottom: n.offsetTop + n.offsetHeight,
        locked: n.classList.contains('world-node-locked'),
        selected: n.classList.contains('selected'),
    })));
}

// The relation the map draws: for each world's number, the numbers of the worlds with a line to it,
// straight or through a junction, sorted.  Also the lines themselves, as { source, target, unmet }.
async function drawn(page) {
    const lines = await page.evaluate(() => Array.from(document.querySelectorAll('#worldMapEdges .map-edge'))
        .map((e) => ({ source: e.dataset.source, target: e.dataset.target, unmet: e.classList.contains('unmet') })));
    const into = {};
    const add = (t, s) => { (into[t] = into[t] || new Set()).add(s); };
    lines.filter((l) => !l.target.startsWith('j')).forEach(function (l) {
        if (!l.source.startsWith('j')) { add(l.target, l.source); return; }
        lines.filter((m) => m.target === l.source).forEach((m) => add(l.target, m.source));
    });
    const follows = {};
    Object.entries(into).forEach(([t, ss]) => { follows[t] = [...ss].map(Number).sort((a, b) => a - b); });
    return { follows, lines };
}

// The relation levels.js declares, in the same form.
function declared(ws) {
    const follows = {};
    ws.filter((w) => w.previous.length > 0)
        .forEach((w) => { follows[w.number] = w.previous.slice().sort((a, b) => a - b); });
    return follows;
}

function expectNoOverlaps(bs) {
    bs.forEach((a, i) => bs.slice(i + 1).forEach(function (b) {
        const apart = a.right <= b.left || b.right <= a.left || a.bottom <= b.top || b.bottom <= a.top;
        expect(apart, `the boxes of worlds ${a.world} and ${b.world} overlap`).toBe(true);
    }));
}

// Each world's box stands wholly to the right of the box of every world it follows.
function expectFollowersRight(bs, follows) {
    const at = Object.fromEntries(bs.map((b) => [b.world, b]));
    Object.entries(follows).forEach(([t, ss]) => ss.forEach(function (s) {
        expect(at[t].left, `world ${t} is not right of world ${s}, which it follows`)
            .toBeGreaterThanOrEqual(at[s].right);
    }));
}

test.describe('The map of worlds', () => {
    test("has a box for each of the game's worlds, and Custom", async ({ page }) => {
        await open(page);
        const shown = (await boxes(page)).map((b) => b.world);
        expect(shown.sort()).toEqual(worlds().map((w) => String(w.number)).concat(['custom']).sort());
    });

    test('has room in each box for what is written in it', async ({ page }) => {
        await open(page);
        const cramped = await page.evaluate(() => Array.from(document.querySelectorAll(
            '#worldMap .world-node, #worldMap .world-node-name')).filter((e) => e.scrollHeight > e.clientHeight)
            .map((e) => e.innerText));
        expect(cramped).toEqual([]);
    });

    test('draws exactly the worlds each world follows', async ({ page }) => {
        await open(page);
        expect((await drawn(page)).follows).toEqual(declared(worlds()));
    });

    test('puts each world to the right of the worlds it follows, with no boxes overlapping', async ({ page }) => {
        await open(page);
        const bs = await boxes(page);
        expectNoOverlaps(bs);
        expectFollowersRight(bs, declared(worlds()));
    });

    test("greys the worlds a new player can't open yet", async ({ page }) => {
        await open(page);
        const bs = await boxes(page);
        worlds().forEach(function (w) {
            const b = bs.find((x) => x.world === String(w.number));
            expect(b.locked, w.name).toBe(w.previous.length > 0);
        });
    });

    test('draws a line solid once the world it comes from is far enough along', async ({ page }) => {
        const first = worlds().find((w) => w.previous.length === 0);
        await open(page, { seeds: completions(inWorld(first.number), 0) });
        const { lines } = await drawn(page);
        const fromFirst = lines.filter((l) => l.source === String(first.number));
        expect(fromFirst.length).toBeGreaterThan(0);
        fromFirst.forEach((l) => expect(l.unmet).toBe(false));
        lines.filter((l) => !l.source.startsWith('j') && l.source !== String(first.number))
            .forEach((l) => expect(l.unmet, `a line from world ${l.source}`).toBe(true));
        // ...and the world, complete at novice, has a star for it.
        const marks = page.locator(`#worldMap .world-node[data-world="${first.number}"] .lvmark`);
        expect(await marks.first().innerText()).toBe('★');
    });
});

// Each box counts the world's levels done, at the difficulty the world is being worked at: the
// highest it is open at, once it is 80% done at the one below.  Above novice, a level that completes
// itself there (`autoComplete`) isn't counted, done or not.
test.describe("A world's count of levels done", () => {
    const FIRST = worlds().find((w) => w.previous.length === 0);
    // The levels counted above novice.
    const MANUAL = FIRST.levels.filter((l) => !l.autoComplete);
    const count = (page, w) => page.evaluate((n) => {
        const c = document.querySelector(`#worldMap .world-node[data-world="${n}"] .world-progress`);
        return { difficulty: Number(c.dataset.difficulty), text: c.innerText };
    }, w.number);

    test('is at novice for a new player', async ({ page }) => {
        await open(page);
        for (const w of worlds()) {
            expect(await count(page, w), w.name).toEqual({ difficulty: 0, text: `0/${w.levels.length}` });
        }
    });

    test('stays at novice for a world done at novice but not open at adept', async ({ page }) => {
        const olorin = await open(page, { seeds: completions(inWorld(FIRST.number), 0) });
        expect((await olorin.levelStates(FIRST.levels[FIRST.levels.length - 1].name))[1]).toBe('locked');
        const n = FIRST.levels.length;
        expect(await count(page, FIRST)).toEqual({ difficulty: 0, text: `${n}/${n}` });
    });

    test('moves on to adept once the world is done enough at novice and open at adept', async ({ page }) => {
        const olorin = await open(page, {
            seeds: completions(inWorld(FIRST.number), 0).concat(worldGateSeeds(FIRST.number, 1)),
        });
        const solved = [];
        for (const l of MANUAL) {
            if ((await olorin.levelStates(l.name))[1] === 'completed') solved.push(l.name);
        }
        expect(await count(page, FIRST)).toEqual({ difficulty: 1, text: `${solved.length}/${MANUAL.length}` });
        // ...leaving out the levels that have completed themselves at adept -- of which, if the world
        // has any, some have, or this would be testing nothing.
        const auto = FIRST.levels.filter((x) => x.autoComplete);
        let autoDone = 0;
        for (const l of auto) {
            if ((await olorin.levelStates(l.name))[1] === 'completed') autoDone++;
        }
        if (auto.length > 0) expect(autoDone).toBeGreaterThan(0);
    });

    test('is given at every difficulty in the panel, for the world showing', async ({ page }) => {
        await open(page, { seeds: completions(inWorld(FIRST.number), 0) });
        await page.click(`#worldMap .world-node[data-world="${FIRST.number}"]`);
        const n = FIRST.levels.length, m = MANUAL.length;
        const rows = await page.evaluate(() => Array.from(document.querySelectorAll('#previewContent .preview-count'))
            .map((c) => c.innerText));
        expect(rows).toEqual([`: ${n} of ${n} levels solved`, `: 0 of ${m} levels solved`, `: 0 of ${m} levels solved`]);
    });
});

test.describe("Clicking a world's box", () => {
    test('shows only that world\'s levels, and the chooser remembers it', async ({ page }) => {
        const olorin = await open(page);
        const last = worlds()[worlds().length - 1];
        await olorin.showWorldOf(last.levels[0].name);
        expect(await olorin.shownWorlds()).toEqual([last.name]);
        expect((await boxes(page)).filter((b) => b.selected).map((b) => b.world)).toEqual([String(last.number)]);

        await page.reload({ waitUntil: 'load' });
        await page.waitForFunction(() => document.querySelectorAll('#worldMap .world-node').length > 0);
        expect(await olorin.shownWorlds()).toEqual([last.name]);
    });

    test('leaves the chooser the size it was, however many levels the world has', async ({ page }) => {
        const olorin = await open(page);
        const stages = (w) => new Set(w.levels.map((l) => l.stage)).size;
        const byStages = worlds().slice().sort((a, b) => stages(a) - stages(b));
        const size = async () => {
            const b = await page.locator('#levelChooseModal').boundingBox();
            return { width: b.width, height: b.height };
        };
        await olorin.showWorldOf(byStages[0].levels[0].name);
        const small = await size();
        await olorin.showWorldOf(byStages[byStages.length - 1].levels[0].name);
        expect(await size()).toEqual(small);
        await page.click('#worldMap .world-node[data-world="custom"]');
        expect(await size()).toEqual(small);
    });

    test('has room across for the longest stage', async ({ page }) => {
        const olorin = await open(page);
        const longest = (w) => Math.max(...[...new Set(w.levels.map((l) => l.stage))]
            .map((s) => w.levels.filter((l) => l.stage === s).length));
        const widest = worlds().slice().sort((a, b) => longest(b) - longest(a))[0];
        await olorin.showWorldOf(widest.levels[0].name);
        const cut = await page.evaluate(() => {
            const pane = document.getElementById('worlds');
            const right = pane.getBoundingClientRect().left + pane.clientWidth;
            return Array.from(pane.querySelectorAll('.level[data-name]'))
                .filter((b) => b.offsetParent && b.getBoundingClientRect().right > right)
                .map((b) => b.dataset.name);
        });
        expect(cut).toEqual([]);
    });

    test('Custom shows the saved custom levels', async ({ page }) => {
        const olorin = await open(page);
        await page.click('#worldMap .world-node[data-world="custom"]');
        expect(await olorin.shownWorlds()).toEqual(['Custom']);
        expect(await page.isVisible('#customRows')).toBe(true);
    });
});

test.describe("A course's worlds on the map", () => {
    test.skip(!COURSE || !CODE, 'levels.js has no course world with a code');

    test('come after the whole game, and before Custom, joined to none of it', async ({ page }) => {
        await open(page, { code: CODE.code });
        const bs = await boxes(page);
        const game = bs.filter((b) => worlds().some((w) => String(w.number) === b.world));
        const course = bs.filter((b) => courseWorlds().some((w) => String(w.number) === b.world));
        const custom = bs.find((b) => b.world === 'custom');
        expect(course.length).toBeGreaterThan(0);
        course.forEach(function (c) {
            game.forEach((g) => expect(c.left).toBeGreaterThanOrEqual(g.right));
            expect(custom.left).toBeGreaterThanOrEqual(c.right);
        });
        const courseNumbers = courseWorlds().map((w) => String(w.number));
        const gameNumbers = worlds().map((w) => String(w.number));
        const { follows } = await drawn(page);
        Object.entries(follows).forEach(([t, ss]) => ss.forEach(function (s) {
            expect(courseNumbers.includes(t), `a line from world ${s} to world ${t}`)
                .toBe(courseNumbers.includes(String(s)));
            expect(gameNumbers.includes(t) || courseNumbers.includes(t)).toBe(true);
        }));
    });

    test("aren't on it without the code", async ({ page }) => {
        await open(page);
        const shown = (await boxes(page)).map((b) => b.world);
        courseWorlds().forEach((w) => expect(shown).not.toContain(String(w.number)));
    });
});

// Whatever the worlds come to, the map lays them out; when they don't fit, it scrolls.
test.describe('The map, for other relations between the worlds', () => {
    // Make world `ws[i]` follow exactly the worlds `previous(i)` picks out of `ws`.
    async function relate(olorin, ws, previous) {
        for (let i = 0; i < ws.length; i++) {
            await olorin.setWorldOption(ws[i].number, 'previous', previous(i).map((w) => w.name));
        }
    }

    test('scrolls sideways for a long chain, and brings a world clicked into view', async ({ page }) => {
        const olorin = await open(page);
        const ws = worlds();
        await relate(olorin, ws, (i) => (i > 0 ? [ws[i - 1]] : []));

        const follows = {};
        ws.slice(1).forEach((w, i) => { follows[w.number] = [ws[i].number]; });
        expect((await drawn(page)).follows).toEqual(follows);
        const bs = await boxes(page);
        expectNoOverlaps(bs);
        expectFollowersRight(bs, follows);

        const map = () => page.evaluate(() => {
            const m = document.getElementById('worldMap');
            return { scrollWidth: m.scrollWidth, clientWidth: m.clientWidth, scrollLeft: m.scrollLeft,
                     moreRight: document.getElementById('worldMapFrame').classList.contains('more-right') };
        });
        const before = await map();
        expect(before.scrollWidth).toBeGreaterThan(before.clientWidth);
        expect(before.moreRight).toBe(true);

        // Picking the last world of the chain (off the end of what's showing) scrolls the map to it.
        const last = ws[ws.length - 1];
        await page.evaluate((n) => document.querySelector(`#worldMap .world-node[data-world="${n}"]`).click(), last.number);
        const after = await map();
        const box = (await boxes(page)).find((b) => b.world === String(last.number));
        expect(box.left).toBeGreaterThanOrEqual(after.scrollLeft);
        expect(box.right).toBeLessThanOrEqual(after.scrollLeft + after.clientWidth);
    });

    test('scrolls down when the worlds follow nothing', async ({ page }) => {
        const olorin = await open(page);
        const ws = worlds();
        await relate(olorin, ws, () => []);
        expect((await drawn(page)).follows).toEqual({});
        expectNoOverlaps(await boxes(page));
        const m = await page.evaluate(() => {
            const e = document.getElementById('worldMap');
            return { scrollHeight: e.scrollHeight, clientHeight: e.clientHeight };
        });
        expect(m.scrollHeight).toBeGreaterThan(m.clientHeight);
    });

    test('joins worlds all following the same worlds through a junction', async ({ page }) => {
        const olorin = await open(page);
        const ws = worlds();
        expect(ws.length, 'this needs at least four worlds').toBeGreaterThanOrEqual(4);
        // The first two worlds follow nothing, and all the rest follow both of them.
        await relate(olorin, ws, (i) => (i < 2 ? [] : [ws[0], ws[1]]));
        const { follows, lines } = await drawn(page);
        const both = [ws[0].number, ws[1].number].sort((a, b) => a - b);
        expect(follows).toEqual(Object.fromEntries(ws.slice(2).map((w) => [w.number, both])));
        // One junction: a line into it from each of the two, and one out of it to each of the rest.
        const junctions = new Set(lines.filter((l) => l.target.startsWith('j')).map((l) => l.target));
        expect(junctions.size).toBe(1);
        expect(lines.length).toBe(2 + (ws.length - 2));
        expectFollowersRight(await boxes(page), follows);
    });
});
