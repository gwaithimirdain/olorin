// Worlds that belong to a course, and the code that lets a student into them.
//
// A world with a `courses` list in levels.js is only for the students of those courses: without the
// "?code=" that names one of them, it isn't in the chooser at all, and it gates nothing and is
// gated by nothing, exactly as if levels.js didn't hold it.  With such a code, it is there -- and
// the rest of the game opens differently for the student who came for a term's work rather than to
// play through: every world outside any course is theirs at novice from the start, and the rule
// that makes a world wait on a difficulty *above* the one being opened (rule 3) is dropped.
//
// The course, its code and its worlds are read from levels.js, so adding a course or moving its
// worlds can't leave these tests testing nothing.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { courseWorlds, courseCodes, worlds, world, inWorld, completions, worldGateSeeds,
        worldCount, oneWireLevel, thresholdCount } = require('../lib/levels');

const COURSE = courseWorlds()[0];
const CODE = COURSE && courseCodes().find((c) => COURSE.courses.includes(c.course));
if (!COURSE || !CODE) {
    throw new Error('This suite needs a world in levels.js with a `courses` list, and a code in '
                  + 'COURSE_CODES for one of those courses; update levels.js or this suite.');
}

// A level of the game's own, as deep in as they go: the one a player has to reach everything else
// to get to, so that finding it open says the course opened all of them.
const DEEPEST = inWorld(worldCount()).slice(-1)[0];

const states = (olorin, name) => olorin.levelStates(name);

test.describe("A course's worlds", () => {
    test('are not in the game without its code', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect(await olorin.worldNames()).not.toContain(COURSE.name);
        // Nor are its levels anything the app knows about.
        expect(await states(olorin, COURSE.levels[0].name)).toBe(null);
    });

    test('are not in it for a code no course claims either', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open({ code: 'not-a-course-code' });
        expect(await olorin.worldNames()).not.toContain(COURSE.name);
        expect(await states(olorin, COURSE.levels[0].name)).toBe(null);
    });

    test('are there for a student with the code, after the world they follow', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open({ code: CODE.code });
        const names = await olorin.worldNames();
        expect(names).toContain(COURSE.name);
        // The game's own worlds are all still there, in their own order.
        for (const w of worlds()) { expect(names).toContain(w.name); }
    });

    // A course starts where it starts: the game's own worlds are no prerequisite for it, so its
    // first level is open the moment the student arrives with the code.
    test('start open, since the game\'s own worlds are no prerequisite for them', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open({ code: CODE.code });
        expect((await states(olorin, COURSE.levels[0].name))[0]).toBe('unlocked');
    });

    // Within the world, though, the ordinary rules still hold: the level after one with a hint
    // waits for it (rule 6).
    test('open level by level inside, as any world does', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open({ code: CODE.code });
        expect((await states(olorin, COURSE.levels[1].name))[0]).toBe('locked');
        await olorin.seed(completions([COURSE.levels[0]], 0));
        await olorin.open({ code: CODE.code });
        expect((await states(olorin, COURSE.levels[1].name))[0]).toBe('unlocked');
    });

    // A course's world passes its own gates from the start, having none -- so a snapshot that
    // counted it would announce it, to a player who can't even see it.
    test('are never announced to a player who hasn\'t got them', async ({ page }) => {
        const FIRST = oneWireLevel();
        const COUNTED = world(FIRST.world).counted;
        const olorin = new Olorin(page);
        // One short of that world's 80%, so proving this level with a single wire opens the next.
        await olorin.seed(completions(
            COUNTED.filter((l) => l !== FIRST).slice(0, thresholdCount(COUNTED.length, 0.8) - 1), 0));
        await olorin.open();
        await olorin.selectLevel(FIRST.name);
        await olorin.connect({ vertex: 'hyp0', sort: 'output' }, { vertex: 'concl0', sort: 'input' });
        await olorin.page.waitForTimeout(200);

        expect(await olorin.unlockModalVisible()).toBe(true);
        expect(await olorin.unlockModalText()).not.toContain(COURSE.name);
    });

    // And they gate nothing of the game's own: a student's last world opens at adept on what the
    // game asks for, with no part of the course among it -- otherwise a course world sitting after
    // it would hold it shut, since rule 2 asks about every world that follows.
    test('gate nothing of the game\'s own', async ({ page }) => {
        const LAST = world(worldCount());
        const olorin = new Olorin(page);
        await olorin.seed(worldGateSeeds(LAST.number, 1));
        await olorin.open({ code: CODE.code });
        expect((await states(olorin, LAST.levels[0].name))[1]).toBe('unlocked');
    });
});

test.describe('A student with a course code', () => {
    test('has every level of the game\'s own worlds at novice from the start', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open({ code: CODE.code });
        // The last level of the last world, which a player reaches only at the end of everything.
        expect((await states(olorin, DEEPEST.name))[0]).toBe('unlocked');
        // Only novice, though: the higher difficulties are still earned.
        expect((await states(olorin, DEEPEST.name))[1]).toBe('locked');
    });

    test('...which a player without the code does not', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        expect((await states(olorin, DEEPEST.name))[0]).toBe('locked');
    });
});

// The code is kept, so a course hands out its link once rather than every time.  A code in the URL
// always wins and takes the remembered one's place, which is also how a player leaves a course: an
// empty "?code=" is a code, and no course claims it.
test.describe('The code a student was given', () => {
    const seen = async (olorin) => (await olorin.worldNames()).includes(COURSE.name);

    test('is remembered, so the link is needed only once', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open({ code: CODE.code });
        expect(await seen(olorin)).toBe(true);
        // Back to the plain address: the course is still theirs.
        await olorin.open();
        expect(await seen(olorin)).toBe(true);
    });

    test('gives way to another one in the URL', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open({ code: CODE.code });
        await olorin.open({ code: 'not-a-course-code' });
        expect(await seen(olorin)).toBe(false);
        // And that is what is remembered now.
        await olorin.open();
        expect(await seen(olorin)).toBe(false);
    });

    test('is given up by an empty one', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open({ code: CODE.code });
        await olorin.open({ code: '' });
        expect(await seen(olorin)).toBe(false);
    });

    test('is not something a player without one acquires', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.open();
        expect(await seen(olorin)).toBe(false);
    });
});

// Rule 3: a world normally waits until every world followed by a world it follows is 50% complete
// one difficulty ABOVE the one being opened -- so opening world 3 at adept asks for world 1 at
// master.  A course drops that; its students haven't the whole game behind them.
test.describe('Rule 3, the difficulty above', () => {
    // Put every world on the plain chain, each following the one before it, so the relation under
    // test is this suite's and not whatever levels.js happens to declare.
    async function chain(olorin) {
        for (const w of worlds()) { await olorin.setWorldOption(w.number, 'previous', [1]); }
    }
    // World 3 at adept: world 2 is finished at adept (rule 1) and world 4 at novice (rule 2), but
    // world 1 is only at adept, where rule 3 wants master.
    const seeds = [].concat(
        completions(inWorld(1), 1), completions(inWorld(2), 1), completions(inWorld(4), 0));
    const adept = async (olorin) => (await olorin.levelStates(inWorld(3)[0].name))[1];

    test('holds a world back for a player without a code', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed(seeds);
        await olorin.open();
        await chain(olorin);
        expect(await adept(olorin)).toBe('locked');
    });

    test('is dropped for a student with one', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.seed(seeds);
        await olorin.open({ code: CODE.code });
        await chain(olorin);
        expect(await adept(olorin)).toBe('unlocked');
    });
});
