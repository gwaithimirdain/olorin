// Tests for assignments: an instructor's own selection of levels, handed to students as a file,
// played as a world of its own, handed back as a submission, and graded by re-checking every
// proof (see client/assignments.js and the Assignments section of client/main.js).

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { oneWireLevel, conjunctionLevel, inStage, isBuiltinStatement } = require('../lib/levels');
const { assignmentOf } = require('../lib/assignments');

// A one-wire level and a conjunction level, in a stage each: the first is solved by a wire from
// its hypothesis to its conclusion, and offers whatever its stage does.
const WIRE = oneWireLevel();
const AND = conjunctionLevel();
const HOMEWORK = assignmentOf({
    id: 'ahomework',
    title: 'Homework',
    author: 'Prof. Boole',
    stages: [
        { name: 'Wires', levels: [WIRE] },
        { name: 'Conjunction', levels: [AND] },
    ],
});

// A custom level for the builder to pick, stating something no built-in level does (P |- P, say,
// is one), so that it is plainly the custom level and not the game's in what the builder makes.
const CUSTOM = { name: 'Lemma', parameters: 'P : Type\nQ : Type\nR : Type', hypotheses: '(P∧Q)∧R', conclusion: '(P∧Q)∧R' };
if (isBuiltinStatement({ hypotheses: [CUSTOM.hypotheses], conclusion: CUSTOM.conclusion })) {
    throw new Error('CUSTOM is now a built-in level; pick a statement levels.js does not state.');
}

// Solve the one-wire level of the assignment, which is open on the diagram.  Its blocks are found
// rather than named: their ids count up over every level opened in the page.
async function solveWire(olorin) {
    const nodes = await olorin.nodes();
    const id = (rule) => nodes.find((n) => n.rule === rule).id;
    await olorin.connect({ vertex: id('hypothesis'), sort: 'output' }, { vertex: id('conclusion'), sort: 'input' });
    await olorin.waitForTypecheck();
    expect(await olorin.isComplete()).toBe(true);
}

test.describe('Assignments', () => {
    let olorin;

    test.beforeEach(async ({ page }) => {
        olorin = new Olorin(page);
    });

    test('a file brings the assignment in as a world, and it stays', async () => {
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        expect(await olorin.assignmentTitles()).toEqual(['Homework']);
        // Ahead of Custom, after the game's own worlds.
        const names = await olorin.worldNames();
        expect(names.indexOf('Homework')).toBe(names.length - 2);
        // What was stored is the assignment, with nothing done on it yet.
        const stored = await olorin.assignments();
        expect(stored).toHaveLength(1);
        expect(stored[0].assignment.title).toBe('Homework');
        expect(stored[0].progress).toEqual([[[false, false, false]], [[false, false, false]]]);
        // A plain reload still has it.
        await olorin.open();
        expect(await olorin.assignmentTitles()).toEqual(['Homework']);
    });

    test('a level opens with its stage palette, and solving it counts toward the assignment', async ({ page }) => {
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        expect(await olorin.assignmentLevelStates('Homework', '1-1')).toEqual(['unlocked', 'locked', 'locked']);
        expect(await olorin.assignmentProgress('Homework')).toBe('0/2');

        await olorin.openAssignmentLevel('Homework', '2-1');
        expect(await olorin.paletteRules()).toEqual(HOMEWORK.stages[1].rules);
        expect(await page.textContent('#currentDifficulty')).toContain('Novice');
        // An assignment's level is no custom level: nothing to Save.
        expect(await page.isVisible('#saveLevel')).toBe(false);

        await olorin.openAssignmentLevel('Homework', '1-1');
        expect(await olorin.paletteRules()).toEqual(HOMEWORK.stages[0].rules);
        await solveWire(olorin);
        expect(await olorin.completeBannerVisible()).toBe(true);
        // The proof is saved under the assignment, not under the game's own level.
        expect(await olorin.savedKey()).toContain(':assignment:ahomework:');

        // Completed at novice, so adept has opened; the chip counts it.
        await olorin.openChooser();
        expect(await olorin.assignmentLevelStates('Homework', '1-1')).toEqual(['completed', 'unlocked', 'locked']);
        expect(await olorin.assignmentProgress('Homework')).toBe('1/2');
        expect((await olorin.assignments())[0].progress[0][0]).toEqual([true, false, false]);
        // The game's own copy of the level knows nothing of it.
        expect(await olorin.completionRecord(WIRE.name)).toBeNull();

        // "Next" goes on through the assignment.
        await page.evaluate(() => (document.getElementById('levelChooseBG').style.display = 'none'));
        await olorin.next();
        expect(await olorin.currentLevelName()).toBe('Homework 2-1');
    });

    test('an assignment at Adept opens its levels there', async ({ page }) => {
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(Object.assign({}, HOMEWORK, { difficulty: 1 })));
        expect(await olorin.assignmentLevelStates('Homework', '1-1')).toEqual(['unlocked', 'unlocked', 'locked']);
        await olorin.openAssignmentLevel('Homework', '1-1');
        expect(await page.textContent('#currentDifficulty')).toContain('Adept');
    });

    test('Submit gathers the proofs, and grading checks them rather than believing them', async () => {
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        await olorin.openAssignmentLevel('Homework', '1-1');
        await solveWire(olorin);

        const text = await olorin.submitAssignment('Homework', 'Ada Lovelace');
        const submission = JSON.parse(text);
        expect(submission.olorinSubmission).toBe(1);
        expect(submission.student).toBe('Ada Lovelace');
        expect(submission.assignment.id).toBe('ahomework');
        expect(submission.results[0][0].complete).toBe(true);
        expect(submission.results[0][0].proof.connections).toHaveLength(1);
        expect(submission.results[1][0].proof).toBeNull();

        // A student who says the other level is done too, on the strength of a proof with no
        // wires in it, is found out: grading re-checks every proof.
        const solved = submission.results[0][0].proof;
        submission.results[1][0] = {
            difficulty: 0, complete: true,
            proof: Object.assign({}, solved, { level: HOMEWORK.stages[1].levels[0], connections: [] }),
        };
        const { assignment, graded } = await olorin.gradeText(JSON.stringify(submission));
        expect(assignment.id).toBe('ahomework');
        expect(graded).toHaveLength(1);
        expect(graded[0].student).toBe('Ada Lovelace');
        expect(graded[0].levels.map((v) => [v.started, v.complete, v.difficulty])).toEqual([
            [true, true, 0],
            [true, false, 0],
        ]);
        expect(await olorin.gradeRows()).toEqual([
            ['Student', '1-1', '2-1', 'Done'],
            ['Ada Lovelace', '★', '✗', '1/2'],
        ]);
    });

    test('a proof built with a block the palette does not offer does not pass', async () => {
        // The one-wire level's stage may well offer nothing at all: a block of any kind, even one
        // wired to nothing, is then one the student could not have placed.
        const strayRule = HOMEWORK.stages[0].rules.includes('andI') ? 'orI1' : 'andI';
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        await olorin.openAssignmentLevel('Homework', '1-1');
        await solveWire(olorin);
        const submission = JSON.parse(await olorin.submitAssignment('Homework', 'Ada Lovelace'));
        const proof = submission.results[0][0].proof;
        proof.nodes.push({ id: 'stray', rule: strayRule, left: '400px', top: '300px' });
        const { graded } = await olorin.gradeText(JSON.stringify(submission));
        expect(graded[0].levels[0].complete).toBe(false);
        expect(graded[0].levels[0].stray).toEqual([strayRule]);
    });

    test('a submission naming a block that is not one fails that level, not the grading', async ({ page }) => {
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        await olorin.openAssignmentLevel('Homework', '1-1');
        await solveWire(olorin);
        const submission = JSON.parse(await olorin.submitAssignment('Homework', 'Ada Lovelace'));
        // The palette bar's own element, named as a block: nothing a proof could be made of.
        const bad = JSON.parse(JSON.stringify(submission.results[0][0]));
        bad.proof.nodes.push({ id: 'x', rule: 'paletteBar', left: '0px', top: '0px' });
        submission.results[1][0] = Object.assign(bad, { proof: Object.assign(bad.proof, { level: HOMEWORK.stages[1].levels[0] }) });
        const crashes = [];
        page.on('pageerror', (e) => crashes.push(String(e)));
        const { graded } = await olorin.gradeText(JSON.stringify(submission));
        expect(graded[0].levels[0].complete).toBe(true);
        expect(graded[0].levels[1].complete).toBe(false);
        expect(graded[0].levels[1].error).toContain('paletteBar');
        expect(crashes).toEqual([]);
        // The app is still usable afterwards: a level opens and typechecks.
        await page.click('#doneGrade');
        await olorin.openAssignmentLevel('Homework', '1-1');
        await solveWire(olorin);
    });

    test('a level\'s hint must be one of the page\'s hints, and an id must be plain', async ({ page }) => {
        await olorin.open();
        const withHint = JSON.parse(JSON.stringify(HOMEWORK));
        withHint.stages[0].levels[0].hint = 'levelChooseBG';
        await olorin.loadAssignmentText(JSON.stringify(withHint));
        await olorin.openAssignmentLevel('Homework', '1-1');
        // No hint is offered for it: the named element is not a hint.
        expect(await page.isVisible('#showHint')).toBe(false);

        const alerts = [];
        page.on('dialog', (d) => { alerts.push(d.message()); });
        await olorin.loadAssignmentText(JSON.stringify(Object.assign({}, HOMEWORK, { id: 'a:b' })));
        expect(alerts).toHaveLength(1);
        await page.click('#cancelAssignmentLoad');
    });

    test('the builder makes an assignment from picked levels, whose file opens it elsewhere', async ({ page }) => {
        // Two levels of one stage, and a custom level: the built-in ones share a stage with that
        // stage's rules, and the custom one has a stage of its own with every rule.
        const [first, second] = inStage(AND.world, AND.stage);
        await olorin.open();
        await olorin.buildCustom(CUSTOM);
        const file = await olorin.buildAssignment({
            title: 'Built', author: 'Prof. Boole', difficulty: 1,
            levels: [first.name, second.name], customs: ['Lemma'],
        });
        expect(await olorin.assignmentTitles()).toEqual(['Built']);
        const [{ assignment }] = await olorin.assignments();
        // The file is the assignment as stored, whole.
        expect(JSON.parse(file)).toEqual(assignment);
        expect(assignment.title).toBe('Built');
        expect(assignment.author).toBe('Prof. Boole');
        expect(assignment.difficulty).toBe(1);
        expect(assignment.stages.map((s) => [s.rules, s.levels.length])).toEqual([
            [first.rules.filter((r) => !first.extrarules.includes(r)), 2],
            ['all', 1],
        ]);
        // A level taken from the game brings its hint along.
        expect(assignment.stages[0].levels[0]).toEqual(
            Object.assign({}, first.saveable, first.hint ? { hint: first.hint } : {}));
        expect(assignment.stages[1].levels[0].conclusion.ty).toBe(CUSTOM.conclusion);

        // The file, loaded as a student would (with nothing stored), brings the same assignment.
        await page.evaluate(() => localStorage.clear());
        await olorin.open();
        await olorin.loadAssignmentText(file);
        expect(await olorin.assignmentTitles()).toEqual(['Built']);
        expect((await olorin.assignments())[0].assignment).toEqual(assignment);
        await olorin.openAssignmentLevel('Built', '1-2');
        expect(await olorin.paletteRules()).toEqual(assignment.stages[0].rules);
    });

    test('an assignment made here can be edited, keeping what was done on the levels kept', async () => {
        await olorin.open();
        // The wire level comes before the conjunction level in the game, so it is 1-1 here.
        await olorin.buildAssignment({ title: 'Homework', levels: [WIRE.name, AND.name] });
        expect(await olorin.assignmentTools('Homework')).toContain('Edit');
        const [{ assignment: built, own }] = await olorin.assignments();
        expect(own).toBe(true);
        await olorin.openAssignmentLevel('Homework', '1-1');
        await solveWire(olorin);
        // Drop the conjunction level, keep the wire one, and rename it.
        await olorin.buildAssignment({ edit: 'Homework', title: 'Homework 2', levels: [WIRE.name] });
        expect(await olorin.assignmentTitles()).toEqual(['Homework 2']);
        const [{ assignment, progress }] = await olorin.assignments();
        expect(assignment.id).toBe(built.id);
        expect(assignment.stages).toHaveLength(1);
        expect(progress).toEqual([[[true, false, false]]]);
        expect(await olorin.assignmentProgress('Homework 2')).toBe('1/1');
    });

    test('an assignment loaded from a file cannot be edited here', async () => {
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        expect(await olorin.assignmentTools('Homework')).toEqual(['Submit', 'Share', 'Remove']);
        expect((await olorin.assignments())[0].own).toBe(false);
    });

    test('grading goes by the instructor\'s copy of the assignment, not the submission\'s', async () => {
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        await olorin.openAssignmentLevel('Homework', '1-1');
        await solveWire(olorin);
        const submission = JSON.parse(await olorin.submitAssignment('Homework', 'Ada Lovelace'));
        // A student who put an easier statement in the conjunction level's place, and proved that
        // (with the wire proof), gets nothing for the conjunction level: the instructor's level is
        // what is graded, on whatever proof the submission holds for its statement -- none.
        submission.assignment.stages[1].levels[0] = WIRE.saveable;
        submission.results[1][0] = submission.results[0][0];
        const { graded } = await olorin.gradeText(JSON.stringify(submission));
        expect(graded[0].differs).toBe(true);
        expect(graded[0].levels.map((v) => [v.started, v.complete])).toEqual([[true, true], [false, false]]);
        expect((await olorin.gradeRows())[1][0]).toBe('Ada Lovelace ⚠');
    });

    test('grading an assignment that is not in the chooser is refused', async ({ page }) => {
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        const submission = await olorin.submitAssignment('Homework', 'Ada Lovelace');
        await olorin.assignmentTool('Homework', 'Remove');
        const alerts = [];
        page.on('dialog', (d) => { alerts.push(d.message()); });
        await olorin.openChooser();
        await page.click('#gradeAssignment');
        await page.fill('#gradeText', submission);
        await page.click('#submitGrade');
        await expect.poll(() => alerts.length).toBe(1);
        expect(alerts[0]).toContain('not in your chooser');
    });

    test('Load takes an assignment from pasted text, and Remove takes it away with its proofs', async ({ page }) => {
        await olorin.open();
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        expect(await olorin.assignmentTitles()).toEqual(['Homework']);
        // The same assignment again is one assignment.
        await olorin.loadAssignmentText(JSON.stringify(HOMEWORK));
        expect(await olorin.assignmentTitles()).toEqual(['Homework']);

        await olorin.openAssignmentLevel('Homework', '1-1');
        await solveWire(olorin);
        const key = await olorin.savedKey();
        expect(await page.evaluate((k) => localStorage.getItem(k) !== null, key)).toBe(true);

        await olorin.assignmentTool('Homework', 'Remove'); // the confirm is auto-accepted
        expect(await olorin.assignmentTitles()).toEqual([]);
        expect(await olorin.assignments()).toEqual([]);
        expect(await page.evaluate((k) => localStorage.getItem(k), key)).toBeNull();
    });

    test('a file that is not an assignment is refused', async ({ page }) => {
        const alerts = [];
        await olorin.open();
        page.on('dialog', (d) => { alerts.push(d.message()); });
        await olorin.loadAssignmentText('{"title": "nope"}');
        expect(alerts).toHaveLength(1);
        expect(alerts[0]).toContain('not an assignment');
        await page.click('#cancelAssignmentLoad');
        expect(await olorin.assignmentTitles()).toEqual([]);
    });
});
