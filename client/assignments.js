// Assignments: a selection of levels an instructor puts together for their students, without
// touching levels.js or any server.
//
// An assignment is a small world of its own -- stages of levels, each stage with the palette its
// levels may use -- built in the game (see the assignment builder in main.js) and handed out as a
// file.  A student who loads the file has it in their chooser as a world of its own, solves its
// levels, and hands back a submission: one JSON with their proofs in it.  The instructor grades
// submissions in the game too, which re-checks every proof rather than trusting what the file
// says about it (see gradeSubmissions in main.js).
//
// This module is the part of that with no page in it: what the two files hold, and the
// spreadsheet grading ends in.  Everything that touches the diagram or the chooser is in main.js,
// beside the custom levels it most resembles.

// The version of each file's layout, written into every one so a later Olorin can tell an old
// file from a broken one.
export const ASSIGNMENT_FORMAT = 1;
export const SUBMISSION_FORMAT = 1;

// The names a difficulty goes by, as main.js shows them.  Here too, so a file can say "Adept".
export const DIFFICULTIES = ['Novice', 'Adept', 'Master'];

// ===== Levels =====

// Whether an object is a level definition a proof could be built on: the four parts of a
// statement, as levels.js and the custom-level dialog make them.
export function isLevelDef(def) {
    return !!def && Array.isArray(def.parameters) && Array.isArray(def.variables)
        && Array.isArray(def.hypotheses) && !!def.conclusion && typeof def.conclusion.ty === 'string'
        && def.parameters.every((p) => p && typeof p.name === 'string' && typeof p.ty === 'string')
        && def.variables.every((v) => v && typeof v.name === 'string' && typeof v.ty === 'string')
        && def.hypotheses.every((h) => h && typeof h.ty === 'string');
}

// A clean copy of just a level's statement, in the shape levels.js's `saveable` gives a built-in
// level -- so a level an assignment took from the game has the same identity there as in it.
export function statementOf(def) {
    return {
        parameters: def.parameters.map((p) => ({ name: p.name, ty: p.ty })),
        variables: def.variables.map((v) => ({ name: v.name, ty: v.ty })),
        hypotheses: def.hypotheses.map((h) => ({ ty: h.ty })),
        conclusion: { ty: def.conclusion.ty },
    };
}

// The identity of a level's statement as a string: what its proofs and completions are filed
// under, and what an edited assignment matches its levels up by.
export const statementKey = (def) => JSON.stringify(statementOf(def));

// The statement as a person reads it: the hypotheses, a turnstile, the conclusion.
export function statementText(def) {
    const hyps = def.hypotheses.map((h) => h.ty).join(', ');
    return (hyps ? hyps + ' ' : '') + '⊢ ' + def.conclusion.ty;
}

// A level as an assignment carries it: its statement, and the options a level may set on top of
// its stage (see levels.js) -- the extra palette rules and the block budget -- plus its hint, which
// names one of the game's own hints and so only means anything for a level taken from the game.
export function assignmentLevel(level) {
    const out = statementOf(level);
    if(Array.isArray(level.extrarules) && level.extrarules.length > 0) { out.extrarules = level.extrarules.slice(); }
    if(typeof level.maxrules === 'number') { out.maxrules = level.maxrules; }
    if(typeof level.hint === 'string') { out.hint = level.hint; }
    return out;
}

// The palette an assignment level offers: its stage's rules plus its own, or "all" for a stage
// that restricts nothing (one made of custom levels).
export function paletteOf(stage, level) {
    if(stage.rules === 'all') { return 'all'; }
    return stage.rules.concat(level.extrarules || []);
}

// ===== Assignments =====

// A fresh id for an assignment, unique enough that two made on different machines never collide.
export const newAssignmentId = () => 'a' + Date.now().toString(36) + Math.floor(Math.random() * 1e9).toString(36);

// Build an assignment.  `stages` is [{ name, rules, levels }] with the levels already in the
// shape assignmentLevel gives; `difficulty` is the one its levels open at, and count at.
export function makeAssignment({ id, title, author, difficulty, stages }) {
    const out = {
        olorinAssignment: ASSIGNMENT_FORMAT,
        id: id || newAssignmentId(),
        title: title,
        difficulty: difficulty,
        stages: stages,
    };
    if(author) { out.author = author; }
    return out;
}

const isRuleList = (rules) => rules === 'all' || (Array.isArray(rules) && rules.every((r) => typeof r === 'string'));

// Whether an object is an assignment this Olorin can play: everything the chooser and the level
// setup will read out of it is there and of the right kind.  A file that fails this is refused
// whole rather than half-loaded.
export function isAssignment(a) {
    return !!a && a.olorinAssignment === ASSIGNMENT_FORMAT
        // The id goes into localStorage keys (see assignmentProofKey in main.js), so it is kept to
        // characters that can't run into the key's own punctuation.
        && typeof a.id === 'string' && /^[A-Za-z0-9_-]{1,64}$/.test(a.id)
        && typeof a.title === 'string' && a.title.trim().length > 0
        && (a.author === undefined || typeof a.author === 'string')
        && Number.isInteger(a.difficulty) && a.difficulty >= 0 && a.difficulty <= 2
        && Array.isArray(a.stages) && a.stages.length > 0
        && a.stages.every((s) => !!s && typeof s.name === 'string' && isRuleList(s.rules)
                          && Array.isArray(s.levels) && s.levels.length > 0
                          && s.levels.every((l) => isLevelDef(l)
                                            && (l.extrarules === undefined || isRuleList(l.extrarules))
                                            && (l.maxrules === undefined || Number.isInteger(l.maxrules))
                                            && (l.hint === undefined || typeof l.hint === 'string')));
}

// A copy of an assignment holding only what isAssignment reads: whatever else a file carried
// (a student's progress, say, or fields from a later format) is left behind.
export function assignmentCopy(a) {
    return makeAssignment({
        id: a.id,
        title: a.title.trim(),
        author: a.author ? a.author.trim() : undefined,
        difficulty: a.difficulty,
        stages: a.stages.map((s) => ({
            name: s.name,
            rules: s.rules === 'all' ? 'all' : s.rules.slice(),
            levels: s.levels.map(assignmentLevel),
        })),
    });
}

// Every level of an assignment in order, each with where it sits: { s, l, stage, level, name }.
// `name` is the "stage-level" the chooser shows it as (1-based), and the label a submission's
// grades come out under.
export function assignmentLevels(a) {
    const out = [];
    a.stages.forEach((stage, s) => {
        stage.levels.forEach((level, l) => {
            out.push({ s: s, l: l, stage: stage, level: level, name: (s + 1) + '-' + (l + 1) });
        });
    });
    return out;
}

// ===== Submissions =====

// What a student hands in: who they are, the assignment as they had it (so grading needs nothing
// else), and for each level the proof they made -- at the highest difficulty they made one, and
// whether it was complete there as the game saw it.  Grading checks the proofs again, so the
// `complete` and `difficulty` here are what the student's game said, not what the grade is.
export function makeSubmission({ assignment, student, results }) {
    return {
        olorinSubmission: SUBMISSION_FORMAT,
        student: student,
        submitted: new Date().toISOString(),
        assignment: assignment,
        // results[s][l] is { difficulty, complete, proof } -- proof null for a level never started.
        results: results,
    };
}

export function isSubmission(sub) {
    return !!sub && sub.olorinSubmission === SUBMISSION_FORMAT
        && typeof sub.student === 'string' && sub.student.trim().length > 0
        && isAssignment(sub.assignment)
        && Array.isArray(sub.results) && sub.results.length === sub.assignment.stages.length
        && sub.results.every((row, s) => Array.isArray(row) && row.length === sub.assignment.stages[s].levels.length
                             && row.every((r) => !!r && (r.proof === null || (typeof r.proof === 'object' && Array.isArray(r.proof.nodes)))));
}

// A file name a submission or an assignment can be saved under: its title, in the characters
// every file system takes.
export function fileSlug(text) {
    return text.trim().replace(/[^A-Za-z0-9._-]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 60) || 'olorin';
}

// ===== Grades =====

// One line per student, one column per level, as the server's grades page lays a course out (see
// client/grades.js): 0 for a level not completed, and otherwise 1, 2 or 3 for the difficulty it
// was completed at -- as grading verified it, not as the file said.  The last column counts the
// levels completed at the assignment's difficulty or above.
//
// `graded` is [{ student, levels: [{ complete, difficulty }...] }], the levels in assignmentLevels
// order.
export function gradesCsv(assignment, graded) {
    const cell = (text) => '"' + String(text).replace(/"/g, '""') + '"';
    const names = assignmentLevels(assignment).map((x) => x.name);
    const lines = [['student'].concat(names, ['completed at ' + DIFFICULTIES[assignment.difficulty] + '+']).map(cell).join(',')];
    graded.forEach((g) => {
        const marks = g.levels.map((r) => (r.complete ? r.difficulty + 1 : 0));
        const done = g.levels.filter((r) => r.complete && r.difficulty >= assignment.difficulty).length;
        lines.push([g.student].concat(marks, [done]).map(cell).join(','));
    });
    return lines.join('\n') + '\n';
}
