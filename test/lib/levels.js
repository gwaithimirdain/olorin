// Enumerate the game's levels on the Node side (for parameterizing tests and generating
// fixtures), reading the same data the client uses.
//
// client/levels.js is an ES module of pure data (no imports), so we read it, strip the
// `export` keywords, and evaluate it in a sandboxed Function.  This keeps the level list
// automatically in sync with the client with no separate build step.
//
// Tests should pick their levels through the selectors below (`oneWireLevel`, `conjunctionLevel`,
// `inStage`, ...) rather than naming ids like "1-2-5": levels.js gets levels inserted and
// reordered, which renumbers everything after them.

const fs = require('fs');
const path = require('path');

function loadLevelsModule() {
    const src = fs.readFileSync(path.join(__dirname, '..', '..', 'client', 'levels.js'), 'utf8');
    const transformed = src
        .replace(/export\s+const\s+/g, 'const ')
        .replace(/export\s+function\s+/g, 'function ')
        + '\nreturn { LEVELS, saveable, legacySaveable };';
    // eslint-disable-next-line no-new-func
    return new Function(transformed)();
}

// All levels, in play order.  `name` is the "world-stage-level" id the app shows (1-indexed),
// `saveable` is the level identity used as its localStorage key, and the rest is the level's own
// data, for tests to select on.
let cached = null;
function allLevels() {
    if (cached) return cached;
    const { LEVELS, saveable, legacySaveable } = loadLevelsModule();
    const out = [];
    LEVELS.forEach((world, x) => {
        world.stages.forEach((stage, y) => {
            stage.levels.forEach((level, z) => {
                out.push({
                    name: `${x + 1}-${y + 1}-${z + 1}`,
                    world: x + 1,
                    stage: y + 1,
                    index: z + 1,
                    worldName: world.name,
                    rules: stage.rules,
                    saveable: saveable(level),
                    // DEPRECATED (see client/levels.js): the statement this level was stored under
                    // before its notation changed, for the few levels that moved; null otherwise.
                    legacySaveable: legacySaveable(level),
                    parameters: level.parameters.map((p) => p.name),
                    variables: level.variables.map((v) => v.name),
                    hypotheses: level.hypotheses.map((h) => h.ty),
                    conclusion: level.conclusion.ty,
                    trivial: !!level.trivial,
                    autoComplete: !!level.autoComplete,
                    hint: level.hint || null,
                });
            });
        });
    });
    cached = out;
    return out;
}

// The worlds' display names, in order (as the chooser and the unlock announcement show them).
function worldNames() {
    return loadLevelsModule().LEVELS.map((w) => w.name);
}

const inWorld = (w) => allLevels().filter((l) => l.world === w);
const inStage = (w, s) => allLevels().filter((l) => l.world === w && l.stage === s);
// A world's stages, in order, with the unlock options they declare in levels.js: `previous` (which
// stages back this one requires, defaulted to [1] here) and `bonus` (left out of the world total).
function stagesInWorld(w) {
    const { LEVELS } = loadLevelsModule();
    return LEVELS[w - 1].stages.map(function (stage, i) {
        return {
            number: i + 1,
            name: stage.name,
            previous: stage.previous || [1],
            bonus: !!stage.bonus,
            levels: inStage(w, i + 1),
        };
    });
}

// The stages `stage` requires to be complete (its `previous` entries that name a real stage),
// given that world's stages.
const prereqStages = (stage, stages) =>
    stage.previous.map(function (n) { return stages[stage.number - 1 - n]; }).filter(Boolean);
const worldCount = () => worldNames().length;

// The first level matching a predicate.  `what` describes what was wanted, so a levels.js change
// that removes the last such level fails with an explanation rather than "undefined.name".
function find(pred, what) {
    const level = allLevels().find(pred);
    if (!level) throw new Error(`No level in client/levels.js is ${what}; update the test's selector.`);
    return level;
}

// ===== Selectors for the kinds of level the tests need =====

// The first level of the game: the only one a fresh player has unlocked.
const firstLevel = () => allLevels()[0];

// A level proved by a single wire, from its only hypothesis straight to the conclusion.
const oneWireLevel = () =>
    find((l) => l.hypotheses.length === 1 && l.variables.length === 0 && l.conclusion === l.hypotheses[0],
        'proved by one wire (a single hypothesis identical to the conclusion)');

// A level with two hypotheses whose conclusion is their conjunction, in a stage that has both
// ∧-rules -- so a proof can be built with an andI box, and andE boxes are available too.
const conjunctionLevel = () =>
    find((l) => l.hypotheses.length === 2 && l.conclusion === `${l.hypotheses[0]}∧${l.hypotheses[1]}`
             && l.rules.includes('andI') && l.rules.includes('andE'),
        'two hypotheses P, Q with conclusion P∧Q in a stage with the andI and andE rules');

// A level whose conclusion is a statement iff itself, proved by one iffI box with each of its
// brackets closed (assumption wired to subgoal).
const iffIdentityLevel = (pred = () => true) =>
    find((l) => pred(l) && l.hypotheses.length === 0 && /^(.+)⇔\1$/.test(l.conclusion),
        'a hypothesis-free "P ⇔ P" provable by a single iffI box');

// The first level that pops a hint on its first visit.
const hintedLevel = (pred = () => true) => find((l) => l.hint && pred(l), 'given a hint');

// Some other level, to switch away to and back from.
const otherLevel = (level) => find((l) => l.name !== level.name, 'a second level');

// The next level in play order, or null at the end of the list.
const nextLevel = (level) => allLevels()[allLevels().indexOf(level) + 1] || null;

// Whether some built-in level states this ({hypotheses, conclusion} as written in the level dialog)
// -- so a test that needs a statement the app CAN'T match to a built-in level can assert as much.
function isBuiltinStatement({ hypotheses, conclusion }) {
    return allLevels().some(
        (l) => l.conclusion === conclusion && JSON.stringify(l.hypotheses) === JSON.stringify(hypotheses));
}

// ===== localStorage seeds =====

// The localStorage key under which a level's completion is recorded.
const completionKey = (level) => JSON.stringify(level.saveable);

// The key it was recorded under before its statement's notation changed, or null.  Only the
// migration tests should need this.
const legacyCompletionKey = (level) =>
    level.legacySaveable ? JSON.stringify(level.legacySaveable) : null;

// Seed pairs (for Olorin.seed) marking each level complete at a difficulty.  `extra` is merged
// into the stored record, for the per-difficulty completion `times` rule 7 reads.
const completions = (levels, difficulty, extra) =>
    levels.map((l) => [completionKey(l), JSON.stringify(Object.assign({ complete: true, difficulty }, extra))]);

// The fewest of `total` completed levels that reach fraction `frac`, computed the same way the app
// gates worlds (`done / total >= frac`), so tests don't hardcode level counts.  `thresholdCount`
// just-unlocks; `thresholdCount(total, frac) - 1` is the largest count that stays below the gate.
function thresholdCount(total, frac) {
    let need = 0;
    while (need / total < frac) need++;
    return need;
}

// Levels whose completion unlocks `level` at `difficulty` (>= 1), as [levels, difficulty] groups:
// the next world at half done one difficulty lower (rule 2), the previous world mostly done (rule
// 1), this world's earlier stages (rule 4), and this stage's earlier levels (rules 5 and 6).
// Deliberately generous -- it satisfies each gate outright rather than just clearing it.
function prereqs(level, difficulty) {
    const groups = [];
    const next = inWorld(level.world + 1);
    if (next.length > 0 && difficulty > 0) {
        groups.push([next.slice(0, thresholdCount(next.length, 0.5)), difficulty - 1]);
    }
    const prev = inWorld(level.world - 1);
    if (prev.length > 0) groups.push([prev, difficulty]);
    groups.push([inWorld(level.world).filter((l) => l.stage < level.stage), difficulty]);
    groups.push([inStage(level.world, level.stage).filter((l) => l.index < level.index), difficulty]);
    return groups.filter(([ls]) => ls.length > 0);
}

// The seed pairs for all of `prereqs`.
const prereqSeeds = (level, difficulty) =>
    prereqs(level, difficulty).flatMap(([levels, d]) => completions(levels, d));

module.exports = {
    allLevels, worldNames, worldCount, inWorld, inStage, stagesInWorld, prereqStages, find,
    firstLevel, oneWireLevel, conjunctionLevel, iffIdentityLevel, hintedLevel, otherLevel, nextLevel,
    isBuiltinStatement, completionKey, legacyCompletionKey, completions, thresholdCount, prereqs,
    prereqSeeds,
};
