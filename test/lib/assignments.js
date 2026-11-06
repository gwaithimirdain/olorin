// Assignments for the tests to hand the app, written the way client/assignments.js reads them.

// An assignment of the given stages, each { name, levels } with the levels as lib/levels.js
// records.  A stage's palette is its levels' stage's -- what the records' `rules` hold, less any
// level's own `extrarules`, which go back on the level.
function assignmentOf({ id = 'atest', title = 'Homework', author, difficulty = 0, stages }) {
    const out = {
        olorinAssignment: 1,
        id,
        title,
        difficulty,
        stages: stages.map(({ name, levels, rules }) => ({
            name,
            rules: rules || levels[0].rules.filter((r) => !levels[0].extrarules.includes(r)),
            levels: levels.map((l) => Object.assign({}, l.saveable,
                l.extrarules.length > 0 ? { extrarules: l.extrarules } : {})),
        })),
    };
    if (author) out.author = author;
    return out;
}

module.exports = { assignmentOf };
