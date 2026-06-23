// Enumerate the game's levels on the Node side (for parameterizing tests and generating
// fixtures), reading the same data the client uses.
//
// client/levels.js is an ES module of pure data (no imports), so we read it, strip the
// `export` keywords, and evaluate it in a sandboxed Function.  This keeps the level list
// automatically in sync with the client with no separate build step.

const fs = require('fs');
const path = require('path');

function loadLevelsModule() {
    const src = fs.readFileSync(path.join(__dirname, '..', '..', 'client', 'levels.js'), 'utf8');
    const transformed = src
        .replace(/export\s+const\s+/g, 'const ')
        .replace(/export\s+function\s+/g, 'function ')
        + '\nreturn { LEVELS, saveable };';
    // eslint-disable-next-line no-new-func
    return new Function(transformed)();
}

// All levels, in play order, as { name, saveable }.  `name` is the "world-stage-level" id the
// app shows (1-indexed), and `saveable` is the level identity used as its localStorage key.
function allLevels() {
    const { LEVELS, saveable } = loadLevelsModule();
    const out = [];
    LEVELS.forEach((world, x) => {
        world.stages.forEach((stage, y) => {
            stage.levels.forEach((level, z) => {
                out.push({
                    name: `${x + 1}-${y + 1}-${z + 1}`,
                    saveable: saveable(level),
                    trivial: !!level.trivial,
                });
            });
        });
    });
    return out;
}

module.exports = { allLevels };
