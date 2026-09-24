// Proofs that must NOT be accepted: each one looks complete to the eye but breaks a rule of the
// game, and the test pins down which error it is rejected with, so it can't slip back in (or start
// failing for some unrelated reason and still pass).
//
// The proofs live in test/fixtures/rejected/, as exported from the app.  Like the level fixtures
// they carry their own statement in the `level` field, which finds the level to restore them on,
// so they don't depend on where that level sits in the game.  Every file there needs an entry in
// REJECTED saying why it is wrong, and every entry needs its file.

const fs = require('fs');
const path = require('path');
const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');
const { allLevels } = require('../lib/levels');
const { statementHash, unavailableRules } = require('../lib/fixtures');

const REJECTED_DIR = path.join(__dirname, '..', 'fixtures', 'rejected');

// For each rejected proof, the error it must be rejected with and the block it is reported on, and
// optionally a repair: wires which, added to the proof, make it complete -- showing that the error
// really is the only thing wrong with it.
const REJECTED = {
    // An expr block may only use variables wired to it directly.  Here "k+m" is wired only to k,
    // the witness of an ∃ that came from instantiating the induction hypothesis at m -- so the term
    // on k's wire depends on m, but that doesn't make m available to the expression.
    'expr-uses-unwired-variable.json': {
        code: 'E3100-04',
        vertex: 'rule9',
        repair: [
            {
                source: { vertex: 'rule1', sort: 'assumption', label: 'pred' },
                target: { vertex: 'rule9', sort: 'input' },
                connector: 'Flowchart',
            },
        ],
    },
};

const readRejected = (file) => JSON.parse(fs.readFileSync(path.join(REJECTED_DIR, file), 'utf8'));

// The level a rejected proof was made on, as the player sees it.
function levelOf(state) {
    const hash = statementHash(state.level);
    return allLevels().find((l) => statementHash(l) === hash);
}

// Open the proof's level and restore the proof (plus any extra wires) onto it.
async function restoreOnLevel(page, state, extra = []) {
    const olorin = new Olorin(page);
    await olorin.open();
    const level = levelOf(state);
    await olorin.selectLevel(level.name);
    // The proof has to be one a player could build there, or its rejection proves nothing.
    expect(unavailableRules(state, await olorin.paletteRules())).toEqual([]);
    await olorin.restore(Object.assign({}, state, { connections: state.connections.concat(extra) }));
    return olorin;
}

test.describe('Proofs that are rejected', () => {
    test('every rejected proof on disk says why it is rejected', () => {
        const files = fs.readdirSync(REJECTED_DIR).filter((f) => f.endsWith('.json')).sort();
        expect(files).toEqual(Object.keys(REJECTED).sort());
    });

    for (const [file, why] of Object.entries(REJECTED)) {
        test(`${file} is rejected`, async ({ page }) => {
            const state = readRejected(file);
            expect(levelOf(state), 'no level states what this proof proves').toBeTruthy();
            const olorin = await restoreOnLevel(page, state);

            expect(await olorin.isComplete()).toBe(false);
            const errors = (await olorin.diagnostics())
                .filter((d) => d.isfatal)
                .map((d) => ({ code: d.code, vertices: d.locs.filter((l) => !l.isEdge).map((l) => l.id) }));
            expect(errors).toContainEqual(expect.objectContaining({
                code: why.code,
                vertices: expect.arrayContaining([why.vertex]),
            }));
        });

        if (why.repair) {
            test(`${file} is accepted once repaired`, async ({ page }) => {
                const olorin = await restoreOnLevel(page, readRejected(file), why.repair);
                expect(await olorin.isComplete()).toBe(true);
            });
        }
    }
});
