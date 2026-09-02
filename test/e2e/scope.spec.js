// Regression test for a proof losing most of its labels when one connection reaches out of scope.
//
// A wire from inside a binder (the ∀-introduction's variable) to something outside it can't be
// resolved in any scope, so synthesizing that fragment failed outright: every wire in it went
// blank, and the error was reported with no location at all, so nothing was even marked as wrong.
// Now the wires that no scope can resolve are reported on themselves, and the fragment is
// synthesized again without them, so the rest of it keeps its labels.

const { test, expect } = require('@playwright/test');
const { Olorin } = require('../helpers/olorin');

// A partial proof of ¬∀x∈A,P(x) ⊢ ∃x∈A,¬P(x), with a ∀-introduction binding "chez".
const STATE = {
        "level": {
            "parameters": [
                {
                    "name": "A",
                    "ty": "Type"
                },
                {
                    "name": "P",
                    "ty": "A→Type"
                }
            ],
            "variables": [],
            "hypotheses": [
                {
                    "ty": "¬∀x∈A,P(x)"
                }
            ],
            "conclusion": {
                "ty": "∃x∈A,¬P(x)"
            }
        },
        "complete": false,
        "difficulty": 0,
        "nodes": [
            {
                "id": "hyp15",
                "rule": "hypothesis",
                "left": "50px",
                "top": "489px",
                "value": "¬∀x∈A,P(x)"
            },
            {
                "id": "concl22",
                "rule": "conclusion",
                "left": "1593px",
                "top": "464px",
                "value": "∃x∈A,¬P(x)"
            },
            {
                "id": "rule128",
                "rule": "negE",
                "left": "515px",
                "top": "418px"
            },
            {
                "id": "rule129",
                "rule": "allI",
                "left": "187px",
                "top": "585px",
                "name": "chez",
                "width": "494px",
                "height": "50px",
                "variable": "chez"
            },
            {
                "id": "rule130",
                "rule": "cnegI",
                "left": "188.183px",
                "top": "897px",
                "width": "1446px",
                "height": "50px"
            },
            {
                "id": "rule131",
                "rule": "negE",
                "left": "1100px",
                "top": "522px"
            },
            {
                "id": "rule132",
                "rule": "exI",
                "left": "996px",
                "top": "633px"
            },
            {
                "id": "rule133",
                "rule": "cnegI",
                "left": "714.183px",
                "top": "777px",
                "width": "203px",
                "height": "50px"
            },
            {
                "id": "rule139",
                "rule": "negE",
                "left": "948px",
                "top": "131px"
            },
            {
                "id": "rule140",
                "rule": "exI",
                "left": "712px",
                "top": "182px"
            },
            {
                "id": "rule141",
                "rule": "cnegI",
                "left": "391px",
                "top": "288px",
                "width": "200px",
                "height": "50px"
            }
        ],
        "connections": [
            {
                "source": {
                    "vertex": "hyp15",
                    "sort": "output"
                },
                "target": {
                    "vertex": "rule128",
                    "sort": "input",
                    "label": "negation"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule129",
                    "sort": "output"
                },
                "target": {
                    "vertex": "rule128",
                    "sort": "input",
                    "label": "statement"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule130",
                    "sort": "output"
                },
                "target": {
                    "vertex": "concl22",
                    "sort": "input"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule130",
                    "sort": "assumption"
                },
                "target": {
                    "vertex": "rule131",
                    "sort": "input",
                    "label": "negation"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule131",
                    "sort": "output"
                },
                "target": {
                    "vertex": "rule130",
                    "sort": "subgoal"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule132",
                    "sort": "output"
                },
                "target": {
                    "vertex": "rule131",
                    "sort": "input",
                    "label": "statement"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule133",
                    "sort": "output"
                },
                "target": {
                    "vertex": "rule132",
                    "sort": "input",
                    "label": "property"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule130",
                    "sort": "assumption"
                },
                "target": {
                    "vertex": "rule139",
                    "sort": "input",
                    "label": "negation"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule140",
                    "sort": "output"
                },
                "target": {
                    "vertex": "rule139",
                    "sort": "input",
                    "label": "statement"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule141",
                    "sort": "output"
                },
                "target": {
                    "vertex": "rule140",
                    "sort": "input",
                    "label": "property"
                },
                "connector": "Bezier"
            },
            {
                "source": {
                    "vertex": "rule129",
                    "sort": "assumption"
                },
                "target": {
                    "vertex": "rule140",
                    "sort": "input",
                    "label": "element"
                },
                "connector": "Bezier"
            }
        ]
    };

const redWires = (page) => page.evaluate(() =>
    Array.from(document.querySelectorAll('#canvas svg path'))
        .filter((p) => p.getAttribute('stroke') === '#ff0000').length);

test.describe('An out-of-scope connection', () => {
    test('takes only its own wire down, not every label around it', async ({ page }) => {
        const olorin = new Olorin(page);
        await olorin.open();
        await olorin.buildCustom({
            parameters: STATE.level.parameters.map((p) => `${p.name} : ${p.ty}`).join('\n'),
            hypotheses: STATE.level.hypotheses.map((h) => h.ty).join('\n'),
            conclusion: STATE.level.conclusion.ty,
        });
        await olorin.restore(STATE);

        // Nothing is wrong yet: the proof is unfinished, but every wire that carries a type says so.
        await expect.poll(async () => (await olorin.labelRects()).length).toBeGreaterThan(8);
        expect(await redWires(page)).toBe(0);

        // Wire the two ports that show P(chez) together: the ∀-introduction's subgoal wants it, and
        // a box outside that binder offers it -- which puts "chez" somewhere it doesn't exist.
        const ports = await page.evaluate(() => window.__olorin.ports());
        const wants = ports.find((p) => p.sort === 'subgoal' && p.type === 'P(chez)');
        const offers = ports.find((p) => p.sort === 'assumption' && p.type === 'P(chez)');
        expect(wants && offers).toBeTruthy();
        await olorin.connect(offers, wants);

        // The offending wire is marked...
        await expect.poll(() => redWires(page)).toBeGreaterThan(0);
        // ...and the rest of the diagram is still labeled: everything that doesn't depend on the
        // variable that escaped keeps its type.
        const labels = (await olorin.labelRects()).map((l) => l.text);
        expect(labels).toEqual(expect.arrayContaining(
            ['¬∀x∈A,P(x)', '∀x∈A,P(x)', '∃x∈A,¬P(x)', '⊥']));
    });
});
