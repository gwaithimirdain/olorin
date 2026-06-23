// Generate proof fixtures for as many levels as can be solved automatically.
//
// For each level it drives the real app in a browser, plans and builds a proof using a small
// propositional strategy, and — only if the app confirms the proof is COMPLETE — writes the
// exported JSON to test/fixtures/proofs/<name>.json.  Because every written fixture is verified
// complete by the real typechecker, generated fixtures are correct by construction.  Levels it
// can't solve are left without a fixture (they show up as `fixme` in the levels spec).
//
// Strategy (propositional, no case-split / classical / quantifiers):
//   - forward: derive new facts from hypotheses by ∧-elimination and modus ponens
//   - backward: prove a goal by using a known fact directly, or by ⊤/∧/∨/⇒ introduction
//     (⇒ introduction adds a bracket whose local assumption extends the available facts)
//
// Usage (static/ must be built; see scripts/build-static.sh):
//   node test/generate-fixtures.js [--only 1-2-1,1-3-4]

const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');
const { chromium } = require('@playwright/test');
const { allLevels } = require('./lib/levels');

const PORT = process.env.OLORIN_PORT || 8127;
const FIXTURE_DIR = path.join(__dirname, 'fixtures', 'proofs');

// ---- type-string analysis (principal binary connective; no full parser) ----

const PRECEDENCE = { '⇔': 0, '⇒': 1, '∨': 2, '∧': 3 }; // loosest binding first

function norm(s) {
    s = s.trim();
    // Strip parentheses that wrap the whole string.
    for (;;) {
        if (!(s.startsWith('(') && s.endsWith(')'))) break;
        let depth = 0, wraps = true;
        for (let i = 0; i < s.length; i++) {
            if (s[i] === '(') depth++;
            else if (s[i] === ')') { depth--; if (depth === 0 && i < s.length - 1) { wraps = false; break; } }
        }
        if (wraps) s = s.slice(1, -1).trim(); else break;
    }
    return s;
}

// Split a type at its principal (top-level, loosest-binding) binary connective.
function splitPrincipal(type) {
    const t = norm(type);
    let depth = 0, best = null;
    for (let i = 0; i < t.length; i++) {
        const c = t[i];
        if (c === '(') depth++;
        else if (c === ')') depth--;
        else if (depth === 0 && PRECEDENCE[c] !== undefined) {
            if (best === null || PRECEDENCE[c] < PRECEDENCE[best.op]) best = { op: c, idx: i };
        }
    }
    if (!best) return null;
    return { op: best.op, A: norm(t.slice(0, best.idx)), B: norm(t.slice(best.idx + 1)) };
}

// Close a set of known type strings under ∧-elimination and modus ponens.
function typeClosure(base) {
    const set = new Set([...base].map(norm));
    let changed = true, guard = 0;
    while (changed && guard++ < 200) {
        changed = false;
        for (const t of [...set]) {
            const sp = splitPrincipal(t);
            if (sp && sp.op === '∧') {
                for (const x of [sp.A, sp.B]) if (!set.has(x)) { set.add(x); changed = true; }
            }
            if (sp && sp.op === '⇒' && set.has(sp.A) && !set.has(sp.B)) { set.add(sp.B); changed = true; }
        }
    }
    return set;
}

// Plan a proof of `type` given base facts (type strings).  Returns a plan tree or null.
function planType(type, baseSet) {
    const t = norm(type);
    if (typeClosure(baseSet).has(t)) return { kind: 'direct', type: t };
    if (t === '⊤') return { kind: 'topI' };
    const sp = splitPrincipal(t);
    if (sp) {
        if (sp.op === '∧') {
            const L = planType(sp.A, baseSet), R = planType(sp.B, baseSet);
            if (L && R) return { kind: 'andI', L, R };
        }
        if (sp.op === '∨') {
            const L = planType(sp.A, baseSet);
            if (L) return { kind: 'orI1', P: L };
            const R = planType(sp.B, baseSet);
            if (R) return { kind: 'orI2', P: R };
        }
        if (sp.op === '⇒') {
            const sub = planType(sp.B, new Set([...baseSet, sp.A]));
            if (sub) return { kind: 'impI', A: sp.A, sub };
        }
    }
    return null;
}

// ---- browser helpers ----

function advance(pos) {
    pos.y += 70;
    if (pos.y > 820) { pos.y = 120; pos.x += 180; }
}

async function dragRule(page, ruleId, pos) {
    const x = pos.x, y = pos.y;
    advance(pos);
    await page.evaluate(({ ruleId, x, y }) => {
        const src = document.getElementById(ruleId);
        const diagram = document.getElementById('diagram');
        const dt = new DataTransfer();
        const fire = (el, t, cx, cy) => el.dispatchEvent(new DragEvent(t, { bubbles: true, cancelable: true, dataTransfer: dt, clientX: cx, clientY: cy }));
        const sr = src.getBoundingClientRect();
        fire(src, 'dragstart', sr.x + 5, sr.y + 5);
        const dr = diagram.getBoundingClientRect();
        fire(diagram, 'dragover', dr.x + x, dr.y + y);
        fire(diagram, 'drop', dr.x + x, dr.y + y);
        fire(src, 'dragend', dr.x + x, dr.y + y);
    }, { ruleId, x, y });
    await dismissModals(page);
    return page.evaluate(() => { const n = window.__olorin.nodes(); return n[n.length - 1].id; });
}

async function connect(page, source, target) {
    await page.evaluate(({ s, t }) => window.__olorin.connect(s, t), { s: source, t: target });
    await dismissModals(page);
}

async function dismissModals(page) {
    await page.evaluate(() => {
        const h = document.getElementById('hintBG');
        if (h && getComputedStyle(h).display !== 'none') h.click();
        const s = document.getElementById('savedProofBG');
        if (s) s.style.display = 'none';
    });
}

// Forward-saturate a map of type -> output port using ∧-elimination and modus ponens.
async function saturate(page, portMap, pos) {
    let changed = true, guard = 0;
    while (changed && guard++ < 200) {
        changed = false;
        for (const t of Object.keys(portMap)) {
            const sp = splitPrincipal(t);
            if (sp && sp.op === '∧' && !(sp.A in portMap && sp.B in portMap)) {
                const id = await dragRule(page, 'andE', pos);
                await connect(page, portMap[t], { vertex: id, sort: 'input' });
                if (!(sp.A in portMap)) portMap[sp.A] = { vertex: id, sort: 'output', label: 'fst' };
                if (!(sp.B in portMap)) portMap[sp.B] = { vertex: id, sort: 'output', label: 'snd' };
                changed = true;
            }
            if (sp && sp.op === '⇒' && (sp.A in portMap) && !(sp.B in portMap)) {
                const id = await dragRule(page, 'impE', pos);
                await connect(page, portMap[t], { vertex: id, sort: 'input', label: 'implication' });
                await connect(page, portMap[sp.A], { vertex: id, sort: 'input', label: 'antecedent' });
                portMap[sp.B] = { vertex: id, sort: 'output' };
                changed = true;
            }
        }
    }
}

// Build the proof described by `plan`, wiring its result into `target`.
async function executePlan(page, plan, target, portMap, pos) {
    if (plan.kind === 'direct') {
        await connect(page, portMap[plan.type], target);
    } else if (plan.kind === 'topI') {
        const id = await dragRule(page, 'topI', pos);
        await connect(page, { vertex: id, sort: 'output' }, target);
    } else if (plan.kind === 'andI') {
        const id = await dragRule(page, 'andI', pos);
        await executePlan(page, plan.L, { vertex: id, sort: 'input', label: 'fst' }, portMap, pos);
        await executePlan(page, plan.R, { vertex: id, sort: 'input', label: 'snd' }, portMap, pos);
        await connect(page, { vertex: id, sort: 'output' }, target);
    } else if (plan.kind === 'orI1' || plan.kind === 'orI2') {
        const rule = plan.kind === 'orI1' ? 'orI1' : 'orI2';
        const label = plan.kind === 'orI1' ? 'left' : 'right';
        const id = await dragRule(page, rule, pos);
        await executePlan(page, plan.P, { vertex: id, sort: 'input', label }, portMap, pos);
        await connect(page, { vertex: id, sort: 'output' }, target);
    } else if (plan.kind === 'impI') {
        const id = await dragRule(page, 'impI', pos);
        await connect(page, { vertex: id, sort: 'output' }, target);
        // The local assumption extends the available facts within the bracket.
        const childMap = Object.assign({}, portMap);
        childMap[plan.A] = { vertex: id, sort: 'assumption' };
        await saturate(page, childMap, pos);
        await executePlan(page, plan.sub, { vertex: id, sort: 'subgoal' }, childMap, pos);
    }
}

async function solveLevel(page, level) {
    await page.evaluate(() => {
        const bg = document.getElementById('levelChooseBG');
        if (getComputedStyle(bg).display === 'none') document.getElementById('selectLevel').click();
    });
    await page.click(`#worlds .level[data-name="${level.name}"]`);
    await page.waitForFunction((n) => document.getElementById('currentLevel').innerText.includes(n), level.name);
    await dismissModals(page);

    const nodes = await page.evaluate(() => window.__olorin.nodes());
    const concl = nodes.find((n) => n.rule === 'conclusion');
    if (!concl) return null;

    const portMap = {};
    for (const n of nodes) {
        if (n.rule === 'hypothesis' && !(norm(n.value) in portMap)) {
            portMap[norm(n.value)] = { vertex: n.id, sort: 'output' };
        }
    }
    const plan = planType(concl.value, new Set(Object.keys(portMap)));
    if (!plan) return null;

    const pos = { x: 380, y: 120 };
    await saturate(page, portMap, pos);
    await executePlan(page, plan, { vertex: concl.id, sort: 'input' }, portMap, pos);

    const complete = await page.evaluate(() => window.__olorin.complete());
    return complete ? page.evaluate(() => window.__olorin.serialize()) : null;
}

function fixturePath(name) {
    return path.join(FIXTURE_DIR, `${name}.json`);
}

async function main() {
    const onlyArg = process.argv.indexOf('--only');
    const only = onlyArg >= 0 ? new Set(process.argv[onlyArg + 1].split(',')) : null;

    fs.mkdirSync(FIXTURE_DIR, { recursive: true });
    const server = spawn('node', [path.join(__dirname, 'server.js'), String(PORT)], { stdio: 'ignore' });
    await new Promise((r) => setTimeout(r, 800));

    const browser = await chromium.launch();
    const page = await browser.newPage();
    page.on('dialog', (d) => d.accept());
    await page.addInitScript(() => localStorage.setItem('visited', 'true'));
    await page.goto(`http://localhost:${PORT}/?test=1`, { waitUntil: 'load' });
    await page.waitForFunction(() => typeof window.__olorin !== 'undefined' && typeof window.Narya !== 'undefined');

    let solved = 0, attempted = 0;
    for (const level of allLevels().filter((l) => !only || only.has(l.name))) {
        attempted++;
        let state = null;
        try {
            state = await solveLevel(page, level);
        } catch (e) {
            console.log(`  ${level.name}: error ${e.message}`);
        }
        if (state) {
            fs.writeFileSync(fixturePath(level.name), JSON.stringify(state, null, 2) + '\n');
            solved++;
            console.log(`  ${level.name}: solved`);
        } else {
            console.log(`  ${level.name}: not auto-solved`);
        }
        await page.evaluate(() => { const k = window.__olorin.savedProofKey(); if (k) localStorage.removeItem(k); });
    }

    await browser.close();
    server.kill();
    console.log(`\nSolved ${solved}/${attempted} levels. Fixtures in ${FIXTURE_DIR}`);
}

main().catch((e) => { console.error(e); process.exit(1); });
