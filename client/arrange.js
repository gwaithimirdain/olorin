// The "Arrange" button: tidy up the layout of a proof.
//
// This works on a plain description of the diagram (see `arrange` below), with no access to the
// page, so it can be run and tested on its own.  It tidies the layout the player already has rather
// than laying the proof out afresh: where the player put things says what they meant, especially in
// a proof that isn't finished yet.  It goes like this.
//
// 1. Scopes.  Which subproof each block belongs to is a matter of the wires, not of where it sits:
//    a block has to be inside every bracket whose assumption it uses (directly or through other
//    blocks), and it can be no deeper than the subproofs using what it proves.  Between those two,
//    it stays in whichever subproof the player drew it in.  This gives a tree of regions: the whole
//    diagram at the root, and inside it one region for each branch of each bracket (the part above
//    its bar, and for a bracket with two subgoals like ∨-elimination, the part below it).
//
// 2. Constraints.  Everything a tidy layout must satisfy is a linear inequality between two
//    coordinates: each subproof between its bracket's uprights and on its side of the bar; each
//    wire running left to right; and blocks kept apart.  Which way two blocks are kept apart -- side
//    by side, or one above the other -- is whichever way the wires put them, or failing that, read
//    off the layout the player has, so the arrangement keeps its shape.  A block that isn't part of
//    a subproof may sit between its brackets, as long as it is clearly above or below the subproof.
//
// 3. Optimization.  Gradient descent on a "niceness" energy -- wires short and level, brackets snug,
//    wire labels clear of the blocks and of each other, wires not running through blocks, and at
//    first, blocks not far from where they were -- projecting back onto the constraints after each
//    step.
//
// 4. What the gradient can't see: wires crossing.  Blocks stacked one above the other trade places
//    if another round of descent from there shows it untangles the wires.
//
// 5. The whole of it is tried at several spacings, and the most spread out that fits in the
//    window wins.  And it is all done over from its own result until that stays put, so that
//    arranging an arranged proof leaves it as it is.

// A bracket's uprights are this wide.
const UPRIGHT = 22;
// The spacing of a layout, in pixels.  A small proof is spread out further than this to fill the
// window (up to MAX_SPREAD times as far), so everything here is scaled together.
const SPACING = {
    // How far a subproof keeps from its bracket's uprights, and above (or below) its bar.
    padX: 14,
    padY: 36,
    // The least room between two blocks side by side, and one above the other.
    gapX: 30,
    gapY: 30,
    // The least room between a subproof and a block that isn't part of it, above or below it: well
    // more than the spacing within a subproof, so which blocks belong to it is plain to see.
    scopeGap: 60,
    // The least horizontal run of a wire, and what it would like to have.  (Room for its label is
    // the business of the energy's label term: a label can as well sit where the wire goes up or
    // down.)
    wireMin: 40,
    wireIdeal: 80,
    // How much of a wire should show past its label, all told (see shownOf).
    wireShown: 80,
};
const MAX_SPREAD = 2;
// The spreads tried go down from there in steps of this much.
const SPREAD_STEP = 0.25;
// A layout that arranging would move no block of further than this is left as it is.
const SETTLED = 50;
// How much room to leave around a layout that fits in the window.
const VIEW_MARGIN = 30;
// How much room a wire label would like around it.
const LABEL_MARGIN = 10;
// A bracket is never narrower than this (the least width resizing it by hand allows).
const BRACKET_MIN_W = 100;

// How much each part of the energy counts.
const WEIGHTS = {
    level: 1,        // a wire's two ends at the same height (see HUBER)
    levelSquare: 0.02, // ...and a little more so, the further out of level they are
    length: 0.3,     // a wire's horizontal run close to what it would like
    snug: 2,         // brackets no wider than they need to be (per pixel of width)
    labels: 20,      // wire labels clear of the blocks and of each other
    visible: 5,      // enough of each wire showing past its label
    through: 20,      // wires not running through blocks
    stay: 0.02,      // blocks close to where the player put them
};

// Past this many pixels, a wire that is out of level or out of length costs only in proportion,
// rather than as the square: otherwise a few wires that have to go a long way up or down, or across,
// would outweigh everything else.
const HUBER = 30;

const ROOT = '';

// The region of one branch ('upper' or 'lower') of a bracket.
function regionOf(id, side) { return id + '/' + side; }
function bracketOf(region) { return region.slice(0, region.lastIndexOf('/')); }
function sideOf(region) { return region.slice(region.lastIndexOf('/') + 1); }
function portSide(port) { return port.side === 'lower' ? 'lower' : 'upper'; }

// ------------------------------------------------------------------------------------------------
// 1. Scopes

// Work out which region each block goes in.  Returns { place, ancestors }: a Map from block id to
// region, and a function giving the regions a region is inside (see below).
function assignRegions(model) {
    const blocks = model.blocks;
    const byId = new Map(blocks.map((b) => [b.id, b]));
    const wires = model.wires.filter((w) => byId.has(w.src.block) && byId.has(w.tgt.block));
    const srcPort = (w) => byId.get(w.src.block).ports[w.src.port];
    const tgtPort = (w) => byId.get(w.tgt.block).ports[w.tgt.port];

    // The branches whose assumptions each block uses, through any chain of wires.  A bracket's own
    // branches don't count for it: using its own assumption inside it is what it's for.
    const need = new Map(blocks.map((b) => [b.id, new Set()]));
    for(var changed = true; changed;) {
        changed = false;
        wires.forEach(function (w) {
            if(w.src.block === w.tgt.block) { return; }
            const from = new Set(need.get(w.src.block));
            const sp = srcPort(w);
            if(sp.sort === 'assumption') { from.add(regionOf(w.src.block, portSide(sp))); }
            const into = need.get(w.tgt.block);
            from.forEach(function (r) {
                if(bracketOf(r) === w.tgt.block || into.has(r)) { return; }
                into.add(r);
                changed = true;
            });
        });
    }

    const place = new Map(blocks.map((b) => [b.id, ROOT]));
    // The regions containing a region, innermost first, ending with the root.  A proof whose wires
    // are badly out of scope can momentarily put a bracket inside itself; that just stops there.
    function ancestors(region) {
        const out = [];
        const seen = new Set();
        while(region !== ROOT && !seen.has(region)) {
            seen.add(region);
            out.push(region);
            region = place.get(bracketOf(region)) || ROOT;
        }
        out.push(ROOT);
        return out;
    }
    const depth = (r) => ancestors(r).length - 1;
    const within = (inner, outer) => ancestors(inner).includes(outer);
    // Whether a region is inside the bracket `id` itself, where that bracket can't go.
    const insideOf = (r, id) => ancestors(r).some((a) => a !== ROOT && bracketOf(a) === id);

    // Where each block is drawn, for telling which subproof the player put it in: its middle, or
    // for a bracket, the middle of its bar.
    const barY = (k) => k.branches.includes('lower') ? k.y + k.h / 2 : k.y + k.h - 10;
    const spot = new Map(blocks.map((b) => [b.id, {
        x: b.x + b.w / 2, y: b.branches ? barY(b) : b.y + b.h / 2,
    }]));
    const brackets = blocks.filter((b) => b.branches);
    // The nearest bars straight below and straight above each block.  A block above a bar is in
    // the subproof above it; a block below one is in the subproof below it, if the bracket has one,
    // and otherwise it's beside that bracket, in the same region.
    const rays = new Map(blocks.map(function (b) {
        const p = spot.get(b.id);
        var below = null, above = null;
        brackets.forEach(function (k) {
            if(k === b || p.x < k.x + UPRIGHT || p.x > k.x + k.w - UPRIGHT) { return; }
            const y = barY(k);
            if(y > p.y && (!below || y < barY(below))) { below = k; }
            if(y < p.y && (!above || y > barY(above))) { above = k; }
        });
        return [b.id, { below: below, above: above }];
    }));
    // The regions a block is drawn inside, as things stand.
    function drawnIn(b) {
        const r = rays.get(b.id);
        const out = new Set([ROOT]);
        const add = (region) => ancestors(region).forEach((a) => out.add(a));
        if(r.below) { add(regionOf(r.below.id, 'upper')); }
        if(r.above) {
            add(r.above.branches.includes('lower') ? regionOf(r.above.id, 'lower')
                : place.get(r.above.id));
        }
        return out;
    }

    function consumers(b) {
        const out = [];
        wires.forEach(function (w) {
            if(w.src.block !== b.id || w.tgt.block === b.id) { return; }
            // What comes out of a bracket's assumptions is used inside it.
            if(srcPort(w).sort === 'assumption') { return; }
            const t = byId.get(w.tgt.block);
            const tp = tgtPort(w);
            out.push(t.branches && tp.sort === 'subgoal' ? regionOf(t.id, portSide(tp))
                     : place.get(t.id));
        });
        return out;
    }

    function lca(regions) {
        var common = ancestors(regions[0]);
        regions.slice(1).forEach(function (r) {
            const as = new Set(ancestors(r));
            common = common.filter((a) => as.has(a));
        });
        return common[0];
    }

    for(var round = 0; round < 2 * blocks.length + 5; round++) {
        var moved = false;
        blocks.forEach(function (b) {
            if(b.root) { return; }
            // The innermost branch whose assumption it uses: the least it can be inside.
            var least = ROOT, leastDepth = 0;
            need.get(b.id).forEach(function (r) {
                if(insideOf(r, b.id)) { return; }
                const d = depth(r);
                if(d > leastDepth) { least = r; leastDepth = d; }
            });
            // The innermost region holding everything that uses it: the most it can be inside.
            const uses = consumers(b);
            const most = uses.length > 0 ? lca(uses) : null;
            // Between those, wherever the player drew it.
            var best = least, bestDepth = leastDepth;
            drawnIn(b).forEach(function (r) {
                if(insideOf(r, b.id) || !within(r, least)) { return; }
                if(most !== null && !within(most, r)) { return; }
                const d = depth(r);
                if(d > bestDepth) { best = r; bestDepth = d; }
            });
            if(place.get(b.id) !== best) {
                place.set(b.id, best);
                moved = true;
            }
        });
        if(!moved) { break; }
    }
    return { place: place, ancestors: ancestors };
}

// ------------------------------------------------------------------------------------------------
// 2. Constraints

// A system of difference constraints v ≥ u + w, together with the longest path between every two
// variables, so we can tell before adding a constraint whether it would contradict the others (it
// would close a cycle of positive length).
class Constraints {
    constructor(n) {
        this.n = n;
        this.d = new Float64Array(n * n).fill(-Infinity);
        for(var i = 0; i < n; i++) { this.d[i * n + i] = 0; }
        this.edges = [];
    }
    // Whether v ≥ u + w can be added without contradicting what's there.
    fits(u, v, w) { return this.d[v * this.n + u] + w <= 1e-6; }
    add(u, v, w) {
        if(u === v) { return; }
        const n = this.n, d = this.d;
        if(d[u * n + v] >= w) { return; }  // Already implied.
        this.edges.push([u, v, w]);
        for(var i = 0; i < n; i++) {
            const iu = d[i * n + u];
            if(iu === -Infinity) { continue; }
            for(var j = 0; j < n; j++) {
                const via = iu + w + d[v * n + j];
                if(via > d[i * n + j]) { d[i * n + j] = via; }
            }
        }
    }
    // Add a whole set of constraints if they all fit, and say whether they did.
    addAll(list) {
        if(!list.every((c) => this.fits(c[0], c[1], c[2]))) { return false; }
        list.forEach((c) => this.add(c[0], c[1], c[2]));
        return true;
    }
}

// A point on a block, along one axis: the variable it moves with, plus a fixed offset.  Where it is
// in the layout `vals`:
const val = (vals, p) => vals[p.v] + p.o;
// `a + gap ≤ b` as a constraint [u, v, w] meaning x[v] ≥ x[u] + w.
function before(a, b, gap) { return [a.v, b.v, a.o - b.o + gap]; }

// Everything about the diagram the constraints and the energy are written in terms of.
function setUp(model, scopes, sp) {
    const blocks = model.blocks;
    const n = blocks.length;
    const index = new Map(blocks.map((b, i) => [b.id, i]));
    // The variables: every block's left edge and top edge, and every bracket's right edge (the
    // only blocks whose width can change).
    const xs = blocks.map((b) => b.x), ys = blocks.map((b) => b.y);
    const rightVar = new Map();
    blocks.forEach(function (b, i) {
        if(b.branches) { rightVar.set(i, xs.length); xs.push(b.x + b.w); }
    });
    const ext = (b) => b.extent || { left: 0, top: 0, right: 0, bottom: b.h };
    const at = {
        left: (i) => ({ v: i, o: ext(blocks[i]).left }),
        right: (i) => rightVar.has(i) ? { v: rightVar.get(i), o: ext(blocks[i]).right }
            : { v: i, o: blocks[i].w + ext(blocks[i]).right },
        // The inside faces of a bracket's uprights.
        innerLeft: (i) => ({ v: i, o: UPRIGHT }),
        innerRight: (i) => ({ v: rightVar.get(i), o: -UPRIGHT }),
        top: (i) => ({ v: i, o: ext(blocks[i]).top }),
        bottom: (i) => ({ v: i, o: ext(blocks[i]).bottom }),
        portX: (i, p) => p.right ? { v: rightVar.get(i), o: p.dx } : { v: i, o: p.dx },
        portY: (i, p) => ({ v: i, o: p.dy }),
    };
    const wires = model.wires.filter((w) =>
        index.has(w.src.block) && index.has(w.tgt.block) && w.src.block !== w.tgt.block
    ).map(function (w) {
        const s = index.get(w.src.block), t = index.get(w.tgt.block);
        return {
            s: s, t: t,
            sp: blocks[s].ports[w.src.port], tp: blocks[t].ports[w.tgt.port],
            gap: sp.wireMin,
            curved: !!w.curved,
            labels: w.labels || [],
        };
    });
    // Each block with everything inside it: for a bracket, its subproofs.
    const regionsOf = (i) => (blocks[i].branches || []).map((s) => regionOf(blocks[i].id, s));
    const cluster = blocks.map(function (b, i) {
        const mine = new Set(regionsOf(i));
        const out = [i];
        blocks.forEach(function (m, j) {
            if(j !== i && scopes.ancestors(scopes.place.get(m.id)).some((r) => mine.has(r))) {
                out.push(j);
            }
        });
        return out;
    });
    return { blocks, n, index, xs, ys, rightVar, at, wires, cluster, sp };
}

// The rectangle a block covers in the layout (xs, ys), with everything inside it.
function clusterBox(S, i, xs, ys) {
    const ms = S.cluster[i];
    return {
        left: Math.min(...ms.map((j) => val(xs, S.at.left(j)))),
        right: Math.max(...ms.map((j) => val(xs, S.at.right(j)))),
        top: Math.min(...ms.map((j) => val(ys, S.at.top(j)))),
        bottom: Math.max(...ms.map((j) => val(ys, S.at.bottom(j)))),
    };
}

function buildConstraints(model, scopes, S) {
    const { blocks, at, xs, ys, wires, cluster, sp } = S;
    const cx = new Constraints(xs.length), cy = new Constraints(ys.length);

    // Brackets can't get too narrow.
    S.rightVar.forEach(function (r, i) { cx.add(i, r, BRACKET_MIN_W); });

    // Every block inside every subproof it belongs to: between the uprights, and above the bar (or
    // below it).
    blocks.forEach(function (b, j) {
        scopes.ancestors(scopes.place.get(b.id)).forEach(function (r) {
            if(r === ROOT) { return; }
            const k = S.index.get(bracketOf(r));
            cx.addAll([before(at.innerLeft(k), at.left(j), sp.padX),
                       before(at.right(j), at.innerRight(k), sp.padX)]);
            cy.addAll([sideOf(r) === 'lower' ? before(at.bottom(k), at.top(j), sp.padY)
                       : before(at.bottom(j), at.top(k), sp.padY)]);
        });
    });

    // Wires run left to right, with room for their labels.  Those already doing so go first, so
    // that in a cycle, which can't all run left to right, it's one of the wires the player drew
    // backwards that is left out.
    const forward = (w) => val(xs, at.portX(w.t, w.tp)) >= val(xs, at.portX(w.s, w.sp));
    const ordered = wires.filter(forward).concat(wires.filter((w) => !forward(w)));
    const hard = new Set();
    ordered.forEach(function (w) {
        if(cx.addAll([before(at.portX(w.s, w.sp), at.portX(w.t, w.tp), w.gap)])) { hard.add(w); }
    });

    // Keep apart the blocks sharing a region, and the subproofs they carry with them, each pair in
    // whichever way it already is (or nearly is).  Closest pairs first, since theirs is the
    // relationship most plainly there to keep.
    const box = (i) => clusterBox(S, i, xs, ys);
    const pairs = [];
    const byRegion = new Map();
    blocks.forEach(function (b, i) {
        const r = scopes.place.get(b.id);
        if(!byRegion.has(r)) { byRegion.set(r, []); }
        byRegion.get(r).push(i);
    });
    byRegion.forEach(function (items) {
        for(var p = 0; p < items.length; p++) {
            for(var q = p + 1; q < items.length; q++) {
                const a = items[p], b = items[q];
                const A = box(a), B = box(b);
                const dx = Math.max(A.left - B.right, B.left - A.right);
                const dy = Math.max(A.top - B.bottom, B.top - A.bottom);
                pairs.push({ a, b, A, B, dist: Math.max(dx, dy) });
            }
        }
    });
    pairs.sort((p, q) => p.dist - q.dist);
    // How far right of `p` the constraints so far have `q` be, at the least.
    const implied = (p, q) => cx.d[p.v * cx.n + q.v] + q.o - p.o;
    pairs.forEach(function ({ a, b, A, B }) {
        // Two blocks the wires already put one left of the other are side by side, however the
        // player had them: the player's arrangement only decides what the wires leave open.  (A
        // player's proof can have blocks piled up any old way, which read as one above the other
        // would leave them stepping down the page once the wires spread them out.)
        if(implied(at.right(a), at.left(b)) >= 0
           && cx.addAll([before(at.right(a), at.left(b), sp.gapX)])) { return; }
        if(implied(at.right(b), at.left(a)) >= 0
           && cx.addAll([before(at.right(b), at.left(a), sp.gapX)])) { return; }
        const scope = cluster[a].length > 1 || cluster[b].length > 1;
        const gy = scope ? sp.scopeGap : sp.gapY;
        const stack = (upper, lower) => {
            const out = [];
            cluster[upper].forEach((u) => cluster[lower].forEach((l) =>
                out.push(before(at.bottom(u), at.top(l), gy))));
            return out;
        };
        const options = [
            { sys: cx, list: [before(at.right(a), at.left(b), sp.gapX)], gap: B.left - A.right - sp.gapX },
            { sys: cx, list: [before(at.right(b), at.left(a), sp.gapX)], gap: A.left - B.right - sp.gapX },
            { sys: cy, list: stack(a, b), gap: B.top - A.bottom - gy },
            { sys: cy, list: stack(b, a), gap: A.top - B.bottom - gy },
        ];
        // The way that needs the least moving, and among ways that need none, the one with most
        // room to spare.
        options.sort((p, q) => q.gap - p.gap);
        options.some((o) => o.sys.addAll(o.list));
    });

    return { cx, cy, hard };
}

// ------------------------------------------------------------------------------------------------
// 3. Optimization

// What a term of the energy (see energyTerms) costs.
function cost(t) {
    const a = Math.abs(t.value);
    return t.huber && a > HUBER ? t.w * HUBER * (2 * a - HUBER) : t.w * a * a;
}

// Accumulates the energy's gradient and (diagonal) curvature over the variables.  A term that has
// gone past HUBER is treated as the parabola through it with the same slope, which is flatter.
function quadratic(grad, curv, terms) {
    terms.forEach(function (t) {
        const w = t.huber ? t.w * Math.min(1, HUBER / Math.max(1e-9, Math.abs(t.value))) : t.w;
        t.vars.forEach(function ([v, c]) {
            grad[v] += 2 * w * t.value * c;
            curv[v] += 2 * w * c * c;
        });
    });
}

// Push the variables, as little as possible, until every constraint holds.  "As little as
// possible" is weighed by `mass`: a variable the energy holds more firmly moves less.  That has to
// be the same weighing the descent steps use, or the two pull against each other along whatever
// the constraints leave free, and the whole layout creeps off.
function project(vals, edges, sweeps, mass) {
    var worst = 0;
    for(var s = 0; s < sweeps; s++) {
        worst = 0;
        edges.forEach(function ([u, v, w]) {
            const short = vals[u] + w - vals[v];
            if(short > 1e-6) {
                const mu = mass ? 1 / mass[u] : 1, mv = mass ? 1 / mass[v] : 1;
                vals[u] -= short * mu / (mu + mv);
                vals[v] += short * mv / (mu + mv);
                worst = Math.max(worst, short);
            }
        });
        if(worst < 0.01) { break; }
    }
    return worst;
}

// An edge of a rectangle, along one axis: Σ c·x[v] over its `vars` ([[v, c], ...]), plus `k`.
const edge = (p) => ({ vars: [[p.v, 1]], k: p.o });
const edgeAt = (e, vals) => e.vars.reduce((a, [v, c]) => a + c * vals[v], e.k);
const negated = (e) => e.vars.map(([v, c]) => [v, -c]);

// Every rectangle a wire label should keep clear of, and every label, with their edges along each
// axis: [{ x: [left, right], y: [top, bottom], label }].
function rectangles(S) {
    const { at, wires, blocks } = S;
    const out = blocks.map((b, i) => ({
        x: [edge(at.left(i)), edge(at.right(i))], y: [edge(at.top(i)), edge(at.bottom(i))],
    }));
    wires.forEach(function (w) {
        // A wire leaves one port heading right and enters the other heading left, and both kinds of
        // connector draw that the same way turned end to end, so the middle of the wire, where its
        // label goes, is halfway between its ports.
        const mid = function (a, b, half) {
            return [{ vars: [[a.v, 0.5], [b.v, 0.5]], k: (a.o + b.o) / 2 - half },
                    { vars: [[a.v, 0.5], [b.v, 0.5]], k: (a.o + b.o) / 2 + half }];
        };
        w.labels.forEach(function (l) {
            out.push({
                x: mid(at.portX(w.s, w.sp), at.portX(w.t, w.tp), l.w / 2 + LABEL_MARGIN),
                y: mid(at.portY(w.s, w.sp), at.portY(w.t, w.tp), l.h / 2 + LABEL_MARGIN),
                label: true,
            });
        });
    });
    return out;
}

// Points along the path of each wire (see wirePaths), each as a pair of edges (see `edge`) of no
// width, so that how deep one is inside a block is something the gradient can see: the path of a
// wire, curved or angled, is a fixed combination of where its two ends are.  Returns, for each
// wire, its points as [{ x, y }].
function pathPoints(S) {
    return S.wires.map(function (w) {
        const a = S.at.portX(w.s, w.sp), b = S.at.portX(w.t, w.tp);
        const c = S.at.portY(w.s, w.sp), d = S.at.portY(w.t, w.tp);
        // The point α·source + β·target + κ, along one axis.
        const mix = (p, q, alpha, beta, kappa) => ({
            vars: [[p.v, alpha], [q.v, beta]], k: alpha * p.o + beta * q.o + kappa,
            // The same, for working out quickly: [v, α, w, β, k].
            fast: [p.v, alpha, q.v, beta, alpha * p.o + beta * q.o + kappa],
        });
        const out = [];
        if(w.curved) {
            for(var i = 1; i < 8; i++) {
                const t = i / 8, u = 1 - t;
                const bb = 3 * u * u * t, cc = 3 * u * t * t;
                out.push({ x: mix(a, b, u * u * u + bb, cc + t * t * t, CURVINESS * (bb - cc)),
                           y: mix(c, d, u * u * u + bb, cc + t * t * t, 0) });
            }
        } else {
            // Across to halfway, down (or up), and across again, leaving out the very ends.
            [0.25, 0.5, 0.75].forEach((f) => out.push({ x: mix(a, b, 1 - f / 2, f / 2, 0), y: mix(c, d, 1, 0, 0) }));
            [0, 0.25, 0.5, 0.75, 1].forEach((f) => out.push({ x: mix(a, b, 0.5, 0.5, 0), y: mix(c, d, 1 - f, f, 0) }));
            [0.25, 0.5, 0.75].forEach((f) => out.push({ x: mix(a, b, (1 - f) / 2, (1 + f) / 2, 0), y: mix(c, d, 0, 1, 0) }));
        }
        return out;
    });
}
// How far outside a block a wire would like to keep.
const WIRE_CLEARANCE = 4;

// How much of a wire shows past its label, and how that changes as it runs further across (dAcross)
// and rises or falls further (dUpDown).  Its label sits in the middle of it, and the label's white
// box hides whatever of the wire runs under it; and the port at one end and the port and arrowhead
// at the other hide a little more.  So what shows is measured along the wire's path itself (see
// wirePath): a curved wire whose ends are close together loops back through its own middle, where
// the label is, and shows much less than its ends being far apart would suggest.
//
// The rates are only a guide to which way to go: running level, a wire shows more for running
// further across once its run is longer than its label, and for rising or falling, which starts
// moving the label onto a slope, up to the height of the label, beyond which what it rises or falls
// shows as it is.  (They are kept from getting small: a descent step divides by them, and would send
// a block flying off to make up the shortfall at a rate that only holds for the first pixel.)
function shownOf(S, w, xs, ys) {
    const dx = val(xs, S.at.portX(w.t, w.tp)) - val(xs, S.at.portX(w.s, w.sp));
    const dy = val(ys, S.at.portY(w.t, w.tp)) - val(ys, S.at.portY(w.s, w.sp));
    const lw = Math.max(...w.labels.map((l) => l.w)), lh = Math.max(...w.labels.map((l) => l.h));
    const run = Math.max(0, dx - SOURCE_END - TARGET_END), rise = Math.abs(dy);
    return {
        shown: shownAlong(w.curved, dx, dy, lw, lh),
        dAcross: run <= 0 ? 0 : run > lw ? 1 : Math.max(MIN_RATE, Math.min(1, rise / lh)),
        dUpDown: rise < lh ? Math.max(MIN_RATE, Math.min(lw, run) / lh) : 1,
        sign: Math.abs(dy) >= 1 ? Math.sign(dy) : levelWay(w),
    };
}

// How much shows of a wire running (dx, dy) from one end to the other, with a label lw by lh.  That
// is all it depends on, and a descent asks it over and over about wires that have hardly moved, so
// the answers are kept, for whole pixels, and in between it goes smoothly from one to the next
// (or a descent would never settle, for jumping from pixel to pixel).
const shownCache = new Map();
function shownAlong(curved, dx, dy, lw, lh) {
    const at = function (x, y) {
        const key = (curved ? 'c' : 'a') + x + ',' + y + ',' + lw + ',' + lh;
        var shown = shownCache.get(key);
        if(shown === undefined) {
            if(shownCache.size > 100000) { shownCache.clear(); }
            shown = pathShown(wirePath(curved, 0, 0, x, y), lw, lh);
            shownCache.set(key, shown);
        }
        return shown;
    };
    const x = Math.floor(dx), y = Math.floor(dy), fx = dx - x, fy = dy - y;
    return (1 - fx) * ((1 - fy) * at(x, y) + fy * at(x, y + 1)) + fx * ((1 - fy) * at(x + 1, y) + fy * at(x + 1, y + 1));
}

// The length of a path (as wirePath gives it) that shows: outside the label, a box lw by lh around
// the middle of the path, and clear of the ports and arrowhead at its two ends.
function pathShown(path, lw, lh) {
    const segs = [];
    var total = 0;
    for(var i = 1; i < path.length; i++) {
        const len = Math.hypot(path[i][0] - path[i - 1][0], path[i][1] - path[i - 1][1]);
        segs.push(len);
        total += len;
    }
    // The label goes halfway along the path (jsPlumb's location 0.5).
    var mid = null, soFar = 0;
    for(var i = 0; i < segs.length && mid === null; i++) {
        if(soFar + segs[i] >= total / 2) {
            const f = segs[i] === 0 ? 0 : (total / 2 - soFar) / segs[i];
            mid = [path[i][0] + f * (path[i + 1][0] - path[i][0]), path[i][1] + f * (path[i + 1][1] - path[i][1])];
        }
        soFar += segs[i];
    }
    if(mid === null) { return 0; }
    const start = path[0], end = path[path.length - 1];
    const hidden = (p) => (Math.abs(p[0] - mid[0]) < lw / 2 && Math.abs(p[1] - mid[1]) < lh / 2)
        || Math.hypot(p[0] - start[0], p[1] - start[1]) < SOURCE_END
        || Math.hypot(p[0] - end[0], p[1] - end[1]) < TARGET_END;
    // Walk the path a few pixels at a time, counting the steps that show.
    var shown = 0;
    for(var i = 0; i < segs.length; i++) {
        const n = Math.max(1, Math.ceil(segs[i] / PATH_STEP));
        for(var k = 0; k < n; k++) {
            const f = (k + 0.5) / n;
            const p = [path[i][0] + f * (path[i + 1][0] - path[i][0]), path[i][1] + f * (path[i + 1][1] - path[i][1])];
            if(!hidden(p)) { shown += segs[i] / n; }
        }
    }
    return shown;
}
// How far along a path pathShown looks at a time, in pixels.
const PATH_STEP = 3;

// Which way a level wire had better go, up (-1) or down (1), if it goes either way: up out of the
// upper of a block's ports, or into the lower of them, and down out of a lower one or into an upper.
// Down if nothing says either.
function levelWay(w) {
    const out = { upper: -1, lower: 1 }[w.sp.side] || 0, into = { upper: 1, lower: -1 }[w.tp.side] || 0;
    return out + into < 0 ? -1 : 1;
}

// How far from its ends a wire is hidden by the port at its start, and by the port and the
// arrowhead at its end.
const SOURCE_END = 8;
const TARGET_END = 18;
const MIN_RATE = 0.5;
const VISIBLE_BAND = 30;

// A wire that shows less than it should past its label (see shownOf) looks as if there were no
// wire there at all, only a label.  It can be put right by running the wire further across, or up
// or down, whichever costs less.  The term is in both coordinates at once, so it goes in both lists,
// the second time as a `shadow` that the energy's total leaves out.
function visibility(S, w, xs, ys, xTerms, yTerms) {
    if(w.labels.length === 0) { return; }
    // Most wires show plenty, and it can be seen without following their paths: one that heads
    // steadily rightwards (as an angled wire does, and a curved one whose ends are far enough apart
    // not to loop) can have no more of it under its label than the label is wide and tall.
    const dx = val(xs, S.at.portX(w.t, w.tp)) - val(xs, S.at.portX(w.s, w.sp));
    const dy = val(ys, S.at.portY(w.t, w.tp)) - val(ys, S.at.portY(w.s, w.sp));
    if(dx > 0 && (!w.curved || dx >= 2 * CURVINESS)) {
        const lw = Math.max(...w.labels.map((l) => l.w)), lh = Math.max(...w.labels.map((l) => l.h));
        const least = Math.hypot(dx, dy) - lw - lh - SOURCE_END - TARGET_END;
        if(least >= S.sp.wireShown + VISIBLE_BAND) { return; }
    }
    const { shown, dAcross, dUpDown, sign } = shownOf(S, w, xs, ys);
    const short = S.sp.wireShown - shown;
    // Just past showing enough, the term is kept on, only with nothing to push: a descent step
    // takes its size from how firmly the energy holds a variable, and without this, the step that
    // makes a wire show enough would overshoot into where nothing holds it, and the level term
    // would take it all the way back next step, and so on for ever.
    if(!(short > -VISIBLE_BAND)) { return; }
    const value = Math.max(0, short);
    const a = S.at.portX(w.s, w.sp), b = S.at.portX(w.t, w.tp);
    const c = S.at.portY(w.s, w.sp), d = S.at.portY(w.t, w.tp);
    // (A level wire is sent whichever way its ports say: see levelWay.)
    xTerms.push({ kind: 'visible', w: WEIGHTS.visible, value: value,
                  vars: [[b.v, -dAcross], [a.v, dAcross]] });
    yTerms.push({ kind: 'visible', w: WEIGHTS.visible, value: value, shadow: true,
                  vars: [[d.v, -sign * dUpDown], [c.v, sign * dUpDown]] });
}

// The energy's terms, for the layout in (xs, ys), all but the hold on where everything started (see
// `energy` and `descend`).  Each is { kind, w, vars, value }, standing for
// w·value², where value is Σ c·x[v] over vars ([[v, c], ...]) plus a constant -- or with `huber`,
// for w·value² up to HUBER and then growing only in proportion: see `cost`.
function energyTerms(S, xs, ys) {
    const { at, wires } = S;
    const xTerms = [], yTerms = [];
    wires.forEach(function (w) {
        const ys_ = val(ys, at.portY(w.s, w.sp)), yt = val(ys, at.portY(w.t, w.tp));
        yTerms.push({ kind: 'level', w: WEIGHTS.level, value: yt - ys_, huber: true,
                      vars: [[at.portY(w.t, w.tp).v, 1], [at.portY(w.s, w.sp).v, -1]] });
        // And a little of it as the square after all: a block between two wires going up and down
        // to it costs the same anywhere between them in proportion, and would be left to wander;
        // this puts it in the middle.
        yTerms.push({ kind: 'level', w: WEIGHTS.levelSquare, value: yt - ys_,
                      vars: [[at.portY(w.t, w.tp).v, 1], [at.portY(w.s, w.sp).v, -1]] });
        if(!w.hard) { return; }
        const a = at.portX(w.s, w.sp), b = at.portX(w.t, w.tp);
        xTerms.push({ kind: 'length', w: WEIGHTS.length, huber: true,
                      value: val(xs, b) - val(xs, a) - S.sp.wireIdeal,
                      vars: [[b.v, 1], [a.v, -1]] });
        visibility(S, w, xs, ys, xTerms, yTerms);
    });
    // Where every rectangle is, worked out once.
    const rects = S.rects;
    const place = rects.map((r) => [edgeAt(r.x[0], xs), edgeAt(r.x[1], xs), edgeAt(r.y[0], ys), edgeAt(r.y[1], ys)]);
    // A label overlapping something is pushed off it along whichever axis it overlaps less.
    for(var i = 0; i < rects.length; i++) {
        if(!rects[i].label) { continue; }
        const a = place[i];
        for(var j = 0; j < rects.length; j++) {
            if(j === i || (rects[j].label && j < i)) { continue; }
            const b = place[j];
            const ox = Math.min(a[1], b[1]) - Math.max(a[0], b[0]);
            if(ox <= 0) { continue; }
            const oy = Math.min(a[3], b[3]) - Math.max(a[2], b[2]);
            if(oy <= 0) { continue; }
            // The overlap along the axis, as (the nearer far edge) − (the nearer near edge).
            const xAxis = ox < oy, k = xAxis ? 0 : 2, axis = xAxis ? 'x' : 'y';
            const hi = a[k + 1] < b[k + 1] ? rects[i][axis][1] : rects[j][axis][1];
            const lo = a[k] > b[k] ? rects[i][axis][0] : rects[j][axis][0];
            (xAxis ? xTerms : yTerms).push({
                kind: 'labels', w: WEIGHTS.labels, value: xAxis ? ox : oy,
                vars: hi.vars.concat(negated(lo)),
            });
        }
    }
    // A point of a wire inside a block (other than the wire's own two) is pushed out of it, whichever
    // way is nearest.
    const C = WIRE_CLEARANCE;
    const fast = (f, vals) => f[1] * vals[f[0]] + f[3] * vals[f[2]] + f[4];
    S.points.forEach(function (pts, wi) {
        const w = S.wires[wi];
        const ps = pts.map((p) => [fast(p.x.fast, xs), fast(p.y.fast, ys)]);
        var x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
        ps.forEach(function ([px, py]) {
            x0 = Math.min(x0, px); x1 = Math.max(x1, px); y0 = Math.min(y0, py); y1 = Math.max(y1, py);
        });
        for(var k = 0; k < S.n; k++) {
            if(k === w.s || k === w.t) { continue; }
            const r = place[k];
            const l = r[0] - C, rr = r[1] + C, t = r[2] - C, bb = r[3] + C;
            if(x1 <= l || x0 >= rr || y1 <= t || y0 >= bb) { continue; }
            ps.forEach(function ([px, py], pi) {
                if(px <= l || px >= rr || py <= t || py >= bb) { return; }
                const p = pts[pi], e = rects[k];
                // Each way out, as (the depth) = (one edge) − (the other).
                const ways = [
                    { d: px - l, hi: p.x, lo: e.x[0], xAxis: true },
                    { d: rr - px, hi: e.x[1], lo: p.x, xAxis: true },
                    { d: py - t, hi: p.y, lo: e.y[0], xAxis: false },
                    { d: bb - py, hi: e.y[1], lo: p.y, xAxis: false },
                ];
                const way = ways.reduce((m, o) => (o.d < m.d ? o : m));
                (way.xAxis ? xTerms : yTerms).push({
                    kind: 'through', w: WEIGHTS.through, value: way.d,
                    vars: way.hi.vars.concat(negated(way.lo)),
                });
            });
        }
    });
    return { xTerms, yTerms };
}

// The energy of a layout, term by term, for tuning and for the tests.
function energy(S, xs, ys, x0, y0) {
    const { xTerms, yTerms } = energyTerms(S, xs, ys);
    const out = { level: 0, length: 0, labels: 0, visible: 0, through: 0, snug: 0, stay: 0 };
    xTerms.concat(yTerms).forEach((t) => { if(!t.shadow) { out[t.kind] += cost(t); } });
    xs.forEach((x, v) => { out.stay += WEIGHTS.stay * (x - x0[v]) * (x - x0[v]); });
    ys.forEach((y, v) => { out.stay += WEIGHTS.stay * (y - y0[v]) * (y - y0[v]); });
    S.rightVar.forEach((r, i) => { out.snug += WEIGHTS.snug * (xs[r] - xs[i]); });
    return out;
}

// The biggest step (in pixels) a variable may take at once: just a guard against a wild step, since
// a step it cuts short upsets the balance between the steps and the projection (see project).
const MAX_STEP = 200;

// What fraction of a Newton step each step of the descent takes.
const STEP = 0.5;
// How little a step has to move everything by for a descent to count as settled.
const SETTLING = 0.5;
// How weak the hold on where things started gets by the end of a descent (see descend).
const STAY_FADE = 1e-3;

// Move the whole layout along one axis so that on average it is where the anchor is.
function recenter(vals, anchor) {
    var shift = 0;
    for(var v = 0; v < vals.length; v++) { shift += anchor[v] - vals[v]; }
    shift /= Math.max(1, vals.length);
    for(var v = 0; v < vals.length; v++) { vals[v] += shift; }
}

// Minimize the energy under the constraints, starting from the layout S was set up with, and
// holding each variable to the anchor given for it in (x0, y0) -- at first.  Over the second half
// of the descent that hold fades almost to nothing: it has done its job by then, of steering toward
// the tidy layout nearest the player's own, and if it stayed it would stop the descent short of
// that, so that arranging the result again would move it on further.
function descend(S, C, x0, y0, iterations, polish) {
    const xs = S.xs.slice(), ys = S.ys.slice();
    const xEdges = C.cx.edges, yEdges = C.cy.edges;
    project(xs, xEdges, 500);
    project(ys, yEdges, 500);
    const half = iterations / 2, fade = Math.pow(STAY_FADE, 1 / half);
    // After those, carry on until it has settled, however long that takes (up to a point).
    for(var it = 0; it < iterations + polish; it++) {
        const stayScale = it < half ? 1 : it < iterations ? Math.pow(fade, it - half) : STAY_FADE;
        const was = it >= iterations ? [Float64Array.from(xs), Float64Array.from(ys)] : null;
        const { xTerms, yTerms } = energyTerms(S, xs, ys);
        const stay = WEIGHTS.stay * stayScale;
        // A step of Newton's method, taking the curvature one variable at a time, and so the
        // curvature it returns is how firmly the energy holds each variable.
        const step = function (vals, anchor, terms, linear) {
            const grad = new Float64Array(vals.length), curv = new Float64Array(vals.length);
            quadratic(grad, curv, terms);
            for(var v = 0; v < vals.length; v++) {
                grad[v] += 2 * stay * (vals[v] - anchor[v]);
                curv[v] += 2 * stay;
            }
            if(linear) { linear(grad); }
            for(var v = 0; v < vals.length; v++) {
                const d = grad[v] / (curv[v] + 1e-9) * STEP;
                vals[v] -= Math.max(-MAX_STEP, Math.min(MAX_STEP, d));
            }
            return curv;
        };
        const xMass = step(xs, x0, xTerms, function (grad) {
            S.rightVar.forEach(function (r, i) { grad[r] += WEIGHTS.snug; grad[i] -= WEIGHTS.snug; });
        });
        const yMass = step(ys, y0, yTerms);
        project(xs, xEdges, 30, xMass);
        project(ys, yEdges, 30, yMass);
        // Nothing but the hold on where things started cares where the layout as a whole is, and
        // what it wants is for it to be where it was on average -- but a step taken one variable at
        // a time can nudge the whole of it along, and many such nudges add up.  So put it back.
        recenter(xs, x0);
        recenter(ys, y0);
        if(was) {
            var change = 0;
            xs.forEach((x, v) => { change = Math.max(change, Math.abs(x - was[0][v])); });
            ys.forEach((y, v) => { change = Math.max(change, Math.abs(y - was[1][v])); });
            if(change < SETTLING) { break; }
        }
    }
    const worst = Math.max(project(xs, xEdges, 2000), project(ys, yEdges, 2000));
    return { xs, ys, worst };
}

// ------------------------------------------------------------------------------------------------
// 4. What gradients can't see

// How far out from its ports a curved wire's control points are (jsPlumb's Bezier connector).
const CURVINESS = 150;
// What each wire crossing another, and each wire running through a block, adds to the energy, when
// weighing one layout against another.
const CROSSING = 3000;
const THROUGH = 3000;

// The path a wire from (sx, sy) to (tx, ty) is drawn along, as a list of points: a curved wire is
// jsPlumb's Bezier curve, and an angled one runs across, then up or down halfway along, then across
// again.
function wirePath(curved, sx, sy, tx, ty) {
    if(!curved) {
        const mx = (sx + tx) / 2;
        return [[sx, sy], [mx, sy], [mx, ty], [tx, ty]];
    }
    const pts = [];
    for(var i = 0; i <= 24; i++) {
        const t = i / 24, u = 1 - t;
        const a = u * u * u, b = 3 * u * u * t, c = 3 * u * t * t, d = t * t * t;
        pts.push([a * sx + b * (sx + CURVINESS) + c * (tx - CURVINESS) + d * tx,
                  a * sy + b * sy + c * ty + d * ty]);
    }
    return pts;
}

// The path each wire is drawn along (see wirePath).
function wirePaths(S, xs, ys) {
    return S.wires.map((w) => wirePath(w.curved, val(xs, S.at.portX(w.s, w.sp)), val(ys, S.at.portY(w.s, w.sp)),
                                       val(xs, S.at.portX(w.t, w.tp)), val(ys, S.at.portY(w.t, w.tp))));
}

function segmentsCross(p, q, r, s) {
    const side = (a, b, c) => Math.sign((b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]));
    return side(p, q, r) * side(p, q, s) < 0 && side(r, s, p) * side(r, s, q) < 0;
}

function pathsCross(a, b) {
    for(var i = 1; i < a.length; i++) {
        for(var j = 1; j < b.length; j++) {
            if(segmentsCross(a[i - 1], a[i], b[j - 1], b[j])) { return true; }
        }
    }
    return false;
}

// Whether a path runs through a rectangle { x0, y0, x1, y1 }.
function pathThrough(path, r) {
    const inside = (p) => p[0] > r.x0 && p[0] < r.x1 && p[1] > r.y0 && p[1] < r.y1;
    const corners = [[r.x0, r.y0], [r.x1, r.y0], [r.x1, r.y1], [r.x0, r.y1]];
    for(var i = 1; i < path.length; i++) {
        if(inside(path[i - 1]) || inside(path[i])) { return true; }
        for(var k = 0; k < 4; k++) {
            if(segmentsCross(path[i - 1], path[i], corners[k], corners[(k + 1) % 4])) { return true; }
        }
    }
    return false;
}

// The wires crossing each other, as pairs of indices into S.wires, and the wires running through
// blocks other than their own two, as [wire, block].
function tangles(S, xs, ys) {
    const paths = wirePaths(S, xs, ys);
    const crossings = [], through = [];
    const samePort = (a, b) => (a.s === b.s && a.sp === b.sp) || (a.t === b.t && a.tp === b.tp);
    for(var i = 0; i < S.wires.length; i++) {
        for(var j = i + 1; j < S.wires.length; j++) {
            if(!samePort(S.wires[i], S.wires[j]) && pathsCross(paths[i], paths[j])) {
                crossings.push([i, j]);
            }
        }
    }
    S.wires.forEach(function (w, i) {
        S.blocks.forEach(function (b, k) {
            if(k === w.s || k === w.t) { return; }
            // A bracket, as far as a wire going past it is concerned, is its bar and uprights.
            const r = { x0: val(xs, S.at.left(k)), x1: val(xs, S.at.right(k)),
                        y0: ys[k], y1: ys[k] + b.h };
            if(pathThrough(paths[i], r)) { through.push([i, k]); }
        });
    });
    return { crossings, through };
}

// The whole energy, gradients' part and all, as a single number to weigh layouts by -- all but how
// far things have moved, which depends on where they started: which of two layouts is better
// mustn't, or arranging an arranged proof could find it better to trade places after all.  (It
// takes a clear improvement to trade places: see untangle.)
function score(S, xs, ys) {
    const e = energy(S, xs, ys, xs, ys);
    const t = tangles(S, xs, ys);
    return Object.keys(e).reduce((a, k) => (k === 'stay' ? a : a + e[k]), 0)
        + CROSSING * t.crossings.length + THROUGH * t.through.length;
}

// ------------------------------------------------------------------------------------------------

// How many more steps a descent may take to settle once the hold on where things started has faded
// (see descend): for the layout itself, and for the trials of trading places (see untangle), which
// only have to be good enough to compare.
const POLISH = 1500;
const TRIAL_ITERATIONS = 150;
const TRIAL_POLISH = 200;
// How many rounds of trading places there are at most, and how many trades each tries in full.
const UNTANGLE_ROUNDS = 3;
const TRADES_TRIED = 4;
// How many times over a layout is tidied from what the last tidying made of it, at most, to reach
// one that tidying again would leave as it is.
const REFINES = 4;

// A layout as { id: { x, y, w } }, with w only for brackets.
function positionsOf(S, xs, ys) {
    const out = {};
    S.blocks.forEach(function (b, i) {
        out[b.id] = { x: xs[i], y: ys[i] };
        if(S.rightVar.has(i)) { out[b.id].w = xs[S.rightVar.get(i)] - xs[i]; }
    });
    return out;
}

// The model with its blocks moved to the given positions.
function movedTo(model, positions) {
    return {
        blocks: model.blocks.map((b) => Object.assign({}, b, positions[b.id])),
        wires: model.wires,
        view: model.view,
    };
}

// Lay out the model starting from `start` (a layout as positionsOf gives), keeping the arrangement
// of that, and holding everything to `anchor`.  Returns the result along with what it was worked
// out with, for scoring it.
function layOut(model, scopes, start, anchor, spread, iterations, polish) {
    const sp = {};
    Object.keys(SPACING).forEach((k) => { sp[k] = SPACING[k] * spread; });
    const S = setUp(movedTo(model, start), scopes, sp);
    S.rects = rectangles(S);
    S.points = pathPoints(S);
    const C = buildConstraints(model, scopes, S);
    S.wires.forEach((w) => { w.hard = C.hard.has(w); });
    const A = setUp(movedTo(model, anchor), scopes, sp);
    const { xs, ys, worst } = descend(S, C, A.xs, A.ys, iterations, polish === undefined ? POLISH : polish);
    return { S, C, xs, ys, worst, x0: A.xs, y0: A.ys, positions: positionsOf(S, xs, ys) };
}

// Pairs of blocks sharing a region, one above the other, that could trade places: for each, the
// two blocks and how far down or up each has to move, with everything inside it.
function swaps(L, scopes) {
    const { S, xs, ys } = L;
    const box = (i) => clusterBox(S, i, xs, ys);
    const out = [];
    const byRegion = new Map();
    S.blocks.forEach(function (b, i) {
        const r = scopes.place.get(b.id);
        if(!byRegion.has(r)) { byRegion.set(r, []); }
        byRegion.get(r).push(i);
    });
    byRegion.forEach(function (items) {
        const boxes = new Map(items.map((i) => [i, box(i)]));
        items.forEach(function (a) {
            items.forEach(function (b) {
                const A = boxes.get(a), B = boxes.get(b);
                // a above b, side by side enough to be in each other's way...
                if(a === b || A.bottom > B.top || A.right <= B.left || B.right <= A.left) { return; }
                // ...with nothing else in between.
                const between = items.some(function (c) {
                    const C = boxes.get(c);
                    return c !== a && c !== b && C.top >= A.bottom && C.bottom <= B.top
                        && C.right > Math.max(A.left, B.left) && C.left < Math.min(A.right, B.right);
                });
                if(between) { return; }
                out.push({ a: a, b: b, da: (B.bottom - A.bottom), db: -(B.top - A.top) });
            });
        });
    });
    return out;
}

// Try trading the places of blocks stacked one above the other, keeping a trade if (after another
// round of descent from there) it untangles the wires enough to be worth it.  Only blocks with a
// wire that crosses another, or runs through a block, are worth trading, and of those only the
// few trades that look most promising before any descent are tried out in full.
function untangle(model, scopes, L, spread) {
    var best = L, bestScore = score(L.S, L.xs, L.ys);
    for(var round = 0; round < UNTANGLE_ROUNDS; round++) {
        const S = best.S;
        const t = tangles(S, best.xs, best.ys);
        if(t.crossings.length === 0 && t.through.length === 0) { break; }
        const tangled = new Set();
        const wire = (i) => { tangled.add(S.wires[i].s); tangled.add(S.wires[i].t); };
        t.crossings.forEach(([i, j]) => { wire(i); wire(j); });
        t.through.forEach(([i, k]) => { wire(i); tangled.add(k); });
        const involved = (i) => S.cluster[i].some((j) => tangled.has(j));
        const tries = swaps(best, scopes).filter(({ a, b }) => involved(a) || involved(b)).map(function ({ a, b, da, db }) {
            const start = Object.assign({}, best.positions);
            const shift = (i, d) => S.cluster[i].forEach(function (j) {
                const id = S.blocks[j].id;
                start[id] = Object.assign({}, start[id], { y: start[id].y + d });
            });
            shift(a, da);
            shift(b, db);
            // How it looks with just enough moved to keep the rules, before any descent.  (Each
            // trade is held to where it starts, not to where the player had things, so that
            // whether it is worth making doesn't depend on that: see score.)
            const quick = layOut(model, scopes, start, start, spread, 0, 0);
            return { start, guess: quick.worst > 0.5 ? Infinity : score(quick.S, quick.xs, quick.ys) };
        }).filter((x) => x.guess < Infinity).sort((x, y) => x.guess - y.guess).slice(0, TRADES_TRIED);
        var found = null, foundScore = Infinity;
        tries.forEach(function ({ start }) {
            const trial = layOut(model, scopes, start, start, spread, TRIAL_ITERATIONS, TRIAL_POLISH);
            if(trial.worst > 0.5) { return; }
            const sc = score(trial.S, trial.xs, trial.ys);
            if(sc < foundScore) { found = trial; foundScore = sc; }
        });
        // Only for a clear improvement: trading places back and forth over a hair's difference
        // would make arranging an arranged proof do it all over again.
        if(found === null || foundScore >= bestScore - CROSSING / 2) { break; }
        best = found;
        bestScore = foundScore;
    }
    return best;
}

// Take a layout from its first tidying (at the given spread) to one that tidying again would leave
// as it is.  Which way round each pair of blocks is kept was read off the player's layout, and read
// off the tidied one it can come out differently -- two brackets that started out of line and have
// come into line, say.  So tidy it again from itself until it stays put, trading places where that
// helps along the way, and then arranging it again will leave it be.
function refine(model, scopes, L, spread) {
    for(var round = 0; round < REFINES; round++) {
        const swapped = untangle(model, scopes, L, spread);
        const again = layOut(model, scopes, swapped.positions, swapped.positions, spread, 300);
        if(again.worst > 0.5) { return swapped; }
        const shift = moved(again.positions, L.positions);
        L = again;
        if(shift <= 2) { break; }
    }
    return L;
}

// Whether a tidied layout is enough of an improvement on the player's own to be worth moving
// things for, at the given spread: it isn't if the player's already keeps the rules at that spread
// and scores within IMPROVEMENT of it, or LEAST_IMPROVEMENT.  (The descent can creep on a long way
// for very little.)
function improves(model, scopes, original, tidied, spread) {
    const own = layOut(model, scopes, original, original, spread, 0, 0);
    if(own.worst > 2 || moved(own.positions, original) > 2) { return true; }
    const was = score(own.S, own.xs, own.ys);
    return score(tidied.S, tidied.xs, tidied.ys) < was - Math.max(IMPROVEMENT * was, LEAST_IMPROVEMENT);
}
// (For a small proof, whose whole score is small, a few percent of it is nothing to see.)
const IMPROVEMENT = 0.05;
const LEAST_IMPROVEMENT = 1500;

// How far the furthest block moved from one layout to another (see positionsOf).  Where the whole
// thing is doesn't come into it, only its shape: nothing in the energy cares where the whole thing
// is, so the descent is free to let it wander.
function moved(positions, from) {
    const ids = Object.keys(positions);
    const mean = (f) => ids.reduce((a, id) => a + f(id), 0) / Math.max(1, ids.length);
    const mx = mean((id) => positions[id].x - from[id].x), my = mean((id) => positions[id].y - from[id].y);
    return Math.max(0, ...ids.map(function (id) {
        const p = positions[id], o = from[id];
        return Math.max(Math.abs(p.x - mx - o.x), Math.abs(p.y - my - o.y),
                        p.w === undefined ? 0 : Math.abs(p.w - o.w));
    }));
}

// The rectangle a layout covers, labels and all.
function extent(L) {
    const r = { x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity };
    L.S.rects.forEach(function (rect) {
        r.x0 = Math.min(r.x0, edgeAt(rect.x[0], L.xs));
        r.x1 = Math.max(r.x1, edgeAt(rect.x[1], L.xs));
        r.y0 = Math.min(r.y0, edgeAt(rect.y[0], L.ys));
        r.y1 = Math.max(r.y1, edgeAt(rect.y[1], L.ys));
    });
    return r;
}

// ------------------------------------------------------------------------------------------------

// Tidy up a diagram.  `model` describes it:
//   blocks: [{ id, x, y, w, h,
//              branches: for a bracket, the branches it has (['upper'] or ['upper', 'lower']),
//              root: true for a block that is never inside a subproof (hypotheses and the like),
//              ports: [{ sort, label, side, dx, dy, right }] -- where each port is on the block:
//                     dy below its top, and dx right of its left edge, or for a port that moves
//                     with a bracket's right edge (`right`), right of that,
//              extent: { left, top, right, bottom } -- what the block covers, counting the type
//                      labels on its ports: left and top relative to its top left corner, right
//                      relative to its right edge, and bottom relative to its top }]
//   wires:  [{ src: { block, port }, tgt: { block, port }, labels: [{ w, h }], curved }], with each
//           end a block id and an index into its ports, and `curved` for a wire drawn as a curve
//           rather than at right angles.
//   view:   { x, y, w, h }, the part of the canvas in view, which a small proof is spread to fill.
// Returns where each block goes, as { id: { x, y, w } } (w only for brackets), along with, for
// tuning and testing: the region each block was put in, the wires left running backwards, the energy
// before and after, the spread chosen, whether the layout was tidy already and left as it was, how
// many wires cross and how many run through blocks, and how far short of the constraints it fell.
export function arrange(model) {
    const scopes = assignRegions(model);
    const original = positionsOf(setUp(model, scopes, SPACING), model.blocks.map((b) => b.x),
                                 model.blocks.map((b) => b.y));
    model.blocks.forEach(function (b) { if(b.branches) { original[b.id].w = b.w; } });
    // Whether the layout is tidy already, keeping every rule a tidy layout keeps (to within a pixel
    // or two: a layout arranged before has been rounded to whole pixels).
    const S1 = setUp(model, scopes, SPACING);
    S1.rects = rectangles(S1);
    S1.points = pathPoints(S1);
    const C1 = buildConstraints(model, scopes, S1);
    S1.wires.forEach((w) => { w.hard = C1.hard.has(w); });
    const short = (vals, edges) => Math.max(0, ...edges.map(([u, v, w]) => vals[u] + w - vals[v]));
    const tidy = Math.max(short(S1.xs, C1.cx.edges), short(S1.ys, C1.cy.edges)) <= 2;
    // Tidy it up as it is, spread out as far as it will go and still fit in the window, if it fits
    // at all.  Each spread is tried from the player's own layout: were it tried from a tidied one
    // instead, arranging an arranged proof would take a different route and end up elsewhere.
    const view = model.view;
    const fits = (r) => r.x1 - r.x0 <= view.w - 2 * VIEW_MARGIN && r.y1 - r.y0 <= view.h - 2 * VIEW_MARGIN;
    const first = layOut(model, scopes, original, original, 1, 300);
    const spreads = [];
    if(view && fits(extent(first))) {
        for(var sp = MAX_SPREAD; sp > 1; sp -= SPREAD_STEP) { spreads.push(sp); }
    }
    spreads.push(1);
    // A layout that is tidy already, and within a few pixels of what arranging it at some spread
    // would make it, or next to no worse, stays exactly as it is.  The descent would only edge it on a little further
    // each time, and arranging an arranged proof ought to leave it be.  (Where the whole thing is
    // doesn't come into it: see `moved`.)
    var L = null, settled = false;
    for(var k = 0; k < spreads.length; k++) {
        const spread = spreads[k];
        const start = spread === 1 ? first : layOut(model, scopes, original, original, spread, 300);
        if(spread > 1 && (start.worst > 0.5 || !fits(extent(start)))) { continue; }
        const tidied = refine(model, scopes, start, spread);
        tidied.spread = spread;
        // Trading places and tidying again can make it bigger than it was: if it no longer fits,
        // it has to be less of a spread.
        if(spread > 1 && !fits(extent(tidied))) { continue; }
        if(L === null) { L = tidied; }
        if(tidy && (moved(tidied.positions, original) <= SETTLED
                    || !improves(model, scopes, original, tidied, spread))) {
            L = { S: S1, C: C1, xs: S1.xs, ys: S1.ys, worst: 0, spread: spread, positions: original };
            settled = true;
            break;
        }
        if(!tidy) { break; }
    }
    // A layout that fits in the window goes in the middle of it, and one that doesn't starts at its
    // top left corner, where its labels can't hang off the edge of the canvas (unless it's been left
    // as it was).
    var dx = 0, dy = 0;
    if(view && !settled) {
        const r = extent(L);
        if(fits(r)) {
            dx = view.x + (view.w - (r.x1 - r.x0)) / 2 - r.x0;
            dy = view.y + (view.h - (r.y1 - r.y0)) / 2 - r.y0;
        } else {
            dx = view.x + VIEW_MARGIN - r.x0;
            dy = view.y + VIEW_MARGIN - r.y0;
        }
    }
    const positions = settled ? original : {};
    if(!settled) {
        Object.keys(L.positions).forEach(function (id) {
            const p = L.positions[id];
            positions[id] = { x: Math.round(p.x + dx), y: Math.round(p.y + dy) };
            if(p.w !== undefined) { positions[id].w = Math.round(p.w); }
        });
    }
    const t = tangles(L.S, L.xs, L.ys);
    return {
        positions: positions,
        regions: Object.fromEntries(scopes.place),
        backward: L.S.wires.filter((w) => !w.hard).map((w) => [L.S.blocks[w.s].id, L.S.blocks[w.t].id]),
        energy: {
            before: energy(S1, S1.xs, S1.ys, S1.xs, S1.ys),
            after: energy(L.S, L.xs, L.ys, S1.xs, S1.ys),
        },
        spread: L.spread || 1,
        settled: settled,
        crossings: t.crossings.length,
        hidden: L.S.wires.filter((w) => w.labels.length > 0
                                 && shownOf(L.S, w, L.xs, L.ys).shown < SPACING.wireShown / 2).length,
        through: t.through.length,
        unresolved: L.worst,
    };
}
