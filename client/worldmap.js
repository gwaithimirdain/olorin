// Where things go on the map of worlds at the top of the level chooser.
//
// The worlds are laid out left to right in columns, from nothing but which worlds follow which
// (their `previous` lists), so the map keeps up with levels.js however the relation changes or
// grows: a world always stands to the right of every world it follows.  The map can come out
// wider or taller than the chooser; it scrolls (see makeLevelSelect in main.js).
//
// A world following several others waits for all of them, and several worlds often wait for the
// same ones -- two worlds following Implication and Disjunction both, say.  Rather than a line from
// each of those to each of these, crossing each other, the lines of such a shared set meet at a
// junction, one line from each world waited on in and one to each waiting world out: "all of
// these open all of those".  A world waiting on those and more besides takes a line from the
// junction too, and its own lines from the rest.  Any other line goes straight from the world
// waited on to the world waiting (see junctionsFor).
//
// This module only does the geometry, so that it can be tried out without a page: main.js draws it.

// The size of a world's box on the map, and of a junction's dot.
export const NODE_WIDTH = 104;
export const NODE_HEIGHT = 46;
export const JUNCTION_RADIUS = 4;

// Space around the whole map, between boxes (or junctions) one above the other, between a line and
// whatever it passes between, between columns of worlds, and between the separately laid-out groups
// (see layoutWorldMap).
const MARGIN = 12;
const NODE_SEP = 8;
const LINE_SEP = 14;
const COLUMN_GAP = 72;

// How lines leave and come into boxes and junctions: straight and level for STUB, and then still
// nearly level for LEVEL_ARM of the way on before they bend (see pieces).
const STUB = 8;
const LEVEL_ARM = 0.5;
const GROUP_GAP = 64;

// How far down a group smaller than the tallest may be moved, to centre it: no further, so that in a
// tall map it isn't somewhere below what the chooser shows of it.
const MAX_CENTRING = 100;

// How many times placeHeights goes back and forth over the columns: a few, to compare orders by, and
// more for the heights the map is drawn with.
const SEARCH_SWEEPS = 8;
const FINAL_SWEEPS = 40;

// Lay out the map.  `groups` is a list of groups of worlds, laid out one after another from left to
// right and not joined to each other: the game's own worlds, then a course's, then the Custom one.
// Each group is a list of { id, previous }, where `previous` is the ids of the worlds in the same
// group that this one follows.  An id is anything distinct as a string.
//
// Returns { width, height, nodes, junctions, edges, dividers }:
//   nodes      a Map from each id to { x, y }, the top-left corner of its box;
//   junctions  a list of { x, y, sources, targets }: the centre of a junction's dot, the ids of the
//              worlds whose lines come into it, and those of the worlds its lines go out to;
//   edges      a list of { source, target, path }, one per line: `source` and `target` are each
//              { world: id } or { junction: index into junctions }, and `path` is its SVG path;
//   dividers   the x of a vertical line between each two groups.
export function layoutWorldMap(groups) {
    const nodes = new Map();
    const junctions = [];
    const edges = [];
    const dividers = [];
    const laid = groups.filter((g) => g.length > 0).map(layoutGroup);
    const height = Math.max(0, ...laid.map((l) => l.height));
    var left = 0;
    laid.forEach(function (l, i) {
        // Each group comes with a margin of its own all round, which makes up part of the gap
        // between the boxes of one group and the next.
        if(i > 0) {
            dividers.push(left - MARGIN + GROUP_GAP / 2);
            left += GROUP_GAP - 2 * MARGIN;
        }
        // Centre each group in the height of the tallest, as far as MAX_CENTRING allows.
        const dx = left, dy = Math.min(MAX_CENTRING, (height - l.height) / 2);
        l.nodes.forEach((p, id) => nodes.set(id, { x: p.x + dx, y: p.y + dy }));
        const base = junctions.length;
        l.junctions.forEach((j) => junctions.push({ x: j.x + dx, y: j.y + dy,
                                                     sources: j.sources, targets: j.targets }));
        l.edges.forEach(function (e) {
            const shift = (end) => end.junction === undefined ? end : { junction: end.junction + base };
            edges.push({ source: shift(e.source), target: shift(e.target),
                         path: smoothPath(e.points.map((p) => Object.assign({}, p, { x: p.x + dx, y: p.y + dy }))) });
        });
        left += l.width;
    });
    return { width: left, height: height, nodes: nodes, junctions: junctions, edges: edges,
             dividers: dividers };
}

// Lay out one group by itself, with its top-left corner at (0, 0).  Its edges come back as the
// points their lines pass through, from the middle of the right side of the box they start at (or
// the centre of the junction) to the middle of the left side of the one they end at.
//
// This is the usual way of drawing a graph in layers (Sugiyama's): put each thing in a column, put
// each column in an order, and then give each thing its height.
//
//   Columns.  A world goes in the first column it could, right after the last of the worlds it
//   follows, so that its column says how far into the game it comes.  Worlds are in the even
//   columns, and the odd ones between them hold the junctions.  A line that goes further than the
//   next column passes through each one on the way as a "waypoint", which takes up a place in that
//   column like anything else, so that the line has a way through between the boxes.
//
//   Order.  Crossings are what make a map hard to read, so the order within the columns is first of
//   all the one with fewest lines crossing, and then, of those, the one whose lines have least far
//   to go up or down -- which puts worlds beside the ones they're joined to, and so
//   keeps the lines short and straight.  It starts from each column in the order of the middles of
//   what it's joined to in the column before (the "barycenter" heuristic, swept back and forth),
//   and improves on that by trying out changes to it -- moving one thing elsewhere in its column,
//   turning columns upside down, and moving a long line to the top or bottom of the columns it
//   crosses (see orderColumns) -- for as long as any of them makes it better.
//
//   Height.  A column of worlds is stacked with no more than NODE_SEP between them, so that the map
//   is no taller than it has to be, and moved up or down as a whole to where its lines have least
//   far to go.  The things in the columns between -- junctions, and lines passing through -- are
//   each put where their own lines are straightest, keeping their order and out of each other's way.
//   (See placeHeights.)
function layoutGroup(group) {
    const ids = new Set(group.map((w) => String(w.id)));
    // Every thing in a column: a world's box, a junction's dot, or a line's waypoint.  `rank` is its
    // column, `size` how much height it takes up, and `ins`/`outs` what it is joined to in the
    // columns either side.
    const items = [];
    const item = (kind, size, extra) => {
        const it = Object.assign({ kind: kind, size: size, rank: 0, ins: [], outs: [], y: 0, serial: items.length }, extra);
        items.push(it);
        return it;
    };
    const worldItem = new Map();
    group.forEach((w) => worldItem.set(String(w.id), item('world', NODE_HEIGHT, { id: w.id })));

    // The lines: through the junctions junctionsFor picks, and straight for the rest.
    const wanted = [];
    const worldEnd = (id) => ({ end: { world: id }, item: worldItem.get(String(id)) });
    const { junctions, direct } = junctionsFor(group.map((w) => ({
        id: w.id, previous: w.previous.filter((p) => ids.has(String(p))),
    })));
    junctions.forEach(function (junction, j) {
        const jEnd = { end: { junction: j }, item: item('junction', 2 * JUNCTION_RADIUS, {}) };
        junction.sources.forEach((s) => wanted.push({ from: worldEnd(s), to: jEnd }));
        junction.targets.forEach((t) => wanted.push({ from: jEnd, to: worldEnd(t) }));
    });
    direct.forEach((d) => wanted.push({ from: worldEnd(d.source), to: worldEnd(d.target) }));

    // Columns: a world two after the last of what it follows, a junction one after the last of what
    // comes into it, and so a world one after its junction.  (Should levels.js ever have worlds
    // following each other round in a circle, this gives up going round after as many times as
    // there are things, rather than for ever, and the lines back are drawn as they fall.)
    const step = (w) => (w.from.item.kind === 'world' && w.to.item.kind === 'world' ? 2 : 1);
    for(var pass = 0; pass < items.length; pass++) {
        var moved = false;
        wanted.forEach(function (w) {
            const r = w.from.item.rank + step(w);
            if(w.to.item.rank < r) { w.to.item.rank = r; moved = true; }
        });
        if(!moved) { break; }
    }

    // Each line as the chain of things it passes through, a waypoint for each column between its ends.
    wanted.forEach(function (w) {
        const chain = [w.from.item];
        for(var r = w.from.item.rank + 1; r < w.to.item.rank; r++) { chain.push(item('waypoint', 0, { rank: r })); }
        chain.push(w.to.item);
        for(var i = 0; i + 1 < chain.length; i++) {
            chain[i].outs.push(chain[i + 1]);
            chain[i + 1].ins.push(chain[i]);
        }
        w.chain = chain;
    });

    const lastRank = Math.max(0, ...items.map((it) => it.rank));
    const columns = [];
    for(var r = 0; r <= lastRank; r++) { columns.push([]); }
    items.forEach((it) => columns[it.rank].push(it));

    orderColumns(columns, wanted.map((w) => w.chain.slice(1, -1)).filter((line) => line.length >= 2));
    placeHeights(columns, FINAL_SWEEPS);

    // Where each column is across: the worlds' columns evenly spaced, and the others halfway between.
    const colX = (rank) => MARGIN + NODE_WIDTH / 2 + rank / 2 * (NODE_WIDTH + COLUMN_GAP);
    const top = Math.min(...items.map((it) => it.y - it.size / 2));
    const bottom = Math.max(...items.map((it) => it.y + it.size / 2));
    const y = (it) => it.y - top + MARGIN;

    const nodes = new Map();
    group.forEach(function (w) {
        const it = worldItem.get(String(w.id));
        nodes.set(w.id, { x: colX(it.rank) - NODE_WIDTH / 2, y: y(it) - NODE_HEIGHT / 2 });
    });
    wanted.forEach(function (w) {
        if(w.to.end.junction !== undefined) {
            const j = junctions[w.to.end.junction];
            j.x = colX(w.to.item.rank);
            j.y = y(w.to.item);
        }
    });
    const edges = wanted.map(function (w) {
        const points = [];
        const gaps = [];
        w.chain.forEach(function (it, i) {
            const x = colX(it.rank);
            if(it.kind === 'world') {
                // Out of the right side of the box it starts at, into the left of the one it ends at.
                points.push({ x: x + (i === 0 ? 1 : -1) * NODE_WIDTH / 2, y: y(it) });
            } else if(it.kind === 'junction') {
                points.push({ x: x, y: y(it) });
            } else if(it.rank % 2 === 0) {
                // Through the middle of the way left for it between the boxes of a column of worlds
                // it crosses -- and not so near either box at the column's edges as to clip a corner
                // (see routeLine).  (Its waypoints between the columns, which only kept a place for
                // it there while the map was being laid out, it needn't go through.)
                points.push({ x: x, y: y(it) });
                const col = columns[it.rank];
                const above = col[it.order - 1], below = col[it.order + 1];
                const clear = (n) => (n.kind === 'waypoint' ? 0 : n.size / 2 + LINE_SEP / 2);
                gaps.push({ x: x, top: above ? y(above) + clear(above) : -Infinity,
                            bottom: below ? y(below) - clear(below) : Infinity });
            }
        });
        return { source: w.from.end, target: w.to.end, points: routeLine(withStubs(points), gaps) };
    });
    const lastWorldRank = lastRank + (lastRank % 2);
    return {
        width: 2 * MARGIN + NODE_WIDTH + lastWorldRank / 2 * (NODE_WIDTH + COLUMN_GAP),
        height: bottom - top + 2 * MARGIN,
        nodes: nodes, junctions: junctions, edges: edges,
    };
}

// Which junctions to draw, for worlds `group` ({ id, previous }, each `previous` being of worlds in
// the group): { junctions, direct }, a list of { sources, targets } -- a junction, the worlds whose
// lines come into it and those its lines go out to -- and a list of { source, target }, the lines
// straight from one world to another.
//
// A junction stands for a set of two or more worlds, and every world waiting on all of those (among
// others, maybe) takes a line from it rather than one from each; it's only worth drawing for two or
// more of them.  Which sets to make junctions of is a matter of covering each world's `previous`
// with as few lines as can be.  They're picked one at a time, each the set that saves the most
// lines of those not yet drawn -- a set of s worlds waited on by t, as a junction, replacing s * t
// lines by s + t -- and even a set that saves none, as Implication and Disjunction waited on by
// two others do, for the crossings it saves.  The sets tried are each world's own `previous`, as
// far as it isn't already drawn, and what any two of those have in common.
function junctionsFor(group) {
    const junctions = [];
    // What of each world's `previous` isn't drawn yet.
    const left = group.map((w) => ({ id: w.id, previous: w.previous.slice() }));
    const key = (set) => set.map(String).sort().join('\u0000');
    for(;;) {
        const tried = new Map();
        const consider = function (set) {
            if(set.length >= 2 && !tried.has(key(set))) { tried.set(key(set), set); }
        };
        left.forEach((w) => consider(w.previous));
        left.forEach((a, i) => left.slice(i + 1).forEach(function (b) {
            consider(a.previous.filter((p) => b.previous.some((q) => String(q) === String(p))));
        }));
        var best = null;
        tried.forEach(function (set) {
            const users = left.filter((w) => set.every((p) => w.previous.some((q) => String(q) === String(p))));
            if(users.length < 2) { return; }
            const saves = set.length * users.length - (set.length + users.length);
            if(!best || saves > best.saves) { best = { set: set, users: users, saves: saves }; }
        });
        if(!best) { break; }
        junctions.push({ sources: best.set, targets: best.users.map((w) => w.id) });
        best.users.forEach(function (w) {
            w.previous = w.previous.filter((p) => !best.set.some((q) => String(q) === String(p)));
        });
    }
    const direct = [];
    left.forEach((w) => w.previous.forEach((p) => direct.push({ source: p, target: w.id })));
    return { junctions: junctions, direct: direct };
}

// How far apart the middles of two things one above the other in a column must be: half of each,
// and NODE_SEP between two boxes or junctions, or LINE_SEP where either is a line passing through.
function separation(a, b) {
    return (a.size + b.size) / 2 + (a.kind === 'waypoint' || b.kind === 'waypoint' ? LINE_SEP : NODE_SEP);
}

// Put the things in each column in order (see layoutGroup): each column's list is rearranged in
// place, top to bottom.  `lines` is the waypoints of each line that crosses more than one column.
function orderColumns(columns, lines) {
    const index = (col) => col.forEach((it, i) => { it.order = i; });
    const mean = (xs) => xs.reduce((a, b) => a + b, 0) / xs.length;
    // Sort a column by the middle of what each thing in it is joined to on one side, keeping the
    // things joined to nothing there where they were.
    const sortBy = function (col, side) {
        const key = new Map(col.map((it) => [it, it[side].length > 0 ? mean(it[side].map((n) => n.order)) : it.order]));
        col.sort((a, b) => key.get(a) - key.get(b) || a.order - b.order);
        index(col);
    };
    columns.forEach(function (col) {
        col.sort((a, b) => a.serial - b.serial);
        index(col);
    });
    for(var sweep = 0; sweep < 4; sweep++) {
        for(var r = 1; r < columns.length; r++) { sortBy(columns[r], 'ins'); }
        for(var r = columns.length - 2; r >= 0; r--) { sortBy(columns[r], 'outs'); }
    }

    // Then improve on it, one change at a time, keeping each that makes it better: fewer crossings,
    // or as few and less far for its lines to go.  Crossings are cheap to count, and most changes
    // add some, so they're counted first -- and only between the columns a change touches -- and the
    // heights, which take longer, are only worked out when the crossings tie.
    const crossed = columns.map((_, r) => crossingsAfter(columns, r));
    var bestCrossings = crossed.reduce((a, b) => a + b, 0);
    var bestTravel = null;
    const reindex = (from, to) => { for(var r = from; r < to; r++) { index(columns[r]); } };
    const attempt = function (change, from, to) {
        if(bestTravel === null) { bestTravel = travel(columns); }
        const saved = columns.slice(from, to).map((col) => col.slice());
        change();
        reindex(from, to);
        // The gaps between columns whose crossings the change can have altered.
        const gaps = [];
        for(var r = Math.max(0, from - 1); r < Math.min(to, columns.length - 1); r++) { gaps.push(r); }
        const before = gaps.map((r) => crossed[r]);
        gaps.forEach((r) => { crossed[r] = crossingsAfter(columns, r); });
        const crossings = crossed.reduce((a, b) => a + b, 0);
        if(crossings < bestCrossings) {
            bestCrossings = crossings;
            bestTravel = null;
            return true;
        }
        if(crossings === bestCrossings) {
            const t = travel(columns);
            if(t < bestTravel - 1e-6) { bestTravel = t; return true; }
        }
        saved.forEach((col, i) => { columns[from + i].splice(0, col.length, ...col); });
        reindex(from, to);
        gaps.forEach((r, i) => { crossed[r] = before[i]; });
        return false;
    };
    // The changes tried: moving one thing to another place in its column; turning a column upside
    // down, or it and every column after it; and moving the waypoints of a line that crosses more
    // than one column all to the top of their columns, or all to the bottom -- which no number of
    // smaller changes might get to, each on the way adding a crossing that only the rest take away.
    const move = (col, i, k) => () => { col.splice(k, 0, col.splice(i, 1)[0]); };
    const reverse = (from, to) => () => { for(var r = from; r < to; r++) { columns[r].reverse(); } };
    const toEnd = (line, top) => () => {
        line.forEach(function (it) {
            const col = columns[it.rank];
            col.splice(col.indexOf(it), 1);
            if(top) { col.unshift(it); } else { col.push(it); }
        });
    };
    for(var round = 0; round < 50; round++) {
        var improved = false;
        for(var r = 0; r < columns.length; r++) {
            const col = columns[r];
            for(var i = 0; i < col.length; i++) {
                for(var k = 0; k < col.length; k++) {
                    if(k !== i && attempt(move(col, i, k), r, r + 1)) { improved = true; }
                }
            }
            if(col.length > 1 && attempt(reverse(r, r + 1), r, r + 1)) { improved = true; }
            if(r > 0 && attempt(reverse(r, columns.length), r, columns.length)) { improved = true; }
        }
        lines.forEach(function (line) {
            const from = line[0].rank, to = line[line.length - 1].rank + 1;
            if(attempt(toEnd(line, true), from, to)) { improved = true; }
            if(attempt(toEnd(line, false), from, to)) { improved = true; }
        });
        if(!improved) { break; }
    }
}

// How many lines cross between column r and the next.
function crossingsAfter(columns, r) {
    if(r + 1 >= columns.length) { return 0; }
    const links = [];
    columns[r].forEach((it) => it.outs.forEach((n) => links.push([it.order, n.order])));
    var crossings = 0;
    for(var i = 0; i < links.length; i++) {
        for(var j = i + 1; j < links.length; j++) {
            if((links[i][0] - links[j][0]) * (links[i][1] - links[j][1]) < 0) { crossings++; }
        }
    }
    return crossings;
}

// How far the lines go up or down, in all, with the heights placeHeights gives them: the second
// thing an order is judged by, after its crossings.  Only roughly worked out, as it is worked out
// for every change tried: near enough to compare two orders by.
function travel(columns) {
    placeHeights(columns, SEARCH_SWEEPS);
    var total = 0;
    columns.forEach((col) => col.forEach((it) => it.outs.forEach((n) => { total += Math.abs(it.y - n.y); })));
    return total;
}

// Give everything in the columns its height (`y`, of its middle), keeping each column's order.  A
// column of worlds is stacked tight and moved as a whole; everything else goes where it likes
// within its order.  "Where it likes" is where its lines are straightest: level with the middle of
// what it's joined to either side, which is worked towards by going back and forth over the
// columns (`sweeps` times), each time putting each column where it's best given the others.
function placeHeights(columns, sweeps) {
    const mean = (xs) => xs.reduce((a, b) => a + b, 0) / xs.length;
    // Start with every column stacked tight from the top.
    columns.forEach(function (col) {
        col.forEach((it, i) => { it.y = i === 0 ? 0 : col[i - 1].y + separation(col[i - 1], it); });
    });
    for(var sweep = 0; sweep < sweeps; sweep++) {
        const ranks = columns.map((_, r) => r);
        if(sweep % 2 === 1) { ranks.reverse(); }
        ranks.forEach(function (r) {
            const col = columns[r];
            if(col.length === 0) { return; }
            // Where each thing would like to be, and how much it minds: the middle of what it's
            // joined to, by how many things that is.
            const wants = col.map(function (it) {
                const joined = it.ins.concat(it.outs);
                return joined.length > 0 ? { y: mean(joined.map((n) => n.y)), weight: joined.length } : null;
            });
            if(r % 2 === 0) {
                // The whole stack moves by as much as its things want, on average.
                var shift = 0, weight = 0;
                col.forEach(function (it, i) {
                    if(wants[i]) { shift += wants[i].weight * (wants[i].y - it.y); weight += wants[i].weight; }
                });
                if(weight > 0) { col.forEach((it) => { it.y += shift / weight; }); }
            } else {
                // Each goes where it wants, as near as keeping in order and apart allows: taking away
                // how far down the separations above it push each one, that's putting them in order
                // as near as can be to where they want, which pooling adjacent violators does.
                var below = 0;
                const blocks = [];
                col.forEach(function (it, i) {
                    if(i > 0) { below += separation(col[i - 1], it); }
                    const want = wants[i] || { y: it.y, weight: 0.001 };
                    blocks.push({ value: want.y - below, weight: want.weight, count: 1 });
                    while(blocks.length > 1 && blocks[blocks.length - 2].value > blocks[blocks.length - 1].value) {
                        const b = blocks.pop(), a = blocks.pop();
                        const weight = a.weight + b.weight;
                        blocks.push({ value: (a.value * a.weight + b.value * b.weight) / weight, weight: weight,
                                      count: a.count + b.count });
                    }
                });
                var i = 0;
                below = 0;
                blocks.forEach(function (b) {
                    for(var k = 0; k < b.count; k++, i++) {
                        if(i > 0) { below += separation(col[i - 1], col[i]); }
                        col[i].y = b.value + below;
                    }
                });
            }
        });
    }
}

// The points a line is drawn through (see smoothPath), from `points`: those it has to go through, and,
// where the curve through just those would come too near a box at an edge of a column of worlds
// that it crosses, a point there too, as near as it may.  `gaps` is the way left for it through
// each such column, { x, top, bottom }: the middle of the column across, and how high and low it may
// go there.
function routeLine(points, gaps) {
    var pts = points;
    for(var round = 0; round < 3; round++) {
        const extra = [];
        gaps.forEach(function (g) {
            [g.x - NODE_WIDTH / 2, g.x + NODE_WIDTH / 2].forEach(function (x) {
                if(pts.some((p) => Math.abs(p.x - x) < 0.5)) { return; }
                const y = curveAt(pts, x);
                const kept = Math.min(g.bottom, Math.max(g.top, y));
                if(Math.abs(kept - y) > 0.5) { extra.push({ x: x, y: kept }); }
            });
        });
        if(extra.length === 0) { break; }
        pts = pts.concat(extra).sort((a, b) => a.x - b.x);
    }
    return pts;
}

// A line's points with a short straight stretch added at each end, so that it comes out of a box (or
// a junction's dot) level, and goes into one level, before it bends -- where there's room for it.
// The ends, and the stretches' far ends, are marked `level` (see pieces).
function withStubs(points) {
    const n = points.length;
    const first = Object.assign({}, points[0], { level: true });
    const last = Object.assign({}, points[n - 1], { level: true });
    const middle = points.slice(1, n - 1);
    const room = (a, b) => STUB > 0 && Math.abs(b.x - a.x) > 3 * STUB;
    const out = [first];
    if(room(first, points[1])) { out.push({ x: first.x + STUB, y: first.y, level: true }); }
    out.push(...middle);
    if(room(points[n - 2], last)) { out.push({ x: last.x - STUB, y: last.y, level: true }); }
    out.push(last);
    return out;
}

// The curve through a line's points, as the cubic pieces between each two: for each, its ends and
// its two control points, { a, c1, c2, b }.  At a point marked `level` (an end, or the far end of a
// straight stretch at one) the curve is level, and stays nearly so for LEVEL_ARM of the way to the
// next point before it bends.  Anywhere else it takes the slope from the point before to the point
// after (a "Catmull-Rom" curve), so that it goes on its way without levelling off and waving about.
function pieces(points) {
    const n = points.length;
    const slope = points.map(function (p, i) {
        if(p.level || i === 0 || i === n - 1) { return 0; }
        const a = points[i - 1], b = points[i + 1];
        return b.x === a.x ? 0 : (b.y - a.y) / (b.x - a.x);
    });
    const arm = (p, i, h) => (p.level || i === 0 || i === n - 1 ? LEVEL_ARM : 1 / 3) * h;
    const out = [];
    for(var i = 0; i + 1 < n; i++) {
        const a = points[i], b = points[i + 1], h = b.x - a.x;
        const ka = arm(a, i, h), kb = arm(b, i + 1, h);
        out.push({ a: a, b: b, c1: { x: a.x + ka, y: a.y + slope[i] * ka },
                   c2: { x: b.x - kb, y: b.y - slope[i + 1] * kb } });
    }
    return out;
}

// Where the curve through `points` is at x.
function curveAt(points, x) {
    const piece = pieces(points).find((p) => x >= p.a.x && x <= p.b.x && p.b.x > p.a.x);
    if(!piece) { return points[x < points[0].x ? 0 : points.length - 1].y; }
    const at = (t, k) => {
        const u = 1 - t;
        return u * u * u * piece.a[k] + 3 * u * u * t * piece.c1[k] + 3 * u * t * t * piece.c2[k] + t * t * t * piece.b[k];
    };
    // Its x goes steadily on along it, so the point at x can be found by halving.
    var lo = 0, hi = 1;
    for(var step = 0; step < 30; step++) {
        const mid = (lo + hi) / 2;
        if(at(mid, 'x') < x) { lo = mid; } else { hi = mid; }
    }
    return at((lo + hi) / 2, 'y');
}

// An SVG path through a line's points, left to right: one smooth curve (see pieces).
function smoothPath(points) {
    const fmt = (p) => Math.round(p.x * 10) / 10 + ',' + Math.round(p.y * 10) / 10;
    return 'M' + fmt(points[0]) + pieces(points).map((p) => ' C' + fmt(p.c1) + ' ' + fmt(p.c2) + ' ' + fmt(p.b)).join('');
}
