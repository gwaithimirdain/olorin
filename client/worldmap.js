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
// these open all of those".  A world waiting on a set nothing else does, or a set of only one
// world, just gets its own lines.
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
const COLUMN_GAP = 48;
const GROUP_GAP = 64;

// How far down a group smaller than the tallest may be moved, to centre it: no further, so that in a
// tall map it isn't somewhere below what the chooser shows of it.
const MAX_CENTRING = 100;

// How far along its straight stretches a line may start bending towards its next height: the
// curves are drawn as long as that allows, since there's only a short hop between columns.
const MAX_BEND = 40;

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
                         path: pathThrough(e.points.map((p) => ({ x: p.x + dx, y: p.y + dy }))) });
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
//   and improves on that by trying out each swap of two neighbours in a column, each column turned
//   upside down, and each column turned upside down together with every column after it, for as
//   long as any of those makes it better.
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

    // Gather the worlds waiting on each set of worlds, in the order they come, and join them: through
    // a junction for a set of two or more waited on by two or more, and straight otherwise.
    const sets = new Map();
    group.forEach(function (w) {
        const previous = w.previous.filter((p) => ids.has(String(p)));
        if(previous.length === 0) { return; }
        const k = previous.map(String).sort().join('\u0000');
        if(!sets.has(k)) { sets.set(k, { sources: previous, targets: [] }); }
        sets.get(k).targets.push(w.id);
    });
    const junctions = [];
    const wanted = [];
    const worldEnd = (id) => ({ end: { world: id }, item: worldItem.get(String(id)) });
    sets.forEach(function (set) {
        if(set.sources.length >= 2 && set.targets.length >= 2) {
            const j = junctions.length;
            const jEnd = { end: { junction: j }, item: item('junction', 2 * JUNCTION_RADIUS, {}) };
            junctions.push({ sources: set.sources, targets: set.targets });
            set.sources.forEach((s) => wanted.push({ from: worldEnd(s), to: jEnd }));
            set.targets.forEach((t) => wanted.push({ from: jEnd, to: worldEnd(t) }));
        } else {
            set.sources.forEach((s) => set.targets.forEach((t) => wanted.push({ from: worldEnd(s), to: worldEnd(t) })));
        }
    });

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

    orderColumns(columns);
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
        w.chain.forEach(function (it, i) {
            const x = colX(it.rank);
            if(it.kind === 'world') {
                // Out of the right side of the box it starts at, into the left of the one it ends at.
                points.push({ x: x + (i === 0 ? 1 : -1) * NODE_WIDTH / 2, y: y(it) });
            } else if(it.kind === 'waypoint' && it.rank % 2 === 0) {
                // Level across a column of worlds, so as to keep between their boxes.
                points.push({ x: x - NODE_WIDTH / 2, y: y(it) }, { x: x + NODE_WIDTH / 2, y: y(it) });
            } else {
                points.push({ x: x, y: y(it) });
            }
        });
        return { source: w.from.end, target: w.to.end, points: points };
    });
    const lastWorldRank = lastRank + (lastRank % 2);
    return {
        width: 2 * MARGIN + NODE_WIDTH + lastWorldRank / 2 * (NODE_WIDTH + COLUMN_GAP),
        height: bottom - top + 2 * MARGIN,
        nodes: nodes, junctions: junctions, edges: edges,
    };
}

// How far apart the middles of two things one above the other in a column must be: half of each,
// and NODE_SEP between two boxes or junctions, or LINE_SEP where either is a line passing through.
function separation(a, b) {
    return (a.size + b.size) / 2 + (a.kind === 'waypoint' || b.kind === 'waypoint' ? LINE_SEP : NODE_SEP);
}

// Put the things in each column in order (see layoutGroup): each column's list is rearranged in
// place, top to bottom.
function orderColumns(columns) {
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
        // Every change tried is its own undoing: a swap, or turning columns upside down.
        if(bestTravel === null) { bestTravel = travel(columns); }
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
        change();
        reindex(from, to);
        gaps.forEach((r, i) => { crossed[r] = before[i]; });
        return false;
    };
    const reverse = (from, to) => () => { for(var r = from; r < to; r++) { columns[r].reverse(); } };
    for(var round = 0; round < 50; round++) {
        var improved = false;
        for(var r = 0; r < columns.length; r++) {
            const col = columns[r];
            for(var i = 0; i + 1 < col.length; i++) {
                const swap = ((k) => () => { const t = col[k]; col[k] = col[k + 1]; col[k + 1] = t; })(i);
                if(attempt(swap, r, r + 1)) { improved = true; }
            }
            if(col.length > 1 && attempt(reverse(r, r + 1), r, r + 1)) { improved = true; }
            if(r > 0 && attempt(reverse(r, columns.length), r, columns.length)) { improved = true; }
        }
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

// An SVG path through a line's points, running level between them and bending smoothly from one
// height to the next.  A line goes through a point in every column it crosses, many of them at the
// height of the one before, and changes height in the short hop between two columns; so the path is
// built from those level stretches, each change of height being drawn as a curve that
// takes up to MAX_BEND of the stretch on either side of it to bend in.
function pathThrough(points) {
    // The level stretches, left to right.
    const runs = [];
    points.forEach(function (p) {
        const last = runs[runs.length - 1];
        if(last && Math.abs(last.y - p.y) < 0.5) { last.x1 = p.x; }
        else { runs.push({ x0: p.x, x1: p.x, y: p.y }); }
    });
    // How much of each stretch the bends at its ends may take: half of it at most, so the bends at
    // its two ends don't overlap -- except the first stretch and the last, which have a bend at only
    // one end, and can give it all of their length.
    const bend = runs.map(function (r, i) {
        const ends = (i > 0 ? 1 : 0) + (i < runs.length - 1 ? 1 : 0);
        return Math.min(MAX_BEND, Math.abs(r.x1 - r.x0) / Math.max(1, ends));
    });
    const fmt = (x, y) => Math.round(x * 10) / 10 + ',' + Math.round(y * 10) / 10;
    var d = 'M' + fmt(runs[0].x0, runs[0].y);
    runs.forEach(function (r, i) {
        const next = runs[i + 1];
        if(!next) { d += ' L' + fmt(r.x1, r.y); return; }
        const from = r.x1 - bend[i];
        const to = next.x0 + bend[i + 1];
        const mid = (from + to) / 2;
        d += ' L' + fmt(from, r.y) + ' C' + fmt(mid, r.y) + ' ' + fmt(mid, next.y) + ' ' + fmt(to, next.y);
    });
    return d;
}
