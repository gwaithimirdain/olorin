// Where things go on the map of worlds at the top of the level chooser.
//
// The worlds are laid out left to right in layers by dagre, from nothing but which worlds follow
// which (their `previous` lists), so the map keeps up with levels.js however the relation changes
// or grows: a world always stands to the right of every world it follows.  The map can come out
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

import dagre from '@dagrejs/dagre';

// The size of a world's box on the map, and of a junction's dot.
export const NODE_WIDTH = 104;
export const NODE_HEIGHT = 46;
export const JUNCTION_RADIUS = 4;

// Space around the whole map, between worlds in the same layer, between layers, and between the
// separately laid-out groups (see layoutWorldMap).
const MARGIN = 12;
const NODE_SEP = 8;
const RANK_SEP = 24;
const GROUP_GAP = 64;

// How far down a group smaller than the tallest may be moved, to centre it: no further, so that in a
// tall map it isn't somewhere below what the chooser shows of it.
const MAX_CENTRING = 100;

// How far along its straight stretches a line may start bending towards its next height: the
// curves are drawn as long as that allows, since dagre leaves only a short hop between layers.
const MAX_BEND = 40;

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
function layoutGroup(group) {
    // A world goes in the first column it could, right after the last of the worlds it follows: its
    // column says how far into the game it comes.  dagre's own choice of columns would rather keep
    // lines short, and puts a world that nothing much follows as far right as it can go, next to
    // whatever does follow it.  Its "longest-path" ranking does the opposite of what's wanted here,
    // putting each thing as late as it can go; so it is given the lines reversed, and lays them out
    // right to left, which comes to the same thing as putting each world as early as it can go,
    // left to right.
    const g = new dagre.graphlib.Graph({ multigraph: true });
    g.setGraph({ rankdir: 'RL', ranker: 'longest-path', nodesep: NODE_SEP, ranksep: RANK_SEP,
                 marginx: MARGIN, marginy: MARGIN });
    g.setDefaultEdgeLabel(() => ({}));
    const key = (id) => 'w' + id;
    const ids = new Set(group.map((w) => String(w.id)));
    group.forEach((w) => g.setNode(key(w.id), { width: NODE_WIDTH, height: NODE_HEIGHT }));

    // Gather the worlds waiting on each set of worlds, in the order they come.
    const sets = new Map();
    group.forEach(function (w) {
        const previous = w.previous.filter((p) => ids.has(String(p)));
        if(previous.length === 0) { return; }
        const k = previous.map(String).sort().join('\u0000');
        if(!sets.has(k)) { sets.set(k, { sources: previous, targets: [] }); }
        sets.get(k).targets.push(w.id);
    });

    // A junction sits in a layer of its own between the worlds it joins.  A line straight from one
    // world to another asks for two layers' length, so that every world lands in an even layer and
    // the columns of worlds stay evenly spaced, junctions or none.
    const junctions = [];
    const wanted = [];
    sets.forEach(function (set) {
        if(set.sources.length >= 2 && set.targets.length >= 2) {
            const j = junctions.length;
            junctions.push({ sources: set.sources, targets: set.targets });
            g.setNode('j' + j, { width: 2 * JUNCTION_RADIUS, height: 2 * JUNCTION_RADIUS });
            set.sources.forEach((s) => wanted.push({ source: { world: s }, target: { junction: j }, minlen: 1 }));
            set.targets.forEach((t) => wanted.push({ source: { junction: j }, target: { world: t }, minlen: 1 }));
        } else {
            set.sources.forEach(function (s) {
                set.targets.forEach((t) => wanted.push({ source: { world: s }, target: { world: t }, minlen: 2 }));
            });
        }
    });
    const nodeKey = (end) => end.junction === undefined ? key(end.world) : 'j' + end.junction;
    wanted.forEach((e, i) => g.setEdge(nodeKey(e.target), nodeKey(e.source), { minlen: e.minlen }, String(i)));

    dagre.layout(g);

    const nodes = new Map();
    group.forEach(function (w) {
        const n = g.node(key(w.id));
        nodes.set(w.id, { x: n.x - NODE_WIDTH / 2, y: n.y - NODE_HEIGHT / 2 });
    });
    junctions.forEach(function (j, i) {
        const n = g.node('j' + i);
        j.x = n.x;
        j.y = n.y;
    });
    const edges = wanted.map(function (e, i) {
        const from = g.node(nodeKey(e.source));
        const to = g.node(nodeKey(e.target));
        // dagre's own ends are where the line meets the box's outline, which may be its top or
        // bottom; lines here leave from the right and arrive at the left.
        const start = e.source.junction === undefined ? { x: from.x + NODE_WIDTH / 2, y: from.y } : { x: from.x, y: from.y };
        const end = e.target.junction === undefined ? { x: to.x - NODE_WIDTH / 2, y: to.y } : { x: to.x, y: to.y };
        const points = g.edge(nodeKey(e.target), nodeKey(e.source), String(i)).points.slice(1, -1).reverse();
        return { source: e.source, target: e.target, points: [start].concat(points, [end]) };
    });
    const graph = g.graph();
    return { width: graph.width, height: graph.height, nodes: nodes, junctions: junctions, edges: edges };
}

// An SVG path through a line's points, running level between them and bending smoothly from one
// height to the next.  dagre routes a line through a point in every layer it crosses, most of them
// at the height of the one before, and changes height in the short hop between two layers; so the
// path is built from those level stretches, each change of height being drawn as a curve that
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
