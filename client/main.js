import { ready, newInstance, DotEndpoint, StraightConnector, FlowchartConnector, BezierConnector, EVENT_CONNECTION, EVENT_CONNECTION_MOUSEOVER, EVENT_CONNECTION_MOUSEOUT, EVENT_DRAG_START, EVENT_DRAG_MOVE, EVENT_DRAG_STOP } from "@jsplumb/browser-ui"
import { LEVELS, saveable, legacySaveables } from "./levels.js"
import { SERVER } from "./config.js"

const DIFFICULTIES = ['Novice', 'Adept', 'Master'];

// COLOR[difficulty][darkness] gives a color and backgroundColor, where difficulty is 0=novice, 1=adept, 2=master, and darkness is 0=light, 1=dark.
const COLORS = [
    [ { color: "", backgroundColor: "#ddffdd" }, { color: "", backgroundColor: "#00cc00" } ], // novice: black on green
    [ { color: "", backgroundColor: "#bbddff" }, { color: "", backgroundColor: "#6688ff" } ], // adept:  black on blue
    [ { color: "", backgroundColor: "#ffe0ff" }, { color: "", backgroundColor: "#b420f3" } ], // master: black on purple
];

const CHECKBOXES = [ "□" , "■" ]

// { color: "", backgroundColor: "#ff9900", lightColor: "#ffeecc" }, // black on orange
// { color: "#ffffff", backgroundColor: "#333333", lightColor: "#999999" }, // white on black

document.documentElement.style.setProperty('--novice-color', COLORS[0][1].color);
document.documentElement.style.setProperty('--adept-color', COLORS[1][1].color);
document.documentElement.style.setProperty('--master-color', COLORS[2][1].color);
document.documentElement.style.setProperty('--novice-bg', COLORS[0][1].backgroundColor);
document.documentElement.style.setProperty('--adept-bg', COLORS[1][1].backgroundColor);
document.documentElement.style.setProperty('--master-bg', COLORS[2][1].backgroundColor);

const VALUECOLOR = "#0000ff";
// Where along a wire the X that deletes it sits, before spreadWireLabels moves it off any label.
const CLOSE_BUTTON_HOME = 0.8;

// Unicode characters to put in the button palette below text boxes
const PALETTE = ['∧', '∨', '⇒', '⇔', '¬', '⊤', '⊥', '∀', '∃', '∈', '≠', '≤', '≥', '∼', '∣', '√', 'ℕ', 'ℤ', 'ℚ', 'ℝ', 'ℝ₊', 'ℂ', '𝕊', 'ε', 'δ'];

// An expression is arithmetic, not logic, so its box gets its own shorter row: no connectives, no
// quantifiers, no number systems, just the symbols an expression is written out of that a keyboard
// hasn't got a key for.
const EXPR_PALETTE = ['−', '·', '∣', '√', '²', '³', '⁴', 'ε', 'δ'];

// For some unfathomable reason this is not built into JavaScript
function escapeRegex(string) {
    return string.replace(/[/\-\\^$*+?.()|[\]{}]/g, '\\$&');
}

function escapeHtml(str) {
    return str.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;').replaceAll("'", '&#039;');
}

// Shortcut key sequences for unicode characters, many TeX-inspired
const KEYS = [
    { unicode: '∧',  keys: [ '\\land ', '\\wedge ', '/\\' ] },
    { unicode: '∨',  keys: [ '\\lor ', '\\vee ', '\\/' ] },
    { unicode: '⇔', keys: [ '\\Leftrightarrow ', '\\iff ', '<=>' ] }, // has to come first, so <=> doesn't become <⇒
    { unicode: '⇒', keys: [ '\\Rightarrow ', '=>' ] },
    { unicode: '¬', keys: [ '\\neg ' ] },
    { unicode: '⊤', keys: [ '\\top ' ] },
    { unicode: '⊥', keys: [ '\\bot ' ] },
    { unicode: '∃', keys: [ '\\exists ', '\\ex ' ] },
    { unicode: '∀', keys: [ '\\forall ', '\\all ' ] },
    { unicode: '∈', keys: [ '\\in ' ] },
    // Has to come first, so |-> doesn't become |→.  ∣−> is what typing |-> leaves behind, the
    // bar having become ∣ and the hyphen − on the way past.
    { unicode: '↦', keys: [ '\\mapsto ', '|->', '∣->', '∣−>' ] },
    { unicode: '→', keys: [ '\\to ', '\\rightarrow ', '->' ] },
    { unicode: '×', keys: [ '\\times ', '\\x ', '><' ] },
    { unicode: '⊔', keys: [ '\\sqcup ' ] },
    { unicode: '∣', keys: [ '|', '\\mid ', '\\abs ', '\\divides ' ] },
    { unicode: '√', keys: [ '\\sqrt ', '\\surd ' ] },
    { unicode: '−', keys: [ '-' ] },
    { unicode: '≠', keys: [ '\\neq' ] },
    { unicode: '≤', keys: [ '\\le' ] },
    { unicode: '≥', keys: [ '\\ge' ] },
    { unicode: '∼', keys: [ '\\sim', '~' ] },
    { unicode: 'ℕ', keys: [ '\\N ' ] },
    { unicode: 'ℤ', keys: [ '\\Z ' ] },
    { unicode: 'ℚ', keys: [ '\\Q ' ] },
    // ℝ₊ has to come first, so \R+ isn't read as \R followed by a stray +.
    { unicode: 'ℝ₊', keys: [ '\\R+ ', '\\Rpos ' ] },
    { unicode: 'ℝ', keys: [ '\\R ' ] },
    { unicode: 'ℂ', keys: [ '\\C ' ] },
    { unicode: '𝕊', keys: [ '\\S ' ] },
    { unicode: 'ε', keys: [ '\\eps ', '\\epsilon ' ] },
    { unicode: 'δ', keys: [ '\\delta ' ] },
    // ··2 is what typing **2 leaves behind, each * having already become a ·
    { unicode: '²', keys: [ '^2', '**2', '··2' ] },
    { unicode: '³', keys: [ '^3', '**3', '··3' ] },
    { unicode: '⁴', keys: [ '^4', '**4', '··4' ] },
    { unicode: '·', keys: [ '*' ] }, // has to come last, so ** in a power is read before either * becomes ·
].map(function (entry) {
    entry.regexes = entry.keys.map(function (str) { return new RegExp(escapeRegex(str), 'g'); });
    return entry
});

// Allow the expert user to supply a "rules=andE,asc" query string to get extra rules available
const urlParams = new URLSearchParams(window.location.search);
// In test mode ("?test") we skip unlock enforcement so the suite can select any level.
const TEST_MODE = urlParams.has('test');
const ruleParam = urlParams.get('rules');
var extraRules = [];
if(ruleParam) {
    extraRules = ruleParam.split(",");
}

// All nodes currently in the diagram, including variables, hypotheses, and conclusion, as {id, name, rule, value, node} objects.  The 'rule' is a string denoting the kind of node it is, while the 'value' (which could be undefined) stores a type or value.  The 'name' is a variable name, for variable nodes.
var nodes = [];

// All variables currently in use anywhere, including free ambient (parameters and variables) and local bound.  We insist on the Barendregt convention for all variables.
var varnames = [];

// Conclusion node ID
var conclusion_node = null;

// Autonumber counters for IDs
var counter = 0;
var paramCounter = 0;
var varCounter = 0;
var hypCounter = 0;
var conclCounter = 0;

// jsPlumb instance
var instance;

// Whether the proof engine's one-time global initialization (Narya.init) has run yet.
var naryaInited = false;

// connections to close buttons
var connectionCloseButtons = {};

// difficulty setting
var difficulty = 0;

// current hint, if any
var currentHint;

// Dynamic variable to suppress re-typechecking during batch modifications of the diagram
var suppressChecking = false;

// Whether a round of typechecking is in flight, and whether the diagram has changed since it
// started.  A round that asks Z3 something suspends inside Narya while the answer travels out
// through a promise and back through Narya.reenter, and there is no way to start another round
// meanwhile: the proof engine runs as a coroutine (Pauseable in narya's top.ml) whose continuation
// is only refreshed when a round *finishes*, so a round left suspended leaves that continuation
// spent, and the next call into Narya dies with "Continuation_already_resumed" -- with the
// "Typechecking..." overlay still up and the proof stuck until the page is reloaded.  So a change
// arriving mid-round is noted here and checked once the round it interrupted has landed.
var typecheckPending = false;
var typecheckAgain = false;

// Dynamic variable set while restoring a saved proof, to suppress the wire-label prompt and typechecking that normally fire when a connection is created.
var restoring = false;

// Dynamic variable to suppress autosaving while a level is being set up (so the initial empty proof doesn't clobber a saved one).
var suppressSave = false;

// The world/level select panes and buttons
var worldPanes = [];
var currentWorld = 0;
const levelButtons = [];
var allLevels = [];
var currentLevel;
var currentLevelButton;
// The definition (parameters/variables/hypotheses/conclusion) of whatever level is currently
// loaded, built-in or custom, so the "Edit" button can re-open the custom dialog pre-filled.
var currentLevelDef = null;
// The block budget ("maxrules") of the level currently loaded, or null for a level that sets none.
// Set by setLevel once it knows the new level is good, so a statement Narya rejects leaves the
// level we stay on -- and its budget -- alone.
var currentMaxRules = null;
// The saved custom level currently open (an entry of the localStorage "customLevels" list), or null
// when on a built-in level or an unsaved custom one.  Used so custom levels track completion and
// save proofs like built-in ones.
var currentCustom = null;
// References to the dynamically-built "Custom" world pane, populated by refreshCustomWorld.
var customRowsContainer = null;
var customChipEl = null;

// A counter (in localStorage "time") incremented on each level completion; per-difficulty
// completion times are recorded against it so a higher difficulty can be re-locked for a while
// after its lower difficulty was just completed.
var globalTime = 0;
// Whether the current (complete) proof has already been registered as a completion, so re-running
// typecheck on an already-complete proof doesn't count as a fresh completion.
var proofRegisteredComplete = false;
// When registering the next completion, stamp it at the current global time WITHOUT advancing the
// counter.  Used by the downgrade-restore path so re-loading a saved proof re-locks the higher
// difficulty but doesn't "use up" a completion slot (several levels may share a most-recent time).
var registerWithoutAdvancingTime = false;

// Per-world / per-stage completion data driving the unlock rule (see computeUnlockData).
var unlockData = [];

// Exclude these rules from "all"
const excludeFromAll = [ "negI" ] // Classical negation suffices

// The rules of the blocks a level starts with, laid out by setLevel rather than added by the
// player: everything else in `nodes` is a block the player put there.
const FIXED_RULES = [ 'variable', 'hypothesis', 'conclusion' ];

const diagram = document.getElementById('diagram');
// #diagram is a fixed viewport; #canvas is the scrollable surface that actually holds the nodes,
// so nodes dragged far out stay reachable by scrolling instead of vanishing off the window edge.
// Between them they make an unbounded canvas: the surface grows to the right and down as boxes go
// that way, and past the top/left edge -- where the browser has no scroll room to offer -- the
// whole diagram slides the other way instead (shiftWorld), which looks the same on screen.
const canvas = document.getElementById('canvas');

// Empty space to keep beyond the outermost box, so there's always somewhere to drop the next one.
const CANVAS_MARGIN = 60;

// Size #canvas so it covers every node (plus a margin) and whatever region is scrolled into view,
// or shrink it back to fill the viewport when everything fits.  This is what makes far-out nodes
// reachable via the scrollbars.  The scroll ends up at (scrollX, scrollY), by default where it
// already was: resizing the surface can clamp the scroll, so it has to be restored afterwards.
function resizeCanvas(scrollX, scrollY) {
    if(scrollX === undefined) { scrollX = diagram.scrollLeft; }
    if(scrollY === undefined) { scrollY = diagram.scrollTop; }
    let maxRight = 0, maxBottom = 0;
    nodes.forEach((x) => {
        const el = x.node;
        maxRight = Math.max(maxRight, el.offsetLeft + el.offsetWidth);
        maxBottom = Math.max(maxBottom, el.offsetTop + el.offsetHeight);
    });
    // Clear first so diagram.clientWidth/Height report the true viewport (minus any needed scrollbar).
    canvas.style.width = '';
    canvas.style.height = '';
    // Only grow once something actually extends past the viewport edge (so the conclusion sitting
    // near the right edge doesn't itself trigger a scrollbar); the margin is just breathing room
    // beyond.  Panning can also leave the viewport out past every box, and the surface has to keep
    // covering it or the browser would scroll the view back.
    const width  = Math.max(maxRight  > diagram.clientWidth  ? maxRight  + CANVAS_MARGIN : 0,
                            scrollX + diagram.clientWidth);
    const height = Math.max(maxBottom > diagram.clientHeight ? maxBottom + CANVAS_MARGIN : 0,
                            scrollY + diagram.clientHeight);
    if(width  > diagram.clientWidth)  { canvas.style.width  = width  + 'px'; }
    if(height > diagram.clientHeight) { canvas.style.height = height + 'px'; }
    diagram.scrollLeft = scrollX;
    diagram.scrollTop = scrollY;
}

// Slide the whole diagram by (dx, dy) across the canvas, leaving out any boxes in `frozen` -- the
// ones a drag is holding under the pointer, which have to stay where the pointer put them.  Returns
// whether anything moved.
function shiftWorld(dx, dy, frozen) {
    if(!dx && !dy) { return false; }
    var moved = false;
    nodes.forEach((x) => {
        const el = x.node;
        if(frozen && frozen.has(el)) { return; }
        const left = el.offsetLeft + dx, top = el.offsetTop + dy;
        el.style.left = left + 'px';
        el.style.top = top + 'px';
        // Tell jsPlumb where the box went, so its wires follow.  (setElementPosition only updates
        // jsPlumb's own picture of the diagram and repaints; moving the box is up to us.)
        instance.setElementPosition(el, left, top);
        moved = true;
    });
    return moved;
}

// Panning (and dragging a box past an edge) can leave boxes at negative coordinates, where there's
// no scroll room to reach them.  Slide the whole diagram back into positive territory and scroll by
// the same amount: nothing moves on screen, but everything is now reachable with the scrollbars.
function normalizeOrigin() {
    let minLeft = 0, minTop = 0;
    nodes.forEach((x) => {
        minLeft = Math.min(minLeft, x.node.offsetLeft);
        minTop  = Math.min(minTop,  x.node.offsetTop);
    });
    const dx = -minLeft, dy = -minTop;
    if(!dx && !dy) { return false; }
    shiftWorld(dx, dy, null);
    // The surface has to be big enough for the scroll we're about to ask for, so size it first.
    resizeCanvas(diagram.scrollLeft + dx, diagram.scrollTop + dy);
    return true;
}

// Move the viewport by (dx, dy) across the diagram: a positive dx brings into view what lies off to
// the right.  `frozen`, when given, is the set of boxes a drag is holding under the pointer: they
// mustn't move on screen, so the pan moves the rest of the world the other way instead of
// scrolling (jsPlumb positions a dragged box from the pointer alone, and scrolling the view under
// it would leave it behind).  Returns whether any box moved, i.e. whether positions need saving.
function panView(dx, dy, frozen) {
    if(frozen) { return shiftWorld(-dx, -dy, frozen); }
    // Scrolling right/down needs surface to scroll onto; grow it as we go.
    if(dx > 0) { canvas.style.width  = Math.max(canvas.offsetWidth,  diagram.scrollLeft + diagram.clientWidth  + dx) + 'px'; }
    if(dy > 0) { canvas.style.height = Math.max(canvas.offsetHeight, diagram.scrollTop  + diagram.clientHeight + dy) + 'px'; }
    const wantX = diagram.scrollLeft + dx, wantY = diagram.scrollTop + dy;
    diagram.scrollLeft = wantX;
    diagram.scrollTop = wantY;
    // Whatever the scroll couldn't do is off the top/left, where it has no room: move the world.
    return shiftWorld(diagram.scrollLeft - wantX, diagram.scrollTop - wantY, null);
}

// How close to a viewport edge the pointer has to come before a drag starts panning, how fast that
// pans at the very edge, and the fastest it pans however far outside the window the pointer goes.
const PAN_BAND = 40;
const PAN_EDGE_SPEED = 10;
const PAN_MAX_SPEED = 24;

// How fast to pan along one axis with the pointer at `p`, given a viewport spanning [lo, hi]:
// nothing until the pointer comes within PAN_BAND of an edge, then faster the further past it goes.
function edgeSpeed(p, lo, hi) {
    const over = p > hi - PAN_BAND ? p - (hi - PAN_BAND) : (p < lo + PAN_BAND ? p - (lo + PAN_BAND) : 0);
    const speed = over * PAN_EDGE_SPEED / PAN_BAND;
    return Math.max(-PAN_MAX_SPEED, Math.min(PAN_MAX_SPEED, speed));
}

function pointerXY(e) {
    const t = e.touches && e.touches.length ? e.touches[0] : e;
    return { x: t.clientX, y: t.clientY };
}

// Scroll the view, as little as it takes, to show the given boxes -- for after a drag whose pointer
// wandered off the window, carrying its box out of sight with it.  Sizes the canvas to match, so
// this is also the resizeCanvas every settled change to the diagram needs.
function scrollToShow(els) {
    let left = Infinity, top = Infinity, right = -Infinity, bottom = -Infinity;
    els.forEach((el) => {
        left   = Math.min(left,   el.offsetLeft);
        top    = Math.min(top,    el.offsetTop);
        right  = Math.max(right,  el.offsetLeft + el.offsetWidth);
        bottom = Math.max(bottom, el.offsetTop + el.offsetHeight);
    });
    if(left === Infinity) { resizeCanvas(); return; }
    let x = diagram.scrollLeft, y = diagram.scrollTop;
    // Chase the far edge first and the near edge second, so a box too big for the viewport still
    // ends up with its top left corner showing.  PAD is so it doesn't end up flush against the edge.
    const PAD = 8;
    if(right  + PAD > x + diagram.clientWidth)  { x = right  + PAD - diagram.clientWidth; }
    if(bottom + PAD > y + diagram.clientHeight) { y = bottom + PAD - diagram.clientHeight; }
    if(left - PAD < x) { x = left - PAD; }
    if(top  - PAD < y) { y = top  - PAD; }
    resizeCanvas(Math.max(0, x), Math.max(0, y));
}

// Look at wherever the proof is.  A proof the player laid out by panning off the top or left of
// where the level started is saved with the coordinates that gave it, so opening it with the view
// back at the origin could show nothing but empty canvas.
function scrollToContent() {
    let minLeft = Infinity, minTop = Infinity;
    nodes.forEach((x) => {
        minLeft = Math.min(minLeft, x.node.offsetLeft);
        minTop  = Math.min(minTop,  x.node.offsetTop);
    });
    if(minLeft === Infinity) { resizeCanvas(); return; }
    resizeCanvas(Math.max(0, minLeft - CANVAS_MARGIN), Math.max(0, minTop - CANVAS_MARGIN));
}

// The box drag in progress, if any: which boxes the pointer is carrying (jsPlumb moves the whole
// drag selection, and tells us which elements those are as it moves them), where the pointer was
// last seen, and the animation frame panning the canvas while it sits against an edge.
var dragPan = null;

function dragPanFrame() {
    // Wait for the first move: until jsPlumb has told us which boxes it is carrying, panning would
    // slide the dragged ones out from under the pointer along with everything else.
    if(dragPan.boxes.size > 0) {
        const r = diagram.getBoundingClientRect();
        panView(edgeSpeed(dragPan.pointer.x, r.left, r.right),
                edgeSpeed(dragPan.pointer.y, r.top, r.bottom),
                dragPan.boxes);
    }
    dragPan.frame = requestAnimationFrame(dragPanFrame);
}

function startDragPan(e) {
    dragPan = { boxes: new Set(), pointer: pointerXY(e), frame: 0 };
    dragPan.frame = requestAnimationFrame(dragPanFrame);
}

function stopDragPan() {
    if(dragPan) { cancelAnimationFrame(dragPan.frame); }
    dragPan = null;
}

// Ctrl/Cmd-dragging (or middle-dragging) the blank background pans the whole diagram behind the
// viewport, for moving around a proof spread out beyond the window without using the scrollbars.
var bgPan = null;

function isPanGesture(e) { return e.button === 1 || (e.button === 0 && (e.ctrlKey || e.metaKey)); }

diagram.addEventListener('mousedown', function(e) {
    // Only from the blank background: over a box, the mouse is doing something else.
    if(e.target !== canvas || !isPanGesture(e)) { return; }
    e.preventDefault();
    bgPan = { x: e.clientX, y: e.clientY, moved: false };
    diagram.classList.add('panning');
});

document.addEventListener('mousemove', function(e) {
    if(!bgPan) { return; }
    // The canvas follows the hand, so the viewport goes the opposite way.
    if(panView(bgPan.x - e.clientX, bgPan.y - e.clientY, null)) { bgPan.moved = true; }
    bgPan.x = e.clientX;
    bgPan.y = e.clientY;
});

document.addEventListener('mouseup', function() {
    if(!bgPan) { return; }
    const moved = bgPan.moved;
    bgPan = null;
    diagram.classList.remove('panning');
    // Panning past the top/left leaves boxes at negative coordinates; put the origin back (which
    // resizes the canvas itself), and otherwise trim the surface to what we ended up needing.
    const shifted = normalizeOrigin();
    if(!shifted) { resizeCanvas(); }
    if(moved || shifted) { autosave(); }
});

// Scrolling changes no part of the proof, but it does change where the player is looking, which a
// saved proof remembers so that resuming it looks at what they left.  So save that too, once the
// scrolling settles.
var scrollSaveTimer = null;
var scrollSaveKey = null;
diagram.addEventListener('scroll', function () {
    const key = savedProofKey();
    // Only over a proof that is already saved: merely looking around a level shouldn't start
    // saving one.
    if(suppressSave || !key || !localStorage.getItem(key)) { return; }
    clearTimeout(scrollSaveTimer);
    scrollSaveKey = key;
    scrollSaveTimer = setTimeout(flushScrollSave, 400);
});

// Write out the view we've scrolled to.  Called when the scrolling settles, and by anything that
// would otherwise lose a pending one: opening another level, or leaving the page.
function flushScrollSave() {
    if(scrollSaveTimer === null) { return; }
    clearTimeout(scrollSaveTimer);
    scrollSaveTimer = null;
    // Not if we've moved on since, and not from a diagram with no proof on it: opening a level
    // scrolls the view back to the origin, and the empty level set up behind the "load saved
    // proof?" prompt must not save itself over the very proof that prompt is offering.
    if(savedProofKey() === scrollSaveKey && proofHasProgress(serializeProof())) { autosave(); }
}
window.addEventListener('pagehide', flushScrollSave);

// On a Mac, Ctrl-clicking is also the way to open a context menu; suppress it while panning.
diagram.addEventListener('contextmenu', function(e) { if(bgPan) { e.preventDefault(); } });

// Offer the "grab" cursor while the pan modifier is held, so the gesture is discoverable.
function updatePanCursor(e) { diagram.classList.toggle('panready', e.ctrlKey || e.metaKey); }
document.addEventListener('keydown', updatePanCursor);
document.addEventListener('keyup', updatePanCursor);
window.addEventListener('blur', function() { diagram.classList.remove('panready'); });

// Keep the canvas filling the window as it's resized.
window.addEventListener('resize', function() { resizeCanvas(); });

// Initialize Z3
const { init } = require('z3-solver');
var Solver;
var Real;
var If;
init().then((z3) => {
    const ctx = new z3.Context('main');
    Solver = ctx.Solver;
    Real = ctx.Real;
    If = ctx.If;
});

ready(() => {
    instance = newInstance({
        container: canvas,
        endpoint: {
            type: DotEndpoint.type,
            options: {
                radius: 7,
            },
        },
        connector: FlowchartConnector.type,
        paintStyle: { stroke: "#000000", strokeWidth: 2 },
        endpointStyle: { fill: "#000000" },
        reattachConnections: true,
        connectionOverlays: [
            {
                type: "Arrow",
                options: {
                    location: -5,
                    width: 10,
                    length: 10,
                },
            },
            {
                type: "Custom",
                options: {
                    id: "closeButton",
                    location: CLOSE_BUTTON_HOME,
                    create:(conn) => {
                        const closebutton = document.createElement("div");
                        closebutton.className = "closebutton";
                        closebutton.innerText = "X";
                        closebutton.addEventListener('click', function () {
                            instance.deleteConnection(conn);
                            typecheck();
                        });
                        connectionCloseButtons[conn.id] = { button: closebutton };
                        return closebutton;
                    },
                },
            }
        ]
    });

    // Make close buttons on connections appear on hover, and stay for a second
    instance.bind(EVENT_CONNECTION_MOUSEOVER, (conn, e) => {
        showWireTooltip(conn, e);
        if(connectionCloseButtons[conn.id]) {
            connectionCloseButtons[conn.id].button.style.visibility = 'visible';
            if(connectionCloseButtons[conn.id].timeout) {
                clearTimeout(connectionCloseButtons[conn.id].timeout);
                connectionCloseButtons[conn.id].timeout = undefined;
            }
        }
    });
    instance.bind(EVENT_CONNECTION_MOUSEOUT, (conn) => {
        hideWireTooltip();
        if(connectionCloseButtons[conn.id]) {
            if(connectionCloseButtons[conn.id].timeout) {
                clearTimeout(connectionCloseButtons[conn.id].timeout);
            }
            connectionCloseButtons[conn.id].timeout = setTimeout(function () { connectionCloseButtons[conn.id].button.style.visibility = 'hidden'; }, 1000);
        }
    });

    // When a palette box is dropped on the diagram, we add a copy of it as a new node at the dropped location.
    diagram.addEventListener('drop', function (e) {
        e.preventDefault();
        const id = e.dataTransfer.getData('text/plain');
        const box = addRuleNode(id);
        // Position relative to the canvas, whose rect already folds in the current scroll offset.
        const canvasRect = canvas.getBoundingClientRect();
        box.style.left = `${e.clientX - canvasRect.left}px`;
        box.style.top = `${e.clientY - canvasRect.top}px`;
        resizeCanvas();

        // Add endpoints appropriately for its rule type, if necessary make it larger and resizable, and prompt for variables or ascription types.  Some rules display a modal box, in which case we don't typecheck until it is submitted.
        if (addEndpointsForRule(box, id, false)) {
            typecheck();
        }
    });


    // Whenever the graph changes, we recompute it and pass to Narya to typecheck it.
    // This includes when a new connection is created:
    instance.bind(EVENT_CONNECTION, addConnection);
    // It seems that EVENT_CONNECTION also fires after a connection is moved, so no need to separately bind EVENT_CONNECTION_MOVED.
    // We've forbidden connections from being detached by dropping, since it appears to be kind of broken, e.g. EVENT_CONNECTION_DETACHED fires *before* it's detached.  Instead the user removes connections with the close button.

    // Dragging a box against a window edge pans the canvas that way, so it can be carried off as
    // far as the player likes.  jsPlumb moves the whole drag selection but only announces the drag
    // once, so we collect the boxes it's carrying from the moves themselves, and take the pointer
    // from them too: it stays put while the canvas pans out from under it.
    instance.bind(EVENT_DRAG_START, function (p) { startDragPan(p.e); });
    instance.bind(EVENT_DRAG_MOVE, function (p) {
        if(dragPan) {
            dragPan.boxes.add(p.el);
            dragPan.pointer = pointerXY(p.e);
        }
    });

    // Dragging a node to rearrange the proof changes positions without re-typechecking, so save
    // the new positions when a drag finishes.
    instance.bind(EVENT_DRAG_STOP, function () {
        const dropped = dragPan ? dragPan.boxes : new Set();
        stopDragPan();
        // A box dragged off the top/left is sitting at negative coordinates; put the origin back.
        normalizeOrigin();
        scrollToShow(dropped);
        // Dragging a box moves its wires, which can push labels onto each other.
        spreadWireLabels();
        autosave();
    });

    if(SERVER) {
        // If they have a saved login, use it.
        const email = localStorage.getItem("email");
        const course = localStorage.getItem("course");
        if(email && course) {
            login(email, course);
        } else {
            // Otherwise, prompt them to login.
            document.getElementById("loginBG").style.display = "flex";
        }
    } else {
        // We can make the level-select boxes right away using localStorage, and start the user out by having them select a level.
        migrateLegacyRecords(null);
        makeLevelSelect(null);
        levelChooseBG.style.display = "flex";
        // But if they haven't been here before, we show them the intro page first.
        if(!localStorage.getItem("visited")) {
            document.getElementById("aboutBG").style.display = "flex";
            localStorage.setItem("visited",true);
        }
    }

    // Set a saved connector style if any
    const connectors = localStorage.getItem("connectors");
    if(connectors === 'angle') {
        instance.importDefaults({ connector: FlowchartConnector.type });
        document.getElementById("angleConnectors").checked = true;
        document.getElementById("curvedConnectors").checked = false;
    } else if (connectors === 'curved') {
        instance.importDefaults({ connector: BezierConnector.type });
        document.getElementById("angleConnectors").checked = false;
        document.getElementById("curvedConnectors").checked = true;
    }
});

// The quantifiers over a set that isn't a type of its own: ℝ₊, the positive reals, and [n], the
// whole numbers below n.  Each of their four blocks carries the condition defining that set --
// 0<x, or (0≤x)∧(x<n) -- on a port of its own alongside the value port for x, so the blocks of one
// such quantifier differ from those of another only in that port's label and in how the set is
// written in the placeholder types their ports show while empty.
const SPECIALQUANT = {
    allposI:   { condition: "positive", set: "ℝ₊" },
    allposE:   { condition: "positive", set: "ℝ₊" },
    exposI:    { condition: "positive", set: "ℝ₊" },
    exposE:    { condition: "positive", set: "ℝ₊" },
    allbelowI: { condition: "below", set: "[?]" },
    allbelowE: { condition: "below", set: "[?]" },
    exbelowI:  { condition: "below", set: "[?]" },
    exbelowE:  { condition: "below", set: "[?]" },
};

// Clone the palette rule `id` into a new diagram node: position it, register it in the
// nodes list, and give it a close button.  Endpoints are added separately by
// addEndpointsForRule.  Returns the new box element.
function addRuleNode(id) {
    const originalBox = document.getElementById(id);
    const box = originalBox.cloneNode(true);
    box.style.position = 'absolute';
    box.id = 'rule' + (counter++);
    canvas.appendChild(box);
    // Make it selectable for multi-element dragging.
    box.onmousedown = toggleDragSelected(box);
    // Add it to the master list of nodes.
    nodes.push({id: box.id, rule: box.dataset.rule, node: box});
    // Add a close button.  (Variable, hypothesis, and conclusion nodes aren't closeable.)
    addBoxCloseButton(box);
    // Count it right away: a box that opens a modal for its value (asc, expr, a bound variable)
    // doesn't typecheck until that is submitted, and the count shouldn't lag behind the diagram.
    updateBlockBanner();
    return box;
}

// Add the endpoints (and, for bracket rules, the resizable shape) appropriate to the
// palette rule `id` on the given box.  Returns whether the caller should typecheck right
// away: rules that pop a modal for a variable/ascription/expression return false and
// typecheck when the modal is submitted.  During a restore (`restore` true) those prompts
// are skipped, since the values come from the saved proof.
function addEndpointsForRule(box, id, restore) {
    var typecheck_now = true;
    if (id === 'andE') {
        instance.addEndpoint(box, { anchor: "Left", target: true, parameters: {sort: "input", primary: "?∧?"}} );
        instance.addEndpoint(box, { anchor: [1, 0.2, 1, 0], source: true, maxConnections: -1, parameters: {sort: "output", label: "fst", side: "upper"} });
        instance.addEndpoint(box, { anchor: [1, 0.8, 1, 0], source: true, maxConnections: -1, parameters: {sort: "output", label: "snd", side: "lower"} });
    } else if (id === 'andI') {
        instance.addEndpoint(box, { anchor: [0, 0.2, -1, 0], target: true, parameters: {sort: "input", label: "fst", side: "upper"} });
        instance.addEndpoint(box, { anchor: [0, 0.8, -1, 0], target: true, parameters: {sort: "input", label: "snd", side: "lower"} });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: { sort: "output", primary: "?∧?" } });
    } else if (id === 'impE' ) {
        instance.addEndpoint(box, { anchor: [0, 0.2, -1, 0], target: true, parameters: {sort: "input", label: "implication", side: "upper", primary: "?⇒?"} });
        instance.addEndpoint(box, { anchor: [0, 0.8, -1, 0], target: true, parameters: {sort: "input", label: "antecedent", side: "lower"} });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: { sort: "output" } });
    } else if (id === 'iffE1' || id === 'iffE2') {
        instance.addEndpoint(box, { anchor: [0, 0.2, -1, 0], target: true, parameters: {sort: "input", label: "implication", side: "upper", primary: "?⇔?"} });
        instance.addEndpoint(box, { anchor: [0, 0.8, -1, 0], target: true, parameters: {sort: "input", label: "antecedent", side: "lower"} });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: { sort: "output" } });
    } else if (id === 'orI1') {
        // Even though there is only one input, we give it a label, because *in general* a Constr can have more than one input, so Olorin OCaml expects all inputs of all Constrs to have labels.
        instance.addEndpoint(box, { anchor: "Left", target: true, parameters: { sort: "input", label: "left" } });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: { sort: "output", primary: "?∨?" } });
    } else if (id === 'orI2') {
        instance.addEndpoint(box, { anchor: "Left", target: true, parameters: { sort: "input", label: "right" } });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: { sort: "output", primary: "?∨?" } });
    } else if (id === 'impI' || id === 'allI' || id === 'allposI' || id === 'allbelowI' || id === 'negI' || id === 'cnegI' ) {
        // Every ∀ block binds a variable, so its assumption port carries a value.  The ones that
        // quantify over a special set bind the condition defining it too, on a second port below
        // that one, so their variable port sits higher up a taller box to leave room.
        const q = SPECIALQUANT[id];
        const binds = (id === 'allI' || !!q);
        const dy = (q ? -22 : -12);
        if(binds) {
            instance.addEndpoint(box, {
                anchor: [0, 0.5, 1, 0, 22, dy],
                source: true, maxConnections: -1,
                parameters: { sort: "assumption", hasValue: true, side: "upper" },
                paintStyle: { fill: VALUECOLOR },
                connectorStyle: { stroke: VALUECOLOR, strokeWidth: 2 },
            });
        } else {
            instance.addEndpoint(box, {
                anchor: [0, 0.5, 1, 0, 22, dy],
                source: true, maxConnections: -1,
                parameters: {sort: "assumption", side: "upper"},
            });
        }
        if(q) {
            instance.addEndpoint(box, {
                anchor: [0, 0.5, 1, 0, 22, 2],
                source: true, maxConnections: -1,
                parameters: {sort: "assumption", label: q.condition, side: "upper"},
            });
        }
        instance.addEndpoint(box, { anchor: [1, 0.5, -1, 0, -21, dy], target: true, parameters: {sort: "subgoal", side: "upper"} });
        const primary = (id === 'impI' ? "?⇒?" : (id === 'allI' ? "∀?∈?,?" : (q ? "∀?∈" + q.set + ",?" : (id === 'cnegI' ? "?" : "¬?"))));
        instance.addEndpoint(box, { anchor: [1, 0.5, 1, 0, 3], source: true, maxConnections: -1, parameters: {sort: "output", primary: primary} });
        box.style.width = '200px';
        box.style.height = (q ? '70px' : '50px');
        makeResizable(box);
        if(binds) {
            // Double-clicking the box re-opens the dialog to rename the variable it binds.
            box.addEventListener('dblclick', function () { editVariable(box); });
            if(!restore) { getVariable(box.id); }
            typecheck_now = false;
        }
    } else if (id === 'orE') {
        instance.addEndpoint(box, { anchor: "Left", target: true, parameters: {sort: "input", primary: "?∨?"} });
        instance.addEndpoint(box, { anchor: [0, 0.5, 1, 0, 22, -25], source: true, maxConnections: -1, parameters: {sort: "assumption", label: "left", side: "upper"} });
        instance.addEndpoint(box, { anchor: [1, 0.5, -1, 0, -21, -25], target: true, parameters: {sort: "subgoal", label: "left", side: "upper"} });
        instance.addEndpoint(box, { anchor: [0, 0.5, 1, 0, 22, 25], source: true, maxConnections: -1, parameters: {sort: "assumption", label: "right", side: "lower"} });
        instance.addEndpoint(box, { anchor: [1, 0.5, -1, 0, -21, 25], target: true, parameters: {sort: "subgoal", label: "right", side: "lower"} });
        instance.addEndpoint(box, { anchor: [1, 0.5, 1, 0, 3], source: true, maxConnections: -1, parameters: {sort: "output", primary: "?"} });
        box.style.width = '200px';
        box.style.height = '80px';
        makeResizable(box);
    } else if (id === 'iffI') {
        instance.addEndpoint(box, { anchor: [0, 0.5, 1, 0, 22, -25], source: true, maxConnections: -1, parameters: {sort: "assumption", label: "ltor", side: "upper"} });
        instance.addEndpoint(box, { anchor: [1, 0.5, -1, 0, -21, -25], target: true, parameters: {sort: "subgoal", label: "ltor", side: "upper"} });
        instance.addEndpoint(box, { anchor: [0, 0.5, 1, 0, 22, 25], source: true, maxConnections: -1, parameters: {sort: "assumption", label: "rtol", side: "lower"} });
        instance.addEndpoint(box, { anchor: [1, 0.5, -1, 0, -21, 25], target: true, parameters: {sort: "subgoal", label: "rtol", side: "lower"} });
        instance.addEndpoint(box, { anchor: [1, 0.5, 1, 0, 3], source: true, maxConnections: -1, parameters: {sort: "output", primary: "?⇔?"} });
        box.style.width = '200px';
        box.style.height = '80px';
        makeResizable(box);
    } else if (id === 'exE') {
        instance.addEndpoint(box, { anchor: "Left", target: true, parameters: {sort: "input", primary: "∃?∈?,?"} });
        instance.addEndpoint(box, {
            anchor: [1, 0.2, 1, 0],
            source: true, maxConnections: -1,
            parameters: { sort: "output", label: "element", hasValue: true, side: "upper"},
            paintStyle: { fill: VALUECOLOR },
            connectorStyle: { stroke: VALUECOLOR, strokeWidth: 2 }
        });
        instance.addEndpoint(box, { anchor: [1, 0.8, 1, 0], source: true, maxConnections: -1, parameters: {sort: "output", label: "property", side: "lower"} });
        // Double-clicking the box re-opens the dialog to rename the variable it binds.
        box.addEventListener('dblclick', function () { editVariable(box); });
        if(!restore) { getVariable(box.id); }
        typecheck_now = false;
    } else if (id === 'exI') {
        instance.addEndpoint(box, {
            anchor: [0, 0.2, -1, 0],
            target: true,
            parameters: {sort: "input", label: "element", hasValue: true, side: "upper"},
            paintStyle: { fill: VALUECOLOR },
        });
        instance.addEndpoint(box, { anchor: [0, 0.8, -1, 0], target: true, parameters: {sort: "input", label: "property", side: "lower"} });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output", primary: "∃?∈?,?"} });
    } else if (id === 'allE') {
        instance.addEndpoint(box, { anchor: [0, 0.2, -1, 0], target: true, parameters: {sort: "input", label: "universal", side: "upper", primary: "∀?∈?,?"} });
        instance.addEndpoint(box, {
            anchor: [0, 0.8, -1, 0],
            target: true,
            parameters: {sort: "input", label: "element", hasValue: true, side: "lower"},
            paintStyle: { fill: VALUECOLOR },
        });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output"} });
    } else if (id === 'exposE' || id === 'exbelowE') {
        const q = SPECIALQUANT[id];
        instance.addEndpoint(box, { anchor: "Left", target: true, parameters: {sort: "input", primary: "∃?∈" + q.set + ",?"} });
        instance.addEndpoint(box, {
            anchor: [1, 0.1, 1, 0],
            source: true, maxConnections: -1,
            parameters: { sort: "output", label: "element", hasValue: true, side: "upper"},
            paintStyle: { fill: VALUECOLOR },
            connectorStyle: { stroke: VALUECOLOR, strokeWidth: 2 }
        });
        instance.addEndpoint(box, { anchor: [1, 0.5, 1, 0], source: true, maxConnections: -1, parameters: {sort: "output", label: q.condition, side: "middle"} });
        instance.addEndpoint(box, { anchor: [1, 0.9, 1, 0], source: true, maxConnections: -1, parameters: {sort: "output", label: "property", side: "lower"} });
        // Double-clicking the box re-opens the dialog to rename the variable it binds.
        box.addEventListener('dblclick', function () { editVariable(box); });
        if(!restore) { getVariable(box.id); }
        typecheck_now = false;
    } else if (id === 'exposI' || id === 'exbelowI') {
        const q = SPECIALQUANT[id];
        instance.addEndpoint(box, {
            anchor: [0, 0.1, -1, 0],
            target: true,
            parameters: {sort: "input", label: "element", hasValue: true, side: "upper"},
            paintStyle: { fill: VALUECOLOR },
        });
        instance.addEndpoint(box, { anchor: [0, 0.5, -1, 0], target: true, parameters: {sort: "input", label: q.condition, side: "middle"} });
        instance.addEndpoint(box, { anchor: [0, 0.9, -1, 0], target: true, parameters: {sort: "input", label: "property", side: "lower"} });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output", primary: "∃?∈" + q.set + ",?"} });
    } else if (id === 'allposE' || id === 'allbelowE') {
        const q = SPECIALQUANT[id];
        instance.addEndpoint(box, { anchor: [0, 0.1, -1, 0], target: true, parameters: {sort: "input", label: "universal", side: "upper", primary: "∀?∈" + q.set + ",?"} });
        instance.addEndpoint(box, {
            anchor: [0, 0.5, -1, 0],
            target: true,
            parameters: {sort: "input", label: "element", hasValue: true, side: "middle"},
            paintStyle: { fill: VALUECOLOR },
        });
        instance.addEndpoint(box, { anchor: [0, 0.9, -1, 0], target: true, parameters: {sort: "input", label: q.condition, side: "lower"} });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output"} });
    } else if (id === 'negE') {
        instance.addEndpoint(box, { anchor: [0, 0.2, -1, 0], target: true, parameters: {sort: "input", label: "negation", side: "upper", primary: "¬?"} });
        instance.addEndpoint(box, { anchor: [0, 0.8, -1, 0], target: true, parameters: {sort: "input", label: "statement", side: "lower", primary : "?"} });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output", primary: "?"} });
    } else if (id === 'botE') {
        instance.addEndpoint(box, { anchor: "Left", target: true, parameters: {sort: "input", primary: "⊥"},  });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output", primary: "?"} });
    } else if (id === 'topI') {
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output", primary: "⊤"} });
    } else if (id === 'asc') {
        instance.addEndpoint(box, { anchor: "Left", target: true, parameters: {sort: "input"} });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output"} });
        // Double-clicking the box re-opens the dialog to edit the type it ascribes.
        box.addEventListener('dblclick', function () { editAscription(box); });
        if(!restore) {
            document.getElementById("ascribeBG").style.display = "flex";
            const ascribe = document.getElementById('ascribe');
            ascribe.dataset.name = box.id;
            ascribe.dataset.editing = "";
            ascribe.focus();
        }
        typecheck_now = false;
    } else if (id === 'alg' || id === 'algplus') {
        instance.addEndpoint(box, { anchor: "Left", target: true, maxConnections: -1, parameters: {sort: "input"} });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output"} });
    } else if (id === 'expr') {
        instance.addEndpoint(box, {
            anchor: "Left",
            target: true,
            maxConnections: -1,
            parameters: { sort: "input", hasValue: true },
            paintStyle: { fill: VALUECOLOR },
        });
        instance.addEndpoint(box, {
            anchor: "Right",
            source: true,
            maxConnections: -1,
            parameters: { sort: "output", hasValue: true },
            paintStyle: { fill: VALUECOLOR },
            connectorStyle: { stroke: VALUECOLOR, strokeWidth: 2 },
        });
        // Double-clicking the box re-opens the dialog to edit what it says.
        box.addEventListener('dblclick', function () { editExpr(box); });
        // Prompt for the expression
        if(!restore) {
            document.getElementById("expressionBG").style.display = "flex";
            const expr = document.getElementById('expression');
            expr.dataset.name = box.id;
            expr.dataset.editing = "";
            expr.focus();
        }
        typecheck_now = false;
    } else if (id === 'integral') {
        instance.addEndpoint(box, {
            anchor: [0, 0.1, -1, 0],
            target: true,
            // unknownSet: which number system x and y range over isn't settled while these ports
            // are empty.  The User rule in olorin.ml offers ℤ.integral, ℚ.integral, ℝ.integral and
            // 𝕊.integral as an SFirst, and with a hole here the typechecker just takes the first
            // that goes through -- ℤ when nothing is wired up, 𝕊 once something is -- so whatever
            // it reports for these ports is a guess, and not the set the player is working in.
            parameters: { sort: "input", label: "x", hasValue: true, side: "upper", unknownSet: true },
            paintStyle: { fill: VALUECOLOR },
        });
        instance.addEndpoint(box, {
            anchor: [0, 0.5, -1, 0],
            target: true,
            parameters: { sort: "input", label: "y", hasValue: true, side: "middle", unknownSet: true },
            paintStyle: { fill: VALUECOLOR },
        });
        instance.addEndpoint(box, {
            anchor: [0, 0.9, -1, 0],
            target: true,
            parameters: {sort: "input", label: "xy0", side: "lower"},
        });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output"} });
    } else if (id === 'deceq' || id === 'tord') {
        // Two numbers in, a disjunction about them out.  Which number system they range over is
        // as open as it is for integral above, hence unknownSet on the empty ports.
        instance.addEndpoint(box, {
            anchor: [0, 0.2, -1, 0],
            target: true,
            parameters: { sort: "input", label: "x", hasValue: true, side: "upper", unknownSet: true },
            paintStyle: { fill: VALUECOLOR },
        });
        instance.addEndpoint(box, {
            anchor: [0, 0.8, -1, 0],
            target: true,
            parameters: { sort: "input", label: "y", hasValue: true, side: "lower", unknownSet: true },
            paintStyle: { fill: VALUECOLOR },
        });
        instance.addEndpoint(box, { anchor: "Right", source: true, maxConnections: -1, parameters: {sort: "output"} });
    }
    return typecheck_now;
}

// Set connector style
document.getElementById("angleConnectors").onclick = function() {
    instance.importDefaults({ connector: FlowchartConnector.type });
    localStorage.setItem("connectors", "angle");
};
document.getElementById("curvedConnectors").onclick = function() {
    instance.importDefaults({ connector: BezierConnector.type });
    localStorage.setItem("connectors", "curved");
};

// Make palette boxes draggable
document.querySelectorAll('.rule').forEach(box => {
    box.draggable = true;
});

document.getElementById('palette').addEventListener('dragstart', function (e) {
    if (e.target.classList && e.target.classList.contains('rule')) {
        e.dataTransfer.setData('text/plain', e.target.id);
    }
});

diagram.addEventListener('dragover', function (e) {
    e.preventDefault();
});

// Dragging groups
function toggleDragSelected(box) { return function(e) {
    if(e.shiftKey) {
        if(instance.dragSelection._dragSelection.some((x) => x.id === box.id)) {
            instance.removeFromDragSelection(box);
        } else {
            instance.addToDragSelection(box);
        }
    } else if(! instance.dragSelection._dragSelection.some((x) => x.id === box.id)) {
        instance.clearDragSelection();
    }
}}

// Multi-drag select rectangle
let selectingStartX, selectingStartY, isSelecting, shiftSelecting = false;

// Start selection on mousedown anywhere in the document.
diagram.addEventListener('mousedown', function(e) {
    // Ctrl/Cmd- and middle-dragging the background pan it instead of selecting.
    if(e.target === canvas && !isPanGesture(e)) {
        isSelecting = true;
        if(e.shiftKey) {
            shiftSelecting = true;
        }
        shiftSelecting
        selectingStartX = e.pageX;
        selectingStartY = e.pageY;

        // Initialize and show the selection box.
        selectionBox.style.left = selectingStartX + 'px';
        selectionBox.style.top = selectingStartY + 'px';
        selectionBox.style.width = '0px';
        selectionBox.style.height = '0px';
        selectionBox.style.display = 'block';
    }
});

// Update the selection box as the mouse moves.
diagram.addEventListener('mousemove', function(e) {
    if (!isSelecting) return;

    let currentX = e.pageX;
    let currentY = e.pageY;

    // Calculate the top-left coordinates and dimensions.
    let rectLeft = Math.min(selectingStartX, currentX);
    let rectTop = Math.min(selectingStartY, currentY);
    let rectWidth = Math.abs(selectingStartX - currentX);
    let rectHeight = Math.abs(selectingStartY - currentY);

    selectionBox.style.left = rectLeft + 'px';
    selectionBox.style.top = rectTop + 'px';
    selectionBox.style.width = rectWidth + 'px';
    selectionBox.style.height = rectHeight + 'px';
});

// When the mouse is released, check which divs are fully inside the selection box.
diagram.addEventListener('mouseup', function(e) {
    if (!isSelecting) return;
    isSelecting = false;

    // Get the bounding rectangle of the selection.
    const selectionRect = selectionBox.getBoundingClientRect();

    // Loop through all nodes and test if they're fully inside the selection.
    var newSelected = [];
    nodes.forEach((x) => {
        const div = x.node;
        const divRect = div.getBoundingClientRect();
        // Check if the div is completely inside the selection rectangle.
        if(divRect.left >= selectionRect.left &&
           divRect.right <= selectionRect.right &&
           divRect.top >= selectionRect.top &&
           divRect.bottom <= selectionRect.bottom) {
            newSelected.push(div);
        }
    });

    if(shiftSelecting) {
        // If shift was held down when the drag started, toggle whether the new nodes are selected.
        newSelected.forEach(function (box) {
            if(instance.dragSelection._dragSelection.some((x) => x.id === box.id)) {
                instance.removeFromDragSelection(box);
            } else {
                instance.addToDragSelection(box);
            }
        });
    } else {
        // Otherwise, clear the selection and set it to the new nodes.
        instance.clearDragSelection();
        newSelected.forEach(function (box) {
            instance.addToDragSelection(box);
        });
    }

    shiftSelecting = false;
    // Finally, get rid of the selection Box.
    selectionBox.style.display = 'none';
});

// Delete or Backspace removes every selected box, as if each one's red X had been clicked.  Only
// boxes with a close button (rule boxes, not the fixed context nodes) are deletable.
document.addEventListener('keydown', function(e) {
    if(e.key !== 'Delete' && e.key !== 'Backspace') { return; }
    // Don't hijack the key while typing in a text field (custom-level / variable dialogs, etc.).
    const tag = (e.target.tagName || '').toLowerCase();
    if(tag === 'input' || tag === 'textarea' || e.target.isContentEditable) { return; }
    const selected = instance.dragSelection._dragSelection.slice();
    if(selected.length === 0) { return; }
    e.preventDefault();
    selected.forEach(function(sel) {
        const el = document.getElementById(sel.id);
        if(el && el.querySelector('.closebutton')) { deleteRule(el); }
    });
    instance.clearDragSelection();
});

// In SERVER mode, there is a login box
function submitLogin() {
    login(document.getElementById('loginEmail').value, document.getElementById('loginCourse').value);
}
document.getElementById('submitLogin').onclick = submitLogin;
document.getElementById('loginEmail').onkeypress = function(event) {
    if(event.key == 'Enter') {
        submitLogin();
    }
}
document.getElementById('loginCourse').onkeypress = function(event) {
    if(event.key == 'Enter') {
        submitLogin();
    }
}

function login(email, course) {
    const xhr = new XMLHttpRequest();
    xhr.open('POST', '/login', true);
    xhr.setRequestHeader('Content-Type', 'application/json;charset=UTF-8');
    let loginError = document.getElementById('loginError');
    xhr.onload = function() {
        if (xhr.status === 200) {
            let res = JSON.parse(xhr.responseText);
            if(res.error) {
                loginError.textContent = "Error: " + res.error;
                loginError.style.color = "#ff0000";
                loginError.style.visibility = 'visible';
            } else {
                // Login successful
                localStorage.setItem("email", email);
                localStorage.setItem("course", course);
                // Reset and hide the login box
                document.getElementById('loginEmail').value = '';
                document.getElementById('loginCourse').value = '';
                loginError.style.visibility = 'hidden';
                document.getElementById("loginBG").style.display = "none";
                // The response includes the information about past levels, used to color the level select buttons.  If the level select buttons have already been created, we just re-color and re-star them; otherwise we do that while creating them.
                migrateLegacyRecords(res);
                if(levelButtons.length > 0) {
                    updateLevelSelect(res);
                } else {
                    makeLevelSelect(res);
                }
                // Restore the save difficulty and world
                if(res.difficulty) {
                    setDifficulty(res.difficulty);
                }
                if(res.world) {
                    setWorld(res.world);
                }
                // Display the level-selection dialog
                levelChooseBG.style.display = "flex";
                // If they haven't been here before, we show them the intro page.
                if(!res.visited) {
                    document.getElementById("aboutBG").style.display = "flex";
                }
                localStorage.setItem("visited",true);
            }
        } else {
            let res = JSON.parse(xhr.responseText);
            loginError.innerText = 'Error: ' + res.error;
            // Why is this color not getting used from the HTML style attribute?
            loginError.style.color = "#ff0000";
            loginError.style.visibility = 'visible';
        }
    };
    const data = { email: email, course: course };
    xhr.send(JSON.stringify(data));
};

// Add level select buttons to the dialog box.
// A short label for a world's index chip, e.g. "Quantifier world" -> "Quantifier".  A few names
// have an explicit short form; the rest just drop " world" and keep the first word.
const SHORT_WORLD_NAMES = {
    "Advanced proposition world": "Adv. Prop.",
    "Advanced quantifier world": "Adv. Quant.",
};
function shortWorldName(name) {
    if(SHORT_WORLD_NAMES[name]) { return SHORT_WORLD_NAMES[name]; }
    return name.replace(/ world$/i, '').split(' ')[0];
}

// Recompute and display the "done/total" count on a world's index chip.
function refreshWorldProgress(worldPaneIndex) {
    const entry = worldPanes[worldPaneIndex];
    if(!entry || !entry.chip) { return; }
    const prog = entry.chip.querySelector('.world-progress');
    if(!prog) { return; }
    const done = entry.levels.filter(function (l) { return getPast(null, l).complete; }).length;
    prog.innerText = done + '/' + entry.levels.length;
}

function makeLevelSelect(res) {
    const worldIndex = document.getElementById('worldIndex');
    const worlds = document.getElementById("worlds");
    var maxcols = 0;
    var maxrows = 0;
    // Compute completion data first, so each button can show which difficulties are unlocked.
    computeUnlockData(res);
    applyAutoCompletions(res);
    LEVELS.forEach(function (world, x) {
        // Skip this world if it requires a server and we're not in server mode.
        if(world.server && !SERVER) { return; }

        const worldPane = document.createElement("div");
        worldPane.className = "world";

        // Each world starts with a sticky header showing its name, so it stays visible while
        // scrolling through that world.
        const worldHeader = document.createElement("div");
        worldHeader.className = "world-header";
        worldHeader.innerText = world.name;
        worldPane.appendChild(worldHeader);

        worlds.appendChild(worldPane);
        var countstages = 1;

        // Track this world's levels and how many are completed, for the index-chip progress count.
        const worldLevels = [];
        var worldDone = 0;
        const worldNum = worldPanes.length;

        var nontrivialWorldLevels = [];
        world.stages.forEach(function (stage, y) {
            var stageGrid = document.createElement("div");
            stageGrid.className = "stage";
            worldPane.appendChild(stageGrid);

            const label = document.createElement("div");
            label.innerHTML = stage.name;
            label.className = 'stage-label';
            stageGrid.appendChild(label);
            
            var countlevels = 1;
            stage.levels.forEach(function (level, z) {
                if(level.br) {
                    maxcols = Math.max(maxcols, countlevels);
                    stageGrid = document.createElement("div");
                    stageGrid.className = "stage";
                    worldPane.appendChild(stageGrid);

                    stageGrid.appendChild(document.createElement("div"));

                    countlevels = 2;
                }
                const b = document.createElement("button");
                const name = (x+1) + '-' + (y+1) + '-' + (z+1);
                b.dataset.name = name;
                level.name = name;
                level.stage = stage;
                level.button = b;
                level.worldIndex = x;
                level.stageIndex = y;
                level.levelIndex = z;
                level.worldPaneIndex = worldNum;
                if(!level.trivial) {
                    nontrivialWorldLevels.push(level);
                }

                // Has the user has solved this level before?
                const past = getPast(res, level);
                worldLevels.push(level);
                if(past.complete) { worldDone++; }

                // Render the button showing the number and per-difficulty lock/unlock/done marks.
                renderLevelButton(b, name, levelDifficultyStates(level, past, unlockData), level);
                b.addEventListener('click', function () { chooseLevel(level); } );
                stageGrid.appendChild(b);
                levelButtons.push(b);
                allLevels.push(level);
                ++countlevels;
            });
            ++countstages;
            maxcols = Math.max(maxcols, countlevels);
        });

        maxrows = Math.max(maxrows, countstages);

        // The last "pseudo-stage" has a "Random" level (a single "Custom" button lives at the
        // bottom of the chooser, not per-world).
        const otherStage = document.createElement('div');
        otherStage.className = 'stage';

        const otherLabel = document.createElement('div');
        otherLabel.className = 'stage-label';
        otherStage.appendChild(otherLabel);

        // The "Random" level chooses a random level from that world
        const randomLevel = document.createElement('div');
        randomLevel.className = 'level';
        randomLevel.innerText = 'Random';
        randomLevel.onclick = function () {
            // Pick a random non-trivial level that's actually unlocked.
            var pool = nontrivialWorldLevels;
            if(!TEST_MODE) {
                pool = nontrivialWorldLevels.filter(function (l) {
                    return levelDifficultyStates(l, getPast(null, l), unlockData)[0] !== 'locked';
                });
            }
            if(pool.length === 0) { return; }
            chooseLevel(pool[Math.floor(Math.random() * pool.length)]);
        };
        otherStage.appendChild(randomLevel);

        worldPane.appendChild(otherStage);

        // A clickable chip in the index bar scrolls to this world, with a short name and a
        // running "done/total" level count.
        const chip = document.createElement("div");
        chip.className = "world-chip";
        chip.innerHTML = escapeHtml(shortWorldName(world.name)) +
            ' <span class="world-progress">' + worldDone + '/' + worldLevels.length + '</span>';
        chip.onclick = function () { setWorld(worldNum); };
        worldIndex.appendChild(chip);

        worldPanes.push({
            name: world.name,
            pane: worldPane,
            chip: chip,
            levels: worldLevels,
        });
    });

    // A final "Custom" world holds the player's saved custom levels, listed as named rows (built by
    // refreshCustomWorld), with its own index chip.
    const customPane = document.createElement("div");
    customPane.className = "world";
    const customHeader = document.createElement("div");
    customHeader.className = "world-header";
    customHeader.innerText = "Custom";
    customPane.appendChild(customHeader);
    customRowsContainer = document.createElement("div");
    customRowsContainer.id = "customRows";
    customPane.appendChild(customRowsContainer);
    worlds.appendChild(customPane);

    const customWorldNum = worldPanes.length;
    customChipEl = document.createElement("div");
    customChipEl.className = "world-chip";
    customChipEl.innerHTML = 'Custom <span class="world-progress"></span>';
    customChipEl.onclick = function () { setWorld(customWorldNum); };
    worldIndex.appendChild(customChipEl);
    worldPanes.push({ name: "Custom", pane: customPane, chip: customChipEl, levels: [], custom: true });
    refreshCustomWorld();

    document.getElementById("levelChooseModal").style.width = (maxcols * 80 + 30) + 'px';

    // Keep the active world chip in sync as the user scrolls through the worlds.
    worlds.onscroll = updateActiveWorldFromScroll;

    currentWorld = parseInt(localStorage.getItem("world")) || 0;
    if(! worldPanes[currentWorld] ) {
        currentWorld = 0;
    }

    // Scroll to the most recently viewed world.
    setWorld(currentWorld);

    // Load the recent difficulty
    difficulty = parseInt(localStorage.getItem("difficulty"));
    if(!difficulty) {
        difficulty = 0;
    }
    setDifficulty(difficulty);
}

// Re-render every level button's marks/state -- after logging back in, or when a completion
// may have unlocked further levels/difficulties.
// Levels flagged `autoComplete` (those with no internal wires worth re-labeling) are marked
// complete automatically as soon as they unlock at adept/master -- but only once the player has
// already solved them at least once (at novice), so they still solve the level one time rather
// than redoing a level that has nothing extra to do.  Completing adept can unlock master, and
// completions feed back into the unlock data, so loop to a fixed point.  This never advances the
// global time counter (it isn't a real solve) and preserves any existing per-difficulty times.
function applyAutoCompletions(res) {
    var changed = true;
    while(changed) {
        changed = false;
        // Use the loop indices (x,y,z) rather than level.worldIndex etc., since this can run during
        // makeLevelSelect before those properties are assigned.
        LEVELS.forEach(function (world, x) {
            world.stages.forEach(function (stage, y) {
                stage.levels.forEach(function (level, z) {
                    if(!level.autoComplete) { return; }
                    const past = getPast(res, level);
                    // Only auto-complete the higher difficulties once the player has actually solved
                    // the level at least once (at novice), so they do see and solve it one time.
                    if(!past.complete) { return; }
                    const base = past.difficulty || 0;
                    var newDiff = base;
                    for(var K = 1; K < 3; K++) {
                        if(difficultyUnlocked(x, y, z, K, unlockData)) { newDiff = Math.max(newDiff, K); }
                    }
                    if(newDiff > base) {
                        const key = JSON.stringify(saveable(level));
                        const value = { complete: true, difficulty: newDiff, times: past.times || {} };
                        localStorage.setItem(key, JSON.stringify(value));
                        if(res) { res[key] = value; }
                        changed = true;
                    }
                });
            });
        });
        if(changed) { computeUnlockData(res); }
    }
}

function updateLevelSelect(res) {
    computeUnlockData(res);
    applyAutoCompletions(res);
    LEVELS.forEach(function (world, x) {
        world.stages.forEach(function (stage, y) {
            stage.levels.forEach(function (level, z) {
                const past = getPast(res, level);
                renderLevelButton(level.button, level.name, levelDifficultyStates(level, past, unlockData), level);
            });
        });
    });
}

// Scroll the level chooser to a given world (by its index in worldPanes) and mark its chip active.
function setWorld(newWorld) {
    currentWorld = newWorld;
    localStorage.setItem("world", currentWorld);
    const entry = worldPanes[currentWorld];
    if(entry) {
        entry.pane.scrollIntoView({ block: 'start' });
        highlightWorldChip(currentWorld);
    }
}

// Mark the given world's chip active in the index bar.
function highlightWorldChip(i) {
    worldPanes.forEach(function (entry, j) {
        if(entry.chip) {
            entry.chip.classList.toggle("active", i === j);
        }
    });
}

// As the user scrolls the worlds list, highlight the chip for the world currently at the top.
function updateActiveWorldFromScroll() {
    const worlds = document.getElementById("worlds");
    const top = worlds.getBoundingClientRect().top;
    var active = 0;
    worldPanes.forEach(function (entry, i) {
        if(entry.pane.getBoundingClientRect().top - top <= 5) {
            active = i;
        }
    });
    // When scrolled to the bottom, the last (short) world can't reach the top, so select it.
    if(worlds.scrollTop + worlds.clientHeight >= worlds.scrollHeight - 5) {
        active = worldPanes.length - 1;
    }
    if(active !== currentWorld) {
        currentWorld = active;
        localStorage.setItem("world", currentWorld);
        highlightWorldChip(active);
    }
}

// Set the colors of the difficulty select buttons

const difficultyRadios = [
    [ document.getElementById("noviceRadio"), document.getElementById("noviceRadioCustom") ],
    [ document.getElementById("adeptRadio"),  document.getElementById("adeptRadioCustom") ],
    [ document.getElementById("masterRadio"), document.getElementById("masterRadioCustom") ],
];
        
const difficultyBoxes = [
    [ document.getElementById("noviceBox"), document.getElementById("noviceBoxCustom") ],
    [ document.getElementById("adeptBox"),  document.getElementById("adeptBoxCustom") ],
    [ document.getElementById("masterBox"), document.getElementById("masterBoxCustom") ],
];

function setDifficulty(d) {
    difficultyRadios.forEach(function(radios, i) {
        const selected = (i === d ? 1 : 0);
        radios.forEach(function (radio) {
            radio.style.color = COLORS[i][selected].color;
            radio.style.backgroundColor = COLORS[i][selected].backgroundColor;
        });
    });
    difficultyBoxes.forEach(function(boxes, i) {
        const selected = (i === d ? 1 : 0);
        boxes.forEach(function (box) {
            box.innerText = CHECKBOXES[selected];
        });
    });
    difficulty = d;
    localStorage.setItem("difficulty", d.toString());
    // Tint the palette bar and the difficulty label with the current difficulty's (light) color,
    // so it's obvious at a glance which difficulty you're working at.
    document.getElementById("paletteBar").style.backgroundColor = COLORS[d][0].backgroundColor;
    document.getElementById("currentDifficulty").style.backgroundColor = COLORS[d][0].backgroundColor;
}

difficultyRadios.forEach(function (radios, i) {
    radios.forEach(function (radio) {
        radio.onclick = function () { setDifficulty(i); };
    });
});

// DEPRECATED, with the `saveable` blocks in levels.js: the keys a level's records were filed under
// before its statement was last written differently -- one per earlier statement, and none at all
// for the levels that never moved.
function legacyKeysOf(level) {
    return legacySaveables(level).map(function (old) { return JSON.stringify(old); });
}

// Copy anything still filed under a level's pre-2025 key to the key it uses now: the completion
// record and each difficulty's saved proof.  The old copies are left alone, so a browser still
// running a cached older build goes on finding them.  `res` is the server's records for a logged-in
// student, which are migrated (and saved back) as well.
//
// This runs at startup and after logging in.  Once every student has been through it, this function
// and the `saveable` blocks it reads can go; see levels.js.
function migrateLegacyRecords(res) {
    LEVELS.forEach(function (world) {
        world.stages.forEach(function (stage) {
            stage.levels.forEach(function (level) {
                const key = JSON.stringify(saveable(level));
                legacyKeysOf(level).forEach(function (old) {
                    // The completion record, from the server's copy if we're logged in.
                    if(res) {
                        if(res[old] !== undefined && res[key] === undefined) {
                            res[key] = res[old];
                            localStorage.setItem(key, JSON.stringify(res[key]));
                            saveSolvedToServer(key, res[key], res.difficulty || 0, res.world || 0);
                        }
                    } else if(localStorage.getItem(key) === null) {
                        const record = localStorage.getItem(old);
                        if(record !== null) { localStorage.setItem(key, record); }
                    }
                    // And the proof saved at each difficulty.
                    for(var d = 0; d < 3; d++) {
                        if(localStorage.getItem("proof:" + d + ":" + key) === null) {
                            const proof = localStorage.getItem("proof:" + d + ":" + old);
                            if(proof !== null) { localStorage.setItem("proof:" + d + ":" + key, proof); }
                        }
                    }
                });
            });
        });
    });
}

// Record a completed level on the server, under the key its statement gives it.  The difficulty and
// world go along with it: the server keeps the most recent ones, to reopen the game where the
// student left off.
function saveSolvedToServer(key, value, difficulty, world) {
    if(!SERVER) { return; }
    const xhr = new XMLHttpRequest();
    xhr.open('POST', '/solve', true);
    xhr.setRequestHeader('Content-Type', 'application/json;charset=UTF-8');
    xhr.onload = function() {
        if (xhr.status === 200) {
            // Success, nothing to be done
        } else {
            let res = JSON.parse(xhr.responseText);
            alert("Error saving completed proof (" + res.error + ").  Check your Internet connection, and then delete and replace a wire to re-trigger saving.")
        }
    };
    const data = { email: localStorage.getItem("email"), key: key, value: value, difficulty: difficulty, world: world };
    xhr.send(JSON.stringify(data));
}

// Get the user's past success on a given level, perhaps using a database result
function getPast(res, level) {
    const key = JSON.stringify(saveable(level));
    var past;
    if(res) {
        past = res[key];
        if(past) {
            localStorage.setItem(key, JSON.stringify(past));
        }
    } else {
        past = JSON.parse(localStorage.getItem(key));
    }
    if(!past) {
        past = { complete: false, difficulty: 0 };
    }
    if(! past.difficulty) {
        past.difficulty = 0;
    }
    return past;
}

// === Level-button rendering with per-difficulty lock / unlock / completed states ===

// Small line-art padlock icons, tinted via the surrounding element's text color.
const LOCK_SVG = '<svg class="lockicon" viewBox="0 0 24 24"><rect x="5" y="11" width="14" height="10" rx="2"/><path d="M8 11V7a4 4 0 0 1 8 0v4"/></svg>';
// The "unlocked" padlock's shackle is open, swung up and out to the right.
const UNLOCK_SVG = '<svg class="lockicon" viewBox="0 0 24 24"><rect x="5" y="11" width="14" height="10" rx="2"/><path d="M8 11V7a5 5 0 0 1 8.5-2"/></svg>';

// What fraction of `total` is `done` (an empty world/stage counts as fully complete).
function fraction(done, total) {
    return total === 0 ? 1 : done / total;
}

// Whether difficulty K (0,1,2) of level A-B-C is unlocked, given the completion `data`.  The level
// is passed 0-indexed as world w (=A-1), stage s (=B-1), level c (=C-1).  All conditions must hold.
// Whether a world's three inter-world gates (rules 1-3) pass at difficulty K -- i.e. whether the
// world itself is "open" at K (individual levels still need the stage/level rules 4-6).
//
// Which worlds a world follows is its `previous` list in levels.js, defaulting to [1], the world
// right before it (see computeUnlockData); each gate then asks about ALL the worlds it names, so a
// world following two others waits for both.  The percentages are of each world's non-bonus levels;
// a `bonus` stage is left out of the totals entirely, so solving one can never open a world.
function worldGatesPass(w, K, data) {
    const world = data[w];
    // 1. Every world this one follows is >= 80% complete at difficulty K.
    if(world.previous.some(function (p) { return fraction(data[p].done[K], data[p].total) < 0.8; })) {
        return false;
    }
    // 2. Every world that follows this one is >= 50% complete at K-1 (unless K is 0).
    if(K > 0 && world.followers.some(function (f) {
        return fraction(data[f].done[K - 1], data[f].total) < 0.5;
    })) { return false; }
    // 3. Every world followed by a world this one follows is >= 50% complete at K+1 (unless K=2).
    if(K < 2 && world.previous.some(function (p) {
        return data[p].previous.some(function (q) {
            return fraction(data[q].done[K + 1], data[q].total) < 0.5;
        });
    })) { return false; }
    return true;
}

function difficultyUnlocked(w, s, c, K, data) {
    const world = data[w];
    const stage = world.stages[s];
    // Rules 1-3: the world must be open at this difficulty.
    if(!worldGatesPass(w, K, data)) { return false; }
    // 4. Each of this stage's prerequisite stages is >= 70% complete at K.  By default that's the
    //    single stage right before it; a stage can instead declare `previous: [...]` in levels.js,
    //    listing how many stages back each prerequisite is -- [2] to look past the stage in between
    //    (for two independent tracks), [1, 2] to require both, [] for no stage prerequisite at all.
    //    Entries reaching back past the first stage are ignored, so the first stage is unrestricted.
    const previous = stage.previous || [1];
    for(var pi = 0; pi < previous.length; pi++) {
        const ps = s - previous[pi];
        if(ps >= 0 && fraction(world.stages[ps].done[K], world.stages[ps].total) < 0.7) { return false; }
    }
    // 5. All but (at most) 2 of the levels before this one in the stage are complete at K -- so a
    //    stage's first three levels are available as soon as it opens.
    var completedBefore = 0;
    for(var i = 0; i < c; i++) { if(stage.levelDiff[i] >= K) { completedBefore++; } }
    if(completedBefore < c - 2) { return false; }
    // 6. (Novice only) every earlier level in this stage that has a hint is completed -- so you
    //    can't skip past a level that teaches something new.
    if(K === 0) {
        for(var j = 0; j < c; j++) {
            if(stage.hasHint[j] && stage.levelDiff[j] < 0) { return false; }
        }
    }
    // 7. (Adept/Master) the previous difficulty of THIS level must not have been completed within
    //    the last RECENT_COMPLETION_WINDOW completions, so you can't immediately go up a difficulty
    //    and copy what you just did at the lower one.
    if(K >= 1) {
        const times = stage.levelTimes[c];
        if(times && times[K - 1] !== undefined && globalTime - times[K - 1] <= RECENT_COMPLETION_WINDOW) {
            return false;
        }
    }
    return true;
}

// How many completions must pass before a just-completed difficulty stops re-locking the next.
const RECENT_COMPLETION_WINDOW = 10;

// The state of each of a level's three difficulties: 'completed', 'unlocked', or 'locked'.
function levelDifficultyStates(level, past, data) {
    const states = [];
    for(var K = 0; K < 3; K++) {
        if(past.complete && past.difficulty >= K) { states.push('completed'); }
        else if(difficultyUnlocked(level.worldIndex, level.stageIndex, level.levelIndex, K, data)) { states.push('unlocked'); }
        else { states.push('locked'); }
    }
    return states;
}

// The mark for one difficulty: a star (completed), an open lock (unlocked), or a closed lock
// (locked), tinted to that difficulty's color.
function difficultyMark(state, d) {
    const color = COLORS[d][1].backgroundColor;
    if(state === 'completed') { return '<span class="lvmark" style="color:' + color + '">★</span>'; }
    if(state === 'unlocked')  { return '<span class="lvmark" style="color:' + color + '">' + UNLOCK_SVG + '</span>'; }
    return '<span class="lvmark locked" style="color:' + color + '">' + LOCK_SVG + '</span>';
}

// A level that has a hint carries an "i" in the top-right corner of its button.  While the level
// is open the "i" is blue and clicking it shows the hint without leaving the chooser; while the
// level is locked it is grey and inert, so it says a hint is waiting without giving it away.
function addHintBubble(b, level, unlocked) {
    if(!level || !level.hint) { return; }
    const bubble = document.createElement('div');
    bubble.className = 'hintbubble' + (unlocked ? '' : ' locked');
    bubble.innerText = 'i';
    bubble.title = unlocked ? "Show this level's hint" : "This level has a hint";
    bubble.addEventListener('click', function (e) {
        // The button underneath opens the level, which is never what a click on the badge meant --
        // so it swallows the click whether or not it has a hint to show.
        e.stopPropagation();
        if(unlocked) { showHintById(level.hint); }
    });
    b.appendChild(bubble);
}

// Render a level's button: its number, a row of three per-difficulty marks, and a top stripe in
// the highest completed difficulty's color (the normal black border when nothing is completed).
// In test mode `level` is used to make the marks double-clickable (see makeMarksToggleable).
function renderLevelButton(b, name, states, level) {
    b.className = 'level';
    b.style.borderTop = '';
    // A fully locked level (novice not yet unlocked) is shown disabled, with a lock in front --
    // except in test mode, where every level is playable and every mark is a toggle, so all three
    // marks are shown (greyed) rather than the single summary padlock.
    if(states[0] === 'locked') {
        b.classList.add('level-locked');
        if(!TEST_MODE) {
            b.innerHTML = '<span class="lvmark locked" style="color:#888">' + LOCK_SVG + '</span><span class="level-number">' + name + '</span>';
            addHintBubble(b, level, false);
            return;
        }
        // Still greyed as locked, but laid out like any other level (number above its marks).
        b.classList.add('level-toggles');
    }
    // "Active" = has a difficulty that's unlocked but not yet completed: where to work next.
    if(states.includes('unlocked')) { b.classList.add('level-active'); }
    b.innerHTML = '<div class="level-number">' + name + '</div>' +
        '<div class="level-marks">' +
        difficultyMark(states[0], 0) + difficultyMark(states[1], 1) + difficultyMark(states[2], 2) +
        '</div>';
    var hc = -1;
    for(var d = 0; d < 3; d++) { if(states[d] === 'completed') { hc = d; } }
    if(hc >= 0) { b.style.borderTop = '5px solid ' + COLORS[hc][1].backgroundColor; }
    addHintBubble(b, level, states[0] !== 'locked');
    if(TEST_MODE && level) { makeMarksToggleable(b, level); }
}

// ===== Test-mode completion toggles =====
// With "?test" in the URL every level is playable; on top of that, double-clicking one of a level's
// three difficulty marks flips whether the level counts as completed at that difficulty, so the
// unlock rules can be experimented with directly instead of by hand-editing localStorage.
function makeMarksToggleable(b, level) {
    b.title = 'Test mode: double-click a mark to toggle this level\'s completion at that difficulty';
    const marks = b.querySelectorAll('.level-marks .lvmark');
    marks.forEach(function (mark, d) {
        // A mark's own clicks mustn't open the level (a double-click would open it twice).
        mark.addEventListener('click', function (e) { e.stopPropagation(); });
        mark.addEventListener('dblclick', function (e) {
            e.stopPropagation();
            toggleCompletedAt(level, d);
        });
    });
}

// Flip a level's completion at difficulty d.  Completion is stored as the HIGHEST difficulty
// completed, so turning d on records "completed up to d", and turning it off records "completed up
// to d-1" (clearing the record entirely at novice).  No completion *time* is recorded, so rule 7
// (a just-completed lower difficulty re-locking the next) doesn't apply to a toggled level; and
// re-rendering re-applies the auto-completion rule, which may immediately re-complete a higher
// difficulty of an `autoComplete` level that is unlocked there.
function toggleCompletedAt(level, d) {
    const key = JSON.stringify(saveable(level));
    const past = getPast(null, level);
    const completed = past.complete && past.difficulty >= d;
    if(completed && d === 0) {
        localStorage.removeItem(key);
    } else {
        localStorage.setItem(key, JSON.stringify({
            complete: true,
            difficulty: completed ? d - 1 : Math.max(past.difficulty || 0, d),
        }));
    }
    // Re-render every level (this completion feeds the unlock rules) and this world's chip count.
    updateLevelSelect(null);
    refreshWorldProgress(level.worldPaneIndex);
}

// Recompute, for every world and stage, how many of its levels are complete at each difficulty
// (>= K) and each level's completed difficulty, from the saved results.  Drives the unlock rule.
function computeUnlockData(res) {
    globalTime = parseInt(localStorage.getItem("time")) || 0;
    unlockData = LEVELS.map(function (world, w) {
        // Which worlds this one follows: `previous` lists how many worlds back each is, defaulting
        // to the world right before it.  Entries reaching back past the first world are ignored, so
        // the first world follows nothing; `followers` (filled in below) is the reverse relation.
        const previous = (world.previous || [1]).map(function (n) { return w - n; })
              .filter(function (i) { return i >= 0; });
        const wd = { total: 0, done: [0, 0, 0], stages: [], previous: previous, followers: [] };
        world.stages.forEach(function (stage) {
            // `previous` is which stages back this one's rule-4 prerequisite is; see difficultyUnlocked.
            const sd = { total: 0, done: [0, 0, 0], levelDiff: [], levelTimes: [], hasHint: [],
                         previous: stage.previous };
            // A `bonus` stage is extra credit: its levels are left out of the world's totals, so the
            // inter-world percentages (rules 1-3) are fractions of the non-bonus levels only.  They
            // still count for their own stage, so the stage rules (4-6) treat them like any other.
            const counts = !stage.bonus;
            stage.levels.forEach(function (level) {
                const p = getPast(res, level);
                const cd = p.complete ? p.difficulty : -1;
                sd.levelDiff.push(cd);
                sd.levelTimes.push(p.times || null);
                sd.hasHint.push(!!level.hint);
                sd.total++;
                if(counts) { wd.total++; }
                for(var K = 0; K <= 2; K++) {
                    if(cd >= K) {
                        sd.done[K]++;
                        if(counts) { wd.done[K]++; }
                    }
                }
            });
            wd.stages.push(sd);
        });
        return wd;
    });
    // Now that every world's `previous` is resolved, record each one's followers.
    unlockData.forEach(function (wd, w) {
        wd.previous.forEach(function (p) { unlockData[p].followers.push(w); });
    });
}

// Snapshot which (world, difficulty) pairs are currently "open" (rules 1-3), from unlockData.
function snapshotWorldGates() {
    return unlockData.map(function (_, w) {
        return [0, 1, 2].map(function (K) { return worldGatesPass(w, K, unlockData); });
    });
}

const ABOUT_DIFFICULTY_IDS = ['aboutNovice', 'aboutAdept', 'aboutMaster'];

// After a completion (with unlockData already recomputed), pop up a modal for any world that just
// became open at a difficulty, compared with the `before` snapshot.  The first time a difficulty
// becomes available at all, also include its explanation from the About box.
function announceNewlyUnlockedWorlds(before) {
    const events = [];
    for(var w = 0; w < unlockData.length; w++) {
        for(var K = 0; K < 3; K++) {
            if(worldGatesPass(w, K, unlockData) && !before[w][K]) {
                events.push({ w: w, K: K });
            }
        }
    }
    if(events.length === 0) { return; }
    var html = '';
    events.forEach(function (e) {
        html += '<h3 style="text-align: center">' + escapeHtml(LEVELS[e.w].name) +
            ' is now unlocked at ' + DIFFICULTIES[e.K] + ' difficulty!</h3>';
    });
    // If a difficulty just became available for the very first time, explain it (once).
    [0, 1, 2].forEach(function (K) {
        const newAtK = events.some(function (e) { return e.K === K; });
        const noneBeforeAtK = !before.some(function (row) { return row[K]; });
        if(newAtK && noneBeforeAtK) {
            const p = document.getElementById(ABOUT_DIFFICULTY_IDS[K]);
            if(p) { html += '<p class="about">' + p.innerHTML + '</p>'; }
        }
    });
    document.getElementById("unlockContent").innerHTML = html;
    document.getElementById("unlockBG").style.display = "flex";
}

// The "Select Level" button opens a modal box to choose from pre-set levels.  There's a "custom" button at the bottom that switches to a modal box that sets a custom level.
document.getElementById("selectLevel").onclick = function() {
    document.getElementById("levelChooseBG").style.display = "flex";
};

// To clear the current proof, discard its autosave and re-open the current level fresh.
document.getElementById("clearProof").onclick = function() {
    if(confirm("This will clear your current proof and reset to the beginning of this level!  It cannot be un-done.  Are you sure?")) {
        const key = savedProofKey();
        if(key) { localStorage.removeItem(key); }
        reopenCurrentLevel();
    }
}

// Whether the proof currently reads as complete: the conclusion box has been turned a color, which
// only a typecheck that accepted the whole proof (and kept it within any block budget) does.
function proofIsComplete() {
    return conclusion_node !== null && conclusion_node.style.backgroundColor !== "";
}

// Compute a JSON-serializable snapshot of the current proof state: every node
// (with its position, size, and any associated name/value), and every
// connection (with its endpoints and user-supplied wire label).
function serializeProof() {
    const savedNodes = nodes.map(function (x) {
        const node = x.node;
        const data = {
            id: x.id,
            rule: x.rule,
            left: node.style.left,
            top: node.style.top,
        };
        if(x.name !== undefined) { data.name = x.name; }
        if(x.value !== undefined) { data.value = x.value; }
        if(node.style.width) { data.width = node.style.width; }
        if(node.style.height) { data.height = node.style.height; }
        if(node.dataset.variable) { data.variable = node.dataset.variable; }
        return data;
    });

    const savedConnections = instance.getConnections().map(function (c) {
        return {
            source: {
                vertex: c.source.id,
                sort: c.endpoints[0].parameters.sort,
                label: c.endpoints[0].parameters.label,
            },
            target: {
                vertex: c.target.id,
                sort: c.endpoints[1].parameters.sort,
                label: c.endpoints[1].parameters.label,
            },
            // The user-supplied wire label, if any (entered on Adept/Master difficulty).
            ty: c.parameters.ty,
            // The connector style (angled / curved / straight) of this particular wire.
            connector: c.connector && c.connector.type,
        };
    });

    return {
        // The level this proof belongs to (parameters, variables, hypotheses, conclusion), so
        // an imported proof can be matched to (or used to switch to) the right level.  Custom
        // levels export their whole definition, so an import elsewhere can recreate the level.
        level: currentLevelDefinition(),
        // The name of the saved custom level this proof belongs to, if any, used to pre-fill the
        // prompt when an import has to recreate it.
        levelName: currentCustom ? currentCustom.name : undefined,
        // Whether the proof is currently complete (the conclusion has turned a color).
        complete: proofIsComplete(),
        difficulty: difficulty,
        // Where the player was looking, so resuming this proof puts the diagram back on screen
        // exactly where they left it rather than wherever the boxes happen to be.
        view: { x: diagram.scrollLeft, y: diagram.scrollTop },
        // Autonumber counters, so nodes added after a restore won't reuse saved IDs.
        counters: {
            counter: counter,
            paramCounter: paramCounter,
            varCounter: varCounter,
            hypCounter: hypCounter,
            conclCounter: conclCounter,
        },
        nodes: savedNodes,
        connections: savedConnections,
    };
}

// The definition (parameters, variables, hypotheses, conclusion) identifying the level that's
// currently open: the "saveable" statement of a built-in level, or the full definition of a
// custom one (saved or not).  Undefined only before any level has been set up.
function currentLevelDefinition() {
    if(currentLevel) { return saveable(currentLevel); }
    if(currentLevelDef) { return levelDefCopy(currentLevelDef); }
    return undefined;
}

// The identity of the currently open level as a JSON string, comparable with the "level" field
// of an exported proof, or null if there is no level.
function currentLevelKey() {
    const def = currentLevelDefinition();
    return def ? JSON.stringify(def) : null;
}

// Whether an imported proof's "level" field carries a usable level definition (so a custom level
// could be built from it).
function isLevelDef(def) {
    return !!def && Array.isArray(def.parameters) && Array.isArray(def.variables) &&
        Array.isArray(def.hypotheses) && !!def.conclusion && typeof def.conclusion.ty === 'string';
}

// Find the built-in level whose identity (saveable parameters/hypotheses/conclusion) matches
// the given JSON.stringify(saveable(...)) key, or undefined if none does.  A proof exported before
// a level's notation changed carries the statement it had then, so those are matched too
// (DEPRECATED along with the `saveable` blocks in levels.js).
function findLevelByKey(key) {
    return allLevels.find(function (l) { return JSON.stringify(saveable(l)) === key; })
        || allLevels.find(function (l) { return legacyKeysOf(l).includes(key); });
}

// Find the saved custom level with the same statement as the given key, or undefined if none has.
function findCustomLevelByKey(key) {
    return loadCustomLevels().find(function (c) { return JSON.stringify(levelDefCopy(c)) === key; });
}

// localStorage key under which the proof for the currently selected level is saved.
// localStorage key for the proof saved for the current level at a given difficulty (default the
// current one).  Each level has a separate saved proof per difficulty.
function savedProofKey(d) {
    if(d === undefined) { d = difficulty; }
    // Saved custom levels key by their unique id; built-in levels by their statement.  An unsaved
    // custom level has nowhere to save to.
    if(currentCustom) { return "proof:" + d + ":custom:" + currentCustom.id; }
    if(currentLevel) { return "proof:" + d + ":" + JSON.stringify(saveable(currentLevel)); }
    return null;
}

// Whether a serialized proof represents actual progress worth restoring: at least one
// connection, or one user-added node beyond the level's fixed nodes.
function proofHasProgress(state) {
    return !!state && (
        (Array.isArray(state.connections) && state.connections.length > 0) ||
        (Array.isArray(state.nodes) && state.nodes.some((n) => !FIXED_RULES.includes(n.rule)))
    );
}

// Automatically persist the current proof to localStorage.  Called after every change (via
// typecheck); suppressed while a level is being set up so the empty proof can't clobber a save.
function autosave() {
    if(suppressSave) { return; }
    const key = savedProofKey();
    if(key) {
        localStorage.setItem(key, JSON.stringify(serializeProof()));
    }
}

// When a level is selected, if there's an autosaved proof with real progress for it AT THE
// CURRENT DIFFICULTY, offer to reload it or discard it.  (A level just unlocked at a higher
// difficulty has no saved proof there yet, so it opens blank with no prompt.)  The level is set
// up empty behind the prompt, so "discard" just drops the saved data and leaves the fresh level.
var pendingSavedProof = null;
function offerSavedProof(level) {
    const key = savedProofKey();
    if(!key) { return; }
    const saved = localStorage.getItem(key);
    if(!saved) { return; }
    var state;
    try {
        state = JSON.parse(saved);
    } catch(e) {
        localStorage.removeItem(key);
        return;
    }
    if(!proofHasProgress(state)) { return; }
    pendingSavedProof = { state: state, level: level, key: key };
    document.getElementById("savedProofText").innerText = state.complete
        ? "You have a saved complete proof for this level."
        : "You have a saved partial proof for this level.";
    document.getElementById("savedProofBG").style.display = "flex";
}

document.getElementById("loadSavedProof").onclick = function() {
    document.getElementById("savedProofBG").style.display = "none";
    if(pendingSavedProof) {
        const pending = pendingSavedProof;
        pendingSavedProof = null;
        restoreProof(pending.state, pending.level);
    }
};
document.getElementById("discardSavedProof").onclick = function() {
    document.getElementById("savedProofBG").style.display = "none";
    if(pendingSavedProof) {
        localStorage.removeItem(pendingSavedProof.key);
        pendingSavedProof = null;
    }
};

// Find the endpoint on a node element matching a saved connection's sort and label.
function findEndpoint(el, sort, label) {
    return instance.getEndpoints(el).find(function (ep) {
        return ep.parameters.sort === sort && ep.parameters.label === label;
    });
}

// Rebuild the proof from a snapshot object (as produced by serializeProof), into the given
// level (defaulting to the current one).  Shared by "Load" (from localStorage) and "Import"
// (from pasted JSON).
function restoreProof(state, level, countAsCompletion) {
    // Reset to a clean slate: re-select the target level (an explicit built-in level for an Import,
    // otherwise whatever is currently open, built-in or custom), recreating its fixed nodes and
    // Narya.  Skip the saved-proof prompt here: we're restoring a specific proof on purpose.
    if(level) {
        selectCurrentLevel(level, true);
    } else if(!reopenCurrentLevel()) {
        alert("There is no level to restore this proof into.");
        return;
    }

    // Restore the saved difficulty setting.
    if(typeof state.difficulty === 'number') {
        setDifficulty(state.difficulty);
        updateCurrentDifficulty();
    }

    // Build the rest of the proof in one batch, suppressing typechecking and the
    // per-connection wire-label prompt until we're done.
    suppressChecking = true;
    restoring = true;

    // Map each saved node id to the actual node element now in the diagram.
    const idMap = {};

    // The fixed nodes were just recreated by selectCurrentLevel, in the same order they
    // were saved; pair them up by that order and restore their positions.
    const savedFixed = (state.nodes || []).filter((n) => FIXED_RULES.includes(n.rule));
    nodes.forEach((entry, i) => {
        const sn = savedFixed[i];
        if(!sn) { return; }
        idMap[sn.id] = entry.node;
        if(sn.left) { entry.node.style.left = sn.left; }
        if(sn.top)  { entry.node.style.top  = sn.top; }
    });

    // Recreate the user-added nodes, in their saved order, with their saved geometry and values.
    (state.nodes || []).filter((n) => !FIXED_RULES.includes(n.rule)).forEach((sn) => {
        const rule = sn.rule;
        const box = addRuleNode(rule);
        addEndpointsForRule(box, rule, true);
        if(sn.left)   { box.style.left = sn.left; }
        if(sn.top)    { box.style.top = sn.top; }
        if(sn.width)  { box.style.width = sn.width; }
        if(sn.height) { box.style.height = sn.height; }
        const entry = nodes.find((x) => x.id === box.id);
        // Restore a bound-variable name (∀/∃ rules) into the global list and the node.
        if(sn.name !== undefined && entry) { entry.name = sn.name; }
        if(sn.variable) {
            if(!varnames.includes(sn.variable)) { varnames.push(sn.variable); }
            box.dataset.variable = sn.variable;
        }
        // Restore an ascription/expression value and re-render the box accordingly.
        if(sn.value !== undefined) {
            if(entry) { entry.value = sn.value; }
            if(sn.rule === 'asc' || sn.rule === 'expr') {
                box.innerHTML = (sn.rule === 'asc' ? "🏷&nbsp;" : "") + sn.value;
                box.style.width = 'fit-content';
                box.style.padding = "0px 8px 0px 8px";
                // Re-rendering the box blew away its close button, so add it back.
                addBoxCloseButton(box);
            }
        }
        idMap[sn.id] = box;
    });

    // Repositioning the nodes invalidated jsPlumb's cached geometry; revalidate before reconnecting.
    nodes.forEach((entry) => instance.revalidate(entry.node));
    // Saved nodes may sit beyond the viewport; grow the canvas so they're reachable by scrolling,
    // and look where the proof was left.  A proof saved or exported before the view was recorded
    // carries none, and is found by looking at wherever its boxes actually are.
    if(state.view) { resizeCanvas(state.view.x, state.view.y); } else { scrollToContent(); }

    // Recreate the connections, matching endpoints by their sort and label.
    (state.connections || []).forEach((c) => {
        const srcEl = idMap[c.source.vertex];
        const tgtEl = idMap[c.target.vertex];
        if(!srcEl || !tgtEl) { return; }
        const srcEp = findEndpoint(srcEl, c.source.sort, c.source.label);
        const tgtEp = findEndpoint(tgtEl, c.target.sort, c.target.label);
        if(!srcEp || !tgtEp) { return; }
        const edge = instance.connect({ source: srcEp, target: tgtEp });
        if(edge) {
            // Restore this wire's connector style if it differs from the default just applied
            // (re-adding the arrow overlay, which _setConnector removes).
            if(c.connector && edge.connector && c.connector !== edge.connector.type) {
                edge._setConnector(c.connector);
                edge.addOverlay({ type: "Arrow", options: { location: -5, width: 10, length: 10 } });
            }
            // Restore the user-supplied wire label, if any (Adept/Master difficulty).
            if(c.ty) { setUserWireLabel(edge, c.ty); }
        }
    });

    restoring = false;
    suppressChecking = false;
    // Restoring a proof that was already complete normally shouldn't count as a fresh completion,
    // except when restoring the lower-difficulty proof after a downgrade (countAsCompletion): that
    // re-locks the higher difficulty just as if you'd re-solved it -- but without advancing the
    // global completion counter (it's a re-load, not a brand-new solve).
    proofRegisteredComplete = countAsCompletion ? false : !!state.complete;
    registerWithoutAdvancingTime = !!countAsCompletion;
    typecheck();
}

// The "Export" button shows the current proof state as JSON, for copying (e.g. into a bug report).
document.getElementById("exportProof").onclick = function() {
    document.getElementById("exportJson").value = JSON.stringify(serializeProof(), null, 2);
    document.getElementById("exportBG").style.display = "flex";
};
document.getElementById("doneExport").onclick = function() {
    document.getElementById("exportBG").style.display = "none";
};
document.getElementById("copyExport").onclick = function() {
    const textarea = document.getElementById("exportJson");
    const copyButton = document.getElementById("copyExport");
    const done = function() { copyButton.innerText = "Copied!"; setTimeout(function() { copyButton.innerText = "Copy to clipboard"; }, 1500); };
    if(navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(textarea.value).then(done, function() { textarea.select(); document.execCommand("copy"); done(); });
    } else {
        textarea.select();
        document.execCommand("copy");
        done();
    }
};

// The "Import" button restores a proof from pasted JSON, into the current level.
document.getElementById("importProof").onclick = function() {
    document.getElementById("importJson").value = "";
    document.getElementById("importBG").style.display = "flex";
    document.getElementById("importJson").focus();
};
document.getElementById("cancelImport").onclick = function() {
    document.getElementById("importBG").style.display = "none";
};
document.getElementById("submitImport").onclick = function() {
    const text = document.getElementById("importJson").value;
    var state;
    try {
        state = JSON.parse(text);
    } catch(e) {
        alert("That isn't valid JSON: " + e.message);
        return;
    }
    if(!state || !Array.isArray(state.nodes)) {
        alert("That JSON doesn't look like an exported proof.");
        return;
    }
    // If the proof was exported from a different level, offer to switch to that level.
    const importedKey = state.level ? JSON.stringify(state.level) : null;
    if(importedKey && importedKey !== currentLevelKey()) {
        // A built-in level, or a custom level we've already saved, with the same statement.
        const target = findLevelByKey(importedKey);
        const custom = target ? null : findCustomLevelByKey(importedKey);
        if(target || custom) {
            if(!confirm("You're trying to import a proof that doesn't match the current level.  Switch to the level it was exported from?")) {
                return;
            }
            document.getElementById("importBG").style.display = "none";
            if(target) { restoreProof(state, target); }
            else { restoreProofIntoCustom(state, custom); }
            return;
        }
        // Otherwise the proof came from a custom level we don't have.  If it carries the level's
        // definition, we can recreate it as a new custom level, under a name the player picks.
        if(!isLevelDef(state.level)) {
            alert("This proof was exported from a level that isn't available, so it can't be imported.");
            return;
        }
        const created = createImportedCustom(state);
        if(!created) { return; }
        document.getElementById("importBG").style.display = "none";
        restoreProofIntoCustom(state, created);
        return;
    }
    document.getElementById("importBG").style.display = "none";
    restoreProof(state);
};

// Save a new custom level built from an imported proof's level definition, prompting for its name
// (pre-filled with the name it was exported under).  Returns the saved level, or null if the
// player cancelled.
function createImportedCustom(state) {
    const suggested = typeof state.levelName === 'string' ? state.levelName : "";
    const input = prompt("This proof comes from a custom level you don't have.  Name for the new custom level:", suggested);
    if(input === null) { return null; }
    const name = input.trim();
    if(!name) { return null; }
    // Re-using an existing name would overwrite that level's statement, so ask first.
    if(loadCustomLevels().some(function (c) { return c.name === name; }) &&
       !confirm('You already have a custom level named "' + name + '".  Replace its statement with the imported one?')) {
        return null;
    }
    // Unlock it up to the difficulty the imported proof was made at, so it opens there.
    const d = typeof state.difficulty === 'number' ? state.difficulty : 0;
    const cl = storeCustomLevelNamed(name, levelDefCopy(state.level), d);
    refreshCustomWorld();
    return cl;
}

// Switch to a saved custom level and rebuild an imported proof in it.
function restoreProofIntoCustom(state, cl) {
    currentCustom = cl;
    currentLevel = undefined;
    currentLevelButton = undefined;
    restoreProof(state);
}

// Test instrumentation seam.  When the page is loaded with "?test" in the URL, we expose a
// small read/drive API on window.__olorin so the Playwright suite can create wire
// connections (which are impractical to simulate via raw jsPlumb endpoint dragging) and read
// the proof state for assertions.  It is inert during normal use.
if (new URLSearchParams(window.location.search).has("test")) {
    window.__olorin = {
        // Snapshot of the diagram nodes (id, rule, name/value, geometry).
        nodes: () => nodes.map((n) => ({
            id: n.id, rule: n.rule, name: n.name, value: n.value,
            left: n.node.style.left, top: n.node.style.top,
            width: n.node.style.width, height: n.node.style.height,
        })),
        // Snapshot of the connections (endpoints and user wire label).
        connections: () => instance.getConnections().map((c) => ({
            source: { vertex: c.source.id, sort: c.endpoints[0].parameters.sort, label: c.endpoints[0].parameters.label },
            target: { vertex: c.target.id, sort: c.endpoints[1].parameters.sort, label: c.endpoints[1].parameters.label },
            ty: c.parameters.ty,
        })),
        // Create a connection between two ports, identified as {vertex, sort, label}.
        connect: (s, t) => {
            const se = findEndpoint(document.getElementById(s.vertex), s.sort, s.label);
            const te = findEndpoint(document.getElementById(t.vertex), t.sort, t.label);
            instance.connect({ source: se, target: te });
        },
        // The diagnostics from the last typecheck (code, text and locations of each error).
        diagnostics: () => lastDiagnostics.map((d) => ({
            code: d.code, isfatal: d.isfatal, text: d.text, explanation: d.explanation, locs: d.locs,
        })),
        // Each wire's delete-X: where it sits along its wire, and its rectangle -- it is laid out
        // even while invisible, so the label-spreading tests can check nothing covers it.
        closeButtons: () => instance.getConnections().map((c) => {
            const o = c.getOverlay("closeButton");
            if(!o || !o.canvas) { return null; }
            const r = o.canvas.getBoundingClientRect();
            return { location: o.location, x: r.x, y: r.y, w: r.width, h: r.height };
        }).filter((b) => b !== null),
        // What hovering each wire currently in error would say, in connection order.
        wireErrors: () => instance.getConnections()
            .map((c) => c.parameters.errorText).filter((t) => t !== undefined),
        difficulty: () => difficulty,
        varnames: () => varnames.slice(),
        savedProofKey,
        // The JSON snapshot of the current proof (as autosave/Export produce).
        serialize: () => serializeProof(),
        // Rebuild the proof from a snapshot, into the current level.
        restore: (state) => restoreProof(state),
        // Whether the proof currently reads as complete (the conclusion turns a color).
        complete: proofIsComplete,
        // The per-difficulty ['locked'|'unlocked'|'completed'] states of a level, by name.
        levelStates: (name) => {
            const lvl = allLevels.find((l) => l.name === name);
            return lvl ? levelDifficultyStates(lvl, getPast(null, lvl), unlockData) : null;
        },
        // Every port in the diagram, with the type currently shown for it (if any) -- the label on
        // an output/assumption port, or the type recorded for an input/subgoal port.
        ports: () => nodes.flatMap((n) =>
            instance.getEndpoints(n.node).map((ep) => {
                const ovl = ep.getOverlay("customLabel");
                const shown = ovl && ovl.canvas ? ovl.canvas.innerText.trim() : undefined;
                return {
                    vertex: n.id, sort: ep.parameters.sort, label: ep.parameters.label,
                    type: shown || n.node.dataset["label:" + ep.parameters.sort + ":" + ep.parameters.label],
                };
            })),
        // The localStorage key a level's completion is recorded under, by name.
        completionKey: (name) => {
            const lvl = allLevels.find((l) => l.name === name);
            return lvl ? JSON.stringify(saveable(lvl)) : null;
        },
        // Set (null clears) one of a stage's unlock options -- "previous" or "bonus" -- by 1-based
        // world and stage number, and re-render.  Lets those rules be tested whether or not a stage
        // in levels.js currently declares them.
        setStageOption: (world, stage, option, value) => {
            const st = LEVELS[world - 1].stages[stage - 1];
            if(value === null) { delete st[option]; } else { st[option] = value; }
            updateLevelSelect(null);
        },
        // The same for one level's own options ("extrarules"), by 1-based world, stage and level
        // number.  A level's palette is built when it is opened, so open it after setting this.
        setLevelOption: (world, stage, level, option, value) => {
            const lvl = LEVELS[world - 1].stages[stage - 1].levels[level - 1];
            if(value === null) { delete lvl[option]; } else { lvl[option] = value; }
            updateLevelSelect(null);
        },
        // The same for a world's own options ("previous"), by 1-based world number.
        setWorldOption: (world, option, value) => {
            const w = LEVELS[world - 1];
            if(value === null) { delete w[option]; } else { w[option] = value; }
            updateLevelSelect(null);
        },
    };
}

// Going "Back" from the custom level-select sends us back to the non-custom list of levels.
document.getElementById("backLevel").onclick = function () {
    document.getElementById("levelSelectBG").style.display = "none";
    document.getElementById("levelChooseBG").style.display = "flex";
};

// Canceling either one clears the modal boxes and goes back to the current proof.
document.getElementById("cancelSetLevel").onclick = clearLevelSelect;
document.getElementById("cancelChooseLevel").onclick = clearLevelSelect;

// Open a level (switching worlds in the chooser if needed) -- used by the completion pop-up.
function goToLevel(level) {
    if(level.worldIndex !== currentWorld) { setWorld(level.worldIndex); }
    chooseLevel(level);
}

function levelStatesOf(level) {
    return levelDifficultyStates(level, getPast(null, level), unlockData);
}
function isLevelActive(level) { return levelStatesOf(level).includes('unlocked'); }
function isLevelSelectable(level) { return levelStatesOf(level)[0] !== 'locked'; }

// The two candidate targets for the completion pop-up's "Next": the next level in sequence (if
// it's unlocked at all), and the next "active" level scanning forward and wrapping around.
function computeNextTargets() {
    const i = allLevels.indexOf(currentLevel);
    if(i < 0) { return { seq: null, active: null }; }
    var seq = null;
    if(i + 1 < allLevels.length && isLevelSelectable(allLevels[i + 1])) {
        seq = allLevels[i + 1];
    }
    var active = null;
    for(var k = 1; k < allLevels.length; k++) {
        const lvl = allLevels[(i + k) % allLevels.length];
        if(isLevelActive(lvl)) { active = lvl; break; }
    }
    return { seq: seq, active: active };
}

// Show one "Next" button, or split into "Next" and "Next Unsolved", per the two targets.
var nextButtonTarget = null;
var nextUnsolvedTarget = null;
function configureNextButtons() {
    const targets = computeNextTargets();
    const nextBtn = document.getElementById("nextLevel");
    const unsolvedBtn = document.getElementById("nextUnsolved");
    if(targets.seq && targets.active && targets.seq !== targets.active) {
        nextButtonTarget = targets.seq;
        nextUnsolvedTarget = targets.active;
        nextBtn.style.display = '';
        unsolvedBtn.style.display = '';
    } else {
        nextButtonTarget = targets.seq || targets.active;
        nextUnsolvedTarget = null;
        nextBtn.style.display = nextButtonTarget ? '' : 'none';
        unsolvedBtn.style.display = 'none';
    }
}

document.getElementById("nextLevel").onclick = function() {
    document.getElementById("levelCompleteBanner").classList.remove("shown");
    if(nextButtonTarget) { goToLevel(nextButtonTarget); }
};
document.getElementById("nextUnsolved").onclick = function() {
    document.getElementById("levelCompleteBanner").classList.remove("shown");
    if(nextUnsolvedTarget) { goToLevel(nextUnsolvedTarget); }
};

// The "Select Level" button in the completion pop-up opens the level chooser.
document.getElementById("selectLevelAfterComplete").onclick = function() {
    document.getElementById("levelCompleteBanner").classList.remove("shown");
    document.getElementById("levelChooseBG").style.display = "flex";
};

// The modal box for prompting for a new variable name
document.getElementById("submitVariable").onclick = submitNewVariable;
document.getElementById("cancelVariable").onclick = cancelNewVariable;
document.getElementById('newvar').onkeypress = function(event) {
    if(event.key == 'Enter') {
        submitNewVariable();
    }
}

// Similarly for when the user is prompted for an ascription type
document.getElementById("submitAscribe").onclick = submitAscription;
document.getElementById("cancelAscribe").onclick = cancelAscription;
document.getElementById('ascribe').onkeypress = function(event) {
    if(event.key == 'Enter') {
        submitAscription();
    }
}

document.getElementById("submitExpression").onclick = submitExpr;
document.getElementById("cancelExpression").onclick = cancelExpr;
document.getElementById('expression').onkeypress = function(event) {
    if(event.key == 'Enter') {
        submitExpr();
    }
}

document.getElementById("submitWire").onclick = submitWireLabel;
document.getElementById('wire').onkeypress = function(event) {
    if(event.key == 'Enter') {
        submitWireLabel();
    }
}


// The "clear history" button from the pre-set levels forgets which levels have been solved in the past, and sends us back to the first world.
const clearHistory = document.getElementById("clearHistory");
if(SERVER) {
    clearHistory.innerText = "Log Out";
}
clearHistory.onclick = function () {
    if(SERVER || confirm("This will forget all your completed levels and difficulties!  Are you sure?")) {
        localStorage.clear();
        localStorage.setItem("visited",true);
        updateLevelSelect(null);
        setWorld(0);
        if(SERVER) {
            document.getElementById("levelChooseBG").style.display = "none";
            document.getElementById("levelSelectBG").style.display = "none";
            document.getElementById("loginBG").style.display = "flex";
        }
    }
};

var pendingDowngrade = null;
document.getElementById("reduceDifficulty").onclick = function () {
    if(difficulty === 0) { return; }
    const newDiff = difficulty - 1;
    // Capture any proof saved at the lower difficulty BEFORE the re-typecheck autosaves the
    // current proof over it.
    var oldState = null;
    const oldKey = savedProofKey(newDiff);
    const oldSaved = oldKey ? localStorage.getItem(oldKey) : null;
    if(oldSaved) { try { oldState = JSON.parse(oldSaved); } catch(e) { oldState = null; } }
    // Switch to the lower difficulty and re-check the current proof there (this autosaves it
    // at the lower difficulty's key).
    setDifficulty(newDiff);
    updateCurrentDifficulty();
    typecheck();
    // If there's a saved proof at the lower difficulty with real progress, let the player pick
    // between restoring it, keeping their current proof, or starting fresh.
    if(oldState && proofHasProgress(oldState)) {
        pendingDowngrade = oldState;
        document.getElementById("downgradeText").innerText =
            "You have a saved proof for this level at " + DIFFICULTIES[newDiff] + " difficulty.";
        document.getElementById("downgradeBG").style.display = "flex";
    }
}

document.getElementById("restoreSavedDowngrade").onclick = function() {
    document.getElementById("downgradeBG").style.display = "none";
    if(pendingDowngrade) {
        const state = pendingDowngrade;
        pendingDowngrade = null;
        // Loading the lower difficulty's saved (complete) proof counts as a fresh solve, so it
        // re-locks the higher difficulty (rule 7) the same as re-solving by hand would.
        restoreProof(state, undefined, true);
    }
};
document.getElementById("keepCurrentDowngrade").onclick = function() {
    // The current proof is already autosaved at the new difficulty; nothing to do.
    document.getElementById("downgradeBG").style.display = "none";
    pendingDowngrade = null;
};
document.getElementById("freshDowngrade").onclick = function() {
    document.getElementById("downgradeBG").style.display = "none";
    pendingDowngrade = null;
    const key = savedProofKey();
    if(key) { localStorage.removeItem(key); }
    reopenCurrentLevel();
}

function updateCurrentDifficulty() {
    document.getElementById("currentDifficulty").innerText = "Difficulty: " + DIFFICULTIES[difficulty];
    const reduceDifficulty = document.getElementById("reduceDifficulty");
    if(difficulty > 0) {
        reduceDifficulty.innerText = "Reduce to " + DIFFICULTIES[difficulty-1];
        reduceDifficulty.style.display = 'block';
    } else {
        reduceDifficulty.style.display = 'none';
    }
}

// === Block budgets ("maxrules") ===

// Whether the level currently loaded sets a block budget at all.
function hasBlockBudget() {
    return currentMaxRules !== null && currentMaxRules !== undefined;
}

// How many blocks the player has added: everything in the diagram except the variable, hypothesis
// and conclusion blocks the level was laid out with.
function blocksUsed() {
    return nodes.filter(function (x) { return !FIXED_RULES.includes(x.rule); }).length;
}

// The block count as it is shown to the player: used out of budget.
function blockTally() {
    return blocksUsed() + "/" + currentMaxRules;
}

// Whether the proof is over the current level's block budget.  A level with no budget never is.
function overBlockBudget() {
    return hasBlockBudget() && blocksUsed() > currentMaxRules;
}

// Update the top-center block count of a budgeted level.  It stands until the level is finished,
// when the completion pop-up takes its place (and carries the final count itself) -- except that
// going over budget keeps it up, in red, whether or not the proof would otherwise be correct.  A
// level with no budget never shows it.
function updateBlockBanner() {
    const banner = document.getElementById("blockCountBanner");
    const over = overBlockBudget();
    if(!hasBlockBudget() || (proofIsComplete() && !over)) {
        banner.classList.remove("shown");
        return;
    }
    banner.innerText = over ? "Too many blocks!  Used: " + blockTally() : "Blocks used: " + blockTally();
    banner.classList.toggle("over", over);
    banner.classList.add("shown");
}

function hideBlockBanner() {
    document.getElementById("blockCountBanner").classList.remove("shown");
}

// Show a hint by its id.  Only showing it on the level itself records that it's been seen: a hint
// read from the chooser is browsing, and shouldn't cost the player the greeting when they get
// there.
function showHintById(hint) {
    document.getElementById("hintBG").style.display = 'flex';
    document.getElementById(hint).style.display = 'block';
}

function showHint() {
    showHintById(currentHint);
    localStorage.setItem(currentHint, "true");
}

document.getElementById("showHint").onclick = showHint;

// show and hide the about box
// The "Custom" button switches from the level chooser to the custom-level dialog.
document.getElementById("customLevel").onclick = function () {
    document.getElementById("customName").value = "";
    document.getElementById("levelChooseBG").style.display = "none";
    document.getElementById("levelSelectBG").style.display = "flex";
};

// Fill the custom-level dialog's fields from a level definition (built-in or custom).
function fillCustomDialog(level) {
    document.getElementById("parameters").value =
        level.parameters.map(function (p) { return p.name + " : " + p.ty; }).join("\n");
    document.getElementById("variables").value =
        level.variables.map(function (v) { return v.name + " ∈ " + v.ty; }).join("\n");
    document.getElementById("hypotheses").value =
        level.hypotheses.map(function (h) { return h.ty; }).join("\n");
    document.getElementById("conclusion").value = level.conclusion.ty;
}

// "Edit" opens the custom-level dialog pre-filled with the current level's definition, so the
// player can tweak it.  Submitting the (possibly edited) dialog creates a custom level.
document.getElementById("editLevel").onclick = function () {
    if(!currentLevelDef) { return; }
    fillCustomDialog(currentLevelDef);
    // Pre-fill the name when editing an already-saved custom level, so re-submitting re-saves it.
    document.getElementById("customName").value = currentCustom ? currentCustom.name : "";
    document.getElementById("levelChooseBG").style.display = "none";
    document.getElementById("levelSelectBG").style.display = "flex";
};

// ===== Saved custom levels =====

function loadCustomLevels() {
    try { return JSON.parse(localStorage.getItem("customLevels")) || []; }
    catch(e) { return []; }
}
function storeCustomLevels(list) {
    localStorage.setItem("customLevels", JSON.stringify(list));
}

// A clean copy of just a level's definition fields (no ids or other props), for storing.
function levelDefCopy(def) {
    return {
        parameters: def.parameters.map(function (p) { return { name: p.name, ty: p.ty }; }),
        variables: def.variables.map(function (v) { return { name: v.name, ty: v.ty }; }),
        hypotheses: def.hypotheses.map(function (h) { return { ty: h.ty }; }),
        conclusion: { ty: def.conclusion.ty },
    };
}

// A saved custom level's per-difficulty states: it's unlocked up to the difficulty it was saved at
// (and all lower), completing one difficulty unlocks the next, and completed ones show a star.
function customStates(cl) {
    const states = [];
    for(var K = 0; K < 3; K++) {
        if(cl.completed[K]) { states.push('completed'); }
        else if(K <= cl.unlockDifficulty || (K >= 1 && cl.completed[K - 1])) { states.push('unlocked'); }
        else { states.push('locked'); }
    }
    return states;
}

// Show the lower-left "Save" button only when a custom level is loaded (built-in currentLevel unset
// but a definition is present).
function updateSaveButtonVisibility() {
    document.getElementById("saveLevel").style.display = (!currentLevel && currentLevelDef) ? '' : 'none';
}

// Record that a saved custom level was completed at a difficulty (persisting it and re-rendering).
function markCustomCompleted(cl, d) {
    cl.completed[d] = true;
    const list = loadCustomLevels();
    const stored = list.find(function (c) { return c.id === cl.id; });
    if(stored) {
        stored.completed[d] = true;
        storeCustomLevels(list);
    }
    refreshCustomWorld();
}

// Prompt for a name and save the current custom level: stored as unlocked at the current difficulty
// (and all lower).  Re-saving under an existing name updates that level's definition.
function saveCustomLevel() {
    if(currentLevel || !currentLevelDef) { return; }
    const suggested = currentCustom ? currentCustom.name : "";
    const input = prompt("Name for this custom level:", suggested);
    if(input === null) { return; }
    const name = input.trim();
    if(!name) { return; }
    saveCustomLevelNamed(name);
}

// Store a custom level with the given (already non-empty) name and definition, unlocked at the
// given difficulty (and all lower).  Re-using an existing name updates that level's statement,
// keeping its id and completion record.  Returns the stored level.
function storeCustomLevelNamed(name, def, unlockDifficulty) {
    const list = loadCustomLevels();
    var cl = list.find(function (c) { return c.name === name; });
    if(cl) {
        cl.parameters = def.parameters; cl.variables = def.variables;
        cl.hypotheses = def.hypotheses; cl.conclusion = def.conclusion;
        cl.unlockDifficulty = Math.max(cl.unlockDifficulty || 0, unlockDifficulty);
    } else {
        cl = {
            id: "c" + Date.now() + Math.floor(Math.random() * 100000),
            name: name,
            parameters: def.parameters, variables: def.variables,
            hypotheses: def.hypotheses, conclusion: def.conclusion,
            unlockDifficulty: unlockDifficulty,
            completed: [false, false, false],
        };
        list.push(cl);
    }
    storeCustomLevels(list);
    return cl;
}

// Save the current custom level under the given (already non-empty) name, without prompting.  Used
// by the Save button (via saveCustomLevel) and by the custom dialog's optional Name field.
function saveCustomLevelNamed(name) {
    if(currentLevel || !currentLevelDef) { return; }
    const cl = storeCustomLevelNamed(name, levelDefCopy(currentLevelDef), difficulty);
    currentCustom = cl;
    document.getElementById("currentLevel").innerText = "Level: " + cl.name;
    updateSaveButtonVisibility();
    document.getElementById("saveLevelAfterComplete").style.display =
        (!currentLevel && currentLevelDef) ? '' : 'none';
    refreshCustomWorld();
    autosave(); // keep the current proof under the now-saved level's key
}

// Open a saved custom level at its highest unlocked difficulty, or (with keepDifficulty) at
// whatever difficulty is currently set, for re-opening the level we're already on.
function openCustomLevel(cl, skipSavedPrompt, keepDifficulty) {
    if(!keepDifficulty) {
        const states = customStates(cl);
        var d = 0;
        for(var i = 0; i < 3; i++) { if(states[i] !== 'locked') { d = i; } }
        setDifficulty(d);
    }
    if(!setLevel(levelDefCopy(cl), "all")) { return; }
    currentCustom = cl;
    currentLevel = undefined;
    currentLevelButton = undefined;
    document.getElementById("currentLevel").innerText = "Level: " + cl.name;
    updateSaveButtonVisibility();
    if(!skipSavedPrompt) { offerSavedProof(null); }
}

// Re-set-up whichever level is currently open -- built-in, saved custom, or unsaved custom --
// recreating its fixed nodes and discarding the current diagram, without prompting about a saved
// proof.  The difficulty is left alone, so this can't bump a reduced one back up.  Returns false
// if no level is open at all.
function reopenCurrentLevel() {
    if(currentCustom) { openCustomLevel(currentCustom, true, true); }
    else if(currentLevel) { selectCurrentLevel(currentLevel, true); }
    else if(currentLevelDef) { setLevel(levelDefCopy(currentLevelDef), "all"); }
    else { return false; }
    return true;
}

// Delete a saved custom level (with confirmation).
function deleteCustomLevel(cl) {
    if(!confirm('Delete the custom level "' + cl.name + '"?')) { return; }
    storeCustomLevels(loadCustomLevels().filter(function (c) { return c.id !== cl.id; }));
    if(currentCustom && currentCustom.id === cl.id) {
        currentCustom = null;
        updateSaveButtonVisibility();
    }
    refreshCustomWorld();
}

// (Re)render the "Custom" world's rows from the saved list, and update its chip count.
function refreshCustomWorld() {
    if(!customRowsContainer) { return; }
    const list = loadCustomLevels();
    customRowsContainer.innerHTML = '';
    if(list.length === 0) {
        const empty = document.createElement("div");
        empty.className = "custom-empty";
        empty.innerText = "No saved custom levels yet. Build one with Custom or Edit, then Save it.";
        customRowsContainer.appendChild(empty);
    } else {
        list.forEach(function (cl) {
            const states = customStates(cl);
            const row = document.createElement("div");
            row.className = "custom-row";
            const nameEl = document.createElement("span");
            nameEl.className = "custom-name";
            nameEl.innerText = cl.name;
            const marks = document.createElement("span");
            marks.className = "custom-marks";
            marks.innerHTML = difficultyMark(states[0], 0) + difficultyMark(states[1], 1) + difficultyMark(states[2], 2);
            const del = document.createElement("span");
            del.className = "custom-delete";
            del.innerHTML = "&#10005;";
            del.title = "Delete this custom level";
            del.onclick = function (e) { e.stopPropagation(); deleteCustomLevel(cl); };
            row.appendChild(nameEl);
            row.appendChild(marks);
            row.appendChild(del);
            row.onclick = function () { openCustomLevel(cl); };
            customRowsContainer.appendChild(row);
        });
    }
    if(customChipEl) {
        const prog = customChipEl.querySelector('.world-progress');
        if(prog) { prog.innerText = list.filter(function (c) { return c.completed[0]; }).length + '/' + list.length; }
    }
}

document.getElementById("saveLevel").onclick = saveCustomLevel;
document.getElementById("saveLevelAfterComplete").onclick = saveCustomLevel;

document.getElementById("about").onclick = function () {
    document.getElementById("aboutBG").style.display = "flex";
};
document.getElementById("doneAbout").onclick = function () {
    document.getElementById("aboutBG").style.display = "none";
};

document.getElementById("doneUnlock").onclick = function () {
    document.getElementById("unlockBG").style.display = "none";
};

function selectCurrentLevel(level, skipSavedPrompt) {
    // The palette holds this level's stage's rules, plus any the level itself asks for on top of
    // them (`extrarules`), plus any the ?rules= query string added.
    if(!setLevel(level, level.stage.rules.concat(level.extrarules || [], extraRules))) { return; }
    currentLevel = level;
    currentLevelButton = level.button;
    currentCustom = null;
    updateSaveButtonVisibility();
    document.getElementById("currentLevel").innerText = "Level: " + level.name;
    // If there's an autosaved proof for this level, offer to reload it (unless we're already
    // in the middle of restoring/importing a specific proof, which passes skipSavedPrompt).
    if(!skipSavedPrompt) {
        offerSavedProof(level);
    }
}

// Open a level chosen from the chooser, starting at the highest difficulty unlocked for it (the
// in-level "Reduce difficulty" button can drop lower).  A fully locked level isn't selectable.
// In test mode, enforcement is skipped and the level opens at the current difficulty.
function chooseLevel(level) {
    if(!TEST_MODE) {
        const states = levelDifficultyStates(level, getPast(null, level), unlockData);
        if(states[0] === 'locked') { return; }
        var d = 0;
        for(var i = 0; i < 3; i++) { if(states[i] !== 'locked') { d = i; } }
        setDifficulty(d);
    }
    selectCurrentLevel(level);
}

// Add a close button to a box
function addBoxCloseButton(box) {
    const closebutton = document.createElement("div");
    closebutton.className = "closebutton";
    closebutton.innerText = "X";
    closebutton.addEventListener('click', function () { deleteRule(box) });
    box.appendChild(closebutton);
}

function deleteRule(box) {
    suppressChecking = true;
    if(box.dataset.variable) {
        varnames = varnames.filter(function(x) { return x !== box.dataset.variable })
    }
    nodes = nodes.filter(function (x) { return x.node !== box });
    instance.deleteConnectionsForElement(box);
    instance.removeAllEndpoints(box);
    box.remove();
    // Removing a far-out node may let the canvas shrink back toward the viewport.
    resizeCanvas();
    suppressChecking = false;
    typecheck();
}

// When a node needs a new bound variable, we prompt the user with a modal dialog.
// Renaming a bound variable renames the binder, but not any of the places the player has written a
// name out by hand: the text in an expression or ascription box, or a type typed on a wire (which
// only happens at adept and master).  We don't try to substitute into those, so if the proof has
// any of them, say so -- without checking whether this particular variable is used there, since
// the point is to prompt a look rather than to be exhaustive.
function renameWarningText() {
    const boxes = nodes.some(function (x) { return x.rule === 'asc' || x.rule === 'expr'; });
    const wires = difficulty > 0;
    if(!boxes && !wires) { return ""; }
    const places =
        boxes && wires ? "your expression and ascription boxes, and the types you've written on wires"
        : boxes ? "your expression and ascription boxes"
        : "the types you've written on wires";
    return "Renaming changes where the variable is bound, but not " + places +
        ".  If any of them mention the old name, you'll need to change them yourself.";
}

function openVariableDialog(id, current, editing) {
    const variableBG = document.getElementById("variableBG");
    const variableList = document.getElementById("variableList");
    const newvar = document.getElementById('newvar');

    variableBG.style.display = "flex";
    // A rename can leave hand-written names behind; a brand-new variable has no old name to leave.
    const warning = document.getElementById("renameWarning");
    const caution = editing ? renameWarningText() : "";
    warning.innerText = caution;
    warning.classList.toggle("shown", caution !== "");
    // The names already taken -- not counting the one we're renaming, which is up for grabs.
    const taken = varnames.filter(function (v) { return v !== current; });
    variableList.innerText = taken.length > 0 ? taken.join(" ") : "<none>";
    newvar.dataset.name = id;
    // Cancelling an edit leaves the box alone; cancelling a brand-new one removes it.
    newvar.dataset.editing = editing ? "true" : "";
    newvar.value = current;
    newvar.focus();
    newvar.select();
}

// Prompt for the variable a newly added ∀-introduction or ∃-elimination binds.
function getVariable(id) {
    openVariableDialog(id, '', false);
}

// Re-open that dialog on a box that already binds one, to rename it.  Double-clicking does this.
function editVariable(box) {
    openVariableDialog(box.id, box.dataset.variable || '', true);
}

// When that modal dialog is submitted, we save the variable name and hide it.
function submitNewVariable() {
    const variableBG = document.getElementById("variableBG");
    const newvar = document.getElementById('newvar');
    const box = document.getElementById(newvar.dataset.name);
    // When renaming, the name this box binds now is the one being replaced, so it isn't taken.
    const previous = newvar.dataset.editing === "true" ? box.dataset.variable : undefined;

    if(!Narya.checkVariable(newvar.value).complete) {
        alert("Invalid variable name");
        newvar.focus();
    } else if(varnames.includes(newvar.value) && newvar.value !== previous) {
        // Enforce the Barendregt convention.
        alert("New variable name must be different from all existing variables");
        newvar.focus();
    } else {
        // Save it in the list of variable names, in place of the one it replaces
        if(previous !== undefined) {
            varnames = varnames.filter(function (v) { return v !== previous; });
        }
        varnames.push(newvar.value);
        // Attach it to the node that prompted for it.  NOTE: This doesn't allow a single node to contain more than one variable name.
        for (var i in nodes) {
            if (nodes[i].id === newvar.dataset.name) {
                nodes[i].name = newvar.value;
            }
        }
        // Save the variable associated to the rule box.  This allows us to remove it from the global list of used variables when that rule is deleted.
        box.dataset.variable = newvar.value;
        // And empty and hide the modal dialog
        newvar.value = '';
        newvar.dataset.editing = "";
        variableBG.style.display = "none";
        // And typecheck: either that was delayed when the rule was added, or the name just changed.
        typecheck();
    }
}

function cancelNewVariable() {
    const variableBG = document.getElementById("variableBG");
    const newvar = document.getElementById('newvar');
    // Cancelling the prompt for a new box means it was never made, so it goes away; cancelling a
    // rename of an existing one leaves it (and its wires) exactly as they were.
    if(newvar.dataset.editing !== "true") {
        for (var i in nodes) {
            if (nodes[i].id === newvar.dataset.name) {
                deleteRule(nodes[i].node);
            }
        }
    }
    newvar.value = '';
    newvar.dataset.editing = "";
    variableBG.style.display = "none";
}

// Similarly, submit the modal box that prompts for an ascription
// Re-open the ascription dialog on a box that already has a type, so it can be corrected in place
// instead of deleting the box and wiring a new one up.  Double-clicking a box does this.
function editAscription(box) {
    const ascribe = document.getElementById('ascribe');
    const node = nodes.find(function (x) { return x.id === box.id; });
    ascribe.dataset.name = box.id;
    // Cancelling an edit leaves the box alone; cancelling a brand-new one removes it.
    ascribe.dataset.editing = "true";
    ascribe.value = (node && node.value) || '';
    document.getElementById("ascribeBG").style.display = "flex";
    ascribe.focus();
    ascribe.select();
}

function submitAscription() {
    const ascribeBG = document.getElementById("ascribeBG");
    const ascribe = document.getElementById('ascribe');
    const box = document.getElementById(ascribe.dataset.name);
    const ty = ascribe.value;
    if(!Narya.checkParse(ty).complete) {
        alert("Invalid ascription");
        return;
    }
    // We attach it to the node that asked for it, and label that node with it as well
    for (var i in nodes) {
        if (nodes[i].id === ascribe.dataset.name) {
            nodes[i].value = ty;
        }
    }
    box.innerHTML = "🏷&nbsp;" + ascribe.value;
    box.style.width = 'fit-content';
    // That blew away the close button, so we add it back.
    addBoxCloseButton(box);
    box.style.padding = "0px 8px 0px 8px"
    // And empty and hide the modal dialog
    ascribe.value = '';
    ascribe.dataset.editing = "";
    ascribeBG.style.display = "none";
    // And typecheck: either that was delayed when the rule was added, or the type just changed.
    typecheck();
}

function cancelAscription() {
    const ascribeBG = document.getElementById("ascribeBG");
    const ascribe = document.getElementById('ascribe');
    // Cancelling the prompt for a new box means it was never made, so it goes away; cancelling an
    // edit of an existing one leaves it (and its wires) exactly as they were.
    if(ascribe.dataset.editing !== "true") {
        for (var i in nodes) {
            if (nodes[i].id === ascribe.dataset.name) {
                deleteRule(nodes[i].node);
            }
        }
    }
    ascribe.value = '';
    ascribe.dataset.editing = "";
    ascribeBG.style.display = "none";
}

// Re-open the expression dialog on a box that already has one, so an expression can be corrected
// in place instead of deleting the box and wiring a new one up.  Double-clicking a box does this.
function editExpr(box) {
    const expr = document.getElementById('expression');
    const node = nodes.find(function (x) { return x.id === box.id; });
    expr.dataset.name = box.id;
    // Cancelling an edit leaves the box alone; cancelling a brand-new one removes it (cancelExpr).
    expr.dataset.editing = "true";
    expr.value = (node && node.value) || '';
    document.getElementById("expressionBG").style.display = "flex";
    expr.focus();
    expr.select();
}

// And the modal box that prompts for an expression
function submitExpr() {
    const exprBG = document.getElementById("expressionBG");
    const expr = document.getElementById('expression');
    const box = document.getElementById(expr.dataset.name);
    const e = expr.value;
    if(!Narya.checkParse(e).complete) {
        alert("Invalid expression");
        return;
    }
    // We attach it to the node that asked for it, and label that node with it as well
    for (var i in nodes) {
        if (nodes[i].id === expr.dataset.name) {
            nodes[i].value = e;
        }
    }
    box.innerHTML = expr.value;
    box.style.width = 'fit-content';
    // That blew away the close button, so we add it back.
    addBoxCloseButton(box);
    box.style.padding = "0px 8px 0px 8px"
    // And empty and hide the modal dialog
    expr.value = '';
    expr.dataset.editing = "";
    exprBG.style.display = "none";
    // And typecheck: either that was delayed when the rule was added, or the expression just changed.
    typecheck();
}

function cancelExpr() {
    const exprBG = document.getElementById("expressionBG");
    const expr = document.getElementById('expression');
    // Cancelling the prompt for a new box means it was never made, so it goes away; cancelling an
    // edit of an existing one leaves it (and its wires) exactly as they were.
    if(expr.dataset.editing !== "true") {
        for (var i in nodes) {
            if (nodes[i].id === expr.dataset.name) {
                deleteRule(nodes[i].node);
            }
        }
    }
    expr.value = '';
    expr.dataset.editing = "";
    exprBG.style.display = "none";
}

// Attach a user-supplied label `ty` to a wire (connection), replacing any existing label overlay.
function setUserWireLabel(edge, ty) {
    edge.removeOverlay("label");
    edge.removeOverlay("userLabel");
    edge.addOverlay({ type: "Custom", options: {
        id: "userLabel",
        create: (e) => {
            const d = document.createElement("div");
            d.className = "connLabel userLabel";
            d.innerText = ty;
            d.onclick = function () { getUserLabel(edge); }
            edge.parameters.userLabel = d;
            return d;
        },
    } });
    edge.parameters.ty = ty;
    instance.revalidate(edge.source);
}

// And the modal box that prompts for a wire label
function submitWireLabel() {
    const wire = document.getElementById('wire');
    const ty = wire.value;
    if(ty === "") {
        alert("Invalid label");
        return;
    }
    const source = document.getElementById(wire.dataset.source);
    const target = document.getElementById(wire.dataset.target);
    instance.getConnections({ source: source, target: target }).forEach(function (edge) {
        if(edge.endpoints[0].parameters.sort === wire.dataset.sourceSort &&
           edge.endpoints[0].parameters.label === wire.dataset.sourceLabel &&
           edge.endpoints[1].parameters.sort === wire.dataset.targetSort &&
           edge.endpoints[1].parameters.label === wire.dataset.targetLabel) {
            setUserWireLabel(edge, ty);
        }
    });
    // And empty and hide the modal dialog
    wire.value = '';
    document.getElementById("wireBG").style.display = "none";
    // And finally typecheck!
    typecheck();
}

// The custom level-select dialog, and the type ascription and wire label dialog boxes, have a palette of unicode characters below each text box, and a link to the help dialog listing the shortcut keys.

function insert(elt, str) {
    const i = elt.selectionStart + 1;
    elt.setRangeText(str);
    elt.focus();
    elt.setSelectionRange(i,i);
}

function addToPalette(pal, elt, str) {
    var b = document.createElement('div');
    b.className = "unicode-button";
    b.textContent = str;
    b.addEventListener('click', function() { insert(elt, str) });
    b.tabIndex = "0";
    b.onkeypress = function(event) {
        if(event.key == 'Enter') {
            insert(elt, str);
        }
    };
    pal.appendChild(b);
}

function makePalette(palid, eltid, chars) {
    const pal = document.getElementById(palid);
    const elt = document.getElementById(eltid);
    // Create palette of buttons
    (chars || PALETTE).forEach((chr) => addToPalette(pal, elt, chr));
    // Add TeX help button
    var t = document.createElement('div');
    t.textContent = 'or use';
    t.style.position = 'relative';
    t.style.display = 'inline-block';
    t.margin = '2px';
    pal.appendChild(t);
    var b = document.createElement('div');
    b.className = "unicode-button";
    b.style.width = '80px';
    b.textContent = 'shortcuts';
    b.addEventListener('click', function() {
        document.getElementById("shortcutsBG").style.display = 'flex';
    });
    pal.appendChild(b);
    addShortcuts(eltid);
}

// Replace every shortcut key sequence in a string with the character it stands for.
function substituteShortcuts(str) {
    KEYS.forEach(function (entry) {
        entry.regexes.forEach(function (re) {
            str = str.replace(re, entry.unicode);
        });
    });
    return str;
}

// Detect shortcut key sequences in a text box
function addShortcuts(eltid) {
    const elt = document.getElementById(eltid);
    elt.addEventListener('input', () => {
        const text = substituteShortcuts(elt.value);
        // Leave the box alone when there was nothing to replace, so that ordinary typing never
        // goes near the cursor.
        if(text === elt.value) { return; }
        // Assigning to value drops the cursor at the end of the box, so work out where it belongs
        // first: at the end of whatever preceded it, once that has been through the same
        // substitutions, since they are what changed its length.
        const caret = substituteShortcuts(elt.value.slice(0, elt.selectionStart)).length;
        elt.value = text;
        elt.setSelectionRange(caret, caret);
    });
}

makePalette('paramPalette', 'parameters');
makePalette('varPalette', 'variables');
makePalette('hypPalette', 'hypotheses');
makePalette('conclPalette', 'conclusion');
makePalette('ascPalette', 'ascribe');
makePalette('wirePalette', 'wire');
makePalette('exprPalette', 'expression', EXPR_PALETTE);

var shortcuts = document.getElementById('shortcuts');
var shortcut_thead = document.createElement('thead');
var shortcut_tr = document.createElement('tr');
var shortcut_symlabel = document.createElement('td');
shortcut_symlabel.innerHTML = '<b>Symbol</b>';
shortcut_tr.appendChild(shortcut_symlabel);
var shortcut_keyslabel = document.createElement('td');
shortcut_keyslabel.innerHTML = '<b>Key sequences</b>';
shortcut_keyslabel.style.paddingLeft = '20px';
shortcut_tr.appendChild(shortcut_keyslabel);
shortcut_thead.appendChild(shortcut_tr);
shortcuts.appendChild(shortcut_thead);
var shortcut_tbody = document.createElement('tbody');
KEYS.forEach(function(entry) {
    var tr = document.createElement('tr');
    var sym = document.createElement('td');
    sym.innerText = entry.unicode;
    sym.className = 'symbol';
    tr.appendChild(sym);
    var keys = '';
    entry.keys.forEach(function(seq) {
        if(keys) {
            keys = keys + ', ';
        }
        keys = keys + seq;
    });
    var keylist = document.createElement('td');
    keylist.innerText = keys;
    keylist.className = 'keyseq';
    tr.appendChild(keylist);
    shortcut_tbody.appendChild(tr);
});
shortcuts.appendChild(shortcut_tbody);

document.getElementById("shortcutsBG").onclick = function() {
    document.getElementById("shortcutsBG").style.display = 'none';
};

// Resizing bracket boxes
let isResizingRight = false;
let isResizingLeft = false;
let currentResizable = null;  // Which element is being resized
let lastX = 0;
let resizingLocked = false;
let resizeLockX = 0;

// Make a node resizable
function makeResizable(element) {
    element.querySelectorAll('.resize-image').forEach(function (img) {
        img.style.display = 'block';
    });
    const handleRight = element.querySelector('.resize-handle-right');
    handleRight.style.cursor = 'ew-resize';
    handleRight.addEventListener('mousedown', (e) => {
        e.preventDefault();
        isResizingRight = true;
        currentResizable = element;
        lastX = e.clientX;
        resizingLocked = false;
        resizeLockX = 0;
    });
    const handleLeft = element.querySelector('.resize-handle-left');
    handleLeft.style.cursor = 'ew-resize';
    handleLeft.addEventListener('mousedown', (e) => {
        e.preventDefault();
        isResizingLeft = true;
        currentResizable = element;
        lastX = e.clientX;
        resizingLocked = false;
        resizeLockX = 0;
    });
}

document.addEventListener('mousemove', (e) => {
    if (isResizingRight && currentResizable) {
        const dx = e.clientX - lastX;
        const style = window.getComputedStyle(currentResizable);
        const currentWidth = parseInt(style.width, 10);
        const currentLeft = parseInt(style.left, 10);
        var newWidth = currentWidth + dx;
        if(resizingLocked) {
            newWidth = 100;
            if(e.clientX > resizeLockX) {
                resizingLocked = false;
            }
        } else if(newWidth < 100) {
            newWidth = 100;
            resizingLocked = true;
            resizeLockX = e.clientX;
        }
        currentResizable.style.width = newWidth + 'px';
        lastX = e.clientX;
    } else if(isResizingLeft && currentResizable) {
        const dx = e.clientX - lastX;
        const style = window.getComputedStyle(currentResizable);
        const currentWidth = parseInt(style.width, 10);
        const currentLeft = parseInt(style.left, 10);
        // dx has its sign flipped in this case
        var newWidth = currentWidth - dx;
        // Also shift left, so the right edge stays put
        var newLeft = currentLeft + dx;
        if(resizingLocked) {
            newWidth = 100;
            newLeft = currentLeft;
            if(e.clientX < resizeLockX) {
                resizingLocked = false;
            }
        } else if(newWidth < 100) {
            newWidth = 100;
            newLeft = currentLeft;
            resizingLocked = true;
            resizeLockX = e.clientX;
        }
        currentResizable.style.width = newWidth + 'px';
        currentResizable.style.left = newLeft + 'px';
        lastX = e.clientX;
    }
});

// Stop resizing on mouseup anywhere in the document
document.addEventListener('mouseup', () => {
    isResizingRight = false;
    isResizingLeft = false;
    currentResizable = null;
});


// A wire marked red carries the reason in its parameters; while the pointer is over it, say so.
// Narya's own text is the fallback for the errors Explain doesn't have a student-facing version
// of, so a red wire always explains itself somehow.
function showWireTooltip(conn, e) {
    const text = conn.parameters.errorText;
    if(!text) { return; }
    const tip = document.getElementById("wireTooltip");
    // textContent, not innerText: the newlines are rendered by the pre-wrap on #wireTooltip, and
    // innerText would replace them with <br> and lose the indentation.
    tip.textContent = text;
    tip.style.display = 'block';
    // Follow the pointer, falling back to the middle of the wire if the event carries no position.
    var x, y;
    if(e && typeof e.clientX === 'number') {
        x = e.clientX + 14;
        y = e.clientY + 16;
    } else {
        const r = conn.connector.canvas.getBoundingClientRect();
        x = r.left + r.width / 2;
        y = r.top + r.height / 2 + 16;
    }
    // Keep it on screen (it's already displayed, so it can be measured).
    const tr = tip.getBoundingClientRect();
    tip.style.left = Math.max(4, Math.min(x, window.innerWidth - tr.width - 4)) + 'px';
    tip.style.top = Math.max(4, Math.min(y, window.innerHeight - tr.height - 4)) + 'px';
}

function hideWireTooltip() {
    document.getElementById("wireTooltip").style.display = 'none';
}

// Set the color of a connection
function setStrokeColor(conn, color) {
    const sty = conn.getPaintStyle();
    const hsty = conn.getHoverPaintStyle();
    sty.stroke = color;
    hsty.stroke = color;
    conn.setPaintStyle(sty);
    conn.setHoverPaintStyle(sty);
}

function getUserLabel(edge) {
    const wireBG = document.getElementById("wireBG");
    const wire = document.getElementById("wire");
    wireBG.style.display = 'flex';
    wire.dataset.source = edge.source.id;
    wire.dataset.sourceSort = edge.endpoints[0].parameters.sort;
    if(edge.endpoints[0].parameters.label) {
        wire.dataset.sourceLabel = edge.endpoints[0].parameters.label;
    } else {
        delete wire.dataset.sourceLabel;
    }
    wire.dataset.target = edge.target.id;
    wire.dataset.targetSort = edge.endpoints[1].parameters.sort;
    if(edge.endpoints[1].parameters.label) {
        wire.dataset.targetLabel = edge.endpoints[1].parameters.label;
    } else {
        delete wire.dataset.targetLabel;
    }
    if(edge.parameters.ty) {
        wire.value = edge.parameters.ty;
    }
    wire.focus();
}

function addConnection(params) {
    const edge = params.connection;
    // While restoring a saved proof, we set the wire labels ourselves and typecheck once at the end, so we skip the prompt/typecheck here (but still apply the connector styling below).
    if(!restoring) {
        // If we're on novice difficulty, or the wire connects to a hypothesis or conclusion, or carries a value, we just go ahead and typecheck.
        if(difficulty === 0 ||
           nodes.some(function (x) {
               const ishyp = (x.id === edge.source.id && (x.rule === 'hypothesis' || x.rule === 'variable'));
               const isconcl = (x.id === edge.target.id && x.rule === 'conclusion');
               const hasval = edge.endpoints[0].parameters.hasValue;
               return (ishyp || isconcl || hasval);
           })) {
            typecheck();
        } else {
            // Otherwise, we first prompt the user for a label for the new wire.
            getUserLabel(edge);
        }
    }
    // Connections going straight across from an assumption to a subgoal should be straight.  The flowchart connector bends them out for some reason.
    if(edge.source == edge.target) {
        // A subgoal's label names the branch it belongs to, so an assumption reaches it when the
        // two agree.  A block with only one subgoal leaves it unlabelled, and then every
        // assumption of the block reaches it whatever its own label -- the ∀x∈ℝ₊ and ∀x∈[n] blocks
        // bind the condition defining their set on a labelled port beside the unlabelled one that
        // binds the variable.
        const from = edge.endpoints[0].parameters, to = edge.endpoints[1].parameters;
        if(from.sort === 'assumption' && to.sort === 'subgoal' &&
           (to.label === undefined || from.label === to.label)) {
            // This method isn't published in the jsPlumb community edition, but it's still there!
            edge._setConnector(StraightConnector.type);
        } else {
            // Other cyclic connections are ill-typed, but should at least be displayed looking okay, and Bezier connectors can't handle it.
            edge._setConnector(FlowchartConnector.type);
        }
    } else {
        // If the target of a connection is moved to be non-cyclic, reset it to the selected style.
        if(document.getElementById("angleConnectors").checked) {
            edge._setConnector(FlowchartConnector.type);
        } else if(document.getElementById("curvedConnectors").checked) {
            edge._setConnector(BezierConnector.type);
        }
    }
    // For some reason setting the connector type blows away the Arrow overlay, although it doesn't affect the Custom close-button overlay.
    edge.addOverlay({
        type: "Arrow",
        options: {
            location: -5,
            width: 10,
            length: 10,
        },
    });
}

// Parse the graph into a term and typecheck it, displaying diagnostics.  If 'remove' is true, also remove the connection indicated by the parameters, as this is a detach event.  Since we need to pass the result as an onclick callback, we manually curry the definition.
function typecheck() {
    if(suppressChecking) { return; }
    // Wait for the round already in flight (see typecheckPending); it will come back here with the
    // diagram as it stands then.
    if(typecheckPending) { typecheckAgain = true; return; }
    typecheckPending = true;
    typecheckAgain = false;

    document.getElementById("typecheckingBG").style.display = 'flex';
    hideWireTooltip();

    console.log("typechecking with " + nodes.length + " nodes");
    var connctr = 0;
    var connections = {};

    // Compute the list of all edges as {id:string, source:{vertex, sort, label}, target:{vertex, sort, label}, hasValue:bool, connector} objects.
    const edges = instance.getConnections().map(function (c) {
        const conn_id = 'conn' + (connctr++);
        connections[conn_id] = c;

        // Reset all the colors of the edges according to their hasValue
        if(c.endpoints[0].parameters.hasValue) {
            setStrokeColor(c, VALUECOLOR);
        } else {
            setStrokeColor(c, "#000000");
        }
        // And the color of the label, if any
        if(c.parameters.userLabel) {
            c.parameters.userLabel.style.color = '';
        }
        // Last time's error is no longer this wire's, whatever this typecheck decides.
        c.parameters.errorText = undefined;
        instance.revalidate(c.source);

        // Clear the label overlays.  For some reason, if we *delete* all the overlays here and then add later the ones we want, some of them don't get displayed until the nodes are dragged around.  So instead we set the label text of all existing overlays to empty here, and later we delete only the overlays with empty label text.
        // TODO: Try deleting them and then calling revalidate later.
        const ovl = c.getOverlay("label");
        if(!c.parameters.ty && ovl) {
            ovl.setLabel("");
        }
        // The two ends of a type-mismatch label belong to the error we're about to recompute.
        MISMATCH_LABELS.forEach(function (m) {
            const mo = c.getOverlay(m.id);
            if(mo) { mo.setLabel(""); }
        });

        return {
            id: conn_id,
            source: {
                vertex : c.source.id,
                sort: c.endpoints[0].parameters.sort,
                label: c.endpoints[0].parameters.label,
            },
            target: {
                vertex : c.target.id,
                sort: c.endpoints[1].parameters.sort,
                label: c.endpoints[1].parameters.label,
            },
            hasValue: c.endpoints[0].parameters.hasValue,
            ty: c.parameters.ty,
            connector: c,
        };
    });

    // Clear the port labels and connectorOverlays
    nodes.forEach(function (x) {
        instance.getEndpoints(x.node).forEach(function (endpoint) {
            if(endpoint.getOverlay("customLabel")) {
                endpoint.removeOverlay("customLabel");
            }
            endpoint.connectorOverlays = [];
        });
        for(var d in x.node.dataset) {
            if(d.startsWith("label:")) {
                delete x.node.dataset[d];
            }
        }
    });

    // Call to Narya to do the typechecking.  The result is an object of type {complete:bool, callback:string opt, error:string opt, labels, diagnostics}, which we pass off to the "continue" function.
    continue_typechecking(nodes, edges, connections, Narya.check(nodes, edges));
}

function symbolic_to_z3(sym) {
    if(sym.head === "add") {
        return symbolic_to_z3(sym.args[0]).add(symbolic_to_z3(sym.args[1]));
    } else if(sym.head === "sub") {
        return symbolic_to_z3(sym.args[0]).sub(symbolic_to_z3(sym.args[1]));
    } else if(sym.head === "mul") {
        return symbolic_to_z3(sym.args[0]).mul(symbolic_to_z3(sym.args[1]));
    } else if(sym.head === "div") {
        return symbolic_to_z3(sym.args[0]).div(symbolic_to_z3(sym.args[1]));
    } else if(sym.head === "neg") {
        return symbolic_to_z3(sym.args[0]).neg();
    // Z3 has no |x|, min or max over the reals, but each is a conditional, and a conditional
    // between two polynomials is still something the nonlinear solver decides.
    } else if(sym.head === "abs") {
        const x = symbolic_to_z3(sym.args[0]);
        return If(x.ge(0), x, x.neg());
    } else if(sym.head === "min") {
        const x = symbolic_to_z3(sym.args[0]);
        const y = symbolic_to_z3(sym.args[1]);
        return If(x.le(y), x, y);
    } else if(sym.head === "max") {
        const x = symbolic_to_z3(sym.args[0]);
        const y = symbolic_to_z3(sym.args[1]);
        return If(x.le(y), y, x);
    } else if(sym.head === "val") {
        return Real.val(sym.args[0].head);
    } else if(sym.head === "const") {
        return Real.const(sym.args[0].head);
    } else {
        console.log("Error: invalid symbolic");
    }
}

function callback_to_z3(callback) {
    const solver = new Solver();
    callback.forEach(function (rel) {
        const lhs = symbolic_to_z3(rel.lhs);
        const rhs = symbolic_to_z3(rel.rhs);
        if(rel.op === "eq") {
            solver.add(lhs.eq(rhs));
        } else if(rel.op === "neq") {
            solver.add(lhs.neq(rhs));
        } else if(rel.op === "lt") {
            solver.add(lhs.lt(rhs));
        } else if(rel.op === "le") {
            solver.add(lhs.le(rhs));
        } else {
            console.log("Error: invalid relation");
        }
    });
    return solver;
}

// A wire whose ends disagree about the type gets both types written on it, each at its own end:
// what the source port produces, and what the target port expected.  They're ordinary wire labels,
// so the label-spreading below moves them out of each other's way like any other.
const MISMATCH_LABELS = [
    { id: "gotLabel", home: 0.25, field: "got" },
    { id: "expectedLabel", home: 0.75, field: "expected" },
];

// Show the two types of an Unequal_synthesized_type diagnostic on the wire it was reported for.
// Diagnostics that aren't type mismatches carry neither type, and leave the wire's own label alone.
function labelTypeMismatch(edge, d) {
    if(d.got == null || d.expected == null) { return; }
    // The two ends say it better than one type in the middle would.
    const own = edge.getOverlay("label");
    if(own) { own.setLabel(""); }
    MISMATCH_LABELS.forEach(function (m) {
        const lbl = d[m.field];
        const ovl = edge.getOverlay(m.id);
        if(ovl) {
            ovl.setLabel(lbl);
        } else {
            edge.addOverlay({ type: "Label", options: {
                id: m.id, label: lbl, location: m.home, cssClass: "connLabel mismatchLabel",
            } });
        }
    });
    instance.revalidate(edge.source);
}

// Wire labels sit at the middle of their wire, so wires running close together -- one port fanning
// out to two nearby inputs, say -- end up with their labels on top of each other.  After labeling,
// slide the ones that collide along their own wire: each label tries positions stepping out from
// the middle and takes the first that clears everything already in the way (or, failing that, the
// one that covers least of it).  In the way means the labels already placed, plus the things that
// can't move: the boxes themselves and the type labels on unconnected ports.  Positions are
// predicted from the connector's own geometry, so this costs one repaint of the wires that
// actually moved, not one per position tried.
// The X that deletes a wire goes through the same pass, after all the labels, so it ends up
// somewhere none of them covers -- the two types on a mismatched wire straddle its usual spot.
// How far from its home position along the wire a label may be pushed, in steps of this size.
const LABEL_STEPS = [0, -0.08, 0.08, -0.16, 0.16, -0.24, 0.24, -0.32, 0.32, -0.4, 0.4];
// Positions to try for a label whose home is `home`, nearest first, kept clear of the wire's ends.
function labelLocations(home) {
    return LABEL_STEPS.map(function (d) { return Math.min(0.9, Math.max(0.1, home + d)); });
}
// Labels closer than this (in pixels) count as colliding, so they don't end up flush against
// each other either.
const LABEL_GAP = 4;

function overlapArea(a, b) {
    const w = Math.min(a.x + a.w, b.x + b.w) - Math.max(a.x, b.x) + LABEL_GAP;
    const h = Math.min(a.y + a.h, b.y + b.h) - Math.max(a.y, b.y) + LABEL_GAP;
    return (w > 0 && h > 0) ? w * h : 0;
}

// The rectangles a wire label should keep off: every box in the diagram, and the type labels shown
// beside unconnected output ports.  Neither can be moved out of the way, so they're fixed.
function labelObstacles() {
    const fixed = [];
    const add = function (el) {
        const r = el.getBoundingClientRect();
        if(r.width > 0 && r.height > 0) { fixed.push({ x: r.x, y: r.y, w: r.width, h: r.height }); }
    };
    nodes.forEach(function (x) { add(x.node); });
    document.querySelectorAll('#canvas .lowerOutputLabel, #canvas .upperOutputLabel, ' +
                              '#canvas .lowerInputLabel, #canvas .middleInputLabel, ' +
                              '#canvas .upperInputLabel').forEach(add);
    return fixed;
}

// One thing to be placed along a wire: where it is now, how big it is, and the positions it may
// move to.  `origin` is the point on the path it's currently drawn from, so any other position can
// be predicted by adding the difference between two points on the path -- the same in page
// coordinates as in the connector's own -- without moving it to find out.
function placeable(c, ovl, home) {
    const r = ovl.canvas.getBoundingClientRect();
    if(r.width === 0 || r.height === 0) { return null; }
    return {
        conn: c, ovl: ovl, w: r.width, h: r.height,
        cx: r.x + r.width / 2, cy: r.y + r.height / 2,
        origin: c.connector.pointOnPath(ovl.location),
        locations: labelLocations(home),
    };
}

function spreadWireLabels() {
    // Measure every wire label where it currently sits.  A label jsPlumb hasn't drawn yet has no
    // size; leave it for the next typecheck rather than guessing at it.
    const labels = [];
    // The X that deletes a wire is placed after the labels, so it dodges them rather than the
    // other way round: a label is always on show, while the X only appears under the pointer.  It
    // hides with visibility rather than display, so it can be measured even while invisible.
    const buttons = [];
    instance.getConnections().forEach(function (c) {
        if(!c.connector) { return; }
        const x = c.getOverlay("closeButton");
        if(x && x.canvas) {
            const b = placeable(c, x, CLOSE_BUTTON_HOME);
            if(b) { buttons.push(b); }
        }
        // Both the type we compute for a wire and the one the player types on it (at adept and
        // master) sit in the middle of the wire, so both can collide.
        ["label", "userLabel", "gotLabel", "expectedLabel"].forEach(function (id) {
            const ovl = c.getOverlay(id);
            if(!ovl || !ovl.canvas) { return; }
            if(typeof ovl.getLabel === 'function' && ovl.getLabel() === "") { return; }
            // A mismatch label belongs at its own end of the wire, not in the middle.
            const lb = placeable(c, ovl,
                id === "gotLabel" ? 0.25 : id === "expectedLabel" ? 0.75 : 0.5);
            if(lb) { labels.push(lb); }
        });
    });
    const all = labels.concat(buttons);
    if(all.length === 0) { return; }

    // Seed with the immovable things, so a label prefers a spot clear of them too.
    const placed = labelObstacles();
    const moved = new Set();
    all.forEach(function (lb) {
        var best = null;
        for(var i = 0; i < lb.locations.length; i++) {
            const loc = lb.locations[i];
            const p = lb.conn.connector.pointOnPath(loc);
            const rect = {
                x: lb.cx + (p.x - lb.origin.x) - lb.w / 2,
                y: lb.cy + (p.y - lb.origin.y) - lb.h / 2,
                w: lb.w, h: lb.h,
            };
            // Cost each collision by how much of the LABEL it hides, so a big box doesn't outweigh
            // several small labels just by being big.
            const area = lb.w * lb.h;
            var cost = 0;
            placed.forEach(function (q) { cost += Math.min(overlapArea(rect, q), area); });
            if(best === null || cost < best.cost) { best = { loc: loc, rect: rect, cost: cost }; }
            if(cost === 0) { break; }
        }
        placed.push(best.rect);
        if(best.loc !== lb.ovl.location) {
            lb.ovl.setLocation(best.loc);
            moved.add(lb.conn.source);
        }
    });
    // Repaint only the wires whose labels actually moved.
    moved.forEach(function (el) { instance.revalidate(el); });
}

// The diagnostics from the most recent completed typecheck, for the test seam to read.
var lastDiagnostics = [];

// Narya formats a diagnostic for a terminal: a "￫ error[E0401]" header, then lines flagged with
// ￮ or ￭.  For a tooltip we want just what it says, so drop the header and the flags.
function plainDiagnosticText(text) {
    return text.split(/[\r\n]+/)
        .filter(function (l) { return !/^\s*￫/.test(l); })
        .map(function (l) { return l.replace(/^\s*[￮￭]\s?/, ''); })
        .join('\n')
        .trim();
}

function continue_typechecking(nodes, edges, connections, result) {
    // If a callback string was supplied, we pass it off to Z3 and wait for a response.
    if(result.callback) {
        const solver = callback_to_z3(result.callback);
        solver.check().then(function (answer) {
            continue_typechecking(nodes, edges, connections, Narya.reenter(answer === 'unsat'));
        });
        // For now, we abort this function; we'll come back to it when the response arrives.
        return;
    }

    // The round has landed, so Narya can be called into again.  If the diagram moved on while we
    // were waiting, this answer is about a proof that no longer exists: check the current one
    // instead of drawing a stale result and saving it.
    typecheckPending = false;
    if(typecheckAgain) { typecheck(); return; }

    lastDiagnostics = result.diagnostics || [];
    const diagram = document.getElementById('diagram');
    
    // Display results
    if(result.error) {
        console.log(result.error);
        alert ("Internal error.  Please open the javascript console, take a screenshot, and send them both to the developer.");
        diagram.style.backgroundColor = "";
        conclusion_node.style.backgroundColor = "";
        document.getElementById("levelCompleteBanner").classList.remove("shown");
        updateBlockBanner();
    } else {
        // result.labels is an array of objects of type {loc, ty:string, tm:string opt}, where loc represents either an edge or a port and has type {isEdge:bool, id:string, sort:string optdef, label:string optdef, hasValue:bool}.
        // To this we add the ports that have default labels from being "primary" (synthesizing inputs or checking outputs).  But we add them last, so they don't override any labels produced by Narya.
        var labels = result.labels;
        nodes.forEach(function (x) {
            instance.getEndpoints(x.node).forEach(function (endpoint) {
                if(endpoint.parameters.primary) {
                    labels.push({
                        loc: {
                            isEdge: false,
                            id: x.id,
                            sort: endpoint.parameters.sort,
                            label: endpoint.parameters.label,
                            hasValue: endpoint.parameters.hasValue,
                        },
                        ty: endpoint.parameters.primary,
                    });
                }
            });
        });
        // We add each label with a location to the appropriate connector
        labels.forEach(function(label) {
            if(label.loc.isEdge) {
                const edge = connections[label.loc.id];
                // We only auto-label the wires if we're on novice difficulty, or if they start at a given or end at the goal, or carry a value.
                // (It would be silly to make the user retype the givens or goals to label those wires, and currently the user can't annotate values.)
                if(difficulty === 0 ||
                   nodes.some(function (x) {
                       const ishyp = (x.id === edge.source.id && (x.rule === 'hypothesis' || x.rule === 'variable'));
                       const isconcl = (x.id === edge.target.id && x.rule === 'conclusion');
                       const hasval = edge.endpoints[0].parameters.hasValue;
                       return (ishyp || isconcl || hasval);
                   })) {
                    var cssClass = "connLabel";
                    var lbl = label.ty;
                    if(edge.parameters.hasValue && label.tm) { // or label.loc.hasValue?
                        cssClass = cssClass + " connLabelValue";
                        lbl = label.tm + ' ∈ ' + lbl;
                    }
                    const ovl = edge.getOverlay("label");
                    if(!ovl) {
                        edge.addOverlay({ type: "Label", options: { id: "label", label: lbl, cssClass: cssClass} });
                    } else if (ovl.getLabel() === "") {
                        ovl.setLabel(lbl);
                    }
                    instance.revalidate(edge.source);
                }
            } else if(difficulty === 0) {
                // Only at novice difficulty do we label the ports
                if(label.loc.sort === "output" || label.loc.sort === "assumption") {
                    // For output and assumption ports, we set the connector overlay for the port, so that new edges created will already drag out with the correct type.
                    const node = document.getElementById(label.loc.id);
                    instance.getEndpoints(node).forEach(function(endpoint) {
                        if(endpoint.parameters.sort === label.loc.sort && endpoint.parameters.label === label.loc.label) {
                            var cssClass = "connLabel";
                            var lbl = label.ty;
                            if(endpoint.parameters.hasValue && label.tm) { // or label.loc.hasValue?
                                cssClass = cssClass + " connLabelValue";
                                lbl = label.tm + ' ∈ ' + lbl;
                            }
                            endpoint.connectorOverlays = [ { type: "Label", options: { id: "label", label: lbl, cssClass: cssClass} } ];
                            // Also, if there are no connections leaving that port yet, we add a label so the user can see its type.
                            var hasConnection = false;
                            instance.getConnections({ source: label.loc.id }).filter(function (c) {
                                return (c.endpoints[0].parameters.sort === label.loc.sort) && (c.endpoints[0].parameters.label === label.loc.label);
                            }).map(function (c) {
                                hasConnection = true;
                            });
                            if(!hasConnection && !endpoint.getOverlay("customLabel")) {
                                // console.log("adding overlay label " + lbl + " to " + label.loc.id + " " + label.loc.sort + " " + label.loc.label);
                                endpoint.addOverlay({ type: "Custom", options: {
                                    id: "customLabel",
                                    create:(component) => {
                                        const d = document.createElement("div");
                                        var cssClass = "lowerOutputLabel";
                                        if(endpoint.parameters.side === "upper") {
                                            // Lower is the default
                                            cssClass = "upperOutputLabel";
                                        } else if(endpoint.parameters.side === "middle") {
                                            cssClass = "middleOutputLabel";
                                        }
                                        if(endpoint.parameters.hasValue) {
                                            cssClass = cssClass + " connLabelValue";
                                        }
                                        d.innerHTML = '<div class="' + cssClass + '">' + escapeHtml(lbl) + "</div>";
                                        return d;
                                    },
                                } })
                                instance.revalidate(node);
                            }
                        }
                    });
                } else {
                    // For input and subgoal ports, we mark the type as a property of the node, so that we can use it later to display the type of unconnected input/subgoal ports.
                    // console.log("adding input/subgoal label " + label.ty + " to " + label.loc.id + " " + label.loc.sort + " " + label.loc.label);
                    const key = "label:" + label.loc.sort + ":" + label.loc.label;
                    const node = document.getElementById(label.loc.id);
                    if(! node.dataset[key]) {
                        node.dataset[key] = label.ty;
                    }
                }
            }
        });
        // A proof that is correct but uses more blocks than the level allows doesn't count: the
        // goal stays uncolored and nothing is registered, and the block count stays up (in red,
        // from updateBlockBanner) in place of the completion pop-up.
        if(result.complete && overBlockBudget()) {
            diagram.style.backgroundColor = "";
            conclusion_node.style.backgroundColor = "";
            document.getElementById("levelCompleteBanner").classList.remove("shown");
            // Cutting back to a proof within budget counts as a fresh completion.
            proofRegisteredComplete = false;
        } else if(result.complete) {
            // The level is complete: color the goal and level green.
            diagram.style.backgroundColor = COLORS[difficulty][0].backgroundColor;
            conclusion_node.style.color = COLORS[difficulty][1].color;
            conclusion_node.style.backgroundColor = COLORS[difficulty][1].backgroundColor;
            if(currentLevel) {
                // Register this as a fresh completion only once (not on every re-typecheck of an
                // already-complete proof), advancing the global completion-time counter.
                if(!proofRegisteredComplete) {
                    proofRegisteredComplete = true;
                    const past = getPast(null, currentLevel);
                    // Snapshot which worlds are open before recording this completion.
                    const beforeGates = snapshotWorldGates();
                    // Advance the global time counter and stamp this difficulty's completion time
                    // (a downgrade-restore stamps the current time without advancing the counter).
                    globalTime = parseInt(localStorage.getItem("time")) || 0;
                    if(!registerWithoutAdvancingTime) {
                        globalTime += 1;
                        localStorage.setItem("time", globalTime.toString());
                    }
                    registerWithoutAdvancingTime = false;
                    const times = Object.assign({}, past.times);
                    times[difficulty] = globalTime;
                    // Record completion, with the difficulty and per-difficulty times, in local storage
                    const key = JSON.stringify(saveable(currentLevel));
                    const value = { complete: true, difficulty: Math.max(difficulty, past.difficulty || 0), times: times };
                    localStorage.setItem(key, JSON.stringify(value));
                    // Re-render the level buttons (this level is now complete, and others may have
                    // unlocked or re-locked), and update this world's index-chip progress count.
                    updateLevelSelect(null);
                    refreshWorldProgress(currentLevel.worldPaneIndex);
                    // If a new world just opened at some difficulty, tell the player.
                    announceNewlyUnlockedWorlds(beforeGates);
                    if(SERVER) {
                        // Save it to the server too
                        saveSolvedToServer(key, value, difficulty, currentWorld);
                    }
                }
            } else if(currentCustom) {
                // A saved custom level: record completion at this difficulty (which unlocks the
                // next one) in the stored list and re-render the Custom world.
                if(!proofRegisteredComplete) {
                    proofRegisteredComplete = true;
                    markCustomCompleted(currentCustom, difficulty);
                }
            }
            // The proof is complete: show the (non-modal) completion pop-up at the top, tinted to
            // match the current difficulty (the same color as the conclusion box), with smart
            // "Next" / "Next Unsolved" buttons.  For a custom level there's no "Next" target, so only
            // "Select Level" (and "Save", for an unsaved one) appears.
            configureNextButtons();
            document.getElementById("levelCompleteText").innerText =
                hasBlockBudget() ? "Level Complete! Blocks used: " + blockTally() : "Level Complete!";
            document.getElementById("saveLevelAfterComplete").style.display =
                (!currentLevel && currentLevelDef) ? '' : 'none';
            const banner = document.getElementById("levelCompleteBanner");
            banner.style.backgroundColor = COLORS[difficulty][1].backgroundColor;
            banner.classList.add("shown");
        } else {
            // If there are fatal errors, remove any green color on the goal and indicate the errors somehow.
            diagram.style.backgroundColor = "";
            conclusion_node.style.backgroundColor = "";
            document.getElementById("levelCompleteBanner").classList.remove("shown");
            // The proof is no longer complete; a later re-completion counts afresh.
            proofRegisteredComplete = false;
            var somethingRed = false;
            // result.diagnostics is an array of objects of type {isfatal:bool, code:string, text:string, explanation:string opt, locs}, where locs is an array of objects representing either an edge or a port, with type {isEdge:bool, id:string, sort:string optdef, label:string optdef, hasValue:bool}.
            result.diagnostics.forEach(function (d) {
                // Make the edges with fatal errors red, if we're not on master difficulty
                if(d.isfatal && difficulty <= 1) {
                    d.locs.forEach(function (loc) {
                        if(loc.isEdge) {
                            const edge = connections[loc.id];
                            setStrokeColor(edge, "#ff0000");
                            // Keep the first error reported for this wire; later ones are usually
                            // knock-on effects of it.
                            if(!edge.parameters.errorText) {
                                edge.parameters.errorText = d.explanation || plainDiagnosticText(d.text);
                            }
                            instance.revalidate(edge.source);
                            console.log(d.text);
                            somethingRed = true;
                            if(edge.parameters.userLabel) {
                                edge.parameters.userLabel.style.color = "#ff0000";
                            }
                            // At novice, a wire whose two ends disagree about the type says so:
                            // the type coming out of the source at that end, the one the target
                            // wanted at the other.
                            if(difficulty === 0) { labelTypeMismatch(edge, d); }
                        } else if (loc.sort === "input" || loc.sort === "subgoal") {
                            console.log("error at " + loc.id + " " + loc.sort + " " + loc.label + ": ");
                            console.log(d.text);
                            const node = document.getElementById(loc.id);
                            var ty = node.dataset["label:" + loc.sort + ":" + loc.label] || "?";
                            instance.getEndpoints(node).forEach(function (endpoint) {
                                if(endpoint.parameters.sort === loc.sort && endpoint.parameters.label === loc.label) {
                                    // Don't label ports that have an edge connected to them (that edge should get labeled instead)
                                    var hasEdge = false;
                                    instance.getConnections({target : node}).forEach(function(e) {
                                        if(e.endpoints[1] === endpoint) {
                                            hasEdge = true
                                        }
                                    });
                                    if(!hasEdge) {
                                        // On adept, we count an error on an unconnected input/subgoal port as "something red", even though not displayed.
                                        somethingRed = true;
                                        // We only actually label ports at novice difficulty
                                        if(difficulty === 0) {
                                            if(endpoint.getOverlay("customLabel")) {
                                                endpoint.removeOverlay("customLabel");
                                            }
                                            endpoint.addOverlay({ type: "Custom", options: {
                                                id: "customLabel",
                                                create:(component) => {
                                                    const d = document.createElement("div");
                                                    if(endpoint.parameters.hasValue) {
                                                        // A port whose set isn't determined until
                                                        // something is wired in leaves that open
                                                        // too, rather than showing a guess.
                                                        ty = "? ∈ " + (endpoint.parameters.unknownSet ? "?" : ty);
                                                    }
                                                    const ety = escapeHtml(ty);
                                                    if(endpoint.parameters.side === "upper") {
                                                        d.innerHTML = '<div class="upperInputLabel">' + ety + "</div>";
                                                    } else if(endpoint.parameters.side === "middle") {
                                                        d.innerHTML = '<div class="middleInputLabel">' + ety + "</div>";
                                                    } else {
                                                        // Lower is the default
                                                        d.innerHTML = '<div class="lowerInputLabel">' + ety + "</div>";
                                                    }
                                                    return d;
                                                },
                                            } });
                                        }
                                    }
                                }
                            });
                            instance.revalidate(node);
                        } else {
                            // If the diagnostic doesn't have a location that corresponds to an edge or a vertex, we don't report it to the user.  For instance, this is the case for the "Nonsynthesizing" error reported for the hole that's put in an unconnected input that should be synthesizing.  But for now, we log it.
                            console.log("error at empty location or non-input port:");
                            console.log(d.text);
                        }
                    });
                    if(!d.locs || d.locs.length === 0) {
                        console.log("error with no locations");
                        console.log(d.text);
                    }
                } else {
                    // TODO: Should non-fatal diagnostics be reported at all?
                    console.log(d.text);
                }
            });
            if(difficulty <= 1 && !somethingRed) {
                alert("Your proof isn't complete and correct, but I don't think I've given you any idea why.  This is a bug; please report to the developer.");
            }
        }
        // The block count follows whatever the branches above settled on: hidden once the level is
        // finished within budget, and showing (red, if over) otherwise.
        updateBlockBanner();
        // Now delete the label overlays (ordinary and mismatch) that didn't get set this time, and
        // move whatever is left off each other and off the boxes.
        edges.forEach(function(c) {
            ["label"].concat(MISMATCH_LABELS.map(function (m) { return m.id; })).forEach(function (id) {
                const ovl = c.connector.getOverlay(id);
                if(ovl && ovl.getLabel() === "") { c.connector.removeOverlay(id); }
            });
        });
        spreadWireLabels();
    }

    // Persist the current proof on every change, now that we know whether it's complete.
    autosave();

    document.getElementById("typecheckingBG").style.display = 'none';
}

// Check that the parameters and variables have types, split up grouped variables, and associate
// them to types.  The separator is ":" for parameters and "∈" for variables (so the player writes
// "a ∈ A"); either way the result is the {name, ty} format that Narya consumes.
function checkType(sort, eg, sep) { return function(v) {
    v = v.split(new RegExp(' *' + (sep || ':') + ' *'));
    if(v.length !== 2) {
        throw new Error('All ' + sort + ' must have a unique type, for instance "' + eg + '"');
    }
    return v[0].split(/ +/).map(function(x) {
        return { name: x, ty: v[1] };
    });
}}

// When a new custom level is selected, we parse the parameters, variables, hypotheses, and conclusion entered by the user.
document.getElementById("submitLevel").onclick = function () {
    var parameters = [];
    var variables = [];
    // Read the optional name now, before setLevel clears the dialog fields.
    const customName = document.getElementById("customName").value.trim();

    try {
        parameters = document.getElementById("parameters").value.
            split(/[\r\n]+/).
            filter(Boolean).
            map(checkType('parameters', 'A : Type')).
            flat();
        variables = document.getElementById("variables").value.
            split(/[\r\n]+/).
            filter(Boolean).
            map(checkType('variables', 'a ∈ A', '∈')).
            flat();
    } catch(exn) {
        alert(exn.message);
        return;
    }

    // The hypotheses and conclusions don't have names, they are just types, so these are just arrays of strings.
    const hypotheses = document.getElementById("hypotheses").value.
          split(/[\r\n]+/).
          filter(Boolean).
          map(function(v) { return { ty: v }; });

    // The conclusion just needs to be nonempty.
    const conclText = document.getElementById("conclusion");
    if(!conclText.value) {
        alert('You need a conclusion!');
        return;
    }

    const conclusion = { ty : conclText.value };

    const accepted = setLevel({
        parameters: parameters,
        variables: variables,
        hypotheses: hypotheses,
        conclusion: conclusion,
    }, "all");
    // Narya wouldn't have it: it has said why, and we stay on whatever level we were on.
    if(!accepted) { return; }

    currentLevel = undefined;
    currentLevelButton = undefined;
    currentCustom = null;
    updateSaveButtonVisibility();
    document.getElementById("currentLevel").innerText = "Level: Custom";
    // If the player named the level, save it to the Custom list right away.
    if(customName) { saveCustomLevelNamed(customName); }
}

// Set up a level: lay out its context and conclusion and hand the statement to Narya.  Returns
// whether Narya accepted it -- a statement that doesn't parse is reported and nothing is laid out,
// and the caller must then leave the level it was on alone rather than relabel it for one that
// never opened.
function setLevel(level, rulesAllowed) {
    // Save any pending scroll of the level we're leaving, while it's still the current one.
    flushScrollSave();
    // Remember the raw definition so "Edit" can re-open the custom dialog pre-filled with it, even
    // if it turns out not to parse -- that is how the player gets back what they typed to fix it.
    currentLevelDef = level;
    const new_varnames = [];

    // Assign ids to everything, and check that the variable names have no duplicates.
    const parameters = level.parameters.map(function (x) {
        if(new_varnames.includes(x.name)) {
            throw new Error("All parameter and variable names must be distinct");
        }
        new_varnames.push(x.name);
        return {
            name: x.name,
            ty: x.ty,
            id: 'param' + (paramCounter++),
        };
    });
    const variables = level.variables.map(function (x) {
        if(new_varnames.includes(x.name)) {
            throw new Error("All parameter and variable names must be distinct");
        }
        new_varnames.push(x.name);
        return {
            name: x.name,
            ty: x.ty,
            id: 'var' + (varCounter++),
        };
    });
    const hypotheses = level.hypotheses.map(function (x) {
        return {
            ty: x.ty,
            id: 'hyp' + (hypCounter++),
        };
    });
    const conclusion = {
        ty: level.conclusion.ty,
        id: 'concl' + (conclCounter++),
    };

    // One-time global initialization of the proof engine (loads the startup definitions and installs
    // notations).  Narya's versioned global state can't be re-initialized, so this must happen exactly
    // once for the page; every subsequent level setup reuses it.
    if (!naryaInited) {
        const initResult = Narya.init();
        naryaInited = true;
        if (initResult.error) {
            alert(initResult.error);
            return false;
        }
    }

    // Typecheck everything.
    const result = Narya.start(parameters, variables, hypotheses, conclusion);
    if (result.error) {
        alert(result.error);
        return false;
    }
    console.log("initialized Narya");

    // Now we know the new level is valid, so we blow away the old one and set up the new one.

    suppressChecking = true;
    // Don't autosave while setting up: the initial empty proof must not overwrite a saved one.
    suppressSave = true;

    // Set the global varnames to the new one.
    varnames = new_varnames;

    // Hide the modal dialogs for choosing levels or setting custom levels, and empty the custom text fields.
    clearLevelSelect();
    // A freshly set-up level isn't complete yet, so the completion pop-up starts hidden.
    document.getElementById("levelCompleteBanner").classList.remove("shown");
    hideBlockBanner();

    // Turn on the "cancel" buttons and "proof will be erased" warnings for future level-selections.
    // (setLevelWarning is optional -- it was removed from the custom dialog.)
    const setLevelWarning = document.getElementById("setLevelWarning");
    if(setLevelWarning) { setLevelWarning.style.display = ''; }
    document.getElementById("cancelChooseLevel").style.display = '';
    document.getElementById("cancelSetLevel").style.display = '';

    // Delete all the existing nodes, to prepare for a new level.  We have to remove the jsPlumb connections and endpoints first, or they end up stashed in the corner of the window.
    instance.select().deleteAll();    // This removes all connections
    nodes.forEach((x) => {
        instance.removeAllEndpoints(x.node);
        x.node.remove();
    });
    nodes = [];

    // Start each level with the canvas reset to fill the viewport, scrolled to the origin, so the
    // context is laid out against the visible area rather than a leftover oversized canvas.
    canvas.style.width = '';
    canvas.style.height = '';
    diagram.scrollLeft = 0;
    diagram.scrollTop = 0;

    // Hide the rules that aren't allowed for this stage
    for (const prule of document.getElementById('palette').children) {
        if((rulesAllowed == "all" && excludeFromAll.indexOf(prule.id) === -1) || prule.id == 'buttons' || rulesAllowed.includes(prule.id)) {
            prule.style.display = '';
        } else {
            prule.style.display = 'none';
        }
    }

    // Lay out the context on the left: stack the variables close together at the top, then space
    // the hypotheses out equally in the vertical space remaining below them.
    const VAR_GAP = 10;
    var height = VAR_GAP;

    // The difference between variables and hypotheses is that variables are labeled with their name as well as a type, and they are colored.
    for(const v of variables) {
        const vbx = document.createElement("div");
        vbx.innerHTML = v.name + "&nbsp;∈&nbsp;" + v.ty;
        vbx.dataset.name = v.name;
        vbx.dataset.rule = "variable";
        vbx.style.position = 'absolute';
        vbx.style.top = height + "px";
        vbx.style.left = '50px';
        vbx.style.textAlign = 'center';
        vbx.className = 'basic contextual rule';
        vbx.style.color = VALUECOLOR;
        vbx.id = v.id;
        vbx.onmousedown = toggleDragSelected(vbx);
        canvas.appendChild(vbx);
        nodes.push({id: vbx.id, name: v.name, rule: 'variable', node: vbx, value: v.ty});
        instance.addEndpoint(vbx, {
            anchor: "Right",
            source: true,
            parameters: { sort: "output", hasValue: true },
            maxConnections: -1,
            paintStyle: { fill: VALUECOLOR },
            connectorStyle: { stroke: VALUECOLOR, strokeWidth: 2 }
        });
        height += vbx.offsetHeight + VAR_GAP;
    }

    // Hypotheses fill the space remaining below the variable stack, spaced out equally.
    const hyp_inc = (diagram.offsetHeight - height) / (hypotheses.length + 1);
    height += hyp_inc;
    for(const h of hypotheses) {
        const hyp = document.createElement("div");
        hyp.dataset.rule = "hypothesis";
        hyp.innerText = h.ty;
        hyp.style.position = 'absolute';
        hyp.style.top = height + "px";
        hyp.style.left = '50px';
        hyp.style.textAlign = 'center';
        hyp.className = 'basic contextual rule';
        hyp.id = h.id;
        hyp.onmousedown = toggleDragSelected(hyp);
        canvas.appendChild(hyp);
        nodes.push({id: hyp.id, rule: 'hypothesis', node: hyp, value : h.ty});
        instance.addEndpoint(hyp, {
            anchor: "Right",
            source: true,
            parameters: {sort: "output"},
            maxConnections: -1
        });
        height += hyp_inc;
    }

    // Similarly, the conclusion goes on the right.
    const concl = document.createElement("div");
    concl.dataset.rule = "conclusion";
    concl.innerText = conclusion.ty;
    concl.className = 'basic contextual rule';
    concl.style.textAlign = 'center';
    concl.style.position = 'absolute';
    concl.id = conclusion.id;
    concl.onmousedown = toggleDragSelected(concl);
    canvas.appendChild(concl);
    // Use pixel positions (not 50% / right) so the conclusion stays put if the canvas later grows.
    // The left also apparently has to be set after appendChild for the width to be calculated correctly.
    concl.style.left = (diagram.clientWidth - 50 - concl.clientWidth) + 'px';
    concl.style.top = ((diagram.clientHeight - concl.clientHeight) / 2) + 'px';
    conclusion_node = concl;
    nodes.push({id: concl.id, rule: 'conclusion', node: concl, value: conclusion.ty});
    instance.addEndpoint(concl, { anchor: "Left", target: true, parameters: {sort: "input"} });

    // Set the visible difficulty, and this level's block budget if it sets one.  The budget is
    // recorded here rather than off currentLevel: the typecheck below is the new level's first, and
    // it already has to know the budget, but currentLevel doesn't name the new level until setLevel
    // returns -- and a custom level, which has no budget, never sets it at all.
    updateCurrentDifficulty();
    currentMaxRules = (level.maxrules === undefined) ? null : level.maxrules;

    // Finally, we typecheck.  It will fail since the user hasn't added any connections yet, but it adds labels to ports.
    suppressChecking = false;
    typecheck();
    // The empty level is now set up; subsequent changes should autosave.
    suppressSave = false;

    // Done setting up the new level!

    // Show the level's hint (if any) automatically the first time the player sees this level;
    // afterwards it's available via the "Show Hint" button.  This also means restoring a saved
    // proof (which re-runs setLevel) doesn't pop the hint a second time.
    currentHint = level.hint;
    if(currentHint) {
        document.getElementById("showHint").style.display = 'block';
        if(!localStorage.getItem(currentHint)) {
            showHint();
        }
    } else {
        document.getElementById("showHint").style.display = 'none';
    }
    return true;
}

function clearLevelSelect () {
    document.getElementById("levelSelectBG").style.display = "none";
    document.getElementById("levelChooseBG").style.display = "none";
    document.getElementById("parameters").value = "";
    document.getElementById("variables").value = "";
    document.getElementById("hypotheses").value = "";
    document.getElementById("conclusion").value = "";
    document.getElementById("customName").value = "";
}

// Display hints on certain levels
document.getElementById("hintBG").onclick = function() {
    const hintBG = document.getElementById("hintBG");
    hintBG.style.display = 'none';
    Array.prototype.forEach.call(hintBG.getElementsByClassName("hint"), function (x) {
        x.style.display = 'none';
    });
}
