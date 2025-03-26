import { ready, newInstance, DotEndpoint, StraightConnector, FlowchartConnector, BezierConnector, EVENT_CONNECTION, EVENT_CONNECTION_MOUSEOVER, EVENT_CONNECTION_MOUSEOUT } from "@jsplumb/browser-ui"
import { LEVELS, saveable } from "./levels.js"
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

// Unicode characters to put in the button palette below text boxes
const PALETTE = ['∧', '∨', '⇒', '⇔', '¬', '⊤', '⊥', '∀', '∃', '∈', 'ℤ', '²', '³', '⁴'];

// For some unfathomable reason this is not built into JavaScript
function escapeRegex(string) {
    return string.replace(/[/\-\\^$*+?.()|[\]{}]/g, '\\$&');
}

// Shortcut key sequences for unicode characters, many TeX-inspired
const KEYS = [
    { unicode: '∧',  keys: [ '\\land ', '\\wedge ', '/\\' ] },
    { unicode: '∨',  keys: [ '\\lor ', '\\vee ', '\\/' ] },
    { unicode: '⇔', keys: [ '\\Leftrightarrow ', '\\iff ', '<=>' ] }, // has to come first, so <=> doesn't become <⇒
    { unicode: '⇒', keys: [ '\\Rightarrow ', '=>' ] },
    { unicode: '¬', keys: [ '\\neg ', '~' ] },
    { unicode: '⊤', keys: [ '\\top ' ] },
    { unicode: '⊥', keys: [ '\\bot ' ] },
    { unicode: '∃', keys: [ '\\exists ', '\\ex ' ] },
    { unicode: '∀', keys: [ '\\forall ', '\\all ' ] },
    { unicode: '∈', keys: [ '\\in ' ] },
    { unicode: '↦', keys: [ '\\mapsto ', '|->' ] }, // Has to come first, so |-> doesn't become |→
    { unicode: '→', keys: [ '\\to ', '\\rightarrow ', '->' ] },
    { unicode: '×', keys: [ '\\times ', '\\x ', '><' ] },
    { unicode: '⊔', keys: [ '\\sqcup ' ] },
    { unicode: '−', keys: [ '-' ] },
    { unicode: 'ℤ', keys: [ '\\Z ' ] },
    { unicode: '²', keys: [ '^2', '**2' ] },
    { unicode: '³', keys: [ '^3', '**3' ] },
    { unicode: '³', keys: [ '^4', '**4' ] },
].map(function (entry) {
    entry.regexes = entry.keys.map(function (str) { return new RegExp(escapeRegex(str), 'g'); });
    return entry
});

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

// connections to close buttons
var connectionCloseButtons = {};

// difficulty setting
var difficulty = 0;

// current hint, if any
var currentHint;

// Dynamic variable to suppress re-typechecking during batch modifications of the diagram
var suppressChecking = false;

// The world/level select panes and buttons
var worldPanes = [];
var currentWorld = 0;
const levelButtons = [];
var currentLevel;
var currentLevelButton;

// Exclude these rules from "all"
const excludeFromAll = [ "negI" ] // Classical negation suffices

const diagram = document.getElementById('diagram');

ready(() => {
    instance = newInstance({
        container: diagram,
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
                    location: 0.8,
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
    instance.bind(EVENT_CONNECTION_MOUSEOVER, (conn) => {
        if(connectionCloseButtons[conn.id]) {
            connectionCloseButtons[conn.id].button.style.display = 'block';
            if(connectionCloseButtons[conn.id].timeout) {
                clearTimeout(connectionCloseButtons[conn.id].timeout);
                connectionCloseButtons[conn.id].timeout = undefined;
            }
        }
    });
    instance.bind(EVENT_CONNECTION_MOUSEOUT, (conn) => {
        if(connectionCloseButtons[conn.id]) {
            if(connectionCloseButtons[conn.id].timeout) {
                clearTimeout(connectionCloseButtons[conn.id].timeout);
            }
            connectionCloseButtons[conn.id].timeout = setTimeout(function () { connectionCloseButtons[conn.id].button.style.display = 'none'; }, 1000);
        }
    });

    // When a palette box is dropped on the diagram, we add a copy of it as a new node at the dropped location.
    diagram.addEventListener('drop', function (e) {
        e.preventDefault();
        const id = e.dataTransfer.getData('text/plain');
        const originalBox = document.getElementById(id);
        const box = originalBox.cloneNode(true);
        box.style.position = 'absolute';
        box.style.left = `${e.clientX - diagram.offsetLeft}px`;
        box.style.top = `${e.clientY - diagram.offsetTop}px`;
        box.id = 'rule' + (counter++);
        diagram.appendChild(box);

        // Make it selectable for multi-element dragging.  We have to use mousedown instead of click so that when dragging a non-selected element, we can clear the selection before dragging starts so that only that element will be dragged.
        box.onmousedown = toggleDragSelected(box);

        // We add it to the master list of nodes.
        nodes.push({id: box.id, rule: box.dataset.rule, node: box});

        // We add a close button to the node.  (Variable, hypothesis, and conclusion nodes aren't closeable.)
        addBoxCloseButton(box);

        // Some new rules display a modal box, and we shouldn't typecheck until it is submitted.
        var typecheck_now = true;

        // Now we add endpoints appropriately for its rule type, if necessary make it larger and resizable, and prompt for variables or ascription types.
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
        } else if (id === 'impI' || id === 'allI' || id === 'negI' || id === 'cnegI' ) {
            if(id === 'allI') {
                instance.addEndpoint(box, {
                    anchor: [0, 0.5, 1, 0, 22, -12],
                    source: true, maxConnections: -1,
                    parameters: { sort: "assumption", hasValue: true, side: "upper" },
                    paintStyle: { fill: VALUECOLOR },
                    connectorStyle: { stroke: VALUECOLOR, strokeWidth: 2 },
                });
            } else {
                instance.addEndpoint(box, {
                    anchor: [0, 0.5, 1, 0, 22, -12],
                    source: true, maxConnections: -1,
                    parameters: {sort: "assumption", side: "upper"},
                });
            }
            instance.addEndpoint(box, { anchor: [1, 0.5, -1, 0, -21, -12], target: true, parameters: {sort: "subgoal", side: "upper"} });
            const primary = (id === 'impI' ? "?⇒?" : (id === 'allI' ? "∀?∈?,?" : (id === 'cnegI' ? "?" : "¬?")));
            instance.addEndpoint(box, { anchor: [1, 0.5, 1, 0, 3], source: true, maxConnections: -1, parameters: {sort: "output", primary: primary} });
            box.style.width = '200px';
            box.style.height = '50px';
            makeResizable(box);
            if(id === 'allI') {
                getVariable(box.id);
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
            getVariable(box.id);
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
            document.getElementById("ascribeBG").style.display = "flex";
            const ascribe = document.getElementById('ascribe');
            ascribe.dataset.name = box.id;
            ascribe.focus();
            typecheck_now = false;
        } else if (id === 'alg') {
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
            });
            // Prompt for the expression
            document.getElementById("expressionBG").style.display = "flex";
            const expr = document.getElementById('expression');
            expr.dataset.name = box.id;
            expr.focus();
            typecheck_now = false;
        }
        if(typecheck_now) {
            typecheck();
        }
    });

    // Whenever the graph changes, we recompute it and pass to Narya to typecheck it.
    // This includes when a new connection is created:
    instance.bind(EVENT_CONNECTION, addConnection);
    // It seems that EVENT_CONNECTION also fires after a connection is moved, so no need to separately bind EVENT_CONNECTION_MOVED.
    // We've forbidden connections from being detached by dropping, since it appears to be kind of broken, e.g. EVENT_CONNECTION_DETACHED fires *before* it's detached.  Instead the user removes connections with the close button.

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
        makeLevelSelect(null);
        levelChooseBG.style.display = "flex";
        // But if they haven't been here before, we show them the intro page first.
        if(!localStorage.getItem("visited")) {
            document.getElementById("aboutBG").style.display = "flex";
            localStorage.setItem("visited",true);
        }
    }
});

// Set connector style
document.getElementById("angleConnectors").onclick = function() {
    instance.importDefaults({ connector: FlowchartConnector.type });
};
document.getElementById("curvedConnectors").onclick = function() {
    instance.importDefaults({ connector: BezierConnector.type });
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
    if(e.target === diagram) {
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
function makeLevelSelect(res) {
    const worldName = document.getElementById('worldName');
    const backWorld = document.getElementById('backWorld');
    const forwardWorld = document.getElementById('forwardWorld');

    const worlds = document.getElementById("worlds");
    currentWorld = parseInt(localStorage.getItem("world")) || 0;
    var maxcols = 0;
    var maxrows = 0;
    LEVELS.forEach(function (world, x) {
        const worldPane = document.createElement("div");
        worldPane.className = "world";
        worlds.appendChild(worldPane);
        var countstages = 1;

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
                if(!level.trivial) {
                    nontrivialWorldLevels.push(level);
                }

                // Has the user has solved this level before?
                const past = getPast(res, level);

                // Give a number of stars according to the difficulty completed
                b.innerHTML = name + '<br>' + getStars(past);
                b.className = 'level';
                b.addEventListener('click', function () { selectCurrentLevel(level); } );
                stageGrid.appendChild(b);
                levelButtons.push(b);
                ++countlevels;
                // Color the level if it's completed at all
                if(past.complete) {
                    b.style.color = COLORS[past.difficulty][1].color;
                    b.style.backgroundColor = COLORS[past.difficulty][1].backgroundColor;
                }
            });
            ++countstages;
            maxcols = Math.max(maxcols, countlevels);
        });

        maxrows = Math.max(maxrows, countstages);

        // The last "pseudo-stage" includes "Custom" and "Random" stages
        const otherStage = document.createElement('div');
        otherStage.className = 'stage';

        const otherLabel = document.createElement('div');
        otherLabel.className = 'stage-label';
        otherStage.appendChild(otherLabel);

        // The "Custom" level lets the user specify their own values by switching to another modal box.
        const customLevel = document.createElement('div');
        customLevel.className = 'level';
        customLevel.innerText = 'Custom';
        customLevel.onclick = function () {
            document.getElementById("levelChooseBG").style.display = "none";
            document.getElementById("levelSelectBG").style.display = "flex";
        };
        otherStage.appendChild(customLevel);
        
        // The "Random" level chooses a random level from that world
        const randomLevel = document.createElement('div');
        randomLevel.className = 'level';
        randomLevel.innerText = 'Random';
        randomLevel.onclick = function () {
            const rand = nontrivialWorldLevels[Math.floor(Math.random() * nontrivialWorldLevels.length)];
            selectCurrentLevel(rand);
        };
        otherStage.appendChild(randomLevel);

        worldPane.appendChild(otherStage);

        worldPane.style.display = 'none';
        worldPanes.push({
            name: world.name,
            pane: worldPane,
        });
    });
    document.getElementById("levelChooseModal").style.width = (maxcols * 80 + 30) + 'px';
    document.getElementById("levelChooseModal").style.height = (maxrows * 60 + 200) + 'px';

    // The forwards and backwards arrows have a different look and cursor if there's nowhere to go in that direction.
    setWorld(currentWorld);

    // Load the recent difficulty
    difficulty = parseInt(localStorage.getItem("difficulty"));
    if(!difficulty) {
        difficulty = 0;
    }
    setDifficulty(difficulty);
}

// Just correct the stars and colors for each level select button, when logging back in after logging out.
function updateLevelSelect(res) {
    const worlds = document.getElementById("worlds");
    LEVELS.forEach(function (world, x) {
        world.stages.forEach(function (stage, y) {
            stage.levels.forEach(function (level, z) {
                const past = getPast(res, level);
                level.button.innerHTML = level.name + '<br>' + getStars(past);
                if(past.complete) {
                    level.button.style.color = COLORS[past.difficulty][1].color;
                    level.button.style.backgroundColor = COLORS[past.difficulty][1].backgroundColor;
                }
            });
        });
    });
}

// The backwards and forwards world buttons move to the next world in that direction if there is one, and update their displays.

document.getElementById('backWorld').onclick = function () {
    if(currentWorld > 0) {
        setWorld(currentWorld - 1);
    }
};

document.getElementById('forwardWorld').onclick = function () {
    if(currentWorld < worldPanes.length - 1) {
        setWorld(currentWorld + 1);
    }
};

function setWorld(newWorld) {
    const backWorld = document.getElementById('backWorld');
    const forwardWorld = document.getElementById('forwardWorld');

    // Hide the old world
    worldPanes[currentWorld].pane.style.display = 'none';

    // Set the new world
    currentWorld = newWorld;
    localStorage.setItem("world", currentWorld);

    // Display the new world
    worldPanes[currentWorld].pane.style.display = '';
    worldName.innerText = worldPanes[currentWorld].name;

    // Correct the world arrows
    if(currentWorld === 0) {
        backWorld.innerText = '◁';
        backWorld.style.cursor = 'default';
    } else {
        backWorld.innerText = '◀';
        backWorld.style.cursor = 'pointer';
    }

    if(currentWorld === worldPanes.length - 1) {
        forwardWorld.innerText = '▷';
        forwardWorld.style.cursor = 'default';
    } else {
        forwardWorld.innerText = '▶';
        forwardWorld.style.cursor = 'pointer';
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
}

difficultyRadios.forEach(function (radios, i) {
    radios.forEach(function (radio) {
        radio.onclick = function () { setDifficulty(i); };
    });
});

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

// Make past success into a string of stars
function getStars(past) {
    var stars = "";
    for(var i = 0; i < 3; i++) {
        if(past.complete && i <= past.difficulty) {
            stars = stars + "★";
        } else {
            stars = stars + "☆";
        }
    }
    return stars;
}

// The "Select Level" button opens a modal box to choose from pre-set levels.  There's a "custom" button at the bottom that switches to a modal box that sets a custom level.
document.getElementById("selectLevel").onclick = function() {
    document.getElementById("levelChooseBG").style.display = "flex";
};

// To clear the current proof, just re-select the current level
document.getElementById("clearProof").onclick = function() {
    if(confirm("This will clear your current proof and reset to the beginning of this level!  It cannot be un-done.  Are you sure?")) {
        selectCurrentLevel(currentLevel);
    }
}

// Going "Back" from the custom level-select sends us back to the non-custom list of levels.
document.getElementById("backLevel").onclick = function () {
    document.getElementById("levelSelectBG").style.display = "none";
    document.getElementById("levelChooseBG").style.display = "flex";
};

// Canceling either one clears the modal boxes and goes back to the current proof.
document.getElementById("cancelSetLevel").onclick = clearLevelSelect;
document.getElementById("cancelChooseLevel").onclick = clearLevelSelect;

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
document.getElementById('ascribe').onkeypress = function(event) {
    if(event.key == 'Enter') {
        submitAscription();
    }
}

document.getElementById("submitExpression").onclick = submitExpr;
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
        levelButtons.forEach(function (b) {
            b.style.backgroundColor = '';
            b.style.color = '';
            b.innerHTML = b.dataset.name + '<br>☆☆☆';
        });
        setWorld(0);
        if(SERVER) {
            document.getElementById("levelChooseBG").style.display = "none";
            document.getElementById("levelSelectBG").style.display = "none";
            document.getElementById("loginBG").style.display = "flex";
        }
    }
};

document.getElementById("reduceDifficulty").onclick = function () {
    // Reduce the difficulty by one
    difficulty = Math.max(difficulty - 1, 0);
    // Update the display of the current difficulty in the proof
    updateCurrentDifficulty();
    // Save this new difficulty for the next level select
    setDifficulty(difficulty);
    // Re-typecheck, te create new labels and colors
    typecheck();
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

function showHint() {
    document.getElementById("hintBG").style.display = 'flex';
    document.getElementById(currentHint).style.display = 'block';
    localStorage.setItem(currentHint, "true");
}

document.getElementById("showHint").onclick = showHint;

// show and hide the about box
document.getElementById("about").onclick = function () {
    document.getElementById("aboutBG").style.display = "flex";
};
document.getElementById("doneAbout").onclick = function () {
    document.getElementById("aboutBG").style.display = "none";
};

function selectCurrentLevel(level) {
    setLevel(level, level.stage.rules);
    currentLevel = level;
    currentLevelButton = level.button;
    document.getElementById("currentLevel").innerText = "Level: " + level.name;
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
    suppressChecking = false;
    typecheck();
}

// When a node needs a new bound variable, we prompt the user with a modal dialog.
function getVariable(name) {
    const variableBG = document.getElementById("variableBG");
    const variableList = document.getElementById("variableList");
    const newvar = document.getElementById('newvar');

    variableBG.style.display = "flex";
    if(varnames.length > 0) {
        variableList.innerText = varnames.join(" ");
    } else {
        variableList.innerText = "<none>";
    }
    newvar.dataset.name = name;
    newvar.focus();
}

// When that modal dialog is submitted, we save the variable name and hide it.
function submitNewVariable() {
    const variableBG = document.getElementById("variableBG");
    const newvar = document.getElementById('newvar');

    if(!Narya.checkVariable(newvar.value).complete) {
        alert("Invalid variable name");
        newvar.focus();
    } else if(varnames.includes(newvar.value)) {
        // Enforce the Barendregt convention.
        alert("New variable name must be different from all existing variables");
        newvar.focus();
    } else {
        // Save it in the list of variable names
        varnames.push(newvar.value);
        // Attach it to the node that prompted for it.  NOTE: This doesn't allow a single node to contain more than one variable name.
        for (var i in nodes) {
            if (nodes[i].id === newvar.dataset.name) {
                nodes[i].name = newvar.value;
            }
        }
        // Save the variable associated to the rule box.  This allows us to remove it from the global list of used variables when that rule is deleted.
        document.getElementById(newvar.dataset.name).dataset.variable = newvar.value;
        // And empty and hide the modal dialog
        newvar.value = '';
        variableBG.style.display = "none";
        // And typecheck, since that was delayed
        typecheck();
    }
}

function cancelNewVariable() {
    const variableBG = document.getElementById("variableBG");
    const newvar = document.getElementById('newvar');
    for (var i in nodes) {
        if (nodes[i].id === newvar.dataset.name) {
            deleteRule(nodes[i].node);
        }
    }
    newvar.value = '';
    variableBG.style.display = "none";
}

// Similarly, submit the modal box that prompts for an ascription
function submitAscription() {
    const ascribeBG = document.getElementById("ascribeBG");
    const ascribe = document.getElementById('ascribe');
    const box = document.getElementById(ascribe.dataset.name);
    const ty = ascribe.value;
    if(ty === "") {
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
    ascribeBG.style.display = "none";
    // And typecheck, since that was delayed when the rule was added.
    typecheck();
}

// And the modal box that prompts for an expression
function submitExpr() {
    const exprBG = document.getElementById("expressionBG");
    const expr = document.getElementById('expression');
    const box = document.getElementById(expr.dataset.name);
    const e = expr.value;
    if(e === "") {
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
    exprBG.style.display = "none";
    // And typecheck, since that was delayed when the rule was added.
    typecheck();
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

function makePalette(palid, eltid) {
    const pal = document.getElementById(palid);
    const elt = document.getElementById(eltid);
    // Create palette of buttons
    PALETTE.forEach((chr) => addToPalette(pal, elt, chr));
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
    // Detect shortcut key sequences
    elt.addEventListener('input', () => {
        var text = elt.value;
        KEYS.forEach(function (entry) {
            entry.regexes.forEach(function (re) {
                text = text.replace(re, entry.unicode);
            });
        });
        elt.value = text;
    });
}

makePalette('paramPalette', 'parameters');
makePalette('varPalette', 'variables');
makePalette('hypPalette', 'hypotheses');
makePalette('conclPalette', 'conclusion');
makePalette('ascPalette', 'ascribe');
makePalette('expressionPalette', 'expression');
makePalette('wirePalette', 'wire');

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
    // Connections going straight across from an assumption to a subgoal should be straight.  The flowchart connector bends them out for some reason.
    if(edge.source == edge.target) {
        if(edge.endpoints[0].parameters.sort === 'assumption' &&
           edge.endpoints[1].parameters.sort === 'subgoal' &&
           edge.endpoints[0].parameters.label === edge.endpoints[1].parameters.label) {
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

    const diagram = document.getElementById('diagram');
    
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
        instance.revalidate(c.source);

        // Clear the label overlays.  For some reason, if we *delete* all the overlays here and then add later the ones we want, some of them don't get displayed until the nodes are dragged around.  So instead we set the label text of all existing overlays to empty here, and later we delete only the overlays with empty label text.
        // TODO: Try deleting them and then calling revalidate later.
        const ovl = c.getOverlay("label");
        if(!c.parameters.ty && ovl) {
            ovl.setLabel("");
        }

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

    // Call to Narya to do the typechecking.  The result is an object of type {complete:bool, error:string opt, labels, diagnostics}.
    const result = Narya.check(nodes, edges);

    // Display results
    if(result.error) {
        console.log(result.error);
        alert ("Internal error: see console");
        diagram.style.backgroundColor = "";
        conclusion_node.style.backgroundColor = "";
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
                                        }
                                        if(endpoint.parameters.hasValue) {
                                            cssClass = cssClass + " connLabelValue";
                                        }
                                        d.innerHTML = '<div class="' + cssClass + '">' + lbl + "</div>";
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
        // Now delete the label overlays for the connectors that didn't get set.
        edges.forEach(function(c) {
            const ovl = c.connector.getOverlay("label");
            if(ovl && ovl.getLabel() === "") {
                c.connector.removeOverlay("label");
            }
        });
        // If the level is complete, color the goal and level green.
        if(result.complete) {
            diagram.style.backgroundColor = COLORS[difficulty][0].backgroundColor;
            conclusion_node.style.color = COLORS[difficulty][1].color;
            conclusion_node.style.backgroundColor = COLORS[difficulty][1].backgroundColor;
            if(currentLevel) {
                const past = getPast(null, currentLevel);
                const present = { complete: true, difficulty: Math.max(difficulty, past.difficulty) };
                currentLevelButton.style.color = COLORS[present.difficulty][1].color;
                currentLevelButton.style.backgroundColor = COLORS[present.difficulty][1].backgroundColor;
                currentLevelButton.innerHTML = currentLevelButton.dataset.name + "<br>" + getStars(present)
                // Record completion, with the difficulty, in local storage
                const key = JSON.stringify(saveable(currentLevel));
                const value = present;
                localStorage.setItem(key, JSON.stringify(value));
                if(SERVER) {
                    // Save it to the server too
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
                    const data = { email: localStorage.getItem("email"), key: key, value: value, difficulty: difficulty, world: currentWorld };
                    xhr.send(JSON.stringify(data));
                }
            }
        } else {
            // If there are fatal errors, remove any green color on the goal and indicate the errors somehow.
            diagram.style.backgroundColor = "";
            conclusion_node.style.backgroundColor = "";
            var somethingRed = false;
            // result.diagnostics is an array of objects of type {isfatal:bool, locs, text:string}, where locs is an array of objects representing either an edge or a port, with type {isEdge:bool, id:string, sort:string optdef, label:string optdef, hasValue:bool}.
            result.diagnostics.forEach(function (d) {
                // Make the edges with fatal errors red, if we're not on master difficulty
                if(d.isfatal && difficulty <= 1) {
                    d.locs.forEach(function (loc) {
                        if(loc.isEdge) {
                            const edge = connections[loc.id];
                            setStrokeColor(edge, "#ff0000");
                            instance.revalidate(edge.source);
                            console.log(d.text);
                            somethingRed = true;
                            if(edge.parameters.userLabel) {
                                edge.parameters.userLabel.style.color = "#ff0000";
                            }
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
                                                        ty = "? ∈ " + ty;
                                                    }
                                                    if(endpoint.parameters.side === "upper") {
                                                        d.innerHTML = '<div class="upperInputLabel">' + ty + "</div>";
                                                    } else {
                                                        // Lower is the default
                                                        d.innerHTML = '<div class="lowerInputLabel">' + ty + "</div>";
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
    }
}

// Check that the parameters and variables have types, split up grouped variables, and associate them to types.
function checkType(sort, eg) { return function(v) {
    v = v.split(/ *: */);
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

    try {
        parameters = document.getElementById("parameters").value.
            split(/[\r\n]+/).
            filter(Boolean).
            map(checkType('parameters', 'A : Type')).
            flat();
        variables = document.getElementById("variables").value.
            split(/[\r\n]+/).
            filter(Boolean).
            map(checkType('variables', 'a : A')).
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

    setLevel({
        parameters: parameters,
        variables: variables,
        hypotheses: hypotheses,
        conclusion: conclusion,
    }, "all");

    currentLevel = undefined;
    currentLevelButton = undefined;
    document.getElementById("currentLevel").innerText = "Level: Custom";
}

function setLevel(level, rulesAllowed) {
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

    // Typecheck everything.
    const result = Narya.start(parameters, variables, hypotheses, conclusion);
    if (result.error) {
        alert(result.error);
        return;
    }
    console.log("initialized Narya");

    // Now we know the new level is valid, so we blow away the old one and set up the new one.

    suppressChecking = true;

    // Set the global varnames to the new one.
    varnames = new_varnames;

    // Hide the modal dialogs for choosing levels or setting custom levels, and empty the custom text fields.
    clearLevelSelect();

    // Turn on the "cancel" buttons and "proof will be erased" warnings for future level-selections.
    document.getElementById("setLevelWarning").style.display = '';
    document.getElementById("cancelChooseLevel").style.display = '';
    document.getElementById("cancelSetLevel").style.display = '';

    // Delete all the existing nodes, to prepare for a new level.  We have to remove the jsPlumb connections and endpoints first, or they end up stashed in the corner of the window.
    instance.select().deleteAll();    // This removes all connections
    nodes.forEach((x) => {
        instance.removeAllEndpoints(x.node);
        x.node.remove();
    });
    nodes = [];

    // Hide the rules that aren't allowed for this stage
    for (const prule of document.getElementById('palette').children) {
        if((rulesAllowed == "all" && excludeFromAll.indexOf(prule.id) === -1) || prule.id == 'buttons' || rulesAllowed.includes(prule.id)) {
            prule.style.display = '';
        } else {
            prule.style.display = 'none';
        }
    }

    // We space the variables and hypotheses out vertically equally on the left side.
    const num_inputs = variables.length + hypotheses.length;
    const height_inc = diagram.offsetHeight / (num_inputs + 1);
    var height = height_inc;

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
        diagram.appendChild(vbx);
        nodes.push({id: vbx.id, name: v.name, rule: 'variable', node: vbx, value: v.ty});
        instance.addEndpoint(vbx, {
            anchor: "Right",
            source: true,
            parameters: { sort: "output", hasValue: true },
            maxConnections: -1,
            paintStyle: { fill: VALUECOLOR },
            connectorStyle: { stroke: VALUECOLOR, strokeWidth: 2 }
        });
        height += height_inc;
    }

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
        diagram.appendChild(hyp);
        nodes.push({id: hyp.id, rule: 'hypothesis', node: hyp, value : h.ty});
        instance.addEndpoint(hyp, {
            anchor: "Right",
            source: true,
            parameters: {sort: "output"},
            maxConnections: -1
        });
        height += height_inc;
    }

    // Similarly, the conclusion goes on the right.
    const concl = document.createElement("div");
    concl.dataset.rule = "conclusion";
    concl.innerText = conclusion.ty;
    concl.className = 'basic contextual rule';
    concl.style.textAlign = 'center';
    concl.style.position = 'absolute';
    concl.style.top = "50%";
    concl.id = conclusion.id;
    concl.onmousedown = toggleDragSelected(concl);
    diagram.appendChild(concl);
    // For some reason, setting .right here instead produces weird behavior with dragging.  It also apparently has to be after appendChild for the width to be calculated correctly.
    concl.style.left = (diagram.clientWidth - 50 - concl.clientWidth) + 'px';
    conclusion_node = concl;
    nodes.push({id: concl.id, rule: 'conclusion', node: concl, value: conclusion.ty});
    instance.addEndpoint(concl, { anchor: "Left", target: true, parameters: {sort: "input"} });

    // Set the visible difficulty
    updateCurrentDifficulty();

    // Finally, we typecheck.  It will fail since the user hasn't added any connections yet, but it adds labels to ports.
    suppressChecking = false;
    typecheck();

    // Done setting up the new level!

    // Now we display any associated hints, as long as the user hasn't solved this level yet or hasn't seen the hint yet
    currentHint = level.hint;
    if(currentHint) {
        document.getElementById("showHint").style.display = 'block';
        const past = getPast(null, level);
        if(!past.complete || !localStorage.getItem(level.hint)) {
            showHint();
        }
    } else {
        document.getElementById("showHint").style.display = 'none';
    }
}

function clearLevelSelect () {
    document.getElementById("levelSelectBG").style.display = "none";
    document.getElementById("levelChooseBG").style.display = "none";
    document.getElementById("chooseLevelWarning").style.visibility = 'visible';
    document.getElementById("parameters").value = "";
    document.getElementById("variables").value = "";
    document.getElementById("hypotheses").value = "";
    document.getElementById("conclusion").value = "";
}

// Display hints on certain levels
document.getElementById("hintBG").onclick = function() {
    const hintBG = document.getElementById("hintBG");
    hintBG.style.display = 'none';
    Array.prototype.forEach.call(hintBG.getElementsByClassName("hint"), function (x) {
        x.style.display = 'none';
    });
}
