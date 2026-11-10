// What each kind of block says in an English proof, as a template.  Hovering over a block on the
// diagram (or tapping it, on a touchscreen) shows its sentence, filled in with the statements on
// its own ports.  To change what a block says, edit its template here and rebuild.
//
// The name of each entry is the block's rule, as in the data-rule attributes of static/index.html.
// A block with no entry here has no sentence, so it shows no tooltip on the diagram.
//
// A template is ordinary text with these two things in it:
//
//   {port}      What the port carries.  For a port carrying a statement, that is the statement; for
//               one carrying a value, it is the value, such as b.
//   {port.type} The set that the value on a port belongs to, such as B.
//
//   [...]       A part to leave out unless all the ports named inside it have something to say.
//               This is for the ports that only some blocks show: the condition of a quantifier
//               over ℝ₊ or below n, and the inputs of an algebra block, of which there may be none.
//
// A port is named by its sort -- input, output, assumption or subgoal -- and, if the block has
// several of that sort, a colon and its label: {input:implication}, or {subgoal:left}.  (An
// assumption and a subgoal are the left and right sides of a bracket, respectively.)  The label of
// each port is in addEndpointsForRule in client/main.js.
//
// A statement that isn't known yet, because nothing has been wired up there, appears as BLANK.  A
// template naming a port that its block doesn't have shows the {...} as it is written, so that a
// typo is easy to see; test/e2e/sentences.spec.js checks that there are none.  A "\n" in a template
// starts a new line.
//
// The statements come from what the diagram is already showing at the current difficulty (see
// recordStatements in client/main.js), so a sentence never gives away one the player has to work out.

export const BLANK = "___";

export const SENTENCES = {
    // What the level gives and asks for.
    hypothesis: "By hypothesis, {output}.",
    variable: "Let {output}∈{output.type} be given.",
    conclusion: "We want to prove {input}.",

    // Conjunction and disjunction.
    andI: "Since {input:fst} and {input:snd}, we have {output}.",
    andE: "Since {input}, we have both {output:fst} and {output:snd}.",
    orI1: "Since {input:left}, we have {output}.",
    orI2: "Since {input:right}, we have {output}.",
    orE: "Since {input}, we consider two cases.\n" +
        "Case 1: assume {assumption:left}; we will prove {subgoal:left}.\n" +
        "Case 2: assume {assumption:right}; we will prove {subgoal:right}.",

    // Implication and equivalence.
    impI: "Assume {assumption}; we will prove {subgoal}.",
    impE: "Since {input:implication} and {input:antecedent}, we have {output}.",
    iffI: "We prove both directions.\n" +
        "First, assume {assumption:ltor}; we will prove {subgoal:ltor}.\n" +
        "Conversely, assume {assumption:rtol}; we will prove {subgoal:rtol}.",
    iffE1: "Since {input:implication} and {input:antecedent}, we have {output}.",
    iffE2: "Since {input:implication} and {input:antecedent}, we have {output}.",

    // The quantifiers.
    allI: "Let {assumption}∈{assumption.type}[ with {assumption:condition}] be arbitrary; we will prove {subgoal}.",
    allE: "Since {input:universal}, taking {input:element}[ with {input:condition}] we have {output}.",
    exI: "Taking {input:element}∈{input:element.type}, we have {input:property}[ and {input:condition}], so {output}.",
    exE: "Since {input}, we can choose {output:element}∈{output:element.type}[ with {output:condition}] such that {output:property}.",
    uexI: "Taking {input:element}∈{input:element.type}, we have {input:property} and {input:unique}, so {output}.",
    uexE: "Since {input}, we can choose {output:element}∈{output:element.type} such that {output:property} and {output:unique}.",

    // Negation and contradiction.
    negI: "To prove {output}, suppose {assumption}; we will derive a contradiction.",
    negE: "Since {input:negation} and {input:statement} contradict each other, we have {output}.",
    cnegI: "To prove {output}, suppose for the sake of contradiction that {assumption}.",
    botE: "We have reached a contradiction, so {output}.",
    topI: "{output} is always true.",

    // Saying what a wire carries.
    asc: "That is, {output}.",

    // Algebra.
    alg: "By algebra[ from {input}], we have {output}.",
    algneq: "By algebra[ from {input}], we have {output}.",
    algplus: "By algebra[ from {input}], we have {output}.",

    // Facts about numbers.
    integral: "Since {input:xy0}, we have {output}.",
    deceq: "Comparing {input:x} and {input:y}, we have {output}.",
    tord: "Comparing {input:x} and {input:y}, we have {output}.",
    arch: "By the Archimedean property, we can choose {output:element}∈{output:element.type} such that {output:property}.",
    zton: "Since {input:nonneg}, we can choose {output:element}∈{output:element.type} such that {output:property}.",
    frac: "Since {input:x} is rational, we can choose integers {output:numerator} and {output:denominator} " +
        "such that {output:atleastone}, {output:fraction} and {output:lowest}.",
    omega: "Since ω is bigger than every real number, we have {output}.",

    // The natural numbers.
    natE: "We consider two cases for {input}.\n" +
        "If {input}=0, we will prove {subgoal:zero}.\n" +
        "If {input}={assumption:pred}+1 for some {assumption:pred}∈{assumption:pred.type}, we will prove {subgoal:suc}.",
    natInd: "We prove {output} by strong induction.\n" +
        "Let {assumption:n}∈{assumption:n.type} and assume {assumption:IH}; we will prove {subgoal:step}.",
};

const PLACEHOLDER = /\{(\w+)(?::(\w+))?(\.type)?\}/g;

// The ports a template names, as [sort, label, wantsType], for checking them against a block's own.
export function portsNamedIn(template) {
    return Array.from(template.matchAll(PLACEHOLDER), (m) => [m[1], m[2] || "", !!m[3]]);
}

// "A", "A and B", or "A, B and C": an algebra block can have any number of inputs.
function listed(items) {
    return items.length < 2 ? items.join("") : items.slice(0, -1).join(", ") + " and " + items[items.length - 1];
}

// Fill in a template.  ports(sort, label) says what the block has to say on the ports of that name:
// null if it has no such port, and otherwise a list of { text, type }, one for each port by that
// name that has something to say.  The text is split up before anything is filled in, so that
// brackets or braces in a statement can't be taken for part of the template.
export function renderSentence(template, ports) {
    var missing = false;
    const fill = function (text) {
        return text.replace(PLACEHOLDER, function (whole, sort, label, wantsType) {
            const found = ports(sort, label || "");
            if(found === null) { return whole; }
            const said = found.map(function (p) { return wantsType ? p.type : p.text; }).filter(Boolean);
            if(said.length === 0) { missing = true; return BLANK; }
            return listed(said);
        });
    };
    // Splitting on a captured [...] puts the optional parts at the odd positions.
    return template.split(/(\[[^\]]*\])/).map(function (part, i) {
        if(i % 2 === 0) { return fill(part); }
        missing = false;
        const filled = fill(part.slice(1, -1));
        return missing ? "" : filled;
    }).join("");
}
