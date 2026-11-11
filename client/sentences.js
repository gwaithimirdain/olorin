// What each kind of block says in an English proof, as a template.  On novice difficulty, hovering
// over a block on the diagram (or tapping it, on a touchscreen) shows its sentence, filled in with
// the statements on its own ports; and once the level is complete, the "Proof in English" button
// shows the whole proof, put together from the sentences of its blocks.  To change what a block
// says, edit its template here and rebuild.
//
// The name of each entry is the block's rule, as in the data-rule attributes of static/index.html.
// A block with no entry here has no sentence, so it shows no tooltip on the diagram.  The entry
// "natE in natInd" is for a natE that splits the variable of the natInd it is wired straight into,
// whose two cases are the base case and the induction step.
//
// A template is ordinary text with these things in it:
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
// A bracket's template also has a hole for the proof of each of its subgoals, on a line of its own,
// named like the subgoal: {proof} for the unlabeled subgoal of an impI, say, and {proof:left} for
// the subgoal:left of an orE.  In the whole proof, the hole is where the blocks inside that part of
// the bracket go, indented; in a block's own sentence, it appears as "...".
//
// A statement that isn't known yet, because nothing has been wired up there, appears as BLANK.  A
// template naming a port that its block doesn't have shows the {...} as it is written, so that a
// typo is easy to see; test/e2e/sentences.spec.js checks that there are none, and that every
// subgoal has its hole.  A "\n" in a template starts a new line, and a [...] can't run across one.

export const BLANK = "___";

// What a hole for a subproof says in a block's own sentence.
export const ELLIPSIS = "...";

// What the whole proof says for a subgoal whose proof has nothing to say, as when a bracket's
// subgoal is wired straight from its own assumption.
export const TRIVIAL = "This is trivial.";

export const SENTENCES = {
    // What the level gives and asks for.
    hypothesis: "Suppose {output}.",
    variable: "Suppose {output}∈{output.type}.",
    conclusion: "We want to prove {input}.",

    // Conjunction and disjunction.
    andI: "Since {input:fst} and {input:snd}, we have {output}.",
    andE: "Since {input}, we have both {output:fst} and {output:snd}.",
    orI1: "Since {input:left}, we have {output}.",
    orI2: "Since {input:right}, we have {output}.",
    orE: "Since {input}, we consider two cases.\n" +
        "Case 1: assume {assumption:left}; we will prove {subgoal:left}.\n{proof:left}\n" +
        "Case 2: assume {assumption:right}; we will prove {subgoal:right}.\n{proof:right}",

    // Implication and equivalence.
    impI: "Assume {assumption}; we will prove {subgoal}.\n{proof}",
    impE: "Since {input:implication} and {input:antecedent}, we have {output}.",
    iffI: "We prove both directions.\n" +
        "First, assume {assumption:ltor}; we will prove {subgoal:ltor}.\n{proof:ltor}\n" +
        "Conversely, assume {assumption:rtol}; we will prove {subgoal:rtol}.\n{proof:rtol}",
    iffE1: "Since {input:implication} and {input:antecedent}, we have {output}.",
    iffE2: "Since {input:implication} and {input:antecedent}, we have {output}.",

    // The quantifiers.
    allI: "Let {assumption}∈{assumption.type} be arbitrary[ such that {assumption:condition}]; we will prove {subgoal}.\n{proof}",
    allE: "Since {input:universal} and {input:element}∈{input:element.type}[ with {input:condition}], we have {output}.",
    exI: "Since {input:element}∈{input:element.type}[ and {input:condition}] satisfies {input:property}, we have {output}.",
    exE: "Since {input}, let {output:element}∈{output:element.type}[ with {output:condition}] be such that {output:property}.",
    uexI: "Since {input:element}∈{input:element.type} satisfies {input:property} and {input:unique}, we have {output}.",
    uexE: "Since {input}, let {output:element}∈{output:element.type} be such that {output:property} and {output:unique}.",

    // Negation and contradiction.
    negI: "To prove {output}, assume for contradiction that {assumption}.\n{proof}",
    negE: "Since {input:negation} and {input:statement} contradict each other, we have {output}.",
    cnegI: "To prove {output}, assume for contradiction that {assumption}.\n{proof}",
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
    arch: "By the Archimedean property, let {output:element}∈{output:element.type} be such that {output:property}.",
    zton: "Since {input:nonneg}, let {output:element}∈{output:element.type} be such that {output:property}.",
    frac: "Since {input:x} is rational, let {output:numerator}∈{output:numerator.type} and {output:denominator}∈{output:denominator.type} " +
        "be such that {output:atleastone}, {output:fraction}, and {output:lowest}.",
    omega: "Since ω is larger than every real number, we have {output}.",

    // The natural numbers.
    natE: "Since {input}∈{input.type}, there are two cases.\n" +
        "Case 1: Assume {input}=0; we will prove {subgoal:zero}.\n{proof:zero}\n" +
        "Case 2: Assume {input}={assumption:pred}+1 for some {assumption:pred}∈{assumption:pred.type}; we will prove {subgoal:suc}.\n{proof:suc}",
    "natE in natInd": "Since {input}∈{input.type}, there are two cases.\n" +
        "Base case: Assume {input}=0; we will prove {subgoal:zero}.\n{proof:zero}\n" +
        "Induction step: Assume {input}={assumption:pred}+1 for some {assumption:pred}∈{assumption:pred.type}; we will prove {subgoal:suc}.\n{proof:suc}",
    natInd: "Let {assumption:n}∈{assumption:n.type} and assume inductively {assumption:IH}; we will prove {subgoal:step}.\n{proof:step}",
};

const PLACEHOLDER = /\{(\w+)(?::(\w+))?(\.type)?\}/g;
const HOLE = /^\{proof(?::(\w+))?\}$/;

// The ports a template names, as [sort, label, wantsType], for checking them against a block's own.
// The holes for subproofs aren't ports.
export function portsNamedIn(template) {
    return Array.from(template.matchAll(PLACEHOLDER), (m) => [m[1], m[2] || "", !!m[3]])
        .filter((p) => p[0] !== "proof");
}

// The labels of the subgoals a template has holes for.
export function holesIn(template) {
    return template.split("\n").map((line) => line.match(HOLE)).filter(Boolean).map((m) => m[1] || "");
}

// "A", "A and B", or "A, B and C": an algebra block can have any number of inputs.
function listed(items) {
    return items.length < 2 ? items.join("") : items.slice(0, -1).join(", ") + " and " + items[items.length - 1];
}

// Fill in one line of a template.  ports(sort, label) says what the block has to say on the ports
// of that name: null if it has no such port, and otherwise a list of { text, type }, one for each
// port by that name that has something to say.  The text is split up before anything is filled
// in, so that brackets or braces in a statement can't be taken for part of the template.
function fillLine(line, ports) {
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
    return line.split(/(\[[^\]]*\])/).map(function (part, i) {
        if(i % 2 === 0) { return fill(part); }
        missing = false;
        const filled = fill(part.slice(1, -1));
        return missing ? "" : filled;
    }).join("");
}

// Fill in a template, line by line, with ports as for fillLine: each line is either { text }, or
// { proof: label } for the hole where the proof of the subgoal with that label goes.
export function sentenceLines(template, ports) {
    return template.split("\n").map(function (line) {
        const hole = line.match(HOLE);
        return hole ? { proof: hole[1] || "" } : { text: fillLine(line, ports) };
    });
}

// A block's own sentence: its template filled in, with "..." for each subproof.
export function renderSentence(template, ports) {
    return sentenceLines(template, ports).map(function (line) {
        return line.proof === undefined ? line.text : ELLIPSIS;
    }).join("\n");
}
