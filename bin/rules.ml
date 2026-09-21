open Util
open Core
module RuleMap = Map.Make (String)

(* This file defines the "rules" at the OCaml level.  These are the "blocks" that can be used in Olorin graphs. *)

type match_branch =
  | Branch : {
      assumptions : (string, 'a) Vec.t;
      constr : Constr.t;
      subgoal : string;
    }
      -> match_branch

(* This is the type of abstract rules.  The string arguments are the labels of the corresponding ports.  When there is only one input port, or only one output port, it doesn't have a label. *)
type rule =
  (* A tuple assembles its inputs into the fields of a record.  If it is 'unordered', its two
     inputs can be wired up in either order: we try the natural reading first and the swapped one
     second, so a player who puts the proofs the other way round still gets a proof.  Only a tuple
     with exactly two inputs can be unordered. *)
  | Tuple of { inputs : (string option * string * (string * string list)) list; unordered : bool }
  | Fields of { outputs : ((string * int list) * string) list }
  | Constr of { inputs : string list; constr : Constr.t }
  | Match of { branches : match_branch list; asc_pre : string option }
  | Coconstr of { constr : Constr.t; outputs : (bool * string) list }
  (* Application and abstraction include an optional field because ⇒, ∀, and ¬ are actually records, so for Narya's internals we need to tuple and project in addition to applying and abstracting. *)
  (* The inputs of an application are the port carrying the function and then one port per argument
     it is applied to, in order: ∀x∈ℝ₊ takes the positivity of x as a second argument alongside x. *)
  | App of { field : (string * int list) option; inputs : string * string list }
  | Neg of { field : string * int list; inputs : string * string; implicit_pre : string }
  | Abs of {
      field : (string * string list) option;
      has_value : bool;
      (* Assumptions bound after the main (unlabeled) one, as further nested lambdas: ∀x∈ℝ₊ binds
         the positivity of x alongside x itself, on a labeled port of its own. *)
      extras : string list;
      (* Allow testing for the presence of a field in the goal type, and if it isn't there, insert a specified function (with implicit first argument).  The intended example is so that a single rule can be both proof-of-negation and proof-by-contradiction. *)
      implicit_post : (string * string) option;
    }
  | Asc
  | Expr
  (* Algebra blocks, with flags.  If "plus" is on, then Z3 can decide an absolute value, a minimum or a maximum on its own; otherwise the hypotheses must settle each such case first.  If "neq" is on, then Z3 can solve inequalities as goals; otherwise it insists the user deal with them using proof by contradiction. *)
  | Algebra of { sort : [ `None | `Plus | `Neq ] }
  | Var
  | Conclusion
  | User of {
      consts : string list list;
      (* The arguments the axioms take after any implicit first one, in order. *)
      inputs : user_input list;
      (* If set, the axioms take their first argument implicitly from the goal: either the goal
         itself, a type, or one of the arguments of the constant the goal is an application of,
         such as the P of "forall ℕ P".  The block's term applies them with ImplicitApp, so it is a
         checking term rather than a synthesizing one.  Such a block can't take its conclusion
         apart, since that would need a synthesizing term, so its outputs must be empty. *)
      implicit_first : Raw.implicit_source option;
      (* Some user axioms conclude a statement built up out of ∃ and ∧.  Rather than making the
         player follow such a block with the ∃- and ∧-eliminations that take that statement apart
         again, the block takes its own conclusion apart, handing out one output port per piece.
         Each step takes apart the *last* component of the step before it, which is how a nest of
         ∃s and ∧s comes apart one piece at a time; those in-between components are ports of the
         block's own machinery rather than ones the player sees.  An empty list is a block with the
         usual single unlabeled output carrying the conclusion itself. *)
      outputs : destructure list;
    }

(* An argument of a User rule's axiom is either an ordinary input port with the given label, or a
   bracket on the side of the block, like those of ∨-elimination, for an argument that is a
   function: a case of a proof by cases.  A bracket's assumption ports are bound as nested lambdas,
   outermost first, around what its subgoal port is wired to.  The flag on an assumption says that
   it carries a value the player names, so it takes the next of the block's bound variable names;
   the brackets take theirs first, in order, and the steps of 'outputs' take those left over. *)
and user_input =
  | Arg of string
  | Bracket of { assumptions : (bool * string) list; subgoal : string }

(* One step of that.  A datatype with a single constructor -- an ∃ -- comes apart by matching it,
   which binds a variable for each of its components; the flag says which of them carry a value the
   player names, and those take the block's bound variable names in order.  A record -- a ∧ -- comes
   apart by projecting out its fields, which binds nothing: each such port simply carries that
   projection of what the steps before it left. *)
and destructure =
  | Open of Constr.t * (bool * string) list
  | Project of ((string * int list) * string) list

let labels_of = function
  | Open (_, outs) -> List.map snd outs
  | Project flds -> List.map snd flds

(* The output ports such a block shows the player: every component of every step, except the last
   component of each step that the step after it takes apart. *)
let rec visible_outputs : destructure list -> string list = function
  | [] -> []
  | [ step ] -> labels_of step
  | step :: rest ->
      let labels = labels_of step in
      let n = List.length labels in
      List.filteri (fun i _ -> i < n - 1) labels @ visible_outputs rest

(* Here are the specific rules currently used in graphs.  The port labels used here have to match those used in the JavaScript.  It would be better if the JavaScript could get them from here. *)
let rules =
  RuleMap.of_list
    [
      ("variable", Var);
      ("hypothesis", Var);
      ("conclusion", Conclusion);
      ("andE", Fields { outputs = [ (("fst", []), "fst"); (("snd", []), "snd") ] });
      ( "andI",
        Tuple
          {
            inputs = [ (None, "fst", ("fst", [])); (None, "snd", ("snd", [])) ];
            (* A conjunction's two halves are proved the same way round or the other; either is a
               proof, so the block takes them in either order. *)
            unordered = true;
          } );
      ( "orE",
        Match
          {
            branches =
              [
                Branch { assumptions = [ "left" ]; constr = Constr.intern "left"; subgoal = "left" };
                Branch
                  { assumptions = [ "right" ]; constr = Constr.intern "right"; subgoal = "right" };
              ];
            asc_pre = None;
          } );
      ("orI1", Constr { inputs = [ "left" ]; constr = Constr.intern "left" });
      ("orI2", Constr { inputs = [ "right" ]; constr = Constr.intern "right" });
      ("impE", App { field = Some ("implies", []); inputs = ("implication", [ "antecedent" ]) });
      ( "impI",
        Abs { field = Some ("implies", []); has_value = false; extras = []; implicit_post = None }
      );
      ("iffE1", App { field = Some ("ltor", []); inputs = ("implication", [ "antecedent" ]) });
      ("iffE2", App { field = Some ("rtol", []); inputs = ("implication", [ "antecedent" ]) });
      ( "iffI",
        Tuple
          {
            inputs = [ (Some "ltor", "ltor", ("ltor", [])); (Some "rtol", "rtol", ("rtol", [])) ];
            unordered = false;
          } );
      ( "exE",
        Coconstr
          { constr = Constr.intern "exists"; outputs = [ (true, "element"); (false, "property") ] }
      );
      ("exI", Constr { inputs = [ "element"; "property" ]; constr = Constr.intern "exists" });
      ("allE", App { field = Some ("forall", []); inputs = ("universal", [ "element" ]) });
      ( "allI",
        Abs { field = Some ("forall", []); has_value = true; extras = []; implicit_post = None } );
      (* The quantifiers over the special sets ℝ₊ and [n].  Each carries the condition defining its
         set -- 0<x, or x<n -- on a port of its own alongside the value port for x: the
         field of "forallpos" and "forallbelow" takes it as a second argument, and the constructor
         of "existspos" and "existsbelow" as a second component. *)
      ( "exposE",
        Coconstr
          {
            constr = Constr.intern "existspos";
            outputs = [ (true, "element"); (false, "positive"); (false, "property") ];
          } );
      ( "exposI",
        Constr
          { inputs = [ "element"; "positive"; "property" ]; constr = Constr.intern "existspos" } );
      ( "allposE",
        App { field = Some ("forallpos", []); inputs = ("universal", [ "element"; "positive" ]) } );
      ( "allposI",
        Abs
          {
            field = Some ("forallpos", []);
            has_value = true;
            extras = [ "positive" ];
            implicit_post = None;
          } );
      ( "exbelowE",
        Coconstr
          {
            constr = Constr.intern "existsbelow";
            outputs = [ (true, "element"); (false, "below"); (false, "property") ];
          } );
      ( "exbelowI",
        Constr { inputs = [ "element"; "below"; "property" ]; constr = Constr.intern "existsbelow" }
      );
      ( "allbelowE",
        App { field = Some ("forallbelow", []); inputs = ("universal", [ "element"; "below" ]) } );
      ( "allbelowI",
        Abs
          {
            field = Some ("forallbelow", []);
            has_value = true;
            extras = [ "below" ];
            implicit_post = None;
          } );
      ( "negE",
        Neg
          {
            field = ("negation", []);
            inputs = ("negation", "statement");
            implicit_pre = "contradict";
          } );
      ( "negI",
        Abs { field = Some ("negation", []); has_value = false; extras = []; implicit_post = None }
      );
      ( "cnegI",
        (* Classical proof-by-contradiction *)
        Abs
          {
            field = Some ("negation", []);
            has_value = false;
            extras = [];
            implicit_post = Some ("negation", "negneg");
          } );
      ("botE", Match { branches = []; asc_pre = Some "⊥" });
      ("topI", Tuple { inputs = []; unordered = false });
      ("asc", Asc);
      ("expr", Expr);
      ("alg", Algebra { sort = `None });
      ("algneq", Algebra { sort = `Neq });
      ("algplus", Algebra { sort = `Plus });
      ( "integral",
        User
          {
            consts =
              [
                [ "ℕ"; "integral" ];
                [ "ℤ"; "integral" ];
                [ "ℚ"; "integral" ];
                [ "ℝ"; "integral" ];
                [ "𝕊"; "integral" ];
              ];
            inputs = [ Arg "x"; Arg "y"; Arg "xy0" ];
            implicit_first = None;
            outputs = [];
          } );
      ( "deceq",
        User
          {
            consts =
              [
                [ "ℕ"; "deceq" ];
                [ "ℤ"; "deceq" ];
                [ "ℚ"; "deceq" ];
                [ "ℝ"; "deceq" ];
                [ "𝕊"; "deceq" ];
              ];
            inputs = [ Arg "x"; Arg "y" ];
            implicit_first = None;
            outputs = [];
          } );
      ( "tord",
        User
          {
            consts =
              [
                [ "ℕ"; "tord" ]; [ "ℤ"; "tord" ]; [ "ℚ"; "tord" ]; [ "ℝ"; "tord" ]; [ "𝕊"; "tord" ];
              ];
            inputs = [ Arg "x"; Arg "y" ];
            implicit_first = None;
            outputs = [];
          } );
      (* The Archimedean property: every real is below some natural number.  The axiom concludes an
         ∃, so the block destructs it, giving out the natural number n it produces on a value port
         and the proof that x<n on another.  There is no 𝕊 version: the surreals are exactly the
         number system where this fails. *)
      ( "arch",
        User
          {
            consts = [ [ "ℝ"; "archimedean" ] ];
            inputs = [ Arg "x" ];
            implicit_first = None;
            outputs = [ Open (Constr.intern "exists", [ (true, "element"); (false, "property") ]) ];
          } );
      (* An integer that is at least zero is a natural number.  The proof that it is nonnegative is
         an input of its own, alongside the integer; what comes out is that natural number and the
         equation identifying it with the integer we started from. *)
      ( "zton",
        User
          {
            consts = [ [ "ℤ"; "tonat" ] ];
            inputs = [ Arg "x"; Arg "nonneg" ];
            implicit_first = None;
            outputs = [ Open (Constr.intern "exists", [ (true, "element"); (false, "property") ]) ];
          } );
      (* Every rational is a fraction in lowest terms.  Its axiom concludes two nested ∃s, one for
         each side of the fraction, and then a ∧ of the three things that hold of the two of them,
         so the block comes apart in four steps: the ∃s hand out the numerator and the denominator,
         and the projections hand out each half of the ∧ in turn.  The components in between --
         "rest", "conjunction" and "others" -- are the block's own, so the player sees five ports:
         the two numbers, and the three statements about them.  Two value ports mean two bound
         variables, which the block's variable dialog asks for in this order. *)
      ( "frac",
        User
          {
            consts = [ [ "ℚ"; "frac" ] ];
            inputs = [ Arg "x" ];
            implicit_first = None;
            outputs =
              [
                Open (Constr.intern "exists", [ (true, "numerator"); (false, "rest") ]);
                Open (Constr.intern "exists", [ (true, "denominator"); (false, "conjunction") ]);
                Project [ (("fst", []), "atleastone"); (("snd", []), "others") ];
                Project [ (("fst", []), "fraction"); (("snd", []), "lowest") ];
              ];
          } );
      (* Every real number is smaller than ω.  This one concludes a relation rather than an ∃, so it
         has the ordinary single output, carrying x<ω. *)
      ( "omega",
        User
          {
            consts = [ [ "ℝ"; "ltomega" ] ];
            inputs = [ Arg "x" ];
            implicit_first = None;
            outputs = [];
          } );
      (* Proof by cases on a natural number n: it is either 0 or the successor of some k. *)
      ( "natE",
        Match
          {
            branches =
              [
                Branch { assumptions = []; constr = Constr.intern "zero"; subgoal = "zero" };
                Branch { assumptions = [ "pred" ]; constr = Constr.intern "suc"; subgoal = "suc" };
              ];
            asc_pre = Some "ℕ";
          } );
      (* Strong induction on the natural numbers: to prove ∀n∈ℕ,P(n), prove P(n) for a natural
         number n assuming ∀k∈[n],P(k).  The axiom's first argument is the P of the goal
         "forall ℕ P", its second, so it takes that implicitly from the goal, and the step is a
         bracket binding n, on a value port, and assuming the inductive hypothesis. *)
      ( "natInd",
        User
          {
            consts = [ [ "ℕ"; "induction" ] ];
            inputs = [ Bracket { assumptions = [ (true, "n"); (false, "IH") ]; subgoal = "step" } ];
            implicit_first = Some (`Goal_arg 1);
            outputs = [];
          } );
    ]
