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
  | Tuple of {
      inputs : (string option * string * (string * string list)) list;
      unordered : bool;
    }
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
  (* The two algebra blocks: the "plus" one lets Z3 decide an absolute value, a minimum or a
     maximum on its own, while the plain one requires the hypotheses to settle each such case
     first.  They differ only in which oracle constant they ask through. *)
  | Algebra of { plus : bool }
  | Var
  | Conclusion
  | User of {
      consts : string list list;
      inputs : string list;
      (* Some user axioms conclude an existential statement.  Rather than making the player follow
         such a block with a separate ∃-elimination, the block takes its own conclusion apart,
         handing out one output port per component of the constructor, exactly as a Coconstr does.
         Each further step takes apart the *last* component of the step before it, which is how a
         nest of ∃s is opened one variable at a time; that last component is then a port of the
         block's own machinery rather than one the player sees.  The components flagged 'true' are
         the ones carrying a value, and they take the block's bound variable names in order.  An
         empty list is a block with the usual single unlabeled output carrying the conclusion
         itself. *)
      outputs : (Constr.t * (bool * string) list) list;
    }

(* The output ports such a block shows the player: every component of every step, except the last
   component of each step that the step after it takes apart. *)
let rec visible_outputs : (Constr.t * (bool * string) list) list -> string list = function
  | [] -> []
  | [ (_, outs) ] -> List.map snd outs
  | (_, outs) :: rest ->
      let n = List.length outs in
      List.filteri (fun i _ -> i < n - 1) (List.map snd outs) @ visible_outputs rest

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
        Abs
          {
            field = Some ("implies", []);
            has_value = false;
            extras = [];
            implicit_post = None;
          } );
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
        Constr
          { inputs = [ "element"; "below"; "property" ]; constr = Constr.intern "existsbelow" } );
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
        Abs
          {
            field = Some ("negation", []);
            has_value = false;
            extras = [];
            implicit_post = None;
          } );
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
      ("alg", Algebra { plus = false });
      ("algplus", Algebra { plus = true });
      ( "integral",
        User
          {
            consts =
              [ [ "ℤ"; "integral" ]; [ "ℚ"; "integral" ]; [ "ℝ"; "integral" ]; [ "𝕊"; "integral" ] ];
            inputs = [ "x"; "y"; "xy0" ];
            outputs = [];
          } );
      ( "deceq",
        User
          {
            consts = [ [ "ℤ"; "deceq" ]; [ "ℚ"; "deceq" ]; [ "ℝ"; "deceq" ]; [ "𝕊"; "deceq" ] ];
            inputs = [ "x"; "y" ];
            outputs = [];
          } );
      ( "tord",
        User
          {
            consts = [ [ "ℤ"; "tord" ]; [ "ℚ"; "tord" ]; [ "ℝ"; "tord" ]; [ "𝕊"; "tord" ] ];
            inputs = [ "x"; "y" ];
            outputs = [];
          } );
      (* The Archimedean property: every real is below some natural number.  The axiom concludes an
         ∃, so the block destructs it, giving out the natural number n it produces on a value port
         and the proof that x<n on another.  There is no 𝕊 version: the superreals are exactly the
         number system where this fails. *)
      ( "arch",
        User
          {
            consts = [ [ "ℝ"; "archimedean" ] ];
            inputs = [ "x" ];
            outputs = [ (Constr.intern "exists", [ (true, "element"); (false, "property") ]) ];
          } );
      (* An integer that is at least zero is a natural number.  The proof that it is nonnegative is
         an input of its own, alongside the integer; what comes out is that natural number and the
         equation identifying it with the integer we started from. *)
      ( "zton",
        User
          {
            consts = [ [ "ℤ"; "tonat" ] ];
            inputs = [ "x"; "nonneg" ];
            outputs = [ (Constr.intern "exists", [ (true, "element"); (false, "property") ]) ];
          } );
      (* Every rational is a fraction in lowest terms.  Its axiom concludes two nested ∃s, one for
         each side of the fraction, so the block takes two steps: the first hands out the numerator
         and the second, taking apart what the first leaves, the denominator.  That inner ∃ is the
         "rest" port, which belongs to the block rather than to the player -- what they see is the
         numerator, the denominator, and the statement about the two of them.  Two value ports mean
         two bound variables, which the block's variable dialog asks for in this order. *)
      ( "frac",
        User
          {
            consts = [ [ "ℚ"; "frac" ] ];
            inputs = [ "x" ];
            outputs =
              [
                (Constr.intern "exists", [ (true, "numerator"); (false, "rest") ]);
                (Constr.intern "exists", [ (true, "denominator"); (false, "property") ]);
              ];
          } );
      (* Every real number is smaller than ω.  This one concludes a relation rather than an ∃, so it
         has the ordinary single output, carrying x<ω. *)
      ("omega", User { consts = [ [ "ℝ"; "ltomega" ] ]; inputs = [ "x" ]; outputs = [] });
    ]
