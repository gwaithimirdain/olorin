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
  | Tuple of { inputs : (string option * string * (string * string list)) list }
  | Fields of { outputs : ((string * int list) * string) list }
  | Constr of { inputs : string list; constr : Constr.t }
  | Match of { branches : match_branch list; asc_pre : string option }
  | Coconstr of { constr : Constr.t; outputs : (bool * string) list }
  (* Application and abstraction include an optional field because ⇒, ∀, and ¬ are actually records, so for Narya's internals we need to tuple and project in addition to applying and abstracting. *)
  | App of { field : (string * int list) option; inputs : string * string }
  | Neg of { field : string * int list; inputs : string * string; implicit_pre : string }
  | Abs of {
      field : (string * string list) option;
      has_value : bool;
      (* Allow testing for the presence of a field in the goal type, and if it isn't there, insert a specified function (with implicit first argument).  The intended example is so that a single rule can be both proof-of-negation and proof-by-contradiction. *)
      implicit_post : (string * string) option;
    }
  (* | Asc *)
  | Var
  | Conclusion

(* Here are the specific rules currently used in graphs.  The port labels used here have to match those used in the JavaScript.  It would be better if the JavaScript could get them from here. *)
let rules =
  RuleMap.of_list
    [
      ("variable", Var);
      ("hypothesis", Var);
      ("conclusion", Conclusion);
      ("andE", Fields { outputs = [ (("fst", []), "fst"); (("snd", []), "snd") ] });
      ("andI", Tuple { inputs = [ (None, "fst", ("fst", [])); (None, "snd", ("snd", [])) ] });
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
      ("impE", App { field = Some ("implies", []); inputs = ("implication", "antecedent") });
      ("impI", Abs { field = Some ("implies", []); has_value = false; implicit_post = None });
      ("iffE1", App { field = Some ("ltor", []); inputs = ("implication", "antecedent") });
      ("iffE2", App { field = Some ("rtol", []); inputs = ("implication", "antecedent") });
      ( "iffI",
        Tuple
          { inputs = [ (Some "ltor", "ltor", ("ltor", [])); (Some "rtol", "rtol", ("rtol", [])) ] }
      );
      ( "exE",
        Coconstr
          { constr = Constr.intern "exists"; outputs = [ (true, "element"); (false, "property") ] }
      );
      ("exI", Constr { inputs = [ "element"; "property" ]; constr = Constr.intern "exists" });
      ("allE", App { field = Some ("forall", []); inputs = ("universal", "element") });
      ("allI", Abs { field = Some ("forall", []); has_value = true; implicit_post = None });
      ( "negE",
        Neg
          {
            field = ("negation", []);
            inputs = ("negation", "statement");
            implicit_pre = "contradict";
          } );
      ("negI", Abs { field = Some ("negation", []); has_value = false; implicit_post = None });
      ( "cnegI",
        (* Classical proof-by-contradiction *)
        Abs
          {
            field = Some ("negation", []);
            has_value = false;
            implicit_post = Some ("negation", "negneg");
          } );
      ("botE", Match { branches = []; asc_pre = Some "⊥" });
      ("topI", Tuple { inputs = [] });
      (* ("asc", Asc); *)
    ]
