open Core
open Reporter

(* Narya's error messages are written for someone who knows Narya: they talk about tuples, records,
   constructors, fields and synthesis.  A player sees blocks, wires and goals.  This file turns the
   errors a player can actually provoke in the diagram into that vocabulary; anything not covered
   falls back to Narya's own text.  Each code handled below was observed coming out of an ordinary
   mistake: a block wired to a goal of the wrong shape, a wire between two blocks that disagree
   about the statement it carries, or an algebra block that can't discharge its goal. *)

(* The messages the algebra oracle reports, named here so that oracle.ml and the explanations below
   can't drift apart. *)
module Oracle = struct
  let unprovable = "can't prove equality/inequality"
  let zero_denominator = "can't prove this denominator is nonzero"
  let negative_base = "can't prove this is nonnegative"
  let disequality = "proving disequalities by algebra not allowed"
  let undecided_sign = "can't tell which way this goes"
  let undecided_order = "can't tell which of these two is smaller"
  let not_a_relation = "not an equality or inequality"
  let not_a_relation_input = "input is not an equality or inequality"
  let mixed_types = "input is not an equation or inequality at the same type"
  let mixed_goal = "goal is a conjunction of relations at different types"
end

(* Print a term or type, or nothing if unparsing raises (as it sometimes does). *)
let printed ?(sort = `Other) (pr : printable) : string option =
  try_with ~fatal:(fun _ -> None) @@ fun () ->
  let buf = Buffer.create 30 in
  PPrint.ToBuffer.pretty 1.0 60 buf (print ~sort pr);
  Some (Buffer.contents buf)

(* Set a statement off on its own indented line, as Narya's own messages do. *)
let display str = "\n    " ^ String.concat "\n    " (String.split_on_char '\n' str) ^ "\n"

(* The connective a block's internal field name stands for, named as the palette names it.  These
   are the fields of the record types that firstorder.ml defines the connectives as. *)
let connective_of_field = function
  | "fst" | "snd" -> Some "a conjunction (A∧B)"
  | "implies" -> Some "an implication (A⇒B)"
  | "ltor" | "rtol" -> Some "a biconditional (A⇔B)"
  | "forall" -> Some "a universal statement (∀x∈A,…)"
  | "forallpos" -> Some "a universal statement about positive reals (∀x∈ℝ₊,…)"
  | "forallbelow" -> Some "a universal statement about the whole numbers below some n (∀x∈[n],…)"
  | "negation" -> Some "a negation (¬A)"
  | _ -> None

(* Likewise for the constructors of the connectives defined as datatypes. *)
let connective_of_constr = function
  | "left" | "right" -> Some "a disjunction (A∨B)"
  | "exists" -> Some "an existential statement (∃x∈A,…)"
  | "existspos" -> Some "an existential statement about positive reals (∃x∈ℝ₊,…)"
  | "existsbelow" -> Some "an existential statement about the whole numbers below some n (∃x∈[n],…)"
  | _ -> None

(* The algebra block's own failures, told apart by the message the oracle reported. *)
let oracle_failed str (p : printable) =
  if str = Oracle.unprovable then
    Some
      "I couldn't prove this from the inputs to the algebra block.  Either it doesn't \
       follow from them by algebra alone, or a hypothesis it needs isn't connected."
  else if str = Oracle.zero_denominator then
    Option.map
      (fun den ->
        "I couldn't prove that" ^ display den
        ^ "is nonzero, so I can't divide by it.  Wire in a hypothesis ensuring it's nonzero.")
      (printed p)
  else if str = Oracle.negative_base then
    Option.map
      (fun b ->
        "I couldn't prove that" ^ display b
        ^ "is nonnegative, so I can't take an even root of it.  Wire in a hypothesis ensuring it's nonnegative.")
      (printed p)
  else if str = Oracle.undecided_sign then
    Option.map
      (fun x ->
        "Before I can prove anything about the absolute value of" ^ display x
        ^ "I have to know which way that goes, so that the absolute value goes away.  Wire in a \
           hypothesis making it nonnegative or nonpositive (perhaps by doing a case split).")
      (printed p)
  else if str = Oracle.undecided_order then
    Option.map
      (fun x ->
        "Before I can prove anything about" ^ display x
        ^ "I have to know which of those two numbers is the smaller, so that the min or max goes \
           away.  Wire in a hypothesis saying which is bigger (perhaps by doing a case split).")
      (printed p)
  else if str = Oracle.disequality then
    Some
      "I won't prove a ≠ statement by algebra unless both sides are plain numbers: use a proof by contradiction instead."
  else if str = Oracle.not_a_relation then
    Option.map
      (fun ty ->
        "The algebra block only proves equations and inequalities (=, ≠, <, ≤, >, ≥), and the alg+ \
         block conjunctions (∧) of those.  The goal it's wired to is" ^ display ty
        ^ "which isn't one of them.")
      (printed ~sort:`Type p)
  else if str = Oracle.not_a_relation_input then
    Option.map
      (fun ty ->
        "Everything wired into the algebra block has to be an equation or inequality (=, ≠, <, ≤, \
         >, ≥), or for the alg+ block a conjunction (∧) of those.  This one is" ^ display ty
        ^ "which isn't one of them.")
      (printed ~sort:`Type p)
  else if str = Oracle.mixed_goal then
    Option.map
      (fun ty ->
         "All the conjuncts of the output of an algebra block must be equations or inequalities in sets that share a common superset.  The output "
         ^ display ty
         ^ "mixes incompatible sets.")
      (printed ~sort:`Type p)
  else if str = Oracle.mixed_types then
    Option.map
      (fun ty ->
        "All the inputs and the output of an algebra block must be equations or inequalities in sets that share a common superset.  The statement " ^ display ty ^ "is incompatible with others.")
      (printed ~sort:`Type p)
  else None

let explain : Code.t -> string option = function
  (* A wire whose two ends disagree about the statement it carries. *)
  | Unequal_synthesized_type { got; expected; _ } -> (
      match (printed ~sort:`Type got, printed ~sort:`Type expected) with
      | Some got, Some expected ->
          Some
            ("This wire carries a proof of" ^ display got
           ^ "but the block it runs into needs a proof of" ^ display expected)
      | _, _ -> None)
  (* An introduction block wired to a goal that isn't of its shape.  Narya defines ∧, ⇒, ⇔, ∀ and ¬
     as record types, so building one at the wrong goal reads as checking a tuple. *)
  | Checking_tuple_at_nonrecord ty ->
      Option.map
        (fun ty ->
          "This block proves a conjunction (A∧B), an implication (A⇒B), a \
           biconditional (A⇔B), a universal (∀x∈A,…) or a negation (¬A).  But the goal \
           it's wired to is" ^ display ty ^ "which isn't any of those.")
        (printed ~sort:`Type ty)
  (* An introduction block for ∨ or ∃, which are datatypes, wired to a goal of the wrong shape. *)
  | No_such_constructor (d, c) -> (
      let ty =
        match d with
        | `Data ty -> printed ~sort:`Type ty
        | `Nondata ty -> printed ~sort:`Type ty
        | `Other ty -> printed ~sort:`Type ty in
      match (connective_of_constr (Constr.to_string c), ty) with
      | Some shape, Some ty ->
          Some
            ("This block proves " ^ shape ^ ", but the goal it's wired to is" ^ display ty
           ^ "which isn't of that form.")
      | _, _ -> None)
  (* An elimination block fed something that isn't of the shape it takes apart.  The payload names
     the offending term rather than its type, and that term is an internal variable, so we describe
     only the shape the block wanted. *)
  | No_such_field (_, f) -> (
      let name =
        match f with
        | `Ins (f, _) -> Field.to_string f
        | `Pbij (f, _) -> Field.to_string f
        | `Strings (str, _) -> str
        | `Int n -> string_of_int n in
      match connective_of_field name with
      | Some shape ->
          Some
            ("This block takes apart " ^ shape
           ^ ", but what's wired into it is a proof of something else.")
      | None -> None)
  (* Case-splitting on a proof that offers no cases. *)
  | Matching_on_nondatatype ty ->
      Option.map
        (fun ty ->
          "This block splits a proof into cases, but what's wired into it is a proof of"
          ^ display ty
          ^ "which has no cases to split on.")
        (printed ~sort:`Type ty)
  | Oracle_failed (str, p) -> oracle_failed str p
  (* An unconnected input or subgoal, which Olorin elaborates to a hole. *)
  | No_holes_allowed _ ->
      Some "This part of the proof isn't finished: something that needs to be connected isn't."
  | Nonsynthesizing _ ->
      Some
        "I can't tell what statement belongs here.  Connect a wire to this \
         input, or use a label block to say what it should be."
  (* Wires that lead out of a block and back into it. *)
  | Cyclic_term ->
      Some
        "These wires run in a circle: following them out of a block leads back into that same \
         block, so one of these steps would end up justifying itself.  A proof has to build up \
         from what is already known, so the wires can't loop."
  (* An assumption or bound variable wired out of the block that introduced it. *)
  | Ill_scoped_connection ->
      Some
        "This wire carries an assumption, or a variable, out of the block that introduced it.  \
         Such a thing only exists inside its own block, so it can only be used on the way to that \
         block's subgoal."
  (* An assumption wired into a fragment that leads nowhere, out of a block that nothing ever
     elaborates: its output is dangling, or leads only somewhere that dangles.  Nothing is being
     carried anywhere, and there is no scope to escape from yet, so the message above would point at
     the wrong thing. *)
  | Unattached_assumption ->
      Some
        "This wire carries an assumption, or a variable, out of a block whose own output isn't \
         wired into the proof yet.  Until it is, I can't tell what that block is proving, so \
         I don't know what this assumption says either: connect the block's output on the way to \
         the goal."
  | Unbound_variable (x, _) ->
      Some
        ("There is no variable called " ^ x
       ^ " here.  A variable introduced by a block is only in scope inside that block.")
  | _ -> None
