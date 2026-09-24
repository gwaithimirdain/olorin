open Core
open Reporter

(* Narya's error messages are written for someone who knows Narya: they talk about tuples, records,
   constructors, fields and synthesis.  A player sees blocks, wires and goals.  This file turns the
   errors a player can actually provoke in the diagram into that vocabulary; anything not covered
   falls back to Narya's own text.  Each code handled below was observed coming out of an ordinary
   mistake: a block wired to a goal of the wrong shape, a wire between two blocks that disagree
   about the statement it carries, or an algebra block that can't discharge its goal. *)

(* The ways the algebra oracle can fail, extending the tag that Narya's Oracle_failed carries.  A
   tag carries whatever the message below needs to point at, so that oracle.ml and the explanations
   here can't drift apart.  Narya can't display any of these, so anything raised here should be
   explained below. *)
module Oracle = struct
  (* Which of the algebra blocks was asking.  They take and prove different things, so the
     failures that say what a block will take carry it: the plain block's message must describe
     the plain block, without advertising the other one. *)
  type block = [ `Alg | `Algplus | `Algneq ]

  type Reporter.oracle_error +=
    | (* The goal doesn't follow from the hypotheses by algebra. *)
        Unprovable
    | (* Z3 gave up before settling the goal or one of its side conditions: it ran out of time, or
       the player cancelled the check. *)
        Gave_up
    | (* A denominator that isn't provably nonzero, or an even root whose base isn't provably
       nonnegative: the term in question. *)
        Zero_denominator of
        printable
    | Negative_base of printable
    | (* A disequality between things that aren't both literals. *)
        Disequality
    | (* An absolute value, min or max that the hypotheses don't decide: the term containing it. *)
        Undecided_sign of
        printable
    | Undecided_order of printable
    | (* A goal, or an input, that isn't a relation at all: the block that wouldn't take it, and the
       statement in question.  A goal like that is only reported once the hypotheses have turned
       out to be consistent, since a contradiction among them proves it (see oracle.ml); an input
       like that is refused outright. *)
        Not_a_relation of
        block * printable
    | Not_a_relation_input of block * printable
    | (* Neither of these can happen unless olorin has elaborated an algebra block wrongly: the
       hypotheses aren't a list, or the block isn't an application of an oracle constant. *)
        Not_a_hypothesis_list of
        printable
    | Not_an_oracle_application of printable
end

(* Olorin's own errors, which arise from how it builds terms out of the diagram rather than from
   anything Narya checks, extending the tag that Narya's Extern code carries.  Narya displays each
   with the code and text that 'code' gives it here -- the code as a suffix to Narya's own code for
   extern errors, so "01" is shown as E3100-01 -- so every tag needs a case there as well as an
   explanation below. *)
module Extern = struct
  type Reporter.extern_error +=
    | (* A wire that leads into a term somewhere its source isn't in scope. *)
        Ill_scoped_connection
    | (* An assumption wired out of a block that nothing elaborates. *)
        Unattached_assumption
    | (* Wires that lead out of a block and back into it. *)
        Cyclic_term
    | (* A variable that is in scope at an expr block, but not wired into it. *)
        Unwired_variable of
        string

  let code (error : Reporter.extern_error) : Code.t =
    let code, text =
      match error with
      | Ill_scoped_connection -> ("01", "ill-scoped connection")
      | Unattached_assumption -> ("02", "assumption of an unattached block")
      | Cyclic_term -> ("03", "cycle in graphical term")
      | Unwired_variable x -> ("04", "variable not wired in: " ^ x)
      | _ -> ("00", "unknown olorin error") in
    Extern { code; text; error }
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
  | "negation" -> Some "a negation (¬A)"
  | _ -> None

(* Likewise for the axioms behind blocks that take their goal apart rather than checking against it
   whole: they prove a statement of one particular shape, and the goal has to be of that shape for
   the block to get the predicate it proves out of it.  Keyed by the axiom's name, since that is
   what the error reports. *)
let shape_of_axiom = function
  | "ℕ.induction" -> Some "a universal statement about the natural numbers (∀n∈ℕ,…)"
  | _ -> None

(* Likewise for the constructors of the connectives defined as datatypes. *)
let connective_of_constr = function
  | "left" | "right" -> Some "a disjunction (A∨B)"
  | "exists" -> Some "an existential statement (∃x∈A,…)"
  | _ -> None

(* The algebra block's own failures, told apart by the tag the oracle reported. *)
let oracle_failed : Reporter.oracle_error -> string option =
  let open Oracle in
  function
  | Unprovable ->
      Some
        "I couldn't prove this from the inputs to the algebra block.  Either it doesn't follow from them by algebra alone, or a hypothesis it needs isn't connected."
  | Gave_up ->
      Some
        "I gave up trying to prove this: it took too long, or the check was cancelled.  It may still be true; try breaking it into smaller steps, or connecting only the inputs it needs."
  | Zero_denominator p ->
      Option.map
        (fun den ->
          "I couldn't prove that"
          ^ display den
          ^ "is nonzero, so I can't divide by it.  Wire in a hypothesis ensuring it's nonzero.")
        (printed p)
  | Negative_base p ->
      Option.map
        (fun b ->
          "I couldn't prove that"
          ^ display b
          ^ "is nonnegative, so I can't take an even root of it.  Wire in a hypothesis ensuring it's nonnegative.")
        (printed p)
  | Undecided_sign p ->
      Option.map
        (fun x ->
          "Before I can prove anything about the absolute value of"
          ^ display x
          ^ "I have to know which way that goes, so that the absolute value goes away.  Wire in a hypothesis making it nonnegative or nonpositive (perhaps by doing a case split).")
        (printed p)
  | Undecided_order p ->
      Option.map
        (fun x ->
          "Before I can prove anything about"
          ^ display x
          ^ "I have to know which of those two numbers is the smaller, so that the min or max goes away.  Wire in a hypothesis saying which is bigger (perhaps by doing a case split).")
        (printed p)
  | Disequality ->
      Some
        "I won't prove a ≠ statement by algebra unless both sides are plain numbers: use a proof by contradiction instead."
  | Not_a_relation (block, p) ->
      Option.map
        (fun ty ->
          match block with
          | `Alg | `Algneq ->
              "The algebra block only proves equations and inequalities (=, ≠, <, ≤, >, ≥), unless its inputs are contradictory.  The goal it's wired to here is"
              ^ display ty
              ^ "which isn't one of them, and its inputs are not contradictory."
          | `Algplus ->
              "The alg+ block only proves equations and inequalities (=, ≠, <, ≤, >, ≥), and conjunctions (∧) and disjunctions (∨) of them, unless its inputs are contradictory.  The goal it's wired to here is"
              ^ display ty
              ^ "which isn't one of those, and its inputs are not contradictory.")
        (printed ~sort:`Type p)
  | Not_a_relation_input (block, p) ->
      Option.map
        (fun ty ->
          (match block with
            | `Alg | `Algneq ->
                "Everything wired into the algebra block has to be an equation or inequality (=, ≠, <, ≤, >, ≥).  This one is"
            | `Algplus ->
                "Everything wired into the alg+ block has to be an equation or inequality (=, ≠, <, ≤, >, ≥), or a conjunction (∧) of those.  This one is")
          ^ display ty
          ^ "which isn't one of them.")
        (printed ~sort:`Type p)
  (* Neither of these is anything the player did; Narya has nothing to say about our tags, so we
     say what we can here rather than leaving a bare "oracle failed". *)
  | Not_a_hypothesis_list p ->
      Some
        ("Something has gone wrong inside Olorin: what's wired into this algebra block isn't a list of statements, but"
        ^ Option.fold ~none:" something unprintable." ~some:display (printed p))
  | Not_an_oracle_application p ->
      Some
        ("Something has gone wrong inside Olorin: this block isn't an algebra block, but"
        ^ Option.fold ~none:" something unprintable." ~some:display (printed p))
  | _ -> None

let explain : Code.t -> string option = function
  (* A wire whose two ends disagree about the statement it carries. *)
  | Unequal_synthesized_type { got; expected; _ } -> (
      match (printed ~sort:`Type got, printed ~sort:`Type expected) with
      | Some got, Some expected ->
          Some
            ("This wire carries a proof of"
            ^ display got
            ^ "but the block it runs into needs a proof of"
            ^ display expected)
      | _, _ -> None)
  (* An introduction block wired to a goal that isn't of its shape.  Narya defines ∧, ⇒, ⇔, ∀ and ¬
     as record types, so building one at the wrong goal reads as checking a tuple. *)
  | Checking_tuple_at_nonrecord ty ->
      Option.map
        (fun ty ->
          "This block proves a conjunction (A∧B), an implication (A⇒B), a biconditional (A⇔B), a universal (∀x∈A,…) or a negation (¬A).  But the goal it's wired to is"
          ^ display ty
          ^ "which isn't any of those.")
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
            ("This block proves "
            ^ shape
            ^ ", but the goal it's wired to is"
            ^ display ty
            ^ "which isn't of that form.")
      | _, _ -> None)
  (* An introduction block wired to a goal that's a record of the right general kind, but the
     wrong specific one -- e.g. an ordinary ∀-introduction wired to a ∀x∈ℝ₊ or ∀x∈[n] goal.  ∧, ⇒,
     ⇔, ∀ and ¬ are all single- or two-field records that share this checking path, so unlike
     Checking_tuple_at_nonrecord (the goal isn't a record at all) this fires when it is one, just
     not the one this block builds.  The payload only names the field the goal wanted, not what
     the block actually supplied. *)
  | Missing_field_in_tuple (f, _) -> (
      match connective_of_field (Field.to_string f) with
      | Some shape ->
          Some
            ("This block doesn't prove "
            ^ shape
            ^ ", but the goal it's wired to needs exactly that.")
      | None -> None)
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
            ("This block takes apart "
            ^ shape
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
  | Oracle_failed err -> oracle_failed err
  (* An unconnected input or subgoal, which Olorin elaborates to a hole. *)
  | No_holes_allowed _ ->
      Some "This part of the proof isn't finished: something that needs to be connected isn't."
  | Nonsynthesizing _ ->
      Some
        "I can't tell what statement belongs here.  Connect a wire to this input, or use a label block to say what it should be."
  (* Wires that lead out of a block and back into it. *)
  | Extern { error = Extern.Cyclic_term; _ } ->
      Some
        "These wires run in a circle: following them out of a block leads back into that same block, so one of these steps would end up justifying itself.  A proof has to build up from what is already known, so the wires can't loop."
  (* An assumption or bound variable wired out of the block that introduced it. *)
  | Extern { error = Extern.Ill_scoped_connection; _ } ->
      Some
        "This wire carries an assumption, or a variable, out of the block that introduced it.  Such a thing only exists inside its own block, so it can only be used on the way to that block's subgoal."
  (* An assumption wired into a fragment that leads nowhere, out of a block that nothing ever
     elaborates: its output is dangling, or leads only somewhere that dangles.  Nothing is being
     carried anywhere, and there is no scope to escape from yet, so the message above would point at
     the wrong thing. *)
  | Extern { error = Extern.Unattached_assumption; _ } ->
      Some
        "This wire carries an assumption, or a variable, out of a block whose own output isn't wired into the proof yet.  Until it is, I can't tell what that block is proving, so I don't know what this assumption says either: connect the block's output on the way to the goal."
  | Unbound_variable (x, _) ->
      Some
        ("There is no variable called "
        ^ x
        ^ " here.  A variable introduced by a block is only in scope inside that block.")
  (* A variable that is in scope at an expr block, but not wired into it. *)
  | Extern { error = Extern.Unwired_variable x; _ } ->
      Some
        ("This expression uses "
        ^ x
        ^ ", but "
        ^ x
        ^ " isn't wired into it.  An expression block can only use the variables whose wires lead into it, so connect a wire from "
        ^ x
        ^ " to this block.")
  (* A block whose axiom takes the predicate it proves from the goal, wired to a goal it can't take
     that predicate from: either the goal isn't of the shape the block proves at all, or it is that
     shape but about the wrong set. *)
  | No_implicit_goal_arg (fn, ty) -> (
      match (Option.bind (printed fn) shape_of_axiom, printed ~sort:`Type ty) with
      | Some shape, Some ty ->
          Some
            ("This block proves "
            ^ shape
            ^ ", but the goal it's wired to is"
            ^ display ty
            ^ "which isn't of that form.")
      | _, _ -> None)
  | Choice_mismatch ty ->
      Option.map
        (fun ty -> "This block can't produce a proof of the needed statement" ^ display ty)
        (printed ~sort:`Type ty)
  | _ -> None
