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
  let disequality = "proving disequalities by algebra not allowed"
  let not_a_relation = "not an equality or inequality"
  let mixed_types = "input is not an equation or inequality at the same type"
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

(* Likewise for the constructors of the connectives defined as datatypes. *)
let connective_of_constr = function
  | "left" | "right" -> Some "a disjunction (A∨B)"
  | "exists" -> Some "an existential statement (∃x∈A,…)"
  | _ -> None

(* The algebra block's own failures, told apart by the message the oracle reported. *)
let oracle_failed str (p : printable) =
  if str = Oracle.unprovable then
    Some
      "The algebra block couldn't prove this from the facts wired into it.  Either it doesn't \
       follow from them by algebra alone, or a hypothesis it needs isn't connected."
  else if str = Oracle.zero_denominator then
    Option.map
      (fun den ->
        "The algebra block can't tell that" ^ display den
        ^ "is nonzero, and dividing by it only means anything if it is.  Wire in a hypothesis \
           saying it isn't zero, or one that forces that.")
      (printed p)
  else if str = Oracle.disequality then
    Some
      "The algebra block won't prove a ≠ statement outright: that one is for you to prove by \
       contradiction.  Assume the two sides are equal, and derive a contradiction from that."
  else if str = Oracle.not_a_relation then
    Option.map
      (fun ty ->
        "The algebra block only proves equations and inequalities (=, ≠, <, ≤, >, ≥).  The goal \
         it's wired to is" ^ display ty ^ "which isn't one of those.")
      (printed ~sort:`Type p)
  else if str = Oracle.mixed_types then
    Option.map
      (fun ty ->
        "Everything wired into the algebra block has to be an equation or inequality about the \
         same kind of number as the goal.  This one is about" ^ display ty ^ "which isn't.")
      (printed ~sort:`Type p)
  else None

let explain : Code.t -> string option = function
  (* A wire whose two ends disagree about the statement it carries. *)
  | Unequal_synthesized_type { got; expected; _ } -> (
      match (printed ~sort:`Type got, printed ~sort:`Type expected) with
      | Some got, Some expected ->
          Some
            ("This wire carries a proof of" ^ display got
           ^ "but the block it runs into needs a proof of" ^ display expected
           ^ "and those aren't the same statement.")
      | _, _ -> None)
  (* An introduction block wired to a goal that isn't of its shape.  Narya defines ∧, ⇒, ⇔, ∀ and ¬
     as record types, so building one at the wrong goal reads as checking a tuple. *)
  | Checking_tuple_at_nonrecord ty ->
      Option.map
        (fun ty ->
          "This block proves a compound statement — a conjunction (A∧B), an implication (A⇒B), a \
           biconditional (A⇔B), a universal statement (∀x∈A,…) or a negation (¬A).  But the goal \
           it's wired to is" ^ display ty ^ "which isn't any of those, so it needs a different block.")
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
           ^ "which isn't of that form, so it needs a different block.")
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
          ^ "which has no cases to split on.  ∨-elimination needs a disjunction (A∨B), and the ⊥ \
             block needs a proof of ⊥.")
        (printed ~sort:`Type ty)
  | Oracle_failed (str, p) -> oracle_failed str p
  (* An unconnected input or subgoal, which Olorin elaborates to a hole. *)
  | No_holes_allowed _ ->
      Some "This part of the proof isn't finished: something that needs to be connected isn't."
  | Nonsynthesizing _ ->
      Some
        "Olorin can't work out on its own what statement belongs here.  Connect a wire to this \
         input, or use an ascription block to say what it should be."
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
  | Unbound_variable (x, _) ->
      Some
        ("There is no variable called " ^ x
       ^ " here.  A variable introduced by a block is only in scope inside that block.")
  | _ -> None
