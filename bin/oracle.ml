open Bwd
open Util
open Dim
open Core
open Value
open Subtype
open Reporter
open Parser
open Objects
open Js_of_ocaml

module Callback = struct
  open Effect.Deep

  type _ Effect.t += Callback : Relation.t list -> bool Effect.t

  exception Halt

  let cont : (bool, js_checked Js.t) continuation option ref = ref None

  let effc : type b. b Effect.t -> ((b, js_checked Js.t) continuation -> js_checked Js.t) option =
    function
    | Callback output ->
        Some
          (fun k ->
            cont := Some k;
            object%js
              val mutable complete = Js.bool false

              val mutable callback =
                Js.some @@ Js.array @@ Array.of_list @@ List.map Relation.to_js output

              val mutable error = Js.null
              val mutable labels = Js.array (Array.of_list [])
              val mutable diagnostics = Js.array (Array.of_list [])
            end)
    | _ -> None

  let halt () =
    try
      match !cont with
      | Some k ->
          let _ = discontinue k Halt in
          ()
      | None -> ()
    with Halt -> cont := None

  let run f =
    halt ();
    try_with f () { effc }

  let reenter response =
    match !cont with
    | Some k ->
        cont := None;
        continue k response
    | None -> raise (Jserror "no saved continuation in reenter")
end

module E = Monad.Error (struct
  type t = Code.t
end)

let rec get_equality_or_inequality ctx tm =
  let open Monad.Ops (E) in
  let eq = Scope.lookup [ "eq" ] in
  let neq = Scope.lookup [ "neq" ] in
  let lt = Scope.lookup [ "lt" ] in
  let le = Scope.lookup [ "le" ] in
  let neg = Scope.lookup [ "neg" ] in
  match Norm.view_term tm with
  | Neu
      {
        head = Const { name; ins };
        args = Arg (Arg (Arg (Emp, ty, tyins), lhs, lhsins), rhs, rhsins);
        _;
      }
    when Option.is_some (is_id_ins ins)
         && Option.is_some (is_id_ins tyins)
         && Option.is_some (is_id_ins lhsins)
         && Option.is_some (is_id_ins rhsins) ->
      let* op =
        if Some name = eq then return `Eq
        else if Some name = neq then return `Neq
        else if Some name = lt then return `Lt
        else if Some name = le then return `Le
        else Error (Code.Oracle_failed (Explain.Oracle.not_a_relation, Printable.PVal (ctx, tm)))
      in
      return (op, CubeOf.find_top ty, CubeOf.find_top lhs, CubeOf.find_top rhs)
  | Neu { head = Const { name; ins }; args = Arg (Emp, tm, tyins); _ }
    when Some name = neg && Option.is_some (is_id_ins ins) && Option.is_some (is_id_ins tyins) -> (
      let* op, ty, lhs, rhs = get_equality_or_inequality ctx (CubeOf.find_top tm).tm in
      match op with
      | `Eq -> return (`Neq, ty, lhs, rhs)
      | `Neq -> return (`Eq, ty, lhs, rhs)
      | `Lt -> return (`Le, ty, rhs, lhs)
      | `Le -> return (`Lt, ty, rhs, lhs))
  | _ -> Error (Code.Oracle_failed (Explain.Oracle.not_a_relation, Printable.PVal (ctx, tm)))

(* All the relations a statement asserts.  With 'split' -- which is what the "plus" block asks for
   -- a conjunction contributes those of both its components, so that block takes a conjunction of
   relations as a hypothesis and proves one as a goal; the plain block insists on a bare relation.
   Underneath a negation neither one splits, since the negation of a conjunction is a disjunction,
   which is not something we can hand to Z3 as a fact or ask it to prove. *)
let rec get_relations ~(split : bool) ctx tm =
  let open Monad.Ops (E) in
  let land_ = Scope.lookup [ "land" ] in
  match Norm.view_term tm with
  | Neu { head = Const { name; ins }; args = Arg (Arg (Emp, p, pins), q, qins); _ }
    when split
         && Some name = land_
         && Option.is_some (is_id_ins ins)
         && Option.is_some (is_id_ins pins)
         && Option.is_some (is_id_ins qins) ->
      let* p = get_relations ~split ctx (CubeOf.find_top p).tm in
      let* q = get_relations ~split ctx (CubeOf.find_top q).tm in
      return (p @ q)
  | _ ->
      let* rel = get_equality_or_inequality ctx tm in
      return [ rel ]

(* Keep only the relations that are about the same kind of number as the goal, reporting 'msg'
   about 'src' if one of them isn't. *)
let rec same_type ctx (ty : normal) msg src = function
  | [] -> Ok []
  | (op, (ty' : normal), x, y) :: rest -> (
      let open Monad.Ops (E) in
      match subtype_of ctx ty'.tm ty.tm with
      | Ok () ->
          let* rest = same_type ctx ty msg src rest in
          return ((op, x, y) :: rest)
      | Error _ -> Error (Code.Oracle_failed (msg, src)))

let rec get_givens ~split ctx (ty : normal) givens =
  let open Monad.Ops (E) in
  let cons_eqs = Scope.lookup [ "Cons_eqs" ] in
  let nil_eqs = Scope.lookup [ "Nil_eqs" ] in
  match Norm.view_term givens with
  | Neu
      {
        head = Const { name; ins };
        args = Arg (Arg (Arg (Arg (Emp, eqty, eqtyins), _, _), rest, restins), _, _);
        _;
      }
    when Some name = cons_eqs
         && Option.is_some (is_id_ins ins)
         && Option.is_some (is_id_ins eqtyins)
         && Option.is_some (is_id_ins restins) ->
      let eqty = CubeOf.find_top eqty in
      let* rels =
        (* An input that isn't a relation at all is the same complaint as a goal that isn't one,
           but about a wire rather than about the goal, so it gets its own message. *)
        match get_relations ~split ctx eqty.tm with
        | Ok rels -> Ok rels
        | Error (Code.Oracle_failed (msg, _)) when msg = Explain.Oracle.not_a_relation ->
            Error
              (Code.Oracle_failed
                 (Explain.Oracle.not_a_relation_input, Printable.PNormal (ctx, eqty)))
        | Error e -> Error e in
      let* rels =
        same_type ctx ty Explain.Oracle.mixed_types (Printable.PNormal (ctx, eqty)) rels in
      let* rest = get_givens ~split ctx ty (CubeOf.find_top rest).tm in
      return (rels @ rest)
  | Neu { head = Const { name; ins }; args = Emp; _ }
    when Some name = nil_eqs && Option.is_some (is_id_ins ins) -> return []
  | _ -> Error (Code.Oracle_failed ("not a Cons_eqs or Nil_eqs", Printable.PVal (ctx, givens)))

let rec get_posint tm =
  match Norm.view_term tm with
  | Constr (name, dim, []) when name = Constr.intern "zero" -> (
      match D.compare_zero dim with
      | Zero -> Some 0
      | Pos _ -> None)
  | Constr (name, dim, []) when name = Constr.intern "one" -> (
      match D.compare_zero dim with
      | Zero -> Some 1
      | Pos _ -> None)
  | Constr (name, dim, [ arg ]) when name = Constr.intern "suc" -> (
      match D.compare_zero dim with
      | Zero -> Option.map (fun n -> n + 1) (get_posint (CubeOf.find_top arg))
      | Pos _ -> None)
  | _ -> None

let rec pow p n = if n <= 0 then `Const Q.one else `Times (pow p (n - 1), p)

(* A translated expression read back as a rational literal, if it is one.  get_poly folds a numeral,
   and a quotient of numerals, into a constant, so the only other shape to allow for is a minus sign
   in front. *)
let rec rational_of : Symbolic.t -> Q.t option = function
  | `Const q -> Some q
  | `Neg x -> Option.map Q.neg (rational_of x)
  | _ -> None

let is_literal x = Option.is_some (rational_of x)

(* Past this we would be building a polynomial nothing could decide anyway, and the exponent might
   not even fit in an int, so we give up and treat the power as an opaque term: sound, but nothing
   about it will be provable. *)
let max_exponent = 1000

(* Something the translation turned up, recorded in the order it was met.  get_poly works bottom
   up, so a subterm's steps come before those of the term containing it, and 'ask' below walks them
   in that order. *)
type step =
  (* What a fresh variable stands for: the relations defining a root. *)
  | Define of Relation.t list
  (* A denominator, which the hypotheses have to force to be nonzero, paired with the term it came
     from so we can point at it in an error. *)
  | Nonzero of Symbolic.t * kinetic value
  (* Likewise the base of an even root, which they have to force to be nonnegative. *)
  | Nonneg of Symbolic.t * kinetic value
  (* A case split the translation introduced.  An absolute value, a minimum and a maximum are each
     a conditional on which way two things compare: for ∣x∣ on 0 against x, for min(x,y) and
     max(x,y) on x against y.  Z3 decides such a conditional on its own, so the stronger algebra
     block asks nothing here; the weaker one insists the hypotheses decide the comparison, so that
     the conditional simplifies away and the student has done the case split themselves.  Either
     direction will do, and both are asked non-strictly (a ≤ b, or b ≤ a) since either settles the
     value: ∣x∣ is −x as soon as x ≤ 0, and the two readings agree where the two are equal.  That
     also makes the "≤∨>" block enough to discharge this, which is the point: its branches give
     "a ≤ b" and "b < a", and each of those is one of these two.  The tag says which message to
     give when nothing settles it, and the value is the term to point at there. *)
  | Cases of [ `Sign | `Order ] * Symbolic.t * Symbolic.t * kinetic value

(* State threaded through the translation of a term into a Z3 expression. *)
type translation = {
  (* Subterms we can't interpret, each standing for an opaque variable.  A root's variable is one of
     these, keyed by the power it came from, so that writing the same root twice gets the same
     variable and states its definition once. *)
  vars : kinetic value Bwd.t;
  count : int;
  (* The definitions and obligations met along the way, oldest first. *)
  steps : step Bwd.t;
}

module S = Monad.State (struct
  type t = translation
end)

(* The variable standing for a subterm we can't express directly, and whether we have just met that
   subterm for the first time -- so that a root states its definition once however often it is
   written. *)
let var_for ctx ty tm : (Symbolic.t * bool) S.t =
  let open Monad.Ops (S) in
  let* ({ vars; count; _ } as st) = S.get in
  match Bwd.find_index (fun x -> Result.is_ok (Equal.equal_at ctx tm x ty)) vars with
  | None ->
      let* () = S.put { st with vars = Snoc (vars, tm); count = count + 1 } in
      return (`Var count, true)
  | Some i -> return (`Var (count - i - 1), false)

let var_or_const ctx ty tm : Symbolic.t S.t =
  let open Monad.Ops (S) in
  match get_posint tm with
  | Some i -> return (`Const (Q.of_int i))
  | None ->
      let* v, _ = var_for ctx ty tm in
      return v

let get_poly ctx ty tm =
  let open Monad.Ops (S) in
  let add_step step =
    let* st = S.get in
    S.put { st with steps = Snoc (st.steps, step) } in
  (* A base raised to a rational power.  An integer power is repeated multiplication as before, and
     a negative one is the reciprocal of the positive one, so it carries the ordinary
     nonzero-denominator obligation.  A genuine p/q needs a fresh variable s for the root, defined
     by s^q = base^p.  For even q that leaves two candidates, so we pin s down as the nonnegative
     one -- and then the base itself has to be nonnegative, or "s >= 0 and s^q = base^p" has no
     solution at all and would prove anything.  Odd roots are total on the reals and need neither.
     'src' is the term to point at if an obligation can't be discharged. *)
  let power tm base e src =
    let n, d = (Q.num e, Q.den e) in
    if not (Z.fits_int n && Z.fits_int d && Z.leq (Z.abs n) (Z.of_int max_exponent)
            && Z.leq d (Z.of_int max_exponent)) then var_or_const ctx ty tm
    else
      let n, d = (Z.to_int n, Z.to_int d) in
      (* base^n, with a negative n written as a reciprocal so the denominator obligation applies. *)
      let numerator () =
        if n >= 0 then return (pow base n)
        else
          let p = pow base (-n) in
          let* () = add_step (Nonzero (p, src)) in
          return (`Div (`Const Q.one, p)) in
      if d = 1 then numerator ()
      else
        let even = d mod 2 = 0 in
        let* () = if even then add_step (Nonneg (base, src)) else return () in
        let* rhs = numerator () in
        let* s, fresh = var_for ctx ty tm in
        let* () =
          if fresh then
            add_step
              (Define
                 ((if even then [ (`Le, `Const Q.zero, s) ] else []) @ [ (`Eq, pow s d, rhs) ]))
          else return () in
        return s in
  let rec go tm =
    match Norm.view_term tm with
    (* Binary operation *)
    | Neu { head = Const { name; ins }; args = Arg (Arg (Emp, x, xins), y, yins); _ }
      when Option.is_some (is_id_ins ins)
           && Option.is_some (is_id_ins xins)
           && Option.is_some (is_id_ins yins) -> (
        let* px = go (CubeOf.find_top x).tm in
        let* py = go (CubeOf.find_top y).tm in
        match Firstorder.get_root name with
        | "plus" -> return (`Plus (px, py))
        | "minus" -> return (`Minus (px, py))
        | "times" -> return (`Times (px, py))
        | "min" ->
            let* () = add_step (Cases (`Order, px, py, tm)) in
            return (`Min (px, py))
        | "max" ->
            let* () = add_step (Cases (`Order, px, py, tm)) in
            return (`Max (px, py))
        | "divide" -> (
            (* A quotient of numerals is just a rational constant, and carries no obligation.  We
               ask rational_of rather than matching on `Const, so that a minus sign in front of
               either of them doesn't stop the fold: "−1/2" parses as (−1)/2. *)
            match (rational_of px, rational_of py) with
            | Some a, Some b when not (Q.equal b Q.zero) -> return (`Const (Q.div a b))
            (* Otherwise we hand the division to Z3 as a division.  Z3's real division is total,
               with the value at a zero denominator left uninterpreted, so this is sound however
               the denominator turns out; but we also require it to be provably nonzero. *)
            | _ ->
                let* () = add_step (Nonzero (py, (CubeOf.find_top y).tm)) in
                return (`Div (px, py)))
        | "pow" -> (
            match rational_of py with
            | Some e -> power tm px e (CubeOf.find_top x).tm
            | None -> var_or_const ctx ty tm)
        | _ -> var_or_const ctx ty tm)
    (* Unary operation *)
    | Neu { head = Const { name; ins }; args = Arg (Emp, x, xins); _ }
      when Option.is_some (is_id_ins ins) && Option.is_some (is_id_ins xins) -> (
        let src = (CubeOf.find_top x).tm in
        let* x = go src in
        match Firstorder.get_root name with
        | "sqrt" -> power tm x (Q.of_ints 1 2) src
        | "abs" ->
            let* () = add_step (Cases (`Sign, `Const Q.zero, x, src)) in
            return (`Abs x)
        | "negate" -> (
            match rational_of x with
            | Some q -> return (`Const (Q.neg q))
            | None -> return (`Neg x))
        | "square" -> return (`Times (x, x))
        | "cube" -> return (`Times (`Times (x, x), x))
        | "fourth" -> return (`Times (`Times (x, x), `Times (x, x)))
        | _ -> var_or_const ctx ty tm)
    | _ -> var_or_const ctx ty tm in
  go tm

let vars_of_ctx : type a b. (a, b) Ctx.t -> string Bwd.t = function
  | Permute { ctx; _ } ->
      let rec vars_of_ctx : type a b. (a, b) Ctx.Ordered.t -> string Bwd.t = function
        | Emp -> Emp
        | Lock ctx -> vars_of_ctx ctx
        | Snoc (ctx, Invis _, _) -> vars_of_ctx ctx
        | Snoc (ctx, Vis { vars; _ }, _) -> (
            match NICubeOf.find_top vars with
            | `Named x -> Snoc (vars_of_ctx ctx, x)
            | `Anon _ -> vars_of_ctx ctx) in
      vars_of_ctx ctx

(* We memorize the results of calls to reduce, so we don't have to re-make them every time. *)
let answers : (Relation.t list, bool) Hashtbl.t = Hashtbl.create 20

(* Ask Z3 whether a conjunction of relations is unsatisfiable, i.e. whether its negation is
   provable.  Each question is asked at most once. *)
let unsat (command : Relation.t list) =
  match Hashtbl.find_opt answers command with
  | Some result -> result
  | None ->
      let result = Effect.perform (Callback.Callback command) in
      Hashtbl.add answers command result;
      result

let ask (Ask (ctx, tm) : Check.OracleData.question) =
  let open Monad.Ops (E) in
  (* The two algebra blocks ask through constants of their own, so the question says which one is
     asking: the "plus" block decides an absolute value, a minimum or a maximum itself, while the
     plain one requires the hypotheses to settle each of those first (see Cases below). *)
  let oracle = Scope.lookup [ "oracle" ] in
  let oracle_plus = Scope.lookup [ "oracle_plus" ] in
  let* plus, givens, goal =
    match Norm.view_term tm with
    | Neu
        {
          head = Const { name; ins };
          args = Arg (Arg (Arg (Emp, givens, givins), _, _), goal, appins);
          _;
        }
      when (Some name = oracle || Some name = oracle_plus)
           && Option.is_some (is_id_ins ins)
           && Option.is_some (is_id_ins givins)
           && Option.is_some (is_id_ins appins) ->
        return (Some name = oracle_plus, CubeOf.find_top givens, CubeOf.find_top goal)
    | _ -> Error (Code.Oracle_failed ("not an oracle application", Printable.PVal (ctx, tm))) in
  (* A conjunctive goal is a list of relations to prove, each against all of the hypotheses.  They
     all go through one translation, so that the same subterm gets the same variable throughout,
     and hence they have to be about the same kind of number; we take that from the first of them,
     as a single relation's type was taken from the goal itself. *)
  let* goals =
    (* Report a goal that isn't a relation against the whole goal rather than against the conjunct
       that isn't one, as the hypotheses below are reported against the whole wire. *)
    match get_relations ~split:plus ctx goal.tm with
    | Ok goals -> Ok goals
    | Error (Code.Oracle_failed (msg, _)) when msg = Explain.Oracle.not_a_relation ->
        Error (Code.Oracle_failed (msg, Printable.PNormal (ctx, goal)))
    | Error e -> Error e in
  let* ty =
    match goals with
    | (_, ty, _, _) :: _ -> Ok ty
    | [] ->
        Error (Code.Oracle_failed (Explain.Oracle.not_a_relation, Printable.PNormal (ctx, goal)))
  in
  let* goals =
    same_type ctx ty Explain.Oracle.mixed_goal (Printable.PNormal (ctx, goal)) goals in
  let* givens = get_givens ~split:plus ctx ty givens.tm in
  let ty = ty.tm in
  let (givens, goals), { steps; _ } =
    (let open Monad.Ops (S) in
     let poly (op, (x : normal), (y : normal)) =
       let* x = get_poly ctx ty x.tm in
       let* y = get_poly ctx ty y.tm in
       return (op, x, y) in
     let open Mlist.Monadic (S) in
     (* The goal before the hypotheses, so that the side conditions come out in the order they did
        when a goal was always a single relation. *)
     let* goals = mmapM (fun [ g ] -> poly g) [ goals ] in
     let* givens = mmapM (fun [ g ] -> poly g) [ givens ] in
     return (givens, goals))
      { vars = Emp; count = 0; steps = Emp } in
  (* The quantifier eliminator can prove disequalities, but we only let it do so between rational
     literals, like 0≠1.  A disequality with anything else in it is one we want the student to
     prove by contradiction. *)
  let* () =
    List.fold_left
      (fun acc (op, lhs, rhs) ->
        let* () = acc in
        if op = `Neq && not (is_literal lhs && is_literal rhs) then
          Error (Code.Oracle_failed (Explain.Oracle.disequality, PUnit))
        else Ok ())
      (Ok ()) goals in
  (* Encoding division faithfully means the goal query below is sound whatever the denominators
     turn out to be, since a statement about a quotient by zero is then a statement about an
     unspecified value.  But answering such questions isn't what the student wants: writing a
     quotient whose denominator might vanish is a mistake, so we insist the hypotheses force each
     denominator nonzero, and say which one doesn't when they don't.  An even root's base is the
     same kind of side condition, and worse if neglected: an unsatisfiable definition would let the
     block prove anything at all.  (Both ask Z3 to prove a disequality or an inequality about
     things that aren't literals, which we don't allow as a *goal*; but these are our own side
     conditions rather than something the student is being credited with proving.)

     An absolute value, a minimum or a maximum carries a side condition too, but only for the plain
     algebra block, and for a different reason: Z3 decides those conditionals itself, and we want
     the student to have decided them (see Cases above).

     So we walk the steps in the order the translation met them, innermost first, discharging each
     obligation against the hypotheses and the definitions before it, and gathering the definitions
     for the goal query.  An obligation never sees its own definition: "s >= 0 and s*s = x" implies
     x >= 0 all by itself, so checking with that in hand would be no check at all. *)
  let rec discharge facts = function
    | [] -> Ok facts
    | Define defs :: rest -> discharge (defs @ facts) rest
    | Nonzero (den, src) :: rest ->
        if unsat ((`Eq, den, `Const Q.zero) :: facts) then discharge facts rest
        else
          Error
            (Code.Oracle_failed (Explain.Oracle.zero_denominator, Printable.PVal (ctx, src)))
    | Nonneg (base, src) :: rest ->
        if unsat ((`Lt, base, `Const Q.zero) :: facts) then discharge facts rest
        else
          Error (Code.Oracle_failed (Explain.Oracle.negative_base, Printable.PVal (ctx, src)))
    (* Z3 decides a conditional on its own, so for the "plus" block there is nothing to discharge.
       For the plain one the hypotheses have to settle the comparison -- "a ≤ b" or "b ≤ a", either
       will do -- which is what makes the student split into cases by hand. *)
    | Cases (which, a, b, src) :: rest ->
        if plus || unsat ((`Lt, b, a) :: facts) || unsat ((`Lt, a, b) :: facts) then
          discharge facts rest
        else
          let msg =
            match which with
            | `Sign -> Explain.Oracle.undecided_sign
            | `Order -> Explain.Oracle.undecided_order in
          Error (Code.Oracle_failed (msg, Printable.PVal (ctx, src))) in
  let* facts = discharge givens (Bwd.to_list steps) in
  (* Each conjunct of the goal is then a question of its own, asked against all the hypotheses.  We
     negate it, since Z3 checks for satisfiability; that means negating the operator and also
     swapping the order of the arguments (although for a (dis)equality swapping does nothing). *)
  List.fold_left
    (fun acc (op, lhs, rhs) ->
      let* () = acc in
      let neg_op =
        match op with
        | `Eq -> `Neq
        | `Neq -> `Eq
        | `Lt -> `Le
        | `Le -> `Lt in
      if unsat ((neg_op, rhs, lhs) :: facts) then Ok ()
      else Error (Code.Oracle_failed (Explain.Oracle.unprovable, PUnit)))
    (Ok ()) goals
