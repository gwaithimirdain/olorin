open Bwd
open Util
open Dim
open Modal
open Omode
open Core
open Value
open Subtype
open Reporter
open Parser
open Objects
open Explain.Oracle
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

(* An ordering belongs to one number system -- there is a ℝ.lt and a ℤ.lt and no < that holds of
   anything else -- so the constant itself says which relation this is, and its arguments carry the
   number system, being annotated with the domain of the constant's type. *)
let order_relations () =
  List.concat_map
    (fun ty ->
      List.filter_map
        (fun (str, op) -> Option.map (fun c -> (c, op)) (Scope.lookup [ ty; str ]))
        [ ("lt", `Lt); ("le", `Le) ])
    Firstorder.numbers

(* The arguments of an application spine, oldest first, if it is a plain sequence of applications of
   the ordinary kind: a field projection or an instantiation isn't something we take apart, nor is a
   modal application -- Olorin's logic has no modalities, so an argument always lives at the mode of
   the spine itself, and this is where we recover that.

   The equation between the mode the spine starts at and the ambient one only becomes available at
   the end of the sequence, so it comes back out of the recursion, as in Narya's own
   Check.check_constr_type. *)
let get_head_args : type hmode any.
    (hmode, mode, any) apps -> ((hmode, mode) Eq.t * mode normal list) option =
 fun args ->
  let rec go : type m1. (m1, mode) Fwd_app.fwd -> ((m1, mode) Eq.t * mode normal list) option =
    function
    | Nil -> Some (Eq, [])
    | Cons
        ( Fwd_app.Arg
            (type dom modality n m mk k)
            ((filter, arg, ins) :
              (dom, modality, m1, n, m) Modality.filter_dim
              * (n, dom normal) CubeOf.t
              * (mk, m, k) insertion),
          rest ) -> (
        match go rest with
        | None -> None
        | Some (Eq, acc) -> (
            match (is_id_ins ins, Modality.compare_id (Modality.filter_modality filter)) with
            | Some _, Eq -> Some (Eq, CubeOf.find_top arg :: acc)
            | _ -> None))
    | Cons (Fwd_app.Field _, _) -> None in
  match args with
  | Inst _ -> None
  | _ -> go (Fwd_app.of_apps args)

(* Just the arguments, for the callers that don't need to know the head is at this mode too. *)
let get_args : type hmode any. (hmode, mode, any) apps -> mode normal list option =
 fun args -> Option.map snd (get_head_args args)

let rec get_equality_or_inequality ~(block : Explain.Oracle.block) ctx tm =
  let open Monad.Ops (E) in
  let eq = Scope.lookup [ "eq" ] in
  let neq = Scope.lookup [ "neq" ] in
  let neg = Scope.lookup [ "neg" ] in
  let orders = order_relations () in
  match Norm.view_term tm with
  | Neu { head = Const { name; ins }; args; _ } when Option.is_some (is_id_ins ins) -> (
      match get_args args with
      (* Equality holds of two things of any one type, which it takes as its first argument. *)
      | Some [ ty; lhs; rhs ] ->
          let* op =
            if Some name = eq then return `Eq
            else if Some name = neq then return `Neq
            else Error (Code.Oracle_failed (Not_a_relation (block, Printable.PVal (ctx, tm))))
          in
          return (op, ty.tm, lhs, rhs)
      (* An ordering takes only the two sides. *)
      | Some [ lhs; rhs ] when List.mem_assoc name orders ->
          return (List.assoc name orders, Lazy.force lhs.ty, lhs, rhs)
      | Some [ arg ] when Some name = neg -> (
          let* op, ty, lhs, rhs = get_equality_or_inequality ~block ctx arg.tm in
          match op with
          | `Eq -> return (`Neq, ty, lhs, rhs)
          | `Neq -> return (`Eq, ty, lhs, rhs)
          | `Lt -> return (`Le, ty, rhs, lhs)
          | `Le -> return (`Lt, ty, rhs, lhs))
      | _ -> Error (Code.Oracle_failed (Not_a_relation (block, Printable.PVal (ctx, tm)))))
  | _ -> Error (Code.Oracle_failed (Not_a_relation (block, Printable.PVal (ctx, tm))))

(* The two arguments of a spine that has exactly two, for a guard that has to ask before matching. *)
let two_args : type hmode any. (hmode, mode, any) apps -> (mode normal * mode normal) option =
 fun args ->
  match get_args args with
  | Some [ p; q ] -> Some (p, q)
  | _ -> None

(* All the relations a statement asserts.  With 'split' -- which is what the "plus" block asks for
   -- a conjunction contributes those of both its components, so that block takes a conjunction of
   relations as a hypothesis; the plain block insists on a bare relation.  Underneath a negation
   neither one splits, since the negation of a conjunction is a disjunction, which is not something
   we can hand to Z3 as a fact. *)
let rec get_relations ~(split : bool) ~block ctx tm =
  let open Monad.Ops (E) in
  let land_ = Scope.lookup [ "land" ] in
  match Norm.view_term tm with
  | Neu { head = Const { name; ins }; args; _ }
    when split && Some name = land_ && Option.is_some (is_id_ins ins) && two_args args <> None ->
      let p, q = Option.get (two_args args) in
      let* p = get_relations ~split ~block ctx p.tm in
      let* q = get_relations ~split ~block ctx q.tm in
      return (p @ q)
  | _ ->
      let* rel = get_equality_or_inequality ~block ctx tm in
      return [ rel ]

(* A goal, on the other hand, may be a disjunction as well as a conjunction, for the "plus" block.
   A disjunction is proved the way a single relation is, only with every disjunct negated at once:
   the disjunction fails exactly when all of its sides do, so hypotheses that rule out every one of
   them are contradictory.  (Which side actually holds the block doesn't say, and needn't: it is
   the disjunction it proves.)

   So we read the goal as a conjunction of disjunctions of relations -- each conjunct one query --
   distributing to get there, since a conjunction inside a disjunction is not one query but one per
   conjunct: "a ∨ (b ∧ c)" is proved by proving "a ∨ b" and "a ∨ c".  Without 'split' the goal is a
   bare relation, as before, which is the same thing with one conjunct of one disjunct. *)
let rec get_clauses ~(split : bool) ~block ctx tm =
  let open Monad.Ops (E) in
  let land_ = Scope.lookup [ "land" ] in
  let lor_ = Scope.lookup [ "lor" ] in
  match Norm.view_term tm with
  | Neu { head = Const { name; ins }; args; _ }
    when split
         && (Some name = land_ || Some name = lor_)
         && Option.is_some (is_id_ins ins)
         && two_args args <> None ->
      let p, q = Option.get (two_args args) in
      let* ps = get_clauses ~split ~block ctx p.tm in
      let* qs = get_clauses ~split ~block ctx q.tm in
      if Some name = land_ then return (ps @ qs)
      else return (List.concat_map (fun p -> List.map (fun q -> p @ q) qs) ps)
  | _ ->
      let* rel = get_equality_or_inequality ~block ctx tm in
      return [ [ rel ] ]

(* Whether the block's arithmetic can treat two statements as being about the same kind of number:
   one type is a subtype of the other, so both embed in the ordered field the translation is really
   working in.  (subtype_of falls back to equality of types, so a type is comparable with itself.)
   *)
let comparable ctx ty ty' =
  Result.is_ok (subtype_of ctx ty' ty) || Result.is_ok (subtype_of ctx ty ty')

(* The kind of number a block is about: the largest of the types of the statements in play that
   are about numbers at all.  We start from the goal's, which is what a lone relation's type has
   always been, and widen past any statement about a larger system; the number systems are a chain,
   so there is a largest.  A statement about anything else is comparable with nothing and leaves
   this alone. *)
let widest ctx =
  List.fold_left (fun ty (_, ty', _, _) ->
      if Result.is_ok (subtype_of ctx ty ty') then ty' else ty)

(* Pair each relation with the type to translate it at: that one, when the relation is about the
   same kind of number, so that a subterm two of them share gets the same variable; otherwise its
   own.

   Nothing has to be refused here.  A statement about something the arithmetic knows nothing about
   -- two elements of a parameter type, say -- can only be an equation, since the orderings are
   relations on the number systems and nowhere else, and an equation between opaque terms is all
   Z3 needs to carry the two into the arguments of an uninterpreted function and let congruence do
   the rest.  Terms of two different types never share a variable, so a query can mix them freely.

   What this does rest on, as the translation always has, is that a type whose operations the
   translation interprets -- anything whose plus, times and the rest it reads as arithmetic -- is
   an ordered semiring that embeds in the reals.  That is what makes the numbers' own statements
   faithful. *)
let relation_types ctx ty =
  List.map (fun (op, ty', x, y) -> (op, (if comparable ctx ty ty' then ty else ty'), x, y))

(* The statement and the rest, out of a hypothesis list's four arguments. *)
let cons_args : type hmode any. (hmode, mode, any) apps -> (mode normal * mode normal) option =
 fun args ->
  match get_args args with
  | Some [ eqty; _; rest; _ ] -> Some (eqty, rest)
  | _ -> None

let rec get_givens ~split ~block ctx givens =
  let open Monad.Ops (E) in
  let cons_eqs = Scope.lookup [ "Cons_eqs" ] in
  let nil_eqs = Scope.lookup [ "Nil_eqs" ] in
  match Norm.view_term givens with
  | Neu { head = Const { name; ins }; args; _ }
    when Some name = cons_eqs && Option.is_some (is_id_ins ins) && cons_args args <> None ->
      let eqty, rest = Option.get (cons_args args) in
      let* rels =
        (* An input that isn't a relation at all is the same complaint as a goal that isn't one,
           but about a wire rather than about the goal, so it gets its own message. *)
        match get_relations ~split ~block ctx eqty.tm with
        | Ok rels -> Ok rels
        | Error (Code.Oracle_failed (Not_a_relation _)) ->
            Error (Code.Oracle_failed (Not_a_relation_input (block, Printable.PNormal (ctx, eqty))))
        | Error e -> Error e in
      let* rest = get_givens ~split ~block ctx rest.tm in
      return (rels @ rest)
  | Neu { head = Const { name; ins }; args; _ }
    when Some name = nil_eqs && Option.is_some (is_id_ins ins) && get_args args = Some [] ->
      return []
  | _ -> Error (Code.Oracle_failed (Not_a_hypothesis_list (Printable.PVal (ctx, givens))))

(* The value a constructor's argument carries, at the mode of the constructor itself.  As with the
   arguments of an application, Olorin's constructors are never modal. *)
let get_constr_arg : type n a. (n, mode, a) modal_value_cube -> (mode, a) value option =
 fun (Modal (filter, arg)) ->
  match Modality.compare_id (Modality.filter_modality filter) with
  | Eq -> Some (CubeOf.find_top arg)
  | Neq -> None

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
      | Zero ->
          Option.bind (get_constr_arg arg) (fun arg ->
              Option.map (fun n -> n + 1) (get_posint arg))
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
  (* Something we know about a symbol as soon as we make it, rather than from the hypotheses: the
     relations defining a root, or that a natural is at least zero. *)
  | Define of Relation.t list
  (* A denominator, which the hypotheses have to force to be nonzero, paired with the term it came
     from so we can point at it in an error. *)
  | Nonzero of Symbolic.t * (mode, kinetic) value
  (* Likewise the base of an even root, which they have to force to be nonnegative. *)
  | Nonneg of Symbolic.t * (mode, kinetic) value
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
  | Cases of [ `Sign | `Order ] * Symbolic.t * Symbolic.t * (mode, kinetic) value

(* The head of an application we can hand to Z3 as a function symbol.  A constant or a variable,
   and only a bare one: a degeneracy or a nonidentity insertion on it makes a different term, so
   rather than deciding when two of those agree we leave such a term opaque. *)
type funhead = [ `Const of Constant.t | `Var of level ]

let get_funhead : mode head -> funhead option = function
  | Const { name; ins } when Option.is_some (is_id_ins ins) -> Some (`Const name)
  (* Olorin's mode theory is trivial, so a variable's modal key is always the identity. *)
  | Var { level; deg; key = _ } when Option.is_some (is_id_deg deg) -> Some (`Var level)
  | _ -> None

(* Whether a type is ℕ.  Its elements are nonnegative, which to Z3 -- for whom they are opaque
   reals like any other -- is not a fact about them at all until we say so. *)
let is_natural ty =
  match Norm.view_term ty with
  | Neu { head = Const { name; ins }; args; _ } ->
      Option.is_some (is_id_ins ins)
      && get_args args = Some []
      && Some name = Scope.lookup [ "ℕ" ]
  | _ -> false

(* State threaded through the translation of a term into a Z3 expression. *)
type translation = {
  (* Subterms we can't interpret, each standing for an opaque variable.  A root's variable is one of
     these, keyed by the power it came from, so that writing the same root twice gets the same
     variable and states its definition once.  We record the type each was met at as well as the
     term, since an argument of an uninterpreted function can be of any type at all, and asking
     whether two terms agree only makes sense once we know they're of the same type. *)
  vars : mode normal Bwd.t;
  count : int;
  (* Likewise the heads we've turned into uninterpreted function symbols, each paired with the
     number of arguments it was applied to.  Z3's functions have no partial application, so a head
     written with two arguments in one place and one in another is two symbols, not one. *)
  funs : (funhead * int) Bwd.t;
  funcount : int;
  (* The symbols we've already said are nonnegative, so a natural written twice says it once. *)
  nonnegs : Symbolic.t Bwd.t;
  (* The definitions and obligations met along the way, oldest first. *)
  steps : step Bwd.t;
}

module S = Monad.State (struct
  type t = translation
end)

(* The variable standing for a subterm we can't express directly, and whether we have just met that
   subterm for the first time -- so that a root states its definition once however often it is
   written.  Two subterms share a variable only when they are really the same term, at the same
   type: giving one variable to two different terms would be asserting an equation that doesn't
   hold, and could prove anything. *)
let var_for ctx ty tm : (Symbolic.t * bool) S.t =
  let open Monad.Ops (S) in
  let* ({ vars; count; _ } as st) = S.get in
  let same (x : mode normal) =
    Result.is_ok (Equal.equal_val ctx ty (Lazy.force x.ty))
    && Result.is_ok (Equal.equal_at ctx tm x.tm ty) in
  match Bwd.find_index same vars with
  | None ->
      let* () =
        S.put { st with vars = Snoc (vars, { tm; ty = Lazy.from_val ty }); count = count + 1 } in
      return (`Var count, true)
  | Some i -> return (`Var (count - i - 1), false)

(* Likewise the function symbol standing for a head we can't interpret, applied to that many
   arguments.  Heads are compared as they are written rather than up to conversion, so a constant
   and a variable it's defined to equal get two symbols; that costs us provable goals, never
   soundness. *)
let fun_for (hd : funhead) (arity : int) : int S.t =
  let open Monad.Ops (S) in
  let* ({ funs; funcount; _ } as st) = S.get in
  match Bwd.find_index (fun x -> x = (hd, arity)) funs with
  | None ->
      let* () = S.put { st with funs = Snoc (funs, (hd, arity)); funcount = funcount + 1 } in
      return funcount
  | Some i -> return (funcount - i - 1)

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
  let rec power ty tm base e src =
    let n, d = (Q.num e, Q.den e) in
    if not (Z.fits_int n && Z.fits_int d && Z.leq (Z.abs n) (Z.of_int max_exponent)
            && Z.leq d (Z.of_int max_exponent)) then opaque ty tm
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
        return s
  (* A term the arithmetic doesn't interpret.  A numeral is the constant it names.  An application
     of a bare constant or variable becomes an uninterpreted function symbol applied to the
     translations of its arguments: Z3 knows nothing about such a function beyond congruence, which
     is exactly what we want, as it gives us "f x = f y" from "x = y" and nothing else.  Anything
     else -- a projection, a constructor, a variable on its own -- is a variable of its own, as
     before.  *)
  and opaque ty tm : Symbolic.t S.t =
    match get_posint tm with
    | Some i -> return (`Const (Q.of_int i))
    | None -> (
        match Norm.view_term tm with
        (* A neutral carries its own type, and that is the one that says whether it's a natural --
           not the kind of number the arithmetic around it is about, which a natural reaches by
           being contained in it. *)
        | Neu { head; args; ty = tmty; _ } -> (
            let* v =
              (* The Eq is what says the head is at the ambient mode, so it can be one of ours. *)
              match get_head_args args with
              | Some (Eq, ((_ :: _) as args)) when Option.is_some (get_funhead head) ->
                  let hd = Option.get (get_funhead head) in
                  let* f = fun_for hd (List.length args) in
                  let* args = go_args ty args in
                  return (`App (f, args))
              | _ -> var ty tm in
            natural (Lazy.force tmty) v)
        | _ -> var ty tm)
  and var ty tm =
    let* v, _ = var_for ctx ty tm in
    return v
  (* A term of type ℕ is a natural number, and that it is at least zero is a fact about the type
     rather than anything the hypotheses say -- to Z3 it is an opaque real like any other -- so the
     translation states it the first time it meets such a term.  Only an opaque one needs it: a
     numeral says it for itself, and Z3 gets "n + m ≥ 0" and "n · m ≥ 0" from the parts.  An
     uninterpreted function landing in ℕ counts as one, its value being just as opaque. *)
  and natural tmty v =
    let* st = S.get in
    if is_natural tmty && not (Bwd.exists (fun x -> x = v) st.nonnegs) then
      let* () = S.put { st with nonnegs = Snoc (st.nonnegs, v) } in
      let* () = add_step (Define [ (`Le, `Const Q.zero, v) ]) in
      return v
    else return v
  (* An argument of an uninterpreted function can be of any type at all, not just the kind of
     number the arithmetic is about.  One that is about the same kind of number is translated at
     that type, like everything else, so that a term it shares with the rest of the question gets
     the same variable; one that isn't -- an element of a parameter type, say -- at its own.  On
     the Z3 side every sort collapses to the reals, which only gives the solver more models to
     consider, never fewer. *)
  and go_args ty = function
    | [] -> return []
    | (a : mode normal) :: rest ->
        let aty = Lazy.force a.ty in
        let* a = go (if comparable ctx ty aty then ty else aty) a.tm in
        let* rest = go_args ty rest in
        return (a :: rest)
  and go ty tm =
    match Norm.view_term tm with
    (* Binary operation.  The arguments are translated inside each branch rather than before the
       match, so that a head that isn't one of these doesn't translate them twice -- once here and
       again as the arguments of its function symbol. *)
    | Neu { head = Const { name; ins }; args; _ }
      when Option.is_some (is_id_ins ins) && two_args args <> None -> (
        let x, y = Option.get (two_args args) in
        let binary k =
          let* px = go ty x.tm in
          let* py = go ty y.tm in
          k px py in
        match Firstorder.get_root name with
        | "plus" -> binary (fun px py -> return (`Plus (px, py)))
        | "minus" -> binary (fun px py -> return (`Minus (px, py)))
        | "times" -> binary (fun px py -> return (`Times (px, py)))
        | "min" ->
            binary (fun px py ->
                let* () = add_step (Cases (`Order, px, py, tm)) in
                return (`Min (px, py)))
        | "max" ->
            binary (fun px py ->
                let* () = add_step (Cases (`Order, px, py, tm)) in
                return (`Max (px, py)))
        | "divide" ->
            binary (fun px py ->
                (* A quotient of numerals is just a rational constant, and carries no obligation.
                   We ask rational_of rather than matching on `Const, so that a minus sign in front
                   of either of them doesn't stop the fold: "−1/2" parses as (−1)/2. *)
                match (rational_of px, rational_of py) with
                | Some a, Some b when not (Q.equal b Q.zero) -> return (`Const (Q.div a b))
                (* Otherwise we hand the division to Z3 as a division.  Z3's real division is total,
                   with the value at a zero denominator left uninterpreted, so this is sound however
                   the denominator turns out; but we also require it to be provably nonzero. *)
                | _ ->
                    let* () = add_step (Nonzero (py, y.tm)) in
                    return (`Div (px, py)))
        | "pow" ->
            binary (fun px py ->
                match rational_of py with
                | Some e -> power ty tm px e x.tm
                | None -> opaque ty tm)
        | _ -> opaque ty tm)
    (* Unary operation *)
    | Neu { head = Const { name; ins }; args; _ }
      when Option.is_some (is_id_ins ins)
           && (match get_args args with
              | Some [ _ ] -> true
              | _ -> false) -> (
        let src =
          match get_args args with
          | Some [ x ] -> x.tm
          | _ -> assert false in
        let unary k =
          let* x = go ty src in
          k x in
        match Firstorder.get_root name with
        | "sqrt" -> unary (fun x -> power ty tm x (Q.of_ints 1 2) src)
        | "abs" ->
            unary (fun x ->
                let* () = add_step (Cases (`Sign, `Const Q.zero, x, src)) in
                return (`Abs x))
        | "negate" ->
            unary (fun x ->
                match rational_of x with
                | Some q -> return (`Const (Q.neg q))
                | None -> return (`Neg x))
        | "square" -> unary (fun x -> return (`Times (x, x)))
        | "cube" -> unary (fun x -> return (`Times (`Times (x, x), x)))
        | "fourth" -> unary (fun x -> return (`Times (`Times (x, x), `Times (x, x))))
        | _ -> opaque ty tm)
    | _ -> opaque ty tm in
  go ty tm

let vars_of_ctx : type a b. (mode, a, b) Ctx.t -> string Bwd.t = function
  | Permute { ctx; _ } ->
      (* A lock changes the mode of the context inside it, so this is polymorphic in the mode. *)
      let rec vars_of_ctx : type m a b. (m, a, b) Ctx.Ordered.t -> string Bwd.t = function
        | Emp _ -> Emp
        | Lock (ctx, _) -> vars_of_ctx ctx
        | Weaken (ctx, _) -> vars_of_ctx ctx
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
  (* Narya's question is existential in the mode it was asked at, while everything here is written
     at Olorin's own one (see Omode).  There is only one mode in the process, so this always
     succeeds; it is how the types get to know that. *)
  match Modal.Mode.compare (Ctx.mode ctx) Omode.mode with
  | Neq -> Error (Code.Oracle_failed (Not_an_oracle_application (Printable.PVal (ctx, tm))))
  | Eq ->
  (* The two algebra blocks ask through constants of their own, so the question says which one is
     asking: the "plus" block decides an absolute value, a minimum or a maximum itself, while the
     plain one requires the hypotheses to settle each of those first (see Cases below). *)
  let oracle = Scope.lookup [ "oracle" ] in
  let oracle_plus = Scope.lookup [ "oracle_plus" ] in
  let* block, givens, goal =
    match Norm.view_term tm with
    | Neu { head = Const { name; ins }; args; _ }
      when (Some name = oracle || Some name = oracle_plus)
           && Option.is_some (is_id_ins ins)
           && (match get_args args with
              | Some [ _; _; _ ] -> true
              | _ -> false) ->
        let givens, goal =
          match get_args args with
          | Some [ givens; _; goal ] -> (givens, goal)
          | _ -> assert false in
        return
          ((if Some name = oracle_plus then `Algplus else `Alg), givens, goal)
    | _ -> Error (Code.Oracle_failed (Not_an_oracle_application (Printable.PVal (ctx, tm)))) in
  (* The "plus" block is the one that splits a statement apart, and the one that decides an
     absolute value, a minimum or a maximum on its own (see Cases below). *)
  let plus = block = `Algplus in
  (* The goal is a list of clauses, each a disjunction to prove against all of the hypotheses (see
     get_clauses).  They all go through one translation, so that the same subterm gets the same
     variable throughout.

     A goal that isn't a relation at all isn't refused out of hand: anything whatsoever follows from
     hypotheses that contradict each other, so such a goal leaves the list of clauses to prove
     empty, and what we ask below is whether the hypotheses are inconsistent on their own.  (The
     goal is still reported as a whole, rather than by the part that isn't a relation, as the
     hypotheses are reported by the whole wire.) *)
  let nonalgebraic_goal =
    Code.Oracle_failed (Not_a_relation (block, Printable.PNormal (ctx, goal))) in
  let* goals =
    match get_clauses ~split:plus ~block ctx goal.tm with
    | Ok goals -> Ok goals
    | Error (Code.Oracle_failed (Not_a_relation _)) -> Ok []
    | Error e -> Error e in
  let* givens = get_givens ~split:plus ~block ctx givens.tm in
  (* The kind of number the block is *about* -- which decides what shares variables with what, and
     nothing else -- comes from the first of the goal's relations, as a single relation's type was
     taken from the goal itself; with no goal relation to read it off, the first hypothesis serves
     instead.  If there is neither, there is nothing that could be inconsistent, so a non-algebraic
     goal fails here rather than at a query with no facts in it. *)
  let* ty =
    match List.concat goals @ givens with
    | (_, ty, _, _) :: _ -> Ok ty
    | [] -> Error nonalgebraic_goal in
  (* Both ends are tagged together, so that a hypothesis about a larger number system than the goal
     pulls the goal up to it rather than being translated down. *)
  let ty = widest ctx ty (List.concat goals @ givens) in
  let goals = List.map (relation_types ctx ty) goals in
  let givens = relation_types ctx ty givens in
  let (givens, goals), { steps; _ } =
    (let open Monad.Ops (S) in
     let poly (op, ty, (x : mode normal), (y : mode normal)) =
       let* x = get_poly ctx ty x.tm in
       let* y = get_poly ctx ty y.tm in
       return (op, x, y) in
     let rec polys = function
       | [] -> return []
       | g :: gs ->
           let* g = poly g in
           let* gs = polys gs in
           return (g :: gs) in
     let rec clauses = function
       | [] -> return []
       | c :: cs ->
           let* c = polys c in
           let* cs = clauses cs in
           return (c :: cs) in
     (* The goal before the hypotheses, so that the side conditions come out in the order they did
        when a goal was always a single relation. *)
     let* goals = clauses goals in
     let* givens = polys givens in
     return (givens, goals))
      { vars = Emp; count = 0; funs = Emp; funcount = 0; nonnegs = Emp; steps = Emp } in
  (* The quantifier eliminator can prove disequalities, but we only let it do so between rational
     literals, like 0≠1.  A disequality with anything else in it is one we want the student to
     prove by contradiction -- as a disjunct of a goal as much as on its own, since a disjunction
     with the other sides ruled out is a proof of that disequality like any other. *)
  let* () =
    List.fold_left
      (fun acc (op, lhs, rhs) ->
        let* () = acc in
        if op = `Neq && not (is_literal lhs && is_literal rhs) then
          Error (Code.Oracle_failed Disequality)
        else Ok ())
      (Ok ()) (List.concat goals) in
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
          Error (Code.Oracle_failed (Zero_denominator (Printable.PVal (ctx, src))))
    | Nonneg (base, src) :: rest ->
        if unsat ((`Lt, base, `Const Q.zero) :: facts) then discharge facts rest
        else
          Error (Code.Oracle_failed (Negative_base (Printable.PVal (ctx, src))))
    (* Z3 decides a conditional on its own, so for the "plus" block there is nothing to discharge.
       For the plain one the hypotheses have to settle the comparison -- "a ≤ b" or "b ≤ a", either
       will do -- which is what makes the student split into cases by hand. *)
    | Cases (which, a, b, src) :: rest ->
        if plus || unsat ((`Lt, b, a) :: facts) || unsat ((`Lt, a, b) :: facts) then
          discharge facts rest
        else
          let err =
            match which with
            | `Sign -> Undecided_sign (Printable.PVal (ctx, src))
            | `Order -> Undecided_order (Printable.PVal (ctx, src)) in
          Error (Code.Oracle_failed err) in
  let* facts = discharge givens (Bwd.to_list steps) in
  (* Each conjunct of the goal is then a question of its own, asked against all the hypotheses.  We
     negate it, since Z3 checks for satisfiability; that means negating the operator and also
     swapping the order of the arguments (although for a (dis)equality swapping does nothing).  A
     conjunct with several disjuncts is negated all at once: what makes the disjunction follow is
     that the hypotheses can't be had along with every one of its sides failing. *)
  let negate (op, lhs, rhs) =
    let neg_op =
      match op with
      | `Eq -> `Neq
      | `Neq -> `Eq
      | `Lt -> `Le
      | `Le -> `Lt in
    (neg_op, rhs, lhs) in
  match goals with
  (* A goal that isn't algebraic at all, which we prove only by the hypotheses being contradictory:
     from a contradiction anything follows, that statement included.  Where they aren't, the
     complaint is that the goal isn't a relation, not that it doesn't follow by algebra. *)
  | [] -> if unsat facts then Ok () else Error nonalgebraic_goal
  | _ ->
      List.fold_left
        (fun acc clause ->
          let* () = acc in
          if unsat (List.map negate clause @ facts) then Ok ()
          else Error (Code.Oracle_failed Unprovable))
        (Ok ()) goals
