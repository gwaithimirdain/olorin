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
            else Error (Code.Oracle_failed (Not_a_relation (block, Printable.PVal (ctx, tm)))) in
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
  List.fold_left (fun ty (_, ty', _, _) -> if Result.is_ok (subtype_of ctx ty ty') then ty' else ty)

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
          Option.bind (get_constr_arg arg) (fun arg -> Option.map (fun n -> n + 1) (get_posint arg))
      | Pos _ -> None)
  | _ -> None

let rec pow p n = if n <= 0 then `Const Q.one else `Times (pow p (n - 1), p)

(* Something already translated, multiplied by a base n times: x·b·b·…·b.  Written this way round
   rather than as a product with 'pow', and starting from a 1 that drops out rather than one that
   stays, so that a product of powers comes out with nothing extra in it -- which is what makes the
   two sides of "x^(n+1) = x^n·x" the very same expression. *)
let rec mulpow (x : Symbolic.t) (base : Symbolic.t) (n : int) : Symbolic.t =
  if n <= 0 then x
  else
    let x : Symbolic.t =
      match x with
      | `Const q when Q.equal q Q.one -> base
      | _ -> `Times (x, base) in
    mulpow x base (n - 1)

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

let fits_exponent e =
  let n, d = (Q.num e, Q.den e) in
  Z.fits_int n
  && Z.fits_int d
  && Z.leq (Z.abs n) (Z.of_int max_exponent)
  && Z.leq d (Z.of_int max_exponent)

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
  (* What a power with a variable exponent inherits from the sign of its base, which is a fact
     about it that no amount of algebra on the opaque symbol would give.  Unlike the obligations
     above nothing has to be shown here: the hypotheses either decide the base's sign, in which
     case the power gets the corresponding fact, or they don't, in which case it gets none and the
     goal may or may not still follow.  'nat' says whether the exponent is a natural, since a base
     of zero is only ruled out for the integer ones, and 'nonneg' that the power is already known
     to be nonnegative by its type, which saves asking about that one. *)
  | Positive of { base : Symbolic.t; power : Symbolic.t; nat : bool; nonneg : bool }

(* The head of an application we can hand to Z3 as a function symbol.  A constant or a variable,
   and only a bare one: a degeneracy or a nonidentity insertion on it makes a different term, so
   rather than deciding when two of those agree we leave such a term opaque. *)
type funhead = [ `Const of Constant.t | `Var of level | `Pow ]

let get_funhead : mode head -> funhead option = function
  (* Every number system's power is one function symbol, the way its plus and times are one
     operation: the systems agree wherever they overlap, which is what the translation assumes of
     all of them, so "2^n" written at ℕ and at ℝ is one term to Z3 rather than two. *)
  | Const { name; ins } when Option.is_some (is_id_ins ins) ->
      Some (if Firstorder.get_root name = "pow" then `Pow else `Const name)
  (* Olorin's mode theory is trivial, so a variable's modal key is always the identity. *)
  | Var { level; deg; key = _ } when Option.is_some (is_id_deg deg) -> Some (`Var level)
  | _ -> None

(* Whether a type is one of the number systems named.  That it is ℕ says its elements are
   nonnegative, which to Z3 -- for whom they are opaque reals like any other -- is not a fact about
   them at all until we say so; that it is ℕ or ℤ says an exponent is a whole number, which is what
   lets a power be taken apart (see exponent_form). *)
let is_number_type sys ty =
  match Norm.view_term ty with
  | Neu { head = Const { name; ins }; args; _ } ->
      Option.is_some (is_id_ins ins) && get_args args = Some [] && Some name = Scope.lookup [ sys ]
  | _ -> false

let is_natural ty = is_number_type "ℕ" ty
let is_integer ty = is_number_type "ℤ" ty

(* An exponent in linear form: the terms it is made of, each with an integer coefficient, and an
   integer offset.  "n+1" is n with coefficient 1 and offset 1, "2·n−m" is n with 2 and m with −1,
   and an exponent with no arithmetic on the outside of it is itself with coefficient 1.  Only
   numerals fold into the coefficients and the offset, those being what the translation can turn
   back into a product of powers; anything else stays a term of its own.  Nothing compares the
   terms here -- deciding when two of them are the same is the translation's business, and it has
   already been settled there (see var_for) -- so "n+n" comes back as n twice over. *)
let rec linear_form tm =
  let scale c = List.map (fun (t, d) -> (t, c * d)) in
  match get_posint tm with
  | Some k -> ([], k)
  | None -> (
      match Norm.view_term tm with
      | Neu { head = Const { name; ins }; args; _ } when Option.is_some (is_id_ins ins) -> (
          match (Firstorder.get_root name, get_args args) with
          | "plus", Some [ x; y ] ->
              let ax, kx = linear_form x.tm in
              let ay, ky = linear_form y.tm in
              (ax @ ay, kx + ky)
          | "minus", Some [ x; y ] ->
              let ax, kx = linear_form x.tm in
              let ay, ky = linear_form y.tm in
              (ax @ scale (-1) ay, kx - ky)
          | "negate", Some [ x ] ->
              let ax, kx = linear_form x.tm in
              (scale (-1) ax, -kx)
          (* A product is a coefficient only when one side is a numeral; "n·m" is a term of its
             own, there being no power of the base to raise to it. *)
          | "times", Some [ x; y ] -> (
              match (get_posint x.tm, get_posint y.tm) with
              | Some c, _ ->
                  let a, k = linear_form y.tm in
                  (scale c a, c * k)
              | _, Some c ->
                  let a, k = linear_form x.tm in
                  (scale c a, c * k)
              | None, None -> ([ (tm, 1) ], 0))
          | _ -> ([ (tm, 1) ], 0))
      | _ -> ([ (tm, 1) ], 0))

(* How big a polynomial an exponent in linear form would build: past this we give up and leave the
   power opaque, as a written-out exponent that size already is. *)
let degree (atoms, off) = abs off + List.fold_left (fun s (_, c) -> s + abs c) 0 atoms

(* Whether what's left of an exponent is a whole number, and if so whether it is a natural one.
   The term's own type says so, not the power's: ℝ's exponent is a ℚ whatever is written there, and
   a ℕ or a ℤ written in it is one by being contained in ℚ.  Anything else -- a genuine rational,
   or a term whose type we can't read -- is not something to take apart. *)
let exponent_kind tm =
  match Norm.view_term tm with
  | Neu { ty; _ } ->
      let ty = Lazy.force ty in
      if is_natural ty then Some true else if is_integer ty then Some false else None
  | _ -> None

(* What an opaque variable stands for.  A subterm we can't interpret is identified by the term
   itself, at the type it was met at.  A root is identified instead by the base as the translation
   writes it and the exponent it is raised to: what makes such a variable mean anything is the
   definition stated alongside it, "s >= 0 and s^q = base^p", and two roots with the same base and
   the same exponent have the same definition however they were written.  So √x and x^(1/2) are one
   variable rather than two that Z3 has to reconcile, and a root the problem never writes down at
   all -- the x^(1/2) inside x^(n+1/2) -- has an identity like any other. *)
type tvar = Term of mode normal | Root of Symbolic.t * Q.t

(* State threaded through the translation of a term into a Z3 expression. *)
type translation = {
  (* The variables we've made, oldest first, each identified as above.  A term records the type it
     was met at as well, since an argument of an uninterpreted function can be of any type at all,
     and asking whether two terms agree only makes sense once we know they're of the same type. *)
  vars : tvar Bwd.t;
  count : int;
  (* Likewise the heads we've turned into uninterpreted function symbols, each paired with the
     number of arguments it was applied to.  Z3's functions have no partial application, so a head
     written with two arguments in one place and one in another is two symbols, not one. *)
  funs : (funhead * int) Bwd.t;
  funcount : int;
  (* The symbols we've already said are nonnegative, so a natural written twice says it once. *)
  nonnegs : Symbolic.t Bwd.t;
  (* Likewise the powers whose base we've already asked the sign of: those questions go to Z3, so
     a power written twice -- as it is on the two sides of "x^(n+1) = x^n·x" -- asks once. *)
  signs : Symbolic.t Bwd.t;
  (* And the powers we've already said what the product they came apart into is (see varpower),
     so that too is said once. *)
  powers : Symbolic.t Bwd.t;
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
  let same = function
    | Root _ -> false
    | Term (x : mode normal) ->
        Result.is_ok (Equal.equal_val ctx ty (Lazy.force x.ty))
        && Result.is_ok (Equal.equal_at ctx tm x.tm ty) in
  match Bwd.find_index same vars with
  | None ->
      let* () =
        S.put
          { st with vars = Snoc (vars, Term { tm; ty = Lazy.from_val ty }); count = count + 1 } in
      return (`Var count, true)
  | Some i -> return (`Var (count - i - 1), false)

(* Likewise the variable standing for a root of a base, and whether we have just made it -- so that
   it states its definition once, however many ways the problem writes it.  The base is compared as
   the translation writes it, which is where two ways of writing the same number have already been
   made one. *)
let root_for (base : Symbolic.t) (e : Q.t) : (Symbolic.t * bool) S.t =
  let open Monad.Ops (S) in
  let* ({ vars; count; _ } as st) = S.get in
  let same = function
    | Term _ -> false
    | Root (b, f) -> b = base && Q.equal f e in
  match Bwd.find_index same vars with
  | None ->
      let* () = S.put { st with vars = Snoc (vars, Root (base, e)); count = count + 1 } in
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
     'src' is the term to point at if an obligation can't be discharged, and the exponent is one
     the caller has already found small enough to build from (see fits_exponent). *)
  let rec ratpow base e src =
    let n, d = (Z.to_int (Q.num e), Z.to_int (Q.den e)) in
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
      let* s, fresh = root_for base e in
      let* () =
        if fresh then
          add_step
            (Define ((if even then [ (`Le, `Const Q.zero, s) ] else []) @ [ (`Eq, pow s d, rhs) ]))
        else return () in
      return s
  (* The same, for an exponent that may be too big to build a polynomial from, where there is a
     term to fall back on leaving opaque. *)
  and power ty tm base e src = if fits_exponent e then ratpow base e src else opaque ty tm
  (* A power whose exponent isn't a literal: "x^(n+1)", "x^(n+m)", "x^(2·n)" and their kin.  The
     exponent is a sum of terms with integer coefficients and an integer offset, and the power
     becomes the matching product: x^(k + Σcᵢ·aᵢ) is x^k times each x^(aᵢ) multiplied in cᵢ times,
     with x^(aᵢ) an uninterpreted function of base and exponent, as the whole power was before.

     That is what makes the laws of exponents hold on the nose rather than by anything Z3 has to
     decide: written this way, both sides of "x^(n+1) = x^n·x" and of "x^(n+m) = x^n·x^m" are the
     very same product.  The laws being used are b^(a+c) = b^a·b^c and b^(c·a) = (b^a)^c, which
     hold of every real b when the exponents are naturals and the coefficients positive -- b^0
     being 1 throughout this translation, so a zero exponent and a zero base are no exception.
     Anything that can go negative makes the power a reciprocal and asks for a nonzero base, which
     is the obligation a written-out negative exponent already carries.  'tmty' is the type of the
     power itself and 'src' the base, to point at in an error. *)
  and varpower ty tmty tm base exponent atoms off src =
    (* The terms of the exponent, translated, with the ones that agree merged: they are compared
       as translated expressions rather than as terms, which is where two ways of writing the same
       thing have already been made one, so "x^(n+n)" is x^n·x^n either way it was written.  A
       term that comes out a constant folds into the offset instead, whatever its type -- the 1/2
       in "x^(n+1/2)" is a constant like any other -- and only a term that stays a term has to be
       a whole number.  One that needn't be stops all of this: b^(a+c) = b^a·b^c is false for a
       fractional a and a negative b, there being no real b^a to speak of there. *)
    let rec collect acc k = function
      | [] -> return (Some (acc, k))
      | (t, c) :: rest -> (
          let* a = go ty t in
          match rational_of a with
          | Some q -> collect acc (Q.add k (Q.mul (Q.of_int c) q)) rest
          | None -> (
              match exponent_kind t with
              | None -> return None
              | Some nat ->
                  let acc =
                    if List.exists (fun (b, _, _) -> b = a) acc then
                      List.map
                        (fun (b, d, m) -> if b = a then (b, d + c, m || nat) else (b, d, m))
                        acc
                    else acc @ [ (a, c, nat) ] in
                  collect acc k rest)) in
    let* collected = collect [] (Q.of_int off) atoms in
    match collected with
    | None -> opaque ty tm
    | Some (atoms, k) -> (
        (* Coefficients can cancel, and every term can fold away, in which case the exponent was a
           literal after all -- "x^(1+2)", or "x^(n−n)" -- and the ordinary path applies. *)
        match List.filter (fun (_, c, _) -> c <> 0) atoms with
        | [] -> power ty tm base k src
        | atoms ->
            (* Past a point the product is too big to be worth building, and the power stays
               opaque as a written-out exponent that size already would. *)
            let coefficients = List.fold_left (fun s (_, c, _) -> s + abs c) 0 atoms in
            if (not (fits_exponent k)) || coefficients + abs (Z.to_int (Q.num k)) > max_exponent
            then opaque ty tm
            else
              (* Naturals with positive coefficients and a nonnegative offset ask nothing at all.
                 A term or a coefficient that can go negative makes the power a reciprocal and asks
                 for a nonzero base; a fractional offset is a root of the base, and asks for
                 whatever a written-out root of it would (see ratpow). *)
              let whole =
                Q.geq k Q.zero && List.for_all (fun (_, c, nat) -> c > 0 && nat) atoms in
              let* () = if whole then return () else add_step (Nonzero (base, src)) in
              let rec build acc = function
                | [] -> return acc
                | (a, c, nat) :: rest ->
                    let* f = fun_for `Pow 2 in
                    let p : Symbolic.t = `App (f, [ base; a ]) in
                    (* b^a lands in ℕ exactly when the whole power does: ℕ.pow is the only power
                       landing there, and it takes naturals for both of its arguments. *)
                    let nonneg = nat && is_natural (Lazy.force tmty) in
                    let* p = if nat then natural (Lazy.force tmty) p else return p in
                    let* () = sign base p nat nonneg in
                    let acc = if c > 0 then mulpow acc p c else `Div (acc, pow p (-c)) in
                    build acc rest in
              let* acc = build (`Const Q.one) atoms in
              (* An integer offset is copies of the base multiplied in, which keeps the product
                 free of anything Z3 has to work out; a fractional one is a root of it. *)
              let* result =
                if Z.equal (Q.den k) Z.one then
                  let k = Z.to_int (Q.num k) in
                  return (if k >= 0 then mulpow acc base k else `Div (acc, pow base (-k)))
                else
                  let* s = ratpow base k src in
                  return (`Times (acc, s)) in
              (* And the power as it was written, said to equal that product.  Coming apart at the
                 exponent is what proves the laws of exponents, but it also takes apart a term that
                 congruence would have matched against another way of writing the same power --
                 x^((m+1)·(n+1)) against x^(m·n+m+n+1), whose exponents Z3 can see are equal, one
                 of which comes apart and the other of which doesn't.  Keeping the written form
                 and saying what it equals gives us both. *)
              let* f = fun_for `Pow 2 in
              let plain : Symbolic.t = `App (f, [ base; exponent ]) in
              let* () = if plain = result then return () else stated plain result in
              return result)
  (* What a power that came apart is equal to, said once however often it is written. *)
  and stated plain result =
    let* st = S.get in
    if Bwd.exists (fun x -> x = plain) st.powers then return ()
    else
      let* () = S.put { st with powers = Snoc (st.powers, plain) } in
      add_step (Define [ (`Eq, plain, result) ])
  (* The sign a power takes from its base, asked about once however often the power is written:
     those questions go to Z3 (see Positive), and the two sides of an equation between powers
     would otherwise ask the same ones twice. *)
  and sign base p nat nonneg =
    let* st = S.get in
    if Bwd.exists (fun x -> x = p) st.signs then return ()
    else
      let* () = S.put { st with signs = Snoc (st.signs, p) } in
      add_step (Positive { base; power = p; nat; nonneg })
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
        | Neu { head; args; ty = tmty; _ } ->
            let* v =
              (* The Eq is what says the head is at the ambient mode, so it can be one of ours. *)
              match get_head_args args with
              | Some (Eq, (_ :: _ as args)) when Option.is_some (get_funhead head) ->
                  let hd = Option.get (get_funhead head) in
                  let* f = fun_for hd (List.length args) in
                  let* args = go_args ty args in
                  return (`App (f, args))
              | _ -> var ty tm in
            natural (Lazy.force tmty) v
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
    | Neu { head = Const { name; ins }; args; ty = tmty; _ }
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
                (* A variable exponent comes apart into the terms making it up and is put back
                   together as a product of powers.  How far that can go varpower decides, having
                   the translated terms to look at; all that's asked here is that they won't build
                   a polynomial too big to be worth handing to Z3 at all. *)
                | None ->
                    let atoms, off = linear_form y.tm in
                    if degree (atoms, off) <= max_exponent then
                      varpower ty tmty tm px py atoms off x.tm
                    else opaque ty tm)
        | _ -> opaque ty tm)
    (* Unary operation *)
    | Neu { head = Const { name; ins }; args; _ }
      when Option.is_some (is_id_ins ins)
           &&
           match get_args args with
           | Some [ _ ] -> true
           | _ -> false -> (
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
  | Eq -> (
      (* The two algebra blocks ask through constants of their own, so the question says which one is
     asking: the "plus" block decides an absolute value, a minimum or a maximum itself, while the
     plain one requires the hypotheses to settle each of those first (see Cases below). *)
      let oracle = Scope.lookup [ "oracle" ] in
      let oracle_neq = Scope.lookup [ "oracle_neq" ] in
      let oracle_plus = Scope.lookup [ "oracle_plus" ] in
      let* block, givens, goal =
        match Norm.view_term tm with
        | Neu { head = Const { name; ins }; args; _ }
          when Option.is_some (is_id_ins ins)
               &&
               match get_args args with
               | Some [ _; _; _ ] -> true
               | _ -> false ->
            let givens, goal =
              match get_args args with
              | Some [ givens; _; goal ] -> (givens, goal)
              | _ -> assert false in
            if Some name = oracle then return (`Alg, givens, goal)
            else if Some name = oracle_plus then return (`Algplus, givens, goal)
            else if Some name = oracle_neq then return (`Algneq, givens, goal)
            else Error (Code.Oracle_failed (Not_an_oracle_application (Printable.PVal (ctx, tm))))
        | _ -> Error (Code.Oracle_failed (Not_an_oracle_application (Printable.PVal (ctx, tm))))
      in
      (* The "plus" block is the one that splits a statement apart, and the one that decides an
     absolute value, a minimum or a maximum on its own (see Cases below). *)
      let plus = block = `Algplus in
      let allow_neq = block = `Algneq in
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
          {
            vars = Emp;
            count = 0;
            funs = Emp;
            funcount = 0;
            nonnegs = Emp;
            signs = Emp;
            powers = Emp;
            steps = Emp;
          } in
      (* The quantifier eliminator can prove disequalities, but we only let it do so between rational
     literals, like 0≠1, unless the `Neq flag is in effect.  A disequality with anything else in it is one we want the student to
     prove by contradiction -- as a disjunct of a goal as much as on its own, since a disjunction
     with the other sides ruled out is a proof of that disequality like any other. *)
      let* () =
        List.fold_left
          (fun acc (op, lhs, rhs) ->
            let* () = acc in
            if op = `Neq && (not allow_neq) && not (is_literal lhs && is_literal rhs) then
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
            else Error (Code.Oracle_failed (Zero_denominator (Printable.PVal (ctx, src))))
        | Nonneg (base, src) :: rest ->
            if unsat ((`Lt, base, `Const Q.zero) :: facts) then discharge facts rest
            else Error (Code.Oracle_failed (Negative_base (Printable.PVal (ctx, src))))
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
              Error (Code.Oracle_failed err)
        (* What the base's sign gives the power.  A positive base makes every power of it positive;
           a base that is merely nonzero makes them nonzero, a negative power being a reciprocal;
           and a nonnegative base makes a *natural* power nonnegative, 0^a being 0 or 1.  Nothing
           is required of the hypotheses here -- a power of a base whose sign they leave open just
           gets no such fact -- so these only ever add to what we know.  A literal base answers for
           itself, which saves asking Z3 about the likes of 2^n at all. *)
        | Positive { base; power = p; nat; nonneg } :: rest ->
            let ispos = (`Lt, `Const Q.zero, p) and isnonneg = (`Le, `Const Q.zero, p) in
            let isnonzero = (`Neq, p, `Const Q.zero) in
            let facts =
              match rational_of base with
              | Some q ->
                  if Q.gt q Q.zero then ispos :: facts
                  else if Q.lt q Q.zero then isnonzero :: facts
                  else if nat && not nonneg then isnonneg :: facts
                  else facts
              | None ->
                  if unsat ((`Le, base, `Const Q.zero) :: facts) then ispos :: facts
                  else
                    let facts =
                      if unsat ((`Eq, base, `Const Q.zero) :: facts) then isnonzero :: facts
                      else facts in
                    if nat && (not nonneg) && unsat ((`Lt, base, `Const Q.zero) :: facts) then
                      isnonneg :: facts
                    else facts in
            discharge facts rest in
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
            (Ok ()) goals)
