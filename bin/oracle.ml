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

  (* What Z3 made of a question: the relations can't all hold, they can, or it gave up before
     finding out -- because it ran out of time, or the player cancelled the check. *)
  type answer = Unsat | Sat | Unknown

  type _ Effect.t += Callback : Relation.t list -> answer Effect.t

  exception Halt

  let cont : (answer, js_checked Js.t) continuation option ref = ref None

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

(* The statement and the rest, out of a hypothesis list's two arguments. *)
let cons_args : type hmode any. (hmode, mode, any) apps -> (mode normal * mode normal) option =
 fun args ->
  match get_args args with
  | Some [ eqty; rest ] -> Some (eqty, rest)
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

(* Two translated expressions multiplied, with a unit on either side dropping out, so that a
   product built up a piece at a time comes out with nothing extra in it -- which is what makes the
   two sides of "x^(n+1) = x^n·x" the very same expression. *)
let mulby (x : Symbolic.t) (y : Symbolic.t) : Symbolic.t =
  match (x, y) with
  | `Const q, _ when Q.equal q Q.one -> y
  | _, `Const q when Q.equal q Q.one -> x
  | _ -> `Times (x, y)

let rec pow p n = if n <= 0 then `Const Q.one else mulby (pow p (n - 1)) p

(* Something already translated, multiplied by a base n times: x·b·b·…·b. *)
let rec mulpow (x : Symbolic.t) (base : Symbolic.t) (n : int) : Symbolic.t =
  if n <= 0 then x else mulpow (mulby x base) base (n - 1)

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
  (* What a tower of powers comes to where its base is positive: (u^e)^M is u^(e·M) for every real
     e and M when u > 0, whether or not either of them is a whole number.  Like Positive this asks
     nothing -- the hypotheses either make the base positive, and the equation is there to be used,
     or they don't and it isn't. *)
  | Tower of { bases : Symbolic.t list; written : Symbolic.t; product : Symbolic.t }
  (* What a power comes to where a hypothesis says outright what its exponent is: b^c is c copies
     of b.  Congruence gets this too wherever the problem writes that power of that base down
     somewhere (see anchor_base), but not where it never writes one -- "n=2 ⊢ x^n = x·x" has no
     literal power in it at all -- and reading an equation off the facts costs nothing.  Like
     Positive this asks nothing of the hypotheses: an exponent they leave open gets no such fact. *)
  | Degenerate of { base : Symbolic.t; power : Symbolic.t; exponent : Symbolic.t }

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
   lets a power be taken apart (see poly_form). *)
let is_number_type sys ty =
  match Norm.view_term ty with
  | Neu { head = Const { name; ins }; args; _ } ->
      Option.is_some (is_id_ins ins) && get_args args = Some [] && Some name = Scope.lookup [ sys ]
  | _ -> false

let is_natural ty = is_number_type "ℕ" ty
let is_integer ty = is_number_type "ℤ" ty

(* How big a polynomial an exponent would build: past this we give up and leave the power opaque,
   as a written-out exponent that size already is. *)
let degree (monomials, off) =
  List.fold_left (fun s (_, c) -> Q.add s (Q.abs c)) (Q.abs off) monomials

(* An exponent in polynomial form: the monomials it is made of, each a list of terms multiplied
   together with a rational coefficient, and a rational offset -- the exponents being a module over
   ℚ, where clearing a denominator is taking that root of the base (see power_of).  "n+1" is [n]
   with coefficient 1 and offset 1; "2·n−m" is [n] with 2 and [m] with −1; "n/2" is [n] with 1/2;
   and "(m+1)·(n+1)" multiplies out to [m;n], [m] and [n] with offset 1, which is what makes it the
   same exponent as "m·n+m+n+1".  Only numerals fold into the coefficients and the offset, those
   being what the translation can turn back into a product of powers; anything else stays a term
   inside a monomial.  Nothing compares
   the terms here -- deciding when two of them are the same is the translation's business, and it
   has already been settled there (see var_for) -- so "n+n" comes back as n twice over.

   Multiplying out is what costs something, so a product that would make too many monomials, or
   too big a one, is left a term of its own instead: that only ever means less is taken apart. *)
let max_terms = 32

(* How many terms a product multiplies together, and every such count in an expression.  This is
   what says which exponents an uninterpreted power is worth saying its own value at: b^c can only
   ever meet something of degree c, and a product of c terms is what that looks like, so a problem
   that never multiplies more than two together can do nothing with b^3.  Saying it at every
   exponent up to the longest product instead would be worse than useless -- the ones in between
   meet nothing, and each is a polynomial equation of its own degree for Z3 to carry. *)
let rec product_length : Symbolic.t -> int = function
  | `Times (x, y) -> product_length x + product_length y
  | _ -> 1

let rec product_lengths (t : Symbolic.t) : int list =
  let sub = List.concat_map product_lengths in
  match t with
  | `Times (x, y) -> product_length t :: sub [ x; y ]
  | `Plus (x, y) | `Minus (x, y) | `Div (x, y) | `Min (x, y) | `Max (x, y) -> sub [ x; y ]
  | `Neg x | `Abs x -> sub [ x ]
  | `App (_, args) -> sub args
  | `Var _ | `Const _ -> []

let poly_scale c (ms, k) = (List.map (fun (m, d) -> (m, Q.mul c d)) ms, Q.mul c k)
let poly_add (ms1, k1) (ms2, k2) = (ms1 @ ms2, Q.add k1 k2)

let poly_mul (ms1, k1) (ms2, k2) =
  let cross = List.concat_map (fun (a, c) -> List.map (fun (b, d) -> (a @ b, Q.mul c d)) ms2) ms1 in
  let left = if Q.equal k2 Q.zero then [] else List.map (fun (a, c) -> (a, Q.mul c k2)) ms1 in
  let right = if Q.equal k1 Q.zero then [] else List.map (fun (b, d) -> (b, Q.mul d k1)) ms2 in
  (cross @ left @ right, Q.mul k1 k2)

let poly_ok (ms, k) = List.length ms <= max_terms && Q.leq (degree (ms, k)) (Q.of_int max_exponent)

let rec poly_form tm =
  let atom = ([ ([ tm ], Q.one) ], Q.zero) in
  let scale = poly_scale and add = poly_add and mul = poly_mul and ok = poly_ok in
  (* Stopping as soon as it is too big, rather than at the end, so that multiplying a big one out
     four times over doesn't build what it is about to throw away. *)
  let rec repeat a n =
    if n <= 0 then ([], Q.one)
    else
      let r = repeat a (n - 1) in
      if ok r then mul r a else r in
  match get_posint tm with
  | Some k -> ([], Q.of_int k)
  | None -> (
      let unary f x =
        let r = f (poly_form x) in
        if ok r then r else atom in
      let binary f x y =
        let r = f (poly_form x) (poly_form y) in
        if ok r then r else atom in
      match Norm.view_term tm with
      | Neu { head = Const { name; ins }; args; _ } when Option.is_some (is_id_ins ins) -> (
          match (Firstorder.get_root name, get_args args) with
          | "plus", Some [ x; y ] -> binary add x.tm y.tm
          | "minus", Some [ x; y ] -> binary (fun a b -> add a (scale Q.minus_one b)) x.tm y.tm
          | "times", Some [ x; y ] -> binary mul x.tm y.tm
          | "negate", Some [ x ] -> unary (scale Q.minus_one) x.tm
          (* Division by a numeral is a coefficient like any other, the exponents being a module
             over ℚ and not just over ℤ: "n/2" is n with a coefficient of 1/2, which a power reads
             as a root of its base (see power_of). *)
          | "divide", Some [ x; y ] -> (
              match get_posint y.tm with
              | Some k when k <> 0 -> unary (scale (Q.of_ints 1 k)) x.tm
              | _ -> atom)
          (* A small power in the exponent multiplies out like the product it is: "(m+1)²" has to
             be the same exponent as "(m+1)·(m+1)", and so as "m·m+2·m+1". *)
          | "square", Some [ x ] -> unary (fun a -> repeat a 2) x.tm
          | "cube", Some [ x ] -> unary (fun a -> repeat a 3) x.tm
          | "fourth", Some [ x ] -> unary (fun a -> repeat a 4) x.tm
          | "pow", Some [ x; y ] -> (
              match get_posint y.tm with
              | Some k when k <= 4 -> unary (fun a -> repeat a k) x.tm
              | _ -> atom)
          | _ -> atom)
      (* A successor, which is that number plus one (as 'go' also reads it).  A match on a natural
         refines an exponent written "n" to the constructor "suc m", and it has to normalize to the
         same m+1 that writing "m+1" there would, or 2^(m+1) would be a power of an exponent with
         nothing to do with the m in 2^m. *)
      | Constr (name, dim, [ arg ]) when name = Constr.intern "suc" -> (
          match (D.compare_zero dim, get_constr_arg arg) with
          | Zero, Some a -> unary (fun p -> add p ([], Q.one)) a
          | _ -> atom)
      | _ -> atom)

(* How a base is built up multiplicatively, which is what says how a power of it comes apart (see
   factor_base).  The named small powers are powers like any other here, so that "(x²)^n" is the
   tower "(x^2)^n". *)
let base_shape tm =
  match Norm.view_term tm with
  | Neu { head = Const { name; ins }; args; _ } when Option.is_some (is_id_ins ins) -> (
      match (Firstorder.get_root name, get_args args) with
      | "times", Some [ x; y ] -> `Product (x.tm, y.tm)
      | "divide", Some [ x; y ] -> `Quotient (x.tm, y.tm)
      | "pow", Some [ x; y ] -> `Power (x.tm, poly_form y.tm)
      | "square", Some [ x ] -> `Power (x.tm, ([], Q.of_int 2))
      | "cube", Some [ x ] -> `Power (x.tm, ([], Q.of_int 3))
      | "fourth", Some [ x ] -> `Power (x.tm, ([], Q.of_int 4))
      | _ -> `Irreducible)
  | _ -> `Irreducible

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
  (* And the powers we've already said what the product they came apart into is (see 'stated'),
     so that too is said once. *)
  powers : Symbolic.t Bwd.t;
  (* Likewise the powers of a root we've tied back to powers of what it is a root of. *)
  ties : Symbolic.t Bwd.t;
  (* The bases we've taken an uninterpreted power of, and the literal powers we've folded into
     products, each with what it folded to.  Where a base has both, the symbol is said to agree
     with the product at that exponent, which is what lets congruence carry a settled exponent
     across (see anchor). *)
  powbases : Symbolic.t Bwd.t;
  litpows : (Symbolic.t * int * Symbolic.t) Bwd.t;
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
        S.put { st with vars = Snoc (vars, Term { tm; ty = Lazy.from_val ty }); count = count + 1 }
      in
      return (`Var count, true)
  | Some i -> return (`Var (count - i - 1), false)

(* What a variable was made to stand for, if it was made for a root.  Powers of a root are tied
   back to powers of what it is a root of (see root_tie), which is what this is for. *)
let root_of vars = function
  | `Var i -> (
      match List.nth_opt (Bwd.to_list vars) i with
      | Some (Root (b, e)) -> Some (b, e)
      | _ -> None)
  | _ -> None

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
      if n >= 0 then anchor_literal base n (pow base n)
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
  (* The factors of one monomial, translated.  A factor that comes out a constant multiplies into
     the coefficient instead, whatever its type -- the 1/2 in "x^(n+1/2)" is a constant like any
     other -- and only a factor that stays a factor has to be a whole number.  One that needn't be
     stops all of this: b^(a+c) = b^a·b^c is false for a fractional a and a negative b, there
     being no real b^a to speak of there.  A monomial is a natural when every factor of it is, a
     product of naturals being one. *)
  and factors ty syms q nat = function
    | [] -> return (Some (List.rev syms, q, nat))
    | t :: ts -> (
        let* a = go ty t in
        match rational_of a with
        | Some r -> factors ty syms (Q.mul q r) nat ts
        | None -> (
            match exponent_kind t with
            | None -> return None
            | Some n -> factors ty (a :: syms) q (nat && n) ts))
  (* Whether an exponent is a whole number whatever its terms turn out to be -- every monomial of
     it with a whole coefficient and whole factors -- and if so whether it is a natural, which it
     is when nothing in it can be negative.  This is what factor_base asks of the exponent it
     distributes over. *)
  and whole_poly ty (ms, k) =
    if not (Z.equal (Q.den k) Z.one) then return None
    else
      let rec walk nat = function
        | [] -> return (Some nat)
        | (m, c) :: rest -> (
            let* f = factors ty [] c true m in
            match f with
            | None -> return None
            | Some (syms, q, mnat) ->
                if not (Z.equal (Q.den q) Z.one) then return None
                else walk (nat && Q.geq q Q.zero && (syms = [] || mnat)) rest) in
      walk (Q.geq k Q.zero) ms
  (* The monomials of an exponent, with the ones that agree merged: they are compared as translated
     expressions rather than as terms, which is where two ways of writing the same thing have
     already been made one, so "x^(n+n)" is x^n·x^n either way it was written.  A monomial whose
     factors all fold away is a constant, and folds into the offset. *)
  and collect ty acc k = function
    | [] -> return (Some (acc, k))
    | (m, c) :: rest -> (
        let* f = factors ty [] c true m in
        match f with
        | None -> return None
        | Some ([], q, _) -> collect ty acc (Q.add k q) rest
        | Some (syms, q, nat) ->
            (* The coefficient stays a rational.  One that isn't whole is a root of the base rather
               than a power of it -- x^(n/2) is (x^(1/2))^n -- which is a denominator to be cleared
               rather than anything to refuse (see power_of). *)
            if not (Z.fits_int (Q.num q) && Z.fits_int (Q.den q)) then return None
            else
              let a =
                match syms with
                | [] -> assert false
                | first :: rest -> List.fold_left (fun acc x -> `Times (acc, x)) first rest in
              let acc =
                if List.exists (fun (b, _, _) -> b = a) acc then
                  List.map
                    (fun (b, d, m) -> if b = a then (b, Q.add d q, m || nat) else (b, d, m))
                    acc
                else acc @ [ (a, q, nat) ] in
              collect ty acc k rest)
  (* A base we've taken an uninterpreted power of, and a literal power as it is folded into a
     product: both are noted here and said about once the whole problem has been translated, since
     how far it is worth saying anything is a question about the problem as a whole (see
     anchors). *)
  and anchor_base base =
    let* st = S.get in
    if Bwd.exists (fun b -> b = base) st.powbases then return ()
    else S.put { st with powbases = Snoc (st.powbases, base) }
  and anchor_literal base c v =
    let* st = S.get in
    if c < 0 || c > max_exponent || Bwd.exists (fun (b, d, _) -> b = base && d = c) st.litpows then
      return v
    else
      let* () = S.put { st with litpows = Snoc (st.litpows, (base, c, v)) } in
      return v
  (* A power of a root, tied back to the power of what it is a root of: s being b^(p/q), s^a raised
     to the q is b^(p·a).  Without it a root's powers and the base's own would be unrelated symbols,
     and x^(n/2)·x^(n/2) would not be the x^n it plainly is.  It needs nothing of b that the root
     itself didn't, an exponent that is a natural and a root that is a positive power of b being
     the case it is stated in. *)
  and root_tie power a nat =
    let* st = S.get in
    match Option.bind (root_base_of power) (root_of st.vars) with
    | Some (b, e)
      when nat
           && (not (Bwd.exists (fun x -> x = power) st.ties))
           && Z.fits_int (Q.num e)
           && Z.fits_int (Q.den e)
           && Z.gt (Q.num e) Z.zero
           && Z.leq (Q.num e) (Z.of_int max_exponent)
           && Z.leq (Q.den e) (Z.of_int max_exponent) ->
        let* () = S.put { st with ties = Snoc (st.ties, power) } in
        let* f = fun_for `Pow 2 in
        let bp : Symbolic.t = `App (f, [ b; a ]) in
        add_step (Define [ (`Eq, pow power (Z.to_int (Q.den e)), pow bp (Z.to_int (Q.num e))) ])
    | _ -> return ()
  (* A power of an absolute value, said to be the absolute value of the power: ∣u∣^a is ∣u^a∣ for
     a whole a, without which ∣x∣^(2·n) and (x²)^n would be unrelated symbols.  Said once for each
     such power, and for a natural exponent, where it needs nothing of u. *)
  and abs_tie power a nat =
    let* st = S.get in
    match power with
    | `App (f, [ `Abs b; _ ]) when nat && not (Bwd.exists (fun x -> x = power) st.ties) ->
        let* () = S.put { st with ties = Snoc (st.ties, power) } in
        add_step (Define [ (`Eq, power, `Abs (`App (f, [ b; a ]))) ])
    | _ -> return ()
  (* The base a power was taken of, which is where a root would be. *)
  and root_base_of = function
    | `App (_, [ b; _ ]) -> Some b
    | _ -> None
  (* The powers one monomial each, multiplied together, with what is known about each of them said
     beside it.  Nothing is required of anything here: the obligations that go with a negative
     coefficient or a fractional offset belong to the caller, which knows whether they are called
     for.  A power of a root and a power of an absolute value each get their one fact, and those
     two cases can't both be a given power's, so one list of powers already said about does for
     both of them. *)
  and build_powers tmty base acc = function
    | [] -> return acc
    (* One to any power is one, which no uninterpreted symbol would say. *)
    | _ :: rest
      when match base with
           | `Const q -> Q.equal q Q.one
           | _ -> false -> build_powers tmty base acc rest
    | (a, c, nat) :: rest ->
        let* f = fun_for `Pow 2 in
        let p : Symbolic.t = `App (f, [ base; a ]) in
        (* b^a lands in ℕ exactly when the whole power does: ℕ.pow is the only power landing there,
           and it takes naturals for both of its arguments. *)
        let nonneg = nat && is_natural (Lazy.force tmty) in
        let* p = if nat then natural (Lazy.force tmty) p else return p in
        let* () = sign base p a nat nonneg in
        let* () = anchor_base base in
        let* () = root_tie p a nat in
        let* () = abs_tie p a nat in
        let acc = if c > 0 then mulpow acc p c else `Div (acc, pow p (-c)) in
        build_powers tmty base acc rest
  (* Whether an exponent is an even whole number whatever its terms turn out to be, which is what
     makes a power of it nonnegative: u^(2·k) is ∣u∣^(2·k).  Its terms have to be whole for the
     coefficients to say anything, which is what 'factors' failing reports. *)
  and even_poly ty (ms, k) =
    let even z = Z.equal (Q.den z) Z.one && Z.equal (Z.erem (Q.num z) (Z.of_int 2)) Z.zero in
    if not (even k) then return false
    else
      let rec walk = function
        | [] -> return true
        | (m, c) :: rest -> (
            let* f = factors ty [] c true m in
            match f with
            | None -> return false
            | Some (_, q, _) -> if even q then walk rest else return false) in
      walk ms
  (* The factors a base really is a product of, each with the exponent it carries, when a power of
     it is taken apart.  (u·v)^E is u^E·v^E, (u/v)^E is u^E·v^(−E), and (u^f)^E is u^(f·E); a base
     that is none of those is itself, raised to E.  So a power is a product of powers of the terms
     at the bottom of it, with the exponents multiplied out along the way -- which is the whole of
     what the laws of exponents say, once the exponents are read as the ℚ-module elements they are.

     Every step of it needs the exponent it distributes over to be a whole number: (u·v)^(1/2) is
     not u^(1/2)·v^(1/2) for two negative factors, any more than (u^2)^(1/2) is u.  A step whose
     exponent isn't whole simply isn't taken -- the base it was going to come apart stays a base of
     its own -- so that the steps above and below it still are.  Where the exponents are whole but
     can go negative, the bases they divide by have to be nonzero, which is what 'true' asks for;
     a natural exponent asks nothing.  A positive base would do instead of any of this, but whether
     the hypotheses make it positive isn't known here, so that is left to a fact conditional on it
     (see factor_all and tower).

     A denominator is nonzero whatever the exponent does, as it had to be when it was written as a
     division, so those come back separately to be asked for on their own rather than through the
     exponent.  'cut' says whether any step was left untaken, which is what there is a conditional
     fact to state about. *)
  and factor_base ty basetm p =
    let leaf cut =
      let* b = go ty basetm in
      return ([ (b, basetm, p) ], [], false, cut) in
    match base_shape basetm with
    | `Irreducible -> leaf false
    | `Power (u, inner) -> (
        let q = poly_mul inner p in
        if not (poly_ok q) then leaf true
        else
          (* Both exponents have to be whole, and not merely the product of the two: (u²)^(n+1/2)
             is u^(2·n)·∣u∣, which is not u^(2·n+1) for a negative u, though 2 and n+1/2 multiply
             out to a whole number between them. *)
          let* outer = whole_poly ty p in
          let* w = whole_poly ty inner in
          match (outer, w) with
          | Some _, Some nat ->
              let* fs, nz, nonzero, cut = factor_base ty u q in
              return (fs, nz, nonzero || not nat, cut)
          | _ ->
              (* An even inner exponent asks nothing of the base at all: u^(2·k) is ∣u∣^(2·k), and
                 ∣u∣ is nonnegative whatever u is, so the exponents multiply out over it where
                 they would not over u.  That is what makes (x^6)^(n+1/2) the ∣x∣^(6·n+3) it is
                 for every x, rather than the x^(6·n+3) it is only for a positive one. *)
              let* ev = even_poly ty inner in
              if not ev then leaf true
              else
                let* b = go ty u in
                return ([ (`Abs b, u, q) ], [], false, true))
    | `Product (u, v) -> (
        let* w = whole_poly ty p in
        match w with
        | None -> leaf true
        | Some nat ->
            let* fu, nzu, zu, cu = factor_base ty u p in
            let* fv, nzv, zv, cv = factor_base ty v p in
            return (fu @ fv, nzu @ nzv, (not nat) || zu || zv, cu || cv))
    | `Quotient (u, v) -> (
        let* w = whole_poly ty p in
        match w with
        | None -> leaf true
        | Some nat ->
            let* fu, nzu, zu, cu = factor_base ty u p in
            let* fv, nzv, zv, cv = factor_base ty v (poly_scale Q.minus_one p) in
            let* d = go ty v in
            return (fu @ fv, ((d, v) :: nzu) @ nzv, (not nat) || zu || zv, cu || cv))
  (* The same, with every step taken whether or not the exponent it distributes over is whole:
     what the power would come apart into if the terms at the bottom of it were positive, for which
     nothing but their positivity is needed.  Where that differs from what we could do outright it
     is a fact conditional on them (see tower). *)
  and factor_all ty basetm p =
    let leaf () =
      let* b = go ty basetm in
      return [ (b, basetm, p) ] in
    match base_shape basetm with
    | `Irreducible -> leaf ()
    | `Power (u, inner) ->
        let q = poly_mul inner p in
        if not (poly_ok q) then leaf () else factor_all ty u q
    | `Product (u, v) ->
        let* fu = factor_all ty u p in
        let* fv = factor_all ty v p in
        return (fu @ fv)
    | `Quotient (u, v) ->
        let* fu = factor_all ty u p in
        let* fv = factor_all ty v (poly_scale Q.minus_one p) in
        return (fu @ fv)
  (* What a collected exponent comes to once its coefficients are made whole: the denominator they
     have in common, the terms with their coefficients multiplied by it, and what is left of the
     offset.  x^(n/2) is (x^(1/2))^n, so clearing the denominator is taking the root of the base --
     which is the ℚ-module's own way of saying it, and needs no more of the base than writing that
     root would.  The offset is not cleared along with them: a fractional one is a root of the base
     in its own right (see ratpow), and leaving it be keeps x^(n+1/2) the x^n·√x it has always
     been rather than an (√x)^(2·n)·√x that nothing would recognize. *)
  and cleared atoms k =
    let den (_, c, _) = Q.den c in
    let d = List.fold_left (fun acc a -> Z.lcm acc (den a)) Z.one atoms in
    if not (Z.fits_int d && Z.leq d (Z.of_int max_exponent)) then None
    else
      let d = Z.to_int d in
      let scale q = Q.mul q (Q.of_int d) in
      let fits (_, c, _) = Z.fits_int (Q.num (scale c)) in
      if not (List.for_all fits atoms) then None
      else
        let atoms = List.map (fun (a, c, nat) -> (a, Z.to_int (Q.num (scale c)), nat)) atoms in
        let k = scale k in
        let size = List.fold_left (fun s (_, c, _) -> s + abs c) 0 atoms in
        if (not (fits_exponent k)) || size + abs (Z.to_int (Q.num k)) > max_exponent then None
        else Some (d, atoms, k)
  (* Whether every factor's exponent is one that comes apart, which has to be settled before any of
     them is built: a factor that emitted an obligation and only then met one that can't be built
     would leave that obligation behind for a translation we didn't use. *)
  and all_buildable ty = function
    | [] -> return true
    | (_, _, (monomials, off)) :: rest -> (
        let* collected = collect ty [] off monomials in
        match collected with
        | None -> return false
        | Some (atoms, k) -> (
            let atoms = List.filter (fun (_, c, _) -> not (Q.equal c Q.zero)) atoms in
            match cleared atoms k with
            | None -> return false
            | Some _ -> all_buildable ty rest))
  (* One factor raised to its exponent: the product of powers that exponent comes apart into.
     Naturals with positive coefficients and a nonnegative offset ask nothing at all.  A term or a
     coefficient that can go negative makes the power a reciprocal and asks for a nonzero base, as
     does a base the exponent was taken off a power of with an exponent that could be negative (see
     factor_base); a fractional offset is a root of the base, and asks for whatever a written-out
     root of it would (see ratpow). *)
  and power_of ty tmty nonzero (base, src, (monomials, off)) =
    let* collected = collect ty [] off monomials in
    match collected with
    | None -> return None
    | Some (atoms, k) -> (
        match cleared (List.filter (fun (_, c, _) -> not (Q.equal c Q.zero)) atoms) k with
        | None -> return None
        | Some (d, atoms, k) -> (
            (* A common denominator in the coefficients is a root of the base: the base becomes
               that root, and the exponents become whole. *)
            let* base = if d = 1 then return base else ratpow base (Q.of_ints 1 d) src in
            match atoms with
            (* Coefficients can cancel, and every term can fold away, in which case the exponent
               was a literal after all -- "x^(1+2)", or "x^(n−n)". *)
            | [] ->
                let* r = ratpow base k src in
                return (Some r)
            | atoms ->
                let whole =
                  (not nonzero)
                  && Q.geq k Q.zero
                  && List.for_all (fun (_, c, nat) -> c > 0 && nat) atoms in
                let* () = if whole then return () else add_step (Nonzero (base, src)) in
                let* acc = build_powers tmty base (`Const Q.one) atoms in
                (* An integer offset is copies of the base multiplied in, which keeps the product
                   free of anything Z3 has to work out; a fractional one is a root of it. *)
                if Z.equal (Q.den k) Z.one then
                  let k = Z.to_int (Q.num k) in
                  return (Some (if k >= 0 then mulpow acc base k else `Div (acc, pow base (-k))))
                else
                  let* s = ratpow base k src in
                  return (Some (`Times (acc, s)))))
  (* All of them, multiplied together, or nothing where any one of them doesn't come apart. *)
  and build_factors ty tmty nonzero factors =
    let* ok = all_buildable ty factors in
    if not ok then return None
    else
      let rec build acc = function
        | [] -> return (Some acc)
        | f :: rest -> (
            let* r = power_of ty tmty nonzero f in
            match r with
            | None -> return None
            | Some v -> build (mulby acc v) rest) in
      build (`Const Q.one) factors
  (* What a power would come apart into if the terms at the bottom of it were positive, said as a
     fact conditional on that.  Whether the hypotheses make them positive isn't something we can
     ask here -- they have not been translated yet -- so rather than translating the power that way
     and finding out too late that we shouldn't have, we translate it as it stands and say, beside
     it, what it would have come to.  Nothing is refused that wasn't refused before, and where the
     hypotheses do force those terms positive the equation is there to be used.

     The product is built with no obligations of its own: a negative coefficient divides by a power
     of the base, which is sound whatever that comes to, and the equation only says anything at all
     where the base is positive, which is where those powers are what they should be.  A fractional
     offset is the exception, being a root that has to be *defined* -- and a definition that holds
     only where the base is positive is not one this can state -- so that one is left alone. *)
  and tower ty tmty factors written =
    let rec product acc = function
      | [] -> return acc
      | (base, _, (monomials, off)) :: rest ->
          let* collected = collect ty [] off monomials in
          let* piece =
            match collected with
            | Some (atoms, k)
              when Z.equal (Q.den k) Z.one
                   && Z.fits_int (Q.num k)
                   && List.for_all (fun (_, c, _) -> Z.equal (Q.den c) Z.one) atoms
                   && List.fold_left (fun s (_, c, _) -> s + abs (Z.to_int (Q.num c))) 0 atoms
                      + abs (Z.to_int (Q.num k))
                      <= max_exponent ->
                let atoms =
                  List.filter_map
                    (fun (a, c, nat) ->
                      if Q.equal c Q.zero then None else Some (a, Z.to_int (Q.num c), nat))
                    atoms in
                let k = Z.to_int (Q.num k) in
                let* acc = build_powers tmty base (`Const Q.one) atoms in
                return (if k >= 0 then mulpow acc base k else `Div (acc, pow base (-k)))
            (* An exponent the translation can't turn into a product of powers -- a rational one,
               say -- is still an exponent, and the law is still the law: the factor is that one
               power of the base, with the exponents multiplied out as the arithmetic they are. *)
            | _ ->
                let* e = poly_symbolic ty (monomials, off) in
                let* f = fun_for `Pow 2 in
                return (`App (f, [ base; e ])) in
          product (mulby acc piece) rest in
    let* p = product (`Const Q.one) factors in
    add_step (Tower { bases = List.map (fun (b, _, _) -> b) factors; written; product = p })
  (* An exponent in polynomial form, written out as the arithmetic it is.  Nothing in it has to be
     a whole number here: this is an exponent to hand to Z3 as the argument of a power, not one to
     take a power apart at. *)
  and poly_symbolic ty (ms, k) =
    let rec monomial acc = function
      | [] -> return acc
      | t :: ts ->
          let* a = go ty t in
          let acc : Symbolic.t =
            match acc with
            | `Const q when Q.equal q Q.one -> a
            | _ -> `Times (acc, a) in
          monomial acc ts in
    let rec walk acc = function
      | [] -> return acc
      | (m, c) :: rest ->
          let* p = monomial (`Const c) m in
          let acc : Symbolic.t =
            match acc with
            | `Const q when Q.equal q Q.zero -> p
            | _ -> `Plus (acc, p) in
          walk acc rest in
    walk (`Const k) ms
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
  and sign base p a nat nonneg =
    let* st = S.get in
    if Bwd.exists (fun x -> x = p) st.signs then return ()
    else
      let* () = S.put { st with signs = Snoc (st.signs, p) } in
      let* () = add_step (Positive { base; power = p; nat; nonneg }) in
      add_step (Degenerate { base; power = p; exponent = a })
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
        (* A power translates its exponent first, and its base only once it knows which base that
           is: a variable exponent may take the base's own exponents into itself (see factor_base),
           and translating a base we then drop would leave Z3 asked about a power that isn't
           there. *)
        | "pow" -> (
            let* py = go ty y.tm in
            match rational_of py with
            | Some e ->
                let* px = go ty x.tm in
                power ty tm px e x.tm
            (* A variable exponent comes apart into the terms making it up, and the base into the
               terms at the bottom of it, and the power is put back together as the product of one
               power of each.  How far that can go factor_base decides, having the translated terms
               to look at; all that's asked here is that they won't build a polynomial too big to
               be worth handing to Z3 at all. *)
            | None ->
                let p = poly_form y.tm in
                if not (poly_ok p) then opaque ty tm
                else
                  let* factors, nonzeros, nonzero, cut = factor_base ty x.tm p in
                  (* Whether the base came apart at all, which is what says the power we built is
                     the written power of the written base. *)
                  (* Whether the base came apart at all: where it didn't, the one factor's base is
                     the written one, already translated, and the power we build of it is the
                     written power. *)
                  let trivial =
                    match factors with
                    | [ (b, btm, _) ] when btm == x.tm -> Some b
                    | _ -> None in
                  let* built = build_factors ty tmty nonzero factors in
                  let* result =
                    match built with
                    | Some result ->
                        let rec denominators = function
                          | [] -> return ()
                          | (d, dtm) :: rest ->
                              let* () = add_step (Nonzero (d, dtm)) in
                              denominators rest in
                        let* () = denominators nonzeros in
                        (* The power as written, said to equal that product.  Coming apart at the
                           exponent is what proves the laws of exponents, but it also takes apart a
                           term that congruence would have matched against another way of writing
                           the same power -- x^((m+1)·(n+1)) against x^(m·n+m+n+1), whose exponents
                           Z3 can see are equal, one of which comes apart and the other of which
                           doesn't.  Keeping the written form and saying what it equals gives us
                           both. *)
                        let* () =
                          match trivial with
                          | None -> return ()
                          | Some b ->
                              let* f = fun_for `Pow 2 in
                              let plain : Symbolic.t = `App (f, [ b; py ]) in
                              if plain = result then return () else stated plain result in
                        return result
                    (* An exponent that doesn't come apart at all leaves the power the opaque term
                       it always was -- which is still something to say the rest about. *)
                    | None -> opaque ty tm in
                  (* And what it would have come apart into where the terms at the bottom of it are
                     positive, which is more than we could do outright wherever a step was left
                     untaken. *)
                  let* () =
                    if not cut then return ()
                    else
                      let* full = factor_all ty x.tm p in
                      tower ty tmty full result in
                  return result)
        | _ -> opaque ty tm)
    (* A successor.  This is the constructor a match on a natural refines to -- proof by cases
       gives a branch about "suc x" where the arithmetic says x+1 -- and it is that number, so we
       read it as that.  A numeral is folded to a constant by 'opaque' as it always was, and only
       reaches here with something other than a numeral inside it. *)
    | Constr (name, dim, [ arg ]) when name = Constr.intern "suc" && Option.is_none (get_posint tm)
      -> (
        match (D.compare_zero dim, get_constr_arg arg) with
        | Zero, Some a ->
            let* pa = go ty a in
            return (`Plus (pa, `Const Q.one))
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
        | "square" -> unary (fun x -> anchor_literal x 2 (`Times (x, x)))
        | "cube" -> unary (fun x -> anchor_literal x 3 (`Times (`Times (x, x), x)))
        | "fourth" -> unary (fun x -> anchor_literal x 4 (`Times (`Times (x, x), `Times (x, x))))
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

(* What the uninterpreted power symbol is, at the exponents worth saying it at.  b^c is c copies of
   b, which the symbol doesn't say for itself: a literal power is folded into a product as it is
   translated, so the symbol never appears at that exponent and congruence has no term to work
   with.  With these, an exponent the hypotheses settle carries across on its own -- from 2·n=4 Z3
   has n=2, and from n=2 congruence has b^n = b^2, which these say is b·b.

   Which exponents those are is the problem's own question: a power written as a power is said
   about exactly, wherever it is written, and otherwise the exponents are the lengths of the
   products the problem builds, those being the only things a power could meet.  0 and 1 are always
   among them, a power meeting a bare 1 or the base itself being no product at all.  Only for a
   base that has an uninterpreted power of it somewhere, since otherwise there is nothing for any
   of it to be about. *)
let anchors funs funcount powbases litpows relations =
  match Bwd.find_index (fun x -> x = (`Pow, 2)) funs with
  | None -> []
  | Some i ->
      let f = funcount - i - 1 in
      let lengths =
        List.sort_uniq compare
          (0
          :: 1
          :: List.concat_map
               (fun (_, lhs, rhs) -> product_lengths lhs @ product_lengths rhs)
               relations) in
      let lengths = List.filter (fun c -> c <= max_exponent) lengths in
      List.concat_map
        (fun b ->
          let at c : Symbolic.t = `App (f, [ b; `Const (Q.of_int c) ]) in
          List.map (fun c -> (`Eq, at c, pow b c)) lengths
          @ List.filter_map
              (fun (b', c, v) ->
                if b' = b && not (List.mem c lengths) then Some (`Eq, at c, v) else None)
              (Bwd.to_list litpows))
        (Bwd.to_list powbases)

(* We memorize the results of calls to reduce, so we don't have to re-make them every time. *)
let answers : (Relation.t list, bool) Hashtbl.t = Hashtbl.create 20

(* Z3 gave up on a question.  That settles nothing either way -- not even a side condition, whose
   failure would blame the player for a denominator or a base that may well be fine -- so it abandons
   the whole block, which ask reports as such. *)
exception Solver_gave_up

(* Ask Z3 whether a conjunction of relations is unsatisfiable, i.e. whether its negation is
   provable.  Each question is asked at most once, except one Z3 gave up on: that was a matter of
   time rather than of the question, so it's asked afresh the next time it comes up. *)
let unsat (command : Relation.t list) =
  match Hashtbl.find_opt answers command with
  | Some result -> result
  | None -> (
      match Effect.perform (Callback.Callback command) with
      | Unknown -> raise Solver_gave_up
      | (Unsat | Sat) as answer ->
          let result = answer = Unsat in
          Hashtbl.add answers command result;
          result)

let ask_solver (Ask (ctx, tm) : Check.OracleData.question) =
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
      let (givens, goals), { steps; funs; funcount; powbases; litpows; _ } =
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
            ties = Emp;
            powbases = Emp;
            litpows = Emp;
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
        (* What the tower of powers comes to, where the hypotheses make its base positive. *)
        | Tower { bases; written; product } :: rest ->
            let positive = List.for_all (fun b -> unsat ((`Le, b, `Const Q.zero) :: facts)) bases in
            let facts = if positive then (`Eq, written, product) :: facts else facts in
            discharge facts rest
        (* What the power is where a hypothesis says outright what its exponent is, which costs
           nothing to read off the facts.  An exponent settled any less directly than that is left
           to congruence, which has the symbol's value at every literal the problem writes to work
           with (see anchor_base) and gets there by itself. *)
        | Degenerate { base; power; exponent } :: rest ->
            let stated =
              List.find_map
                (fun (op, lhs, rhs) ->
                  if op <> `Eq then None
                  else if lhs = exponent then rational_of rhs
                  else if rhs = exponent then rational_of lhs
                  else None)
                facts in
            let facts =
              match stated with
              (* Only a nonnegative whole one: a negative or fractional exponent is a reciprocal or
                 a root, which is a definition to make rather than a fact to state, and there is no
                 making one here. *)
              | Some q
                when Z.equal (Q.den q) Z.one
                     && Z.geq (Q.num q) Z.zero
                     && Z.leq (Q.num q) (Z.of_int max_exponent) ->
                  (`Eq, power, pow base (Z.to_int (Q.num q))) :: facts
              | _ -> facts in
            discharge facts rest
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
      (* What the power symbol is at the exponents this problem makes it worth saying (see
         anchors), which is settled once the whole of it has been translated. *)
      let defined =
        List.filter_map
          (function
            | Define defs -> Some defs
            | _ -> None)
          (Bwd.to_list steps) in
      let anchors =
        anchors funs funcount powbases litpows (List.concat goals @ givens @ List.concat defined)
      in
      let* facts = discharge (anchors @ givens) (Bwd.to_list steps) in
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

let ask (question : Check.OracleData.question) =
  try ask_solver question with Solver_gave_up -> Error (Code.Oracle_failed Gave_up)
