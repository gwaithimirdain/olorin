open Bwd
open Util
open Dim
open Core
open Value
open Reporter
open Parser

module type Int = sig
  val dim : int
end

module Poly (Dim : Int) : sig
  type t

  val add : t -> t -> t
  val neg : t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val var : int -> t
  val scal : Q.t -> t -> t
  val zero : t
  val one : t
  val const : Q.t -> t
  val is_zero : t -> bool

  type ideal

  val ideal : t list -> ideal
  val reduce : ideal -> t -> t
  val contains : ideal -> t -> bool

  type symbolic =
    [ `Plus of symbolic * symbolic
    | `Minus of symbolic * symbolic
    | `Times of symbolic * symbolic
    | `Neg of symbolic
    | `Var of int
    | `Const of Q.t ]

  val of_symbolic : symbolic -> t
end = struct
  let rec nat_of_int x = if x <= 0 then Sin_num.O else Sin_num.S (nat_of_int (x - 1))

  let rec to_list = function
    | Sin_num.Nil -> []
    | Sin_num.Cons (x, y) -> x :: to_list y

  let of_list ps = List.fold_right (fun x y -> Sin_num.Cons (x, y)) ps Sin_num.Nil
  let dim = nat_of_int Dim.dim
  let order () = Sin_num.total_orderc_dec dim
  let div1 x y _ = Q.div x y
  let eqd x y = if Q.equal x y then Sin_num.Left else Right

  type t = Q.t Sin_num.poly

  let add (p : t) (q : t) : t = Sin_num.pluspf Q.zero Q.add eqd dim (order ()) p q

  let sub (p : t) (q : t) : t =
    Sin_num.minuspf Q.zero Q.one Q.neg Q.sub Q.mul eqd dim (order ()) p q

  let mul (p : t) (q : t) : t =
    Sin_num.smult Q.zero Q.one Q.add Q.neg Q.sub Q.mul div1 eqd dim (order ()) p q

  let var (i : int) : t = Sin_num.sgen Q.zero Q.one Q.add Q.neg Q.sub Q.mul div1 dim (nat_of_int i)

  let scal (a : Q.t) (p : t) : t =
    Sin_num.sscal Q.zero Q.one Q.add Q.neg Q.sub Q.mul div1 eqd dim a p

  let neg (p : t) : t = scal Q.minus_one p
  let zero : t = Sin_num.spO Q.zero dim
  let one : t = Sin_num.sp1 Q.zero Q.one Q.add Q.neg Q.sub Q.mul div1 dim
  let const (a : Q.t) = scal a one
  let is_zero (p : t) : bool = Sin_num.zerop_dec Q.zero dim p = Left

  type ideal = t Sin_num.list

  let ideal (polys : t list) : ideal =
    Sin_num.redbuch Q.zero Q.one Q.add Q.neg Q.sub Q.mul div1 eqd dim (order ()) (of_list polys)

  let reduce (basis : ideal) (p : t) : t =
    Sin_num.reducef Q.zero Q.one Q.add Q.neg Q.sub Q.mul div1 eqd dim (order ()) basis p

  let contains (basis : ideal) (p : t) : bool = is_zero (reduce basis p)

  type symbolic =
    [ `Plus of symbolic * symbolic
    | `Minus of symbolic * symbolic
    | `Times of symbolic * symbolic
    | `Neg of symbolic
    | `Var of int
    | `Const of Q.t ]

  let rec of_symbolic = function
    | `Plus (p, q) -> add (of_symbolic p) (of_symbolic q)
    | `Minus (p, q) -> sub (of_symbolic p) (of_symbolic q)
    | `Times (p, q) -> mul (of_symbolic p) (of_symbolic q)
    | `Neg p -> neg (of_symbolic p)
    | `Var i -> var i
    | `Const n -> const n
end

let rec print_symbolic = function
  | `Plus (p, q) -> "Plus(" ^ print_symbolic p ^ ", " ^ print_symbolic q ^ ")"
  | `Minus (p, q) -> "Minus(" ^ print_symbolic p ^ ", " ^ print_symbolic q ^ ")"
  | `Times (p, q) -> "Times(" ^ print_symbolic p ^ ", " ^ print_symbolic q ^ ")"
  | `Neg p -> "Negate(" ^ print_symbolic p ^ ")"
  | `Var i -> "Var(" ^ string_of_int i ^ ")"
  | `Const n -> "Const(" ^ Q.to_string n ^ ")"

module E = Monad.Error (struct
  type t = Code.t
end)

let get_equality ctx tm =
  let open Monad.Ops (E) in
  let eq = Scope.lookup [ "eq" ] in
  match Norm.view_term tm with
  | Uninst
      ( Neu
          {
            head = Const { name; ins };
            args =
              Snoc
                ( Snoc (Snoc (Emp, App (Arg ty, tyins)), App (Arg lhs, lhsins)),
                  App (Arg rhs, rhsins) );
            _;
          },
        _ )
    when Some name = eq
         && Option.is_some (is_id_ins ins)
         && Option.is_some (is_id_ins tyins)
         && Option.is_some (is_id_ins lhsins)
         && Option.is_some (is_id_ins rhsins) ->
      return (CubeOf.find_top ty, CubeOf.find_top lhs, CubeOf.find_top rhs)
  | _ -> Error (Code.Oracle_failed ("not an equality", Printable.PVal (ctx, tm)))

let rec get_givens ctx (ty : normal) givens =
  let open Monad.Ops (E) in
  let cons_eqs = Scope.lookup [ "Cons_eqs" ] in
  let nil_eqs = Scope.lookup [ "Nil_eqs" ] in
  match Norm.view_term givens with
  | Uninst
      ( Neu
          {
            head = Const { name; ins };
            args =
              Snoc (Snoc (Snoc (Snoc (Emp, App (Arg eqty, eqtyins)), _), App (Arg rest, restins)), _);
            _;
          },
        _ )
    when Some name = cons_eqs
         && Option.is_some (is_id_ins ins)
         && Option.is_some (is_id_ins eqtyins)
         && Option.is_some (is_id_ins restins) -> (
      let veqty = (CubeOf.find_top eqty).tm in
      let* ty', x, y = get_equality ctx veqty in
      match Equal.equal_at (Ctx.length ctx) ty.tm ty'.tm ty.ty with
      | Some () ->
          let* rest = get_givens ctx ty (CubeOf.find_top rest).tm in
          return ((x, y) :: rest)
      | None ->
          Error
            (Oracle_failed
               ( "input is not an equation at the same type",
                 Printable.PNormal (ctx, CubeOf.find_top eqty) )))
  | Uninst (Neu { head = Const { name; ins }; args = Emp; _ }, _)
    when Some name = nil_eqs && Option.is_some (is_id_ins ins) -> return []
  | _ -> Error (Code.Oracle_failed ("not a Cons_eqs or Nil_eqs", Printable.PVal (ctx, givens)))

let rec get_posint tm =
  match Norm.view_term tm with
  | Constr (name, dim, []) when name = Constr.intern "zero" -> (
      match D.compare_zero dim with
      | Zero -> Some 0
      | Pos _ -> None)
  | Constr (name, dim, [ arg ]) when name = Constr.intern "suc" -> (
      match D.compare_zero dim with
      | Zero -> Option.map (fun n -> n + 1) (get_posint (CubeOf.find_top arg))
      | Pos _ -> None)
  | _ -> None

let rec pow p n = if n <= 0 then `Const Q.one else `Times (pow p (n - 1), p)

module S = Monad.State (struct
  type t = kinetic value Bwd.t * int
end)

let var_or_const ctx ty tm =
  let open Monad.Ops (S) in
  match get_posint tm with
  | Some i -> return (`Const (Q.of_int i))
  | None -> (
      let* vars, count = S.get in
      match Bwd.find_index (fun x -> Option.is_some (Equal.equal_at ctx tm x ty)) vars with
      | None ->
          let* () = S.put (Snoc (vars, tm), count + 1) in
          return (`Var count)
      | Some i -> return (`Var (count - i - 1)))

let get_poly (ctx : int) ty tm =
  let open Monad.Ops (S) in
  let rec go tm =
    match Norm.view_term tm with
    (* Binary operation *)
    | Uninst
        ( Neu
            {
              head = Const { name; ins };
              args = Snoc (Snoc (Emp, App (Arg x, xins)), App (Arg y, yins));
              _;
            },
          _ )
      when Option.is_some (is_id_ins ins)
           && Option.is_some (is_id_ins xins)
           && Option.is_some (is_id_ins yins) -> (
        let* px = go (CubeOf.find_top x).tm in
        let* py = go (CubeOf.find_top y).tm in
        match Firstorder.get_root name with
        | "plus" -> return (`Plus (px, py))
        | "minus" -> return (`Minus (px, py))
        | "times" -> return (`Times (px, py))
        | "pow" -> (
            match get_posint (CubeOf.find_top y).tm with
            | Some e -> return (pow px e)
            | None -> var_or_const ctx ty tm)
        | _ -> var_or_const ctx ty tm)
    (* Unary operation *)
    | Uninst (Neu { head = Const { name; ins }; args = Snoc (Emp, App (Arg x, xins)); _ }, _)
      when Option.is_some (is_id_ins ins) && Option.is_some (is_id_ins xins) ->
        let* x = go (CubeOf.find_top x).tm in
        if Firstorder.get_root name = "negate" then return (`Neg x) else var_or_const ctx ty tm
    | _ -> var_or_const ctx ty tm in
  go tm

let ask (Ask (ctx, tm) : Check.OracleData.question) =
  let open Monad.Ops (E) in
  let* givens, goal =
    match Norm.view_term tm with
    | Uninst
        ( Neu
            {
              head = Const { name; ins };
              args = Snoc (Snoc (Snoc (Emp, App (Arg givens, givins)), _), App (Arg goal, appins));
              _;
            },
          _ )
      when Some name = Scope.lookup [ "oracle" ]
           && Option.is_some (is_id_ins ins)
           && Option.is_some (is_id_ins givins)
           && Option.is_some (is_id_ins appins) ->
        return (CubeOf.find_top givens, CubeOf.find_top goal)
    | _ -> Error (Code.Oracle_failed ("not an oracle application", Printable.PVal (ctx, tm))) in
  let* ty, lhs, rhs = get_equality ctx goal.tm in
  let* givens = get_givens ctx ty givens.tm in
  let ctx, ty = (Ctx.length ctx, ty.tm) in
  let (givens, lhs, rhs), (_, count) =
    (let open Monad.Ops (S) in
     let* lhs = get_poly ctx ty lhs.tm in
     let* rhs = get_poly ctx ty rhs.tm in
     let open Mlist.Monadic (S) in
     let* givens =
       mmapM
         (fun [ ((x : normal), (y : normal)) ] ->
           let* x = get_poly ctx ty x.tm in
           let* y = get_poly ctx ty y.tm in
           return (x, y))
         [ givens ] in
     return (givens, lhs, rhs))
      (Emp, 0) in
  let module P = Poly (struct
    let dim = count
  end) in
  let ideal = P.ideal (List.map (fun (x, y) -> P.sub (P.of_symbolic x) (P.of_symbolic y)) givens) in
  if P.contains ideal (P.sub (P.of_symbolic lhs) (P.of_symbolic rhs)) then return ()
  else Error (Oracle_failed ("can't prove equality", PUnit))
