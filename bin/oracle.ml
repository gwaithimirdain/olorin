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
        else if Some name = lt then return `Lt
        else if Some name = le then return `Le
        else Error (Code.Oracle_failed ("not an equality or inequality", Printable.PVal (ctx, tm)))
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
  | _ -> Error (Code.Oracle_failed ("not an equality or inequality", Printable.PVal (ctx, tm)))

let rec get_givens ctx (ty : normal) givens =
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
         && Option.is_some (is_id_ins restins) -> (
      let veqty = (CubeOf.find_top eqty).tm in
      let* op, ty', x, y = get_equality_or_inequality ctx veqty in
      match subtype_of ctx ty'.tm ty.tm with
      | Some () ->
          let* rest = get_givens ctx ty (CubeOf.find_top rest).tm in
          return ((op, x, y) :: rest)
      | None ->
          Error
            (Oracle_failed
               ( "input is not an equation or inequality at the same type",
                 Printable.PNormal (ctx, CubeOf.find_top eqty) )))
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
        | "pow" -> (
            match get_posint (CubeOf.find_top y).tm with
            | Some e -> return (pow px e)
            | None -> var_or_const ctx ty tm)
        | _ -> var_or_const ctx ty tm)
    (* Unary operation *)
    | Neu { head = Const { name; ins }; args = Arg (Emp, x, xins); _ }
      when Option.is_some (is_id_ins ins) && Option.is_some (is_id_ins xins) -> (
        let* x = go (CubeOf.find_top x).tm in
        match Firstorder.get_root name with
        | "negate" -> return (`Neg x)
        | "square" -> return (`Times (x, x))
        | "cube" -> return (`Times (`Times (x, x), x))
        | "fourth" -> return (`Times (`Times (x, x), `Times (x, x)))
        | _ -> var_or_const ctx ty tm)
    (* Fraction with positive integer denominator *)
    | Constr (constr, dim, [ num; den ]) when constr = Constr.intern "quot" -> (
        match D.compare_zero dim with
        | Zero -> (
            let* num = go (CubeOf.find_top num) in
            match get_posint (CubeOf.find_top den) with
            | Some n -> return (`Times (`Const (Q.make Z.one (Z.of_int n)), num))
            | None -> var_or_const ctx ty tm)
        | Pos _ -> var_or_const ctx ty tm)
    | _ -> var_or_const ctx ty tm in
  go tm

let vars_of_ctx : type a b. (a, b) Ctx.t -> string Bwd.t = function
  | Permute (_, _, ctx) ->
      let rec vars_of_ctx : type a b. (a, b) Ctx.Ordered.t -> string Bwd.t = function
        | Emp -> Emp
        | Lock ctx -> vars_of_ctx ctx
        | Snoc (ctx, Invis _, _) -> vars_of_ctx ctx
        | Snoc (ctx, Vis { vars; _ }, _) -> (
            match NICubeOf.find_top vars with
            | Some x -> Snoc (vars_of_ctx ctx, x)
            | None -> vars_of_ctx ctx) in
      vars_of_ctx ctx

(* We memorize the results of calls to reduce, so we don't have to re-make them every time. *)
let answers : (Relation.t list, bool) Hashtbl.t = Hashtbl.create 20

let ask (Ask (ctx, tm) : Check.OracleData.question) =
  let open Monad.Ops (E) in
  let* givens, goal =
    match Norm.view_term tm with
    | Neu
        {
          head = Const { name; ins };
          args = Arg (Arg (Arg (Emp, givens, givins), _, _), goal, appins);
          _;
        }
      when Some name = Scope.lookup [ "oracle" ]
           && Option.is_some (is_id_ins ins)
           && Option.is_some (is_id_ins givins)
           && Option.is_some (is_id_ins appins) ->
        return (CubeOf.find_top givens, CubeOf.find_top goal)
    | _ -> Error (Code.Oracle_failed ("not an oracle application", Printable.PVal (ctx, tm))) in
  let* goal_op, ty, lhs, rhs = get_equality_or_inequality ctx goal.tm in
  let* givens = get_givens ctx ty givens.tm in
  (* The quantifier eliminator can prove disequalities, but we don't let it, since we want the student to prove those by contradiction. *)
  if goal_op = `Neq then
    Error (Code.Oracle_failed ("proving disequalities by algebra not allowed", PUnit))
  else
    (* Otherwise we call back to javascript for it to query z3. *)
    let ctx, ty = (Ctx.length ctx, ty.tm) in
    let (givens, lhs, rhs), (_vars, _count) =
      (let open Monad.Ops (S) in
       let* lhs = get_poly ctx ty lhs.tm in
       let* rhs = get_poly ctx ty rhs.tm in
       let open Mlist.Monadic (S) in
       let* givens =
         mmapM
           (fun [ (op, (x : normal), (y : normal)) ] ->
             let* x = get_poly ctx ty x.tm in
             let* y = get_poly ctx ty y.tm in
             return (op, x, y))
           [ givens ] in
       return (givens, lhs, rhs))
        (Emp, 0) in
    (* We negate the goal, since Z3 checks for satisfiability.  This involves negating the operator and also swapping the order of the arguments (although in the case of (dis)equalities swapping the arguments does nothing). *)
    let neg_goal_op =
      match goal_op with
      | `Eq -> `Neq
      | `Neq -> `Eq
      | `Lt -> `Le
      | `Le -> `Lt in
    let command = (neg_goal_op, rhs, lhs) :: givens in
    let result =
      match Hashtbl.find_opt answers command with
      | Some result -> result
      | None ->
          let result = Effect.perform (Callback.Callback command) in
          Hashtbl.add answers command result;
          result in
    if result then Ok () else Error (Code.Oracle_failed ("can't prove equality/inequality", PUnit))
