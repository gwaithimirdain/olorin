open Bwd
open Util
open Core
open Reporter
open Parser
open Notation
open Postprocess
open Raw
open Print
open PPrint

let locate_opt = Asai.Range.locate_opt

open Js_of_ocaml
open Objects

let carp str = Js_of_ocaml.Console.console##log (Js.string str)

(* Olorin is designed to look to the user like first-order logic.  This file sets up the definitions and notations to maintain that illusion.  Here is Narya code that defines the basic operations of first-order logic, using untruncated propositions-as-types.  This will be the startup code.  We define implication, negation, and universal quantification to be records rather than simple function-types so that we can distinguish them (e.g. so that the prove-if-then rule can't also be used to prove-forall) and given them distinct notations.  *)

let startup =
  "def land (P Q : Type) : Type ≔ sig ( fst : P, snd : Q )
def lor (P Q : Type) : Type ≔ data [ left. (_ : P) | right. (_ : Q) ]
def imp (P Q : Type) : Type ≔ sig ( implies : P → Q )
def iff (P Q : Type) : Type ≔ sig ( ltor : P → Q, rtol : Q → P )
def ⊤ : Type ≔ sig ( )
def ⊥ : Type ≔ data [ ]
def neg (P : Type) : Type ≔ sig ( negation : P → ⊥ )
def contradict (P : Type) (p : P) (np : neg P) : ⊥ ≔ np .negation p
def forall (A : Type) (P : A → Type) : Type ≔ sig ( forall : (x : A) → P x )
def exists (A : Type) (P : A → Type) : Type ≔ data [ exists. (element : A) (property : P element) ]
def prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )
def coprod (A B : Type) : Type ≔ data [ left. (_:A) | right. (_:B) ]
axiom negneg (P : Type) : neg (neg P) → P

axiom eq (A : Type) (x y : A) : Type
def neq (A : Type) (x y : A) : Type ≔ neg (eq A x y)
axiom Nil_eqs : Type
axiom nil_eqs : Nil_eqs
axiom Cons_eqs (x_eq_y : Type) (_ : x_eq_y) (rest : Type) (_ : rest) : Type
axiom cons_eqs (x_eq_y : Type) (H : x_eq_y) (rest : Type) (r : rest) : Cons_eqs x_eq_y H rest r
axiom oracle (A : Type) (x : A) (C : Type) : C

axiom lt (A : Type) (x y : A) : Type
axiom le (A : Type) (x y : A) : Type
def gt (A : Type) (x y : A) : Type ≔ lt A y x
def ge (A : Type) (x y : A) : Type ≔ le A y x

def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]

def ℕ₊ : Type ≔ data [ one. | suc. (_:ℕ₊) ]

def ℤ : Type ≔ data [ zero. | suc. (_:ℤ) ]
axiom ℤ.plus : ℤ → ℤ → ℤ
axiom ℤ.minus : ℤ → ℤ → ℤ
axiom ℤ.times : ℤ → ℤ → ℤ
axiom ℤ.pow : ℤ → ℕ → ℤ
axiom ℤ.negate : ℤ → ℤ
axiom ℤ.square : ℤ → ℤ
axiom ℤ.cube : ℤ → ℤ
axiom ℤ.fourth : ℤ → ℤ

axiom ℤ.integral (x y : ℤ) : eq ℤ (ℤ.times x y) 0 → lor (eq ℤ x 0) (eq ℤ y 0)

def ℚ : Type ≔ data [ zero. | suc. (_:ℚ) | quot. (_:ℚ) (_:ℕ₊) ]
axiom ℚ.plus : ℚ → ℚ → ℚ
axiom ℚ.minus : ℚ → ℚ → ℚ
axiom ℚ.times : ℚ → ℚ → ℚ
axiom ℚ.pow : ℚ → ℕ → ℚ
axiom ℚ.negate : ℚ → ℚ
axiom ℚ.square : ℚ → ℚ
axiom ℚ.cube : ℚ → ℚ
axiom ℚ.fourth : ℚ → ℚ

axiom ℚ.integral (x y : ℚ) : eq ℚ (ℚ.times x y) 0 → lor (eq ℚ x 0) (eq ℚ y 0)

def ℝ : Type ≔ data [ zero. | suc. (_:ℝ) | quot. (_:ℝ) (_:ℕ₊) ]
axiom ℝ.plus : ℝ → ℝ → ℝ
axiom ℝ.minus : ℝ → ℝ → ℝ
axiom ℝ.times : ℝ → ℝ → ℝ
axiom ℝ.pow : ℝ → ℕ → ℝ
axiom ℝ.negate : ℝ → ℝ
axiom ℝ.square : ℝ → ℝ
axiom ℝ.cube : ℝ → ℝ
axiom ℝ.fourth : ℝ → ℝ

axiom ℝ.integral (x y : ℝ) : eq ℝ (ℝ.times x y) 0 → lor (eq ℝ x 0) (eq ℝ y 0)

def 𝕊 : Type ≔ data [ zero. | suc. (_:𝕊) | quot. (_:𝕊) (_:ℕ₊) | omega. ]
axiom 𝕊.plus : 𝕊 → 𝕊 → 𝕊
axiom 𝕊.minus : 𝕊 → 𝕊 → 𝕊
axiom 𝕊.times : 𝕊 → 𝕊 → 𝕊
axiom 𝕊.pow : 𝕊 → ℕ → 𝕊
axiom 𝕊.negate : 𝕊 → 𝕊
axiom 𝕊.square : 𝕊 → 𝕊
axiom 𝕊.cube : 𝕊 → 𝕊
axiom 𝕊.fourth : 𝕊 → 𝕊

axiom 𝕊.integral (x y : 𝕊) : eq 𝕊 (𝕊.times x y) 0 → lor (eq 𝕊 x 0) (eq 𝕊 y 0)

def divisible (a b : ℤ) : Type ≔ exists ℤ (k ↦ eq ℤ b (ℤ.times k a))
def congruent (a b n : ℤ) : Type ≔ exists ℤ (k ↦ eq ℤ (ℤ.minus b a) (ℤ.times k n))
"

(* Raw.App now takes a *check* function and an *optional* check argument; these helpers build an
   explicit application of a synthesizing head to a list of explicit (always-present) arguments. *)
let some_arg (c : 'a Raw.check located) : 'a Raw.check option located = locate_opt c.loc (Some c.value)

let rec apps (fn : 'a Raw.check located) (args : 'a Raw.check located list) : 'a Raw.check located =
  match args with
  | [] -> fn
  | a :: args ->
      apps (locate_opt fn.loc (Synth (App (fn, some_arg a, locate_opt None `Explicit)))) args

(* Apply a synthesizing head to one explicit check argument, yielding a synth (for SFirst lists). *)
let sapp (fn : 'a Raw.synth located) (arg : 'a Raw.check located) : 'a Raw.synth =
  App (locate_opt fn.loc (Synth fn.value), some_arg arg, locate_opt None `Explicit)

(* A normal, explicit, non-cube lambda over a single variable. *)
let normal_lam name body =
  Lam { name; cube = locate_opt None `Normal; implicit = `Explicit; dom = None; body }

let get_const parts = Scope.lookup parts <||> String.concat "." parts ^ " not found"

let get_root c =
  match Bwd.of_list (Scope.name_of c) with
  | Snoc (_, root) -> root
  | Emp -> raise (Jserror "no name parts")

(* Now we define notations for them.  The propositional connectives could be defined with Narya's built-in notation command, except that we want to have no space around the operator symbols, so we define them custom here.  The quantifiers have to be defined custom because Narya's built-in notation command doesn't yet handle variable-binding notations.  Since we don't have the corresponding constants at compile-time, we hack by looking them up in the Scope at run-time; this depends on using the same names below and above in the startup code.  *)

let onechar_ops =
  let open Token in
  [|
    (0xAC, Ident [ "¬" ]);
    (0x2227, Ident [ "∧" ]);
    (0x2228, Ident [ "∨" ]);
    (0x21D2, Ident [ "⇒" ]);
    (0x21D4, Ident [ "⇔" ]);
    (0x2200, Ident [ "∀" ]);
    (0x2203, Ident [ "∃" ]);
    (0x2208, Ident [ "∈" ]);
    (0xD7, Ident [ "×" ]);
    (0x2294, Ident [ "⊔" ]);
    (0x22A5, Ident [ "⊥" ]);
    (0x22A4, Ident [ "⊤" ]);
    (0x2212, Ident [ "−" ]);
    (0x2260, Ident [ "≠" ]);
    (0xB2, Ident [ "²" ]);
    (0xB3, Ident [ "³" ]);
    (0x2074, Ident [ "⁴" ]);
    (0x2223, Ident [ "∣" ]);
    (0x2261, Ident [ "≡" ]);
  |]

type (_, _, _) identity +=
  | Forall : (closed, No.zero, No.strict opn) identity
  | Exists : (closed, No.zero, No.strict opn) identity
  | And : (No.strict opn, No.zero, No.strict opn) identity
  | Or : (No.strict opn, No.zero, No.strict opn) identity
  | Imp : (No.strict opn, No.zero, No.strict opn) identity
  | Iff : (No.strict opn, No.zero, No.strict opn) identity
  | (* We want these to bind tighter than → which is 0 *)
      Prod :
      (No.strict opn, No.one_half, No.strict opn) identity
  | Coprod : (No.strict opn, No.one_half, No.strict opn) identity
  | Neg : (closed, No.one, No.strict opn) identity
  | Equals : (No.strict opn, No.zero, No.strict opn) identity
  | Lt : (No.strict opn, No.zero, No.strict opn) identity
  | Gt : (No.strict opn, No.zero, No.strict opn) identity
  | Le : (No.strict opn, No.zero, No.strict opn) identity
  | Ge : (No.strict opn, No.zero, No.strict opn) identity
  | Neq : (No.strict opn, No.zero, No.strict opn) identity
  | Plus : (No.nonstrict opn, No.two, No.strict opn) identity
  | Minus : (No.nonstrict opn, No.two, No.strict opn) identity
  | Times : (No.nonstrict opn, No.three, No.strict opn) identity
  | Div : (No.nonstrict opn, No.three, No.strict opn) identity
  | Negate : (closed, No.three, No.nonstrict opn) identity
  | Pow : (No.nonstrict opn, No.four, No.strict opn) identity
  | Square : (No.strict opn, No.four, closed) identity
  | Cube : (No.strict opn, No.four, closed) identity
  | Fourth : (No.strict opn, No.four, closed) identity
  | Divisible : (No.strict opn, No.zero, No.strict opn) identity
  | Congruent : (No.strict opn, No.zero, closed) identity

let forall : (closed, No.zero, No.strict opn) notation = (Forall, Prefix No.zero)
let exists : (closed, No.zero, No.strict opn) notation = (Exists, Prefix No.zero)
let andn : (No.strict opn, No.zero, No.strict opn) notation = (And, Infix No.zero)
let orn : (No.strict opn, No.zero, No.strict opn) notation = (Or, Infix No.zero)
let imp : (No.strict opn, No.zero, No.strict opn) notation = (Imp, Infix No.zero)
let iff : (No.strict opn, No.zero, No.strict opn) notation = (Iff, Infix No.zero)
let neg : (closed, No.one, No.strict opn) notation = (Neg, Prefix No.one)
let prod : (No.strict opn, No.one_half, No.strict opn) notation = (Prod, Infix No.one_half)
let coprod : (No.strict opn, No.one_half, No.strict opn) notation = (Coprod, Infix No.one_half)
let quantifiers = [ ("∀", forall, "forall"); ("∃", exists, "exists") ]
let equals : (No.strict opn, No.zero, No.strict opn) notation = (Equals, Infix No.zero)
let lt : (No.strict opn, No.zero, No.strict opn) notation = (Lt, Infix No.zero)
let gt : (No.strict opn, No.zero, No.strict opn) notation = (Gt, Infix No.zero)
let le : (No.strict opn, No.zero, No.strict opn) notation = (Le, Infix No.zero)
let ge : (No.strict opn, No.zero, No.strict opn) notation = (Ge, Infix No.zero)
let neq : (No.strict opn, No.zero, No.strict opn) notation = (Neq, Infix No.zero)
let plus : (No.nonstrict opn, No.two, No.strict opn) notation = (Plus, Infixl No.two)
let minus : (No.nonstrict opn, No.two, No.strict opn) notation = (Minus, Infixl No.two)
let times : (No.nonstrict opn, No.three, No.strict opn) notation = (Times, Infixl No.three)
let div : (No.nonstrict opn, No.three, No.strict opn) notation = (Div, Infixl No.three)
let pow : (No.nonstrict opn, No.four, No.strict opn) notation = (Pow, Infixl No.four)
let negate : (closed, No.three, No.nonstrict opn) notation = (Negate, Prefixr No.three)
let square : (No.strict opn, No.four, closed) notation = (Square, Postfix No.four)
let cube : (No.strict opn, No.four, closed) notation = (Cube, Postfix No.four)
let fourth : (No.strict opn, No.four, closed) notation = (Fourth, Postfix No.four)
let divisible : (No.strict opn, No.zero, No.strict opn) notation = (Divisible, Infix No.zero)
let congruent : (No.strict opn, No.zero, closed) notation = (Congruent, Postfix No.zero)

type infix = Wrap_infix : (No.strict opn, 'tight, No.strict opn) notation -> infix

let binops =
  [
    ("∧", Wrap_infix andn, [ "land" ]);
    ("∨", Wrap_infix orn, [ "lor" ]);
    ("⇒", Wrap_infix imp, [ "imp" ]);
    ("⇔", Wrap_infix iff, [ "iff" ]);
    ("×", Wrap_infix prod, [ "prod" ]);
    ("⊔", Wrap_infix coprod, [ "coprod" ]);
  ]

type infixl = Wrap_infixl : (No.nonstrict opn, 'tight, No.strict opn) notation -> infixl

let numbers = [ "ℤ"; "ℚ"; "ℝ"; "𝕊" ]

let algebra =
  [
    ("+", [ Token.Op "+" ], Token.Op "+", Token.Op "+", Wrap_infixl plus, [ "plus" ]);
    ("−", [ Ident [ "−" ]; Op "-" ], Ident [ "−" ], Op "-", Wrap_infixl minus, [ "minus" ]);
    ("*", [ Op "*" ], Op "*", Op "*", Wrap_infixl times, [ "times" ]);
    ("^", [ Op "**"; Op "^" ], Op "^", Op "^", Wrap_infixl pow, [ "pow" ]);
  ]

let powers =
  [
    ("²", Token.Ident [ "²" ], Token.Ident [ "^2" ], square, [ "square" ]);
    ("³", Token.Ident [ "³" ], Token.Ident [ "^3" ], cube, [ "cube" ]);
    ("⁴", Token.Ident [ "⁴" ], Token.Ident [ "^4" ], fourth, [ "fourth" ]);
  ]

let rec get_abs quant (body : wrapped_parse) : string option * wrapped_parse =
  match body with
  | Wrap { value = Notn ((Parens, _), n); _ } -> (
      match args n with
      | [ Token (LParen, _); Term body; Token (RParen, _) ] -> get_abs quant (Wrap body)
      | _ -> Builtins.invalid quant)
  | Wrap { value = Notn ((Builtins.Abs, _), n); _ } -> (
      match args n with
      | [ Term { value = Ident ([ x ], _); _ }; Token (Mapsto, _); Term body ] -> (
          match body.value with
          | Notn ((Exists, _), _) | Notn ((Forall, _), _) | Notn ((Neg, _), _) -> (Some x, Wrap body)
          | Notn _ -> (Some x, Wrap (Unparse.parenthesize body))
          | _ -> (Some x, Wrap body))
      | _ -> Builtins.invalid quant)
  | _ -> fatal (Anomaly ("unexpected eta-contracted argument for quantifier " ^ quant))

let pp_op opname obs =
  match obs with
  | [ Term x; Token (op, (wsop, _)); Term y ] ->
      let px, wsx = pp_term x in
      let py, wsy = pp_term y in
      (px ^^ pp_ws `None wsx ^^ Token.pp op ^^ pp_ws `None wsop ^^ py, wsy)
  | _ -> Builtins.invalid opname

(* This is a little tricky because the unparser doesn't know about binding notations (yet), so it sees only two arguments and produces (a parse tree representation of) something like "∃ A (x ↦ P x)" rather than the desired "∃x∈A,P x".  But we also try to support reformatting parse trees produced by parsing the latter. *)
let pp_quant qname obs =
  let quant, wsquant, x, wsin, ty, wscomma, Wrap body =
    match obs with
    | [ Token (quant, (wsquant, _)); Term ty; Token (Op ",", (wscomma, _)); Term body ] ->
        let x, body = get_abs qname (Wrap body) in
        (quant, wsquant, x, [], Wrap ty, wscomma, body)
    | [
     Token (quant, (wsquant, _));
     Term x;
     Token (Ident [ "∈" ], (wsin, _));
     Term ty;
     Token (Op ",", (wscomma, _));
     Term body;
    ] -> (quant, wsquant, Builtins.get_var x, wsin, Wrap ty, wscomma, Wrap body)
    | _ -> Builtins.invalid qname in
  let pbody, wsbody = pp_term body in
  ( Token.pp quant
    ^^ pp_ws `None wsquant
    ^^ pp_var x
    ^^ Token.pp (Ident [ "∈" ])
    ^^ pp_ws `None wsin
    ^^ pp_complete_term ty `None
    ^^ Token.pp (Op ",")
    ^^ pp_ws `None wscomma
    ^^ pbody,
    wsbody )

let () =
  List.iter
    (fun (name, Wrap_infix onotn, ostr) ->
      make onotn
        {
          name;
          tree = Open_entry (eop (Ident [ name ]) (done_open onotn));
          processor =
            (fun ctx obs loc ->
              match obs with
              | [ Term x; Token _; Term y ] ->
                  let x, y = (process ctx x, process ctx y) in
                  let oconst = get_const ostr in
                  apps (locate_opt loc (Synth (Const oconst))) [ x; y ]
              | _ -> Builtins.invalid name);
          print_term = Some (pp_op name);
          print_case = None;
          pattern = (fun _ loc -> fatal ?loc (Invalid_notation_pattern name));
          is_case = (fun _ -> false);
        })
    binops;
  make neg
    {
      name = "¬";
      tree = Closed_entry (eop (Ident [ "¬" ]) (Done_closed neg));
      processor =
        (fun ctx obs loc ->
          match obs with
          | [ Token _; Term x ] ->
              let x = process ctx x in
              let nconst = get_const [ "neg" ] in
              apps (locate_opt loc (Synth (Const nconst))) [ x ]
          | _ -> Builtins.invalid "¬");
      print_term =
        Some
          (fun obs ->
            match obs with
            | [ Token (neg, (wsneg, _)); Term x ] ->
                let px, wsx = pp_term x in
                (Token.pp neg ^^ pp_ws `None wsneg ^^ px, wsx)
            | _ -> Builtins.invalid "¬");
      print_case = None;
      pattern = (fun _ loc -> fatal ?loc (Invalid_notation_pattern "¬"));
      is_case = (fun _ -> false);
    };
  List.iter
    (fun (name, qnotn, qstr) ->
      make qnotn
        {
          name;
          tree =
            Closed_entry
              (eop (Ident [ name ]) (term (Ident [ "∈" ]) (term (Op ",") (Done_closed qnotn))));
          processor =
            (fun ctx obs loc ->
              match obs with
              | [ Token _; Term x; Token _; Term ty; Token _; Term body ] ->
                  let x = Builtins.get_var x in
                  let ty = process ctx ty in
                  let body = process (Bwv.snoc ctx x) body in
                  let qconst = get_const [ qstr ] in
                  apps
                    (locate_opt loc (Synth (Const qconst)))
                    [ ty; locate_opt loc (normal_lam (locate_opt loc x) body) ]
              | _ -> Builtins.invalid qstr);
          print_term = Some (pp_quant name);
          print_case = None;
          pattern = (fun _ loc -> fatal ?loc (Invalid_notation_pattern name));
          is_case = (fun _ -> false);
        })
    quantifiers

(* We don't need separate unicode/ascii versions of these because we detect and print relations specially in the Oracle. *)
let relations =
  [
    ("=", Token.Op "=", equals, "eq", "neq");
    ("≠", Ident [ "≠" ], neq, "neq", "eq");
    ("<", Op "<", lt, "lt", "gt");
    (">", Op ">", gt, "gt", "lt");
    ("≤", Ident [ "≤" ], le, "le", "ge");
    ("≥", Ident [ "≥" ], ge, "ge", "le");
  ]

let () =
  List.iter
    (fun (name, tok, notn, str, opp_str) ->
      make notn
        {
          name;
          tree = Open_entry (eop tok (done_open notn));
          processor =
            (fun ctx obs loc ->
              match obs with
              | Term x :: Token _ :: Term y :: _ ->
                  let x, y = (process ctx x, process ctx y) in
                  let xterm =
                    match x.value with
                    | Synth sx ->
                        [
                          ( `Any,
                            sapp
                              (locate_opt loc
                                 (ImplicitSApp
                                    ( locate_opt loc (Const (get_const [ str ])),
                                      loc,
                                      locate_opt x.loc sx )))
                              y,
                            true );
                        ]
                    | _ -> [] in
                  let yterm =
                    match y.value with
                    | Synth sy ->
                        [
                          ( `Any,
                            sapp
                              (locate_opt loc
                                 (ImplicitSApp
                                    ( locate_opt loc (Const (get_const [ opp_str ])),
                                      loc,
                                      locate_opt y.loc sy )))
                              x,
                            true );
                        ]
                    | _ -> [] in
                  locate_opt loc (Synth (SFirst (xterm @ yterm, None)))
              | _ -> Builtins.invalid name);
          print_term =
            Some
              (fun obs ->
                match obs with
                | Term x :: Token (_, (wseq, _)) :: Term y :: _ ->
                    let px, wsx = pp_term x in
                    let py, wsy = pp_term y in
                    (px ^^ pp_ws `None wsx ^^ Token.pp tok ^^ pp_ws `None wseq ^^ py, wsy)
                | _ -> Builtins.invalid name);
          print_case = None;
          pattern = (fun _ loc -> fatal ?loc (Invalid_notation_pattern name));
          is_case = (fun _ -> false);
        })
    relations

let () =
  List.iter
    (fun (name, syms, usym, asym, Wrap_infixl onotn, ostr) ->
      make onotn
        {
          name;
          tree = Open_entry (eops (List.map (fun sym -> (sym, done_open onotn)) syms));
          processor =
            (fun ctx obs loc ->
              match obs with
              | [ Term x; Token _; Term y ] ->
                  let x, y = (process ctx x, process ctx y) in
                  locate_opt loc
                    (Synth
                       (* Try the first (smallest) number system that works for both arguments. *)
                       (SFirst
                          ( List.map
                              (fun ty ->
                                ( `Any,
                                  sapp
                                    (locate_opt None
                                       (sapp (locate_opt loc (Const (get_const (ty :: ostr)))) x))
                                    y,
                                  true ))
                              numbers,
                            None )))
              | _ -> Builtins.invalid name);
          print_term =
            Some
              (fun obs ->
                let op = if Display.chars () = `Unicode then usym else asym in
                match obs with
                | [ Term x; Token (_, (wsop, _)); Term y ] ->
                    let px, wsx = pp_term x in
                    let py, wsy = pp_term y in
                    (px ^^ pp_ws `None wsx ^^ Token.pp op ^^ pp_ws `None wsop ^^ py, wsy)
                | _ -> Builtins.invalid name);
          print_case = None;
          pattern = (fun _ loc -> fatal ?loc (Invalid_notation_pattern name));
          is_case = (fun _ -> false);
        })
    algebra;
  make negate
    {
      name = "−";
      tree =
        Closed_entry (eops [ (Op "-", Done_closed negate); (Ident [ "−" ], Done_closed negate) ]);
      processor =
        (fun ctx obs loc ->
          match obs with
          | [ Token _; Term x ] ->
              let x = process ctx x in
              locate_opt loc
                (Synth
                   (SFirst
                      ( List.map
                          (fun ty ->
                            (`Any, sapp (locate_opt loc (Const (get_const [ ty; "negate" ]))) x, true))
                          numbers,
                        None )))
          | _ -> Builtins.invalid "negate");
      print_term =
        Some
          (function
          | [ Token (_, (wsop, _)); Term x ] ->
              let px, wsx = pp_term x in
              ( Token.pp (if Display.chars () = `Unicode then Ident [ "−" ] else Op "-")
                ^^ pp_ws `None wsop
                ^^ px,
                wsx )
          | _ -> Builtins.invalid "negate");
      print_case = None;
      pattern = (fun _ loc -> fatal ?loc (Invalid_notation_pattern "−"));
      is_case = (fun _ -> false);
    };
  List.iter
    (fun (name, sym, asym, onotn, ostr) ->
      make onotn
        {
          name;
          tree = Open_entry (eop sym (done_open onotn));
          processor =
            (fun ctx obs loc ->
              match obs with
              | [ Term x; Token _ ] ->
                  let x = process ctx x in
                  locate_opt loc
                    (Synth
                       (SFirst
                          ( List.map
                              (fun ty ->
                                (`Any, sapp (locate_opt loc (Const (get_const (ty :: ostr)))) x, true))
                              numbers,
                            None )))
              | _ -> Builtins.invalid name);
          print_term =
            Some
              (fun obs ->
                let op = if Display.chars () = `Unicode then sym else asym in
                match obs with
                | [ Term x; Token (_, (wsop, _)) ] ->
                    let px, wsx = pp_term x in
                    (px ^^ pp_ws `None wsx ^^ Token.pp op, wsop)
                | _ -> Builtins.invalid name);
          print_case = None;
          pattern = (fun _ loc -> fatal ?loc (Invalid_notation_pattern name));
          is_case = (fun _ -> false);
        })
    powers

let rec add_subtypes = function
  | [] | [ _ ] -> ()
  | subtype :: supertypes ->
      List.iter (Subtype.add subtype) supertypes;
      add_subtypes supertypes

(* Finally, here is a function that installs these notations into the current Situation.  This must be run inside the Pauser. *)

let install_notations () =
  List.iter
    (fun (oname, Wrap_infix onotn, ostr) ->
      Scope.Situation.add_with_print
        {
          keys = [ `Constant (get_const ostr) ];
          notn = Wrap onotn;
          pat_vars = [ "P"; "Q" ];
          val_vars = [ "P"; "Q" ];
          inner_symbols = `Single (Ident [ oname ]);
        })
    binops;
  List.iter
    (fun (qname, qnotn, qstr) ->
      Scope.Situation.add_with_print
        {
          keys = [ `Constant (get_const [ qstr ]) ];
          notn = Wrap qnotn;
          pat_vars = [ "A"; "P" ];
          val_vars = [ "A"; "P" ];
          inner_symbols = `Multiple (Op qname, [ None ], Op ",");
        })
    quantifiers;
  Scope.Situation.add_with_print
    {
      keys = [ `Constant (get_const [ "neg" ]) ];
      notn = Wrap neg;
      pat_vars = [ "P" ];
      val_vars = [ "P" ];
      inner_symbols = `Single (Op "¬");
    };
  List.iter
    (fun (_, tok, notn, str, _) ->
      Scope.Situation.add_with_print
        {
          keys = [ `Constant (get_const [ str ]) ];
          notn = Wrap notn;
          pat_vars = [ "x"; "y"; "A" ];
          val_vars = [ "A"; "x"; "y" ];
          inner_symbols = `Multiple (tok, [ None ], Op ":>");
        })
    relations;
  List.iter
    (fun (_, _, usym, asym, Wrap_infixl onotn, ostr) ->
      Scope.Situation.add_with_print
        {
          keys = List.map (fun ty -> `Constant (get_const (ty :: ostr))) numbers;
          notn = Wrap onotn;
          pat_vars = [ "x"; "y" ];
          val_vars = [ "x"; "y" ];
          inner_symbols = `Single (if Display.chars () = `Unicode then usym else asym);
        })
    algebra;
  let _ =
    Scope.Situation.add_user
      (User
         {
           name = "quot";
           fixity = Infixl No.three;
           pattern = Var (("x", `None, []), Var_nil ((Op "/", `None, []), ("y", [])));
           key = `Constr (Constr.intern "quot", 2);
           val_vars = [ "x"; "y" ];
         }) in
  List.iter
    (fun (_, sym, _, onotn, ostr) ->
      Scope.Situation.add_with_print
        {
          keys = List.map (fun ty -> `Constant (get_const (ty :: ostr))) numbers;
          notn = Wrap onotn;
          pat_vars = [ "x" ];
          val_vars = [ "x" ];
          inner_symbols = `Single sym;
        })
    powers;
  Scope.Situation.add_with_print
    {
      keys = List.map (fun ty -> `Constant (get_const [ ty; "negate" ])) numbers;
      notn = Wrap negate;
      pat_vars = [ "x" ];
      val_vars = [ "x" ];
      inner_symbols = `Single (Ident [ "−" ]);
    };
  let _ =
    Scope.Situation.add_user
      (User
         {
           name = "divisible";
           fixity = Infix No.zero;
           pattern = Var (("a", `Nobreak, []), Var_nil ((Ident [ "∣" ], `Nobreak, []), ("b", [])));
           key = `Constant (get_const [ "divisible" ]);
           val_vars = [ "a"; "b" ];
         }) in
  let _ =
    Scope.Situation.add_user
      (User
         {
           name = "congruent";
           fixity = Postfix No.zero;
           pattern =
             Var
               ( ("a", `None, []),
                 Op
                   ( (Ident [ "≡" ], `None, []),
                     Var
                       ( ("b", `Nobreak, []),
                         Op
                           ( (LParen, `None, []),
                             Op
                               ( (Ident [ "mod" ], `Nobreak, []),
                                 Var (("b", `None, []), Op_nil (RParen, [])) ) ) ) ) );
           key = `Constant (get_const [ "congruent" ]);
           val_vars = [ "a"; "b"; "n" ];
         }) in
  add_subtypes (List.map (fun x -> get_const [ x ]) numbers)
