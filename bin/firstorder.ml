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
axiom Nil_eqs : Type
axiom nil_eqs : Nil_eqs
axiom Cons_eqs (x_eq_y : Type) (_ : x_eq_y) (rest : Type) (_ : rest) : Type
axiom cons_eqs (x_eq_y : Type) (H : x_eq_y) (rest : Type) (r : rest) : Cons_eqs x_eq_y H rest r
axiom oracle (A : Type) (x : A) (C : Type) : C

def ℤ : Type ≔ data [ zero. | suc. (_:ℤ) | negsuc. (_:ℤ) ]
axiom plus : ℤ → ℤ → ℤ
axiom minus : ℤ → ℤ → ℤ
axiom times : ℤ → ℤ → ℤ
axiom pow : ℤ → ℤ → ℤ
axiom negate : ℤ → ℤ
axiom square : ℤ → ℤ
axiom cube : ℤ → ℤ
axiom fourth : ℤ → ℤ
"

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
    (0x2238, Ident [ "∸" ]);
    (0xB2, Ident [ "²" ]);
    (0xB3, Ident [ "³" ]);
    (0x2074, Ident [ "⁴" ]);
  |]

type (_, _, _) identity +=
  | Forall : (closed, No.zero, No.strict opn) identity
  | Exists : (closed, No.zero, No.strict opn) identity
  | And : (No.strict opn, No.zero, No.strict opn) identity
  | Or : (No.strict opn, No.zero, No.strict opn) identity
  | Imp : (No.strict opn, No.zero, No.strict opn) identity
  | Iff : (No.strict opn, No.zero, No.strict opn) identity
  | Prod : (No.strict opn, No.zero, No.strict opn) identity
  | Coprod : (No.strict opn, No.zero, No.strict opn) identity
  | Neg : (closed, No.one, No.strict opn) identity
  | Equals : (No.strict opn, No.zero, No.strict opn) identity
  | Plus : (No.nonstrict opn, No.two, No.strict opn) identity
  | Minus : (No.nonstrict opn, No.two, No.strict opn) identity
  | Times : (No.nonstrict opn, No.three, No.strict opn) identity
  | Negate : (closed, No.three, No.nonstrict opn) identity
  | Pow : (No.nonstrict opn, No.four, No.strict opn) identity
  | Square : (No.strict opn, No.four, closed) identity
  | Cube : (No.strict opn, No.four, closed) identity
  | Fourth : (No.strict opn, No.four, closed) identity

let forall : (closed, No.zero, No.strict opn) notation = (Forall, Prefix No.zero)
let exists : (closed, No.zero, No.strict opn) notation = (Exists, Prefix No.zero)
let andn : (No.strict opn, No.zero, No.strict opn) notation = (And, Infix No.zero)
let orn : (No.strict opn, No.zero, No.strict opn) notation = (Or, Infix No.zero)
let imp : (No.strict opn, No.zero, No.strict opn) notation = (Imp, Infix No.zero)
let iff : (No.strict opn, No.zero, No.strict opn) notation = (Iff, Infix No.zero)
let neg : (closed, No.one, No.strict opn) notation = (Neg, Prefix No.one)
let prod : (No.strict opn, No.zero, No.strict opn) notation = (Prod, Infix No.zero)
let coprod : (No.strict opn, No.zero, No.strict opn) notation = (Coprod, Infix No.zero)
let quantifiers = [ ("∀", forall, "forall"); ("∃", exists, "exists") ]
let equals : (No.strict opn, No.zero, No.strict opn) notation = (Equals, Infix No.zero)
let plus : (No.nonstrict opn, No.two, No.strict opn) notation = (Plus, Infixl No.two)
let minus : (No.nonstrict opn, No.two, No.strict opn) notation = (Minus, Infixl No.two)
let times : (No.nonstrict opn, No.three, No.strict opn) notation = (Times, Infixl No.three)
let pow : (No.nonstrict opn, No.four, No.strict opn) notation = (Pow, Infixl No.four)
let negate : (closed, No.three, No.nonstrict opn) notation = (Negate, Prefixr No.three)
let square : (No.strict opn, No.four, closed) notation = (Square, Postfix No.four)
let cube : (No.strict opn, No.four, closed) notation = (Cube, Postfix No.four)
let fourth : (No.strict opn, No.four, closed) notation = (Fourth, Postfix No.four)

type infix = Wrap_infix : (No.strict opn, 'tight, No.strict opn) notation -> infix

let binops =
  [
    ("∧", Wrap_infix andn, "land");
    ("∨", Wrap_infix orn, "lor");
    ("⇒", Wrap_infix imp, "imp");
    ("⇔", Wrap_infix iff, "iff");
    ("×", Wrap_infix prod, "prod");
    ("⊔", Wrap_infix coprod, "coprod");
  ]

type infixl = Wrap_infixl : (No.nonstrict opn, 'tight, No.strict opn) notation -> infixl

let algebra =
  [
    ("+", Token.Op "+", Token.Op "+", Wrap_infixl plus, "plus");
    ("−", Ident [ "−" ], Op "-", Wrap_infixl minus, "minus");
    ("*", Op "*", Op "*", Wrap_infixl times, "times");
    ("**", Op "**", Op "^", Wrap_infixl pow, "pow");
  ]

let powers =
  [
    ("²", Token.Ident [ "²" ], Token.Ident [ "^2" ], square, "square");
    ("²", Token.Ident [ "³" ], Token.Ident [ "^3" ], cube, "cube");
    ("²", Token.Ident [ "⁴" ], Token.Ident [ "^4" ], fourth, "fourth");
  ]

let rec get_abs quant (body : wrapped_parse) : string option * wrapped_parse =
  match body with
  | Wrap { value = Notn ((Builtins.Parens, _), n); _ } -> (
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
  | [ Term x; Token (op, wsop); Term y ] ->
      let px, wsx = pp_term x in
      let py, wsy = pp_term y in
      (px ^^ pp_ws `None wsx ^^ Token.pp op ^^ pp_ws `None wsop ^^ py, wsy)
  | _ -> Builtins.invalid opname

(* This is a little tricky because the unparser doesn't know about binding notations (yet), so it sees only two arguments and produces (a parse tree representation of) something like "∃ A (x ↦ P x)" rather than the desired "∃x∈A,P x".  But we also try to support reformatting parse trees produced by parsing the latter. *)
let pp_quant qname obs =
  let quant, wsquant, x, wsin, ty, wscomma, Wrap body =
    match obs with
    | [ Token (quant, wsquant); Term ty; Token (Op ",", wscomma); Term body ] ->
        let x, body = get_abs qname (Wrap body) in
        (quant, wsquant, x, [], Wrap ty, wscomma, body)
    | [
     Token (quant, wsquant);
     Term x;
     Token (Ident [ "∈" ], wsin);
     Term ty;
     Token (Op ",", wscomma);
     Term body;
    ] -> (quant, wsquant, get_var x, wsin, Wrap ty, wscomma, Wrap body)
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
                  let oconst = Option.get (Scope.lookup [ ostr ]) in
                  locate_opt loc
                    (Synth
                       (App
                          ( locate_opt loc
                              (App (locate_opt loc (Const oconst), x, locate_opt None `Explicit)),
                            y,
                            locate_opt None `Explicit )))
              | _ -> Builtins.invalid ostr);
          print_term = Some (pp_op name);
          print_case = None;
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
              let nconst = Option.get (Scope.lookup [ "neg" ]) in
              locate_opt loc
                (Synth (App (locate_opt loc (Const nconst), x, locate_opt None `Explicit)))
          | _ -> Builtins.invalid "¬");
      print_term =
        Some
          (fun obs ->
            match obs with
            | [ Token (neg, wsneg); Term x ] ->
                let px, wsx = pp_term x in
                (Token.pp neg ^^ pp_ws `None wsneg ^^ px, wsx)
            | _ -> Builtins.invalid "¬");
      print_case = None;
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
                  let x = get_var x in
                  let ty = process ctx ty in
                  let body = process (Bwv.snoc ctx x) body in
                  let qconst = Option.get (Scope.lookup [ qstr ]) in
                  locate_opt loc
                    (Synth
                       (App
                          ( locate_opt loc
                              (App (locate_opt loc (Const qconst), ty, locate_opt None `Explicit)),
                            locate_opt loc (Lam (locate_opt loc x, `Normal, body)),
                            locate_opt None `Explicit )))
              | _ -> Builtins.invalid qstr);
          print_term = Some (pp_quant name);
          print_case = None;
          is_case = (fun _ -> false);
        })
    quantifiers

let () =
  make equals
    {
      name = "=";
      tree = Open_entry (eop (Op "=") (done_open equals));
      processor =
        (fun ctx obs loc ->
          match obs with
          | Term x :: Token (Op "=", _) :: Term y :: _ -> (
              let x, y = (process ctx x, process ctx y) in
              match x.value with
              | Synth sx ->
                  locate_opt loc
                    (Synth
                       (App
                          ( locate_opt loc
                              (ImplicitSApp
                                 ( locate_opt loc (Const (Option.get (Scope.lookup [ "eq" ]))),
                                   loc,
                                   locate_opt x.loc sx )),
                            y,
                            locate_opt None `Explicit )))
              | _ -> fatal (Nonsynthesizing "first argument of equals"))
          | _ -> Builtins.invalid "=");
      print_term =
        Some
          (fun obs ->
            match obs with
            | Term x :: Token (Op "=", wseq) :: Term y :: _ ->
                let px, wsx = pp_term x in
                let py, wsy = pp_term y in
                (px ^^ pp_ws `None wsx ^^ Token.pp (Op "=") ^^ pp_ws `None wseq ^^ py, wsy)
            | _ -> Builtins.invalid "=");
      print_case = None;
      is_case = (fun _ -> false);
    };
  List.iter
    (fun (name, sym, asym, Wrap_infixl onotn, ostr) ->
      make onotn
        {
          name;
          tree = Open_entry (eops [ (sym, done_open onotn); (asym, done_open onotn) ]);
          processor =
            (fun ctx obs loc ->
              match obs with
              | [ Term x; Token _; Term y ] ->
                  let x, y = (process ctx x, process ctx y) in
                  let oconst = Option.get (Scope.lookup [ ostr ]) in
                  locate_opt loc
                    (Synth
                       (App
                          ( locate_opt loc
                              (App (locate_opt loc (Const oconst), x, locate_opt None `Explicit)),
                            y,
                            locate_opt None `Explicit )))
              | _ -> Builtins.invalid ostr);
          print_term =
            Some
              (fun obs ->
                let op = if Display.chars () = `Unicode then sym else asym in
                match obs with
                | [ Term x; Token (_, wsop); Term y ] ->
                    let px, wsx = pp_term x in
                    let py, wsy = pp_term y in
                    (px ^^ pp_ws `None wsx ^^ Token.pp op ^^ pp_ws `None wsop ^^ py, wsy)
                | _ -> Builtins.invalid name);
          print_case = None;
          is_case = (fun _ -> false);
        })
    algebra;
  make negate
    {
      name = "∸";
      tree =
        Closed_entry (eops [ (Op "--", Done_closed negate); (Ident [ "∸" ], Done_closed negate) ]);
      processor =
        (fun ctx obs loc ->
          match obs with
          | [ Token _; Term x ] ->
              let x = process ctx x in
              let nc = Option.get (Scope.lookup [ "negate" ]) in
              locate_opt loc (Synth (App (locate_opt loc (Const nc), x, locate_opt None `Explicit)))
          | _ -> Builtins.invalid "negate");
      print_term =
        Some
          (function
          | [ Token (_, wsop); Term x ] ->
              let px, wsx = pp_term x in
              (Token.pp (Ident [ "∸" ]) ^^ pp_ws `None wsop ^^ px, wsx)
          | _ -> Builtins.invalid "negate");
      print_case = None;
      is_case = (fun _ -> false);
    };
  List.iter
    (fun (name, sym, asym, onotn, ostr) ->
      make onotn
        {
          name;
          (* The ASCII can't be parsed here, since it conflicts with Narya's generic degeneracies *)
          tree = Open_entry (eop sym (done_open onotn));
          processor =
            (fun ctx obs loc ->
              match obs with
              | [ Term x; Token _ ] ->
                  let x = process ctx x in
                  let oconst = Option.get (Scope.lookup [ ostr ]) in
                  locate_opt loc
                    (Synth (App (locate_opt loc (Const oconst), x, locate_opt None `Explicit)))
              | _ -> Builtins.invalid ostr);
          print_term =
            Some
              (fun obs ->
                let op = if Display.chars () = `Unicode then sym else asym in
                match obs with
                | [ Term x; Token (_, wsop) ] ->
                    let px, wsx = pp_term x in
                    (px ^^ pp_ws `None wsx ^^ Token.pp op, wsop)
                | _ -> Builtins.invalid name);
          print_case = None;
          is_case = (fun _ -> false);
        })
    powers

(* Finally, here is a function that installs these notations into the current Situation.  This must be run inside the Pauser. *)

let install_notations () =
  List.iter
    (fun (oname, Wrap_infix onotn, ostr) ->
      Situation.Current.add_with_print
        {
          key = `Constant (Option.get (Scope.lookup [ ostr ]));
          notn = Wrap onotn;
          pat_vars = [ "P"; "Q" ];
          val_vars = [ "P"; "Q" ];
          inner_symbols = `Single (Ident [ oname ]);
        })
    binops;
  List.iter
    (fun (qname, qnotn, qstr) ->
      Situation.Current.add_with_print
        {
          key = `Constant (Option.get (Scope.lookup [ qstr ]));
          notn = Wrap qnotn;
          pat_vars = [ "A"; "P" ];
          val_vars = [ "A"; "P" ];
          inner_symbols = `Multiple (Op qname, [ None ], Op ",");
        })
    quantifiers;
  Situation.Current.add_with_print
    {
      key = `Constant (Option.get (Scope.lookup [ "neg" ]));
      notn = Wrap neg;
      pat_vars = [ "P" ];
      val_vars = [ "P" ];
      inner_symbols = `Single (Op "¬");
    };
  Situation.Current.add_with_print
    {
      key = `Constant (Option.get (Scope.lookup [ "eq" ]));
      notn = Wrap equals;
      pat_vars = [ "x"; "y"; "A" ];
      val_vars = [ "A"; "x"; "y" ];
      inner_symbols = `Multiple (Op "=", [ None ], Op ":>");
    };
  List.iter
    (fun (_, sym, _, Wrap_infixl onotn, ostr) ->
      Situation.Current.add_with_print
        {
          key = `Constant (Option.get (Scope.lookup [ ostr ]));
          notn = Wrap onotn;
          pat_vars = [ "x"; "y" ];
          val_vars = [ "x"; "y" ];
          inner_symbols = `Single sym;
        })
    algebra;
  List.iter
    (fun (_, sym, _, onotn, ostr) ->
      Situation.Current.add_with_print
        {
          key = `Constant (Option.get (Scope.lookup [ ostr ]));
          notn = Wrap onotn;
          pat_vars = [ "x" ];
          val_vars = [ "x" ];
          inner_symbols = `Single sym;
        })
    powers;
  Situation.Current.add_with_print
    {
      key = `Constant (Option.get (Scope.lookup [ "negate" ]));
      notn = Wrap negate;
      pat_vars = [ "x" ];
      val_vars = [ "x" ];
      inner_symbols = `Single (Ident [ "∸" ]);
    }
