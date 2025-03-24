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
axiom negneg (P : Type) : neg (neg P) → P"

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
  |]

type (_, _, _) identity +=
  | Forall : (closed, No.zero No.plus, No.strict opn) identity
  | Exists : (closed, No.zero No.plus, No.strict opn) identity
  | And : (No.strict opn, No.zero No.plus, No.strict opn) identity
  | Or : (No.strict opn, No.zero No.plus, No.strict opn) identity
  | Imp : (No.strict opn, No.zero No.plus, No.strict opn) identity
  | Iff : (No.strict opn, No.zero No.plus, No.strict opn) identity
  | Prod : (No.strict opn, No.zero No.plus, No.strict opn) identity
  | Coprod : (No.strict opn, No.zero No.plus, No.strict opn) identity
  | Neg : (closed, No.zero No.plus No.plus, No.strict opn) identity

let forall : (closed, No.zero No.plus, No.strict opn) notation = (Forall, Prefix No.one)
let exists : (closed, No.zero No.plus, No.strict opn) notation = (Exists, Prefix No.one)
let andn : (No.strict opn, No.zero No.plus, No.strict opn) notation = (And, Infix No.one)
let orn : (No.strict opn, No.zero No.plus, No.strict opn) notation = (Or, Infix No.one)
let imp : (No.strict opn, No.zero No.plus, No.strict opn) notation = (Imp, Infix No.one)
let iff : (No.strict opn, No.zero No.plus, No.strict opn) notation = (Iff, Infix No.one)
let neg : (closed, No.zero No.plus No.plus, No.strict opn) notation = (Neg, Prefix No.two)
let prod : (No.strict opn, No.zero No.plus, No.strict opn) notation = (Prod, Infix No.one)
let coprod : (No.strict opn, No.zero No.plus, No.strict opn) notation = (Coprod, Infix No.one)
let quantifiers = [ ("∀", forall, "forall"); ("∃", exists, "exists") ]

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

let rec get_abs quant (body : wrapped_parse) : string option * wrapped_parse =
  match body with
  | Wrap { value = Notn ((Builtins.Parens, _), n); _ } -> (
      match args n with
      | [ Term body ] -> get_abs quant (Wrap body)
      | _ -> Builtins.invalid quant)
  | Wrap { value = Notn ((Builtins.Abs, _), n); _ } -> (
      match args n with
      | [ Term { value = Ident ([ x ], _); _ }; Term body ] -> (
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
     Token (Op "∈", wsin);
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
          inner_symbols = `Multiple (Op qname, [], Op ",");
        })
    quantifiers;
  Situation.Current.add_with_print
    {
      key = `Constant (Option.get (Scope.lookup [ "neg" ]));
      notn = Wrap neg;
      pat_vars = [ "P" ];
      val_vars = [ "P" ];
      inner_symbols = `Single (Op "¬");
    }
