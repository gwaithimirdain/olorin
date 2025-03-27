open Bwd
open Util
open Core.Reporter
open Js_of_ocaml
open Rules

let carp str = Js_of_ocaml.Console.console##log (Js.string str)

(* This file defines a bunch of types and objects with conversion functions for passing data back and forth to Javascript. *)

exception Jserror of string

let ( <||> ) : type a. a option -> string -> a =
 fun x e ->
  match x with
  | Some x -> x
  | None -> raise (Jserror e)

let option_of_string_optdef s = Js.Optdef.case s (fun () -> None) (fun x -> Some (Js.to_string x))

(* IDs of DOM objects.  Currently only vertices and edges have IDs, not ports.  (Ports are identified by their vertex ID, their sort, and their label; see below.) *)

module Id = struct
  type t = Id of string

  let counter = ref 0
  let compare = compare
  let to_string (Id x) = x

  (* Sometimes we need to create a "dummy" ID for an object that doesn't have one. *)
  let make () =
    let id = Id ("temp" ^ string_of_int !counter) in
    counter := !counter + 1;
    id
end

module IdMap = Map.Make (Id)
module IdSet = Set.Make (Id)

(* Vertices of the graph *)

module Vertex = struct
  type t = { id : Id.t; name : string option; rule : rule; value : string option }

  class type js = object
    method id : Js.js_string Js.t Js.prop
    method name : Js.js_string Js.t Js.optdef Js.prop
    method rule : Js.js_string Js.t Js.prop
    method value : Js.js_string Js.t Js.optdef Js.prop
  end

  let of_js v =
    let id = Js.to_string v##.id in
    {
      id = Id id;
      name = option_of_string_optdef v##.name;
      rule =
        (match RuleMap.find_opt (Js.to_string v##.rule) rules with
        | Some x -> x
        | None -> raise (Jserror ("RuleMap.find in vertex_of_js: missing " ^ Js.to_string v##.rule)));
      value = option_of_string_optdef v##.value;
    }
end

(* Each vertex has a number of ports.  Each port has a "sort". *)

module Sort = struct
  type t = Input | Output | Assumption | Subgoal

  let of_string = function
    | "input" -> Input
    | "output" -> Output
    | "assumption" -> Assumption
    | "subgoal" -> Subgoal
    | _ -> raise (Invalid_argument "Sort.of_string")

  let to_string = function
    | Input -> "input"
    | Output -> "output"
    | Assumption -> "assumption"
    | Subgoal -> "subgoal"
end

module Port = struct
  type t = { vertex : Id.t; sort : Sort.t; label : string option }

  let compare : t -> t -> int = compare

  (* Encode a port as a string.  This is used not just for displaying but for hacking Asai locations. *)
  let to_string { vertex; sort; label } =
    String.concat " "
      (Id.to_string vertex :: Sort.to_string sort :: List.of_seq (Option.to_seq label))

  (* Decode a port from a string *)
  let of_strings = function
    | [ vertex; sort ] -> { vertex = Id vertex; sort = Sort.of_string sort; label = None }
    | [ vertex; sort; label ] ->
        { vertex = Id vertex; sort = Sort.of_string sort; label = Some label }
    | _ -> raise (Invalid_argument "port_of_strings")

  class type js = object
    method vertex : Js.js_string Js.t Js.prop
    method sort : Js.js_string Js.t Js.prop
    method label : Js.js_string Js.t Js.optdef Js.prop
  end

  let of_js (p : js Js.t) : t =
    {
      vertex = Id (Js.to_string p##.vertex);
      sort =
        (match Js.to_string p##.sort with
        | "input" -> Input
        | "output" -> Output
        | "assumption" -> Assumption
        | "subgoal" -> Subgoal
        | _ -> fatal (Anomaly "unrecognized port sort"));
      label = option_of_string_optdef p##.label;
    }
end

module PortSet = Set.Make (Port)

(* Each vertex has one or more output ports.  When there is only one output port, it is unlabeled. *)
let outputs_of_vertex (v : Vertex.t) : Port.t list =
  let vertex, sort = (v.id, Sort.Output) in
  match v.rule with
  (* Currently Fields and Coconstrs are the only kind of vertex that has multiple output ports. *)
  | Fields { outputs } ->
      List.map (fun (_, label) : Port.t -> { vertex; sort; label = Some label }) outputs
  | Coconstr { outputs; constr = _ } ->
      List.map (fun (_, label) : Port.t -> { vertex; sort; label = Some label }) outputs
  (* While the conclusion has zero. *)
  | Conclusion -> []
  (* All others have one. *)
  | _ -> [ { vertex; sort; label = None } ]

(* Some vertices have one or more assumption (local hypothesis) ports. *)
let assumptions_of_vertex (v : Vertex.t) =
  let vertex, sort = (v.id, Sort.Assumption) in
  match v.rule with
  (* Match and Abstraction (including proof-by-contradiction) vertices, plus some Tuples, are the ones that have assumption ports. *)
  | Match { branches; _ } ->
      List.flatten
        (List.map
           (function
             | Branch { assumptions; _ } ->
                 Vec.to_list_map
                   (* Currently, match assumptions never have values. *)
                   (fun label : Port.t -> { vertex; sort; label = Some label })
                   assumptions)
           branches)
  | Abs _ -> [ { vertex; sort; label = None } ]
  | Tuple { inputs } ->
      List.filter_map
        (fun (a, _, _) -> Option.map (fun label : Port.t -> { vertex; sort; label = Some label }) a)
        inputs
  | _ -> []

(* Two ports can be connected by an edge. *)

module Edge = struct
  type t = { id : Id.t; source : Port.t; target : Port.t; has_value : bool; ty : string option }

  class type js = object
    method id : Js.js_string Js.t Js.prop
    method source : Port.js Js.t Js.prop
    method target : Port.js Js.t Js.prop

    (* Some edges are "value" edges, which are colored differently and display a term in addition to a type. *)
    method hasValue : bool Js.t Js.optdef Js.prop

    (* Edges can have a type label, which if present will ascribe the value they carry. *)
    method ty : Js.js_string Js.t Js.optdef Js.prop
  end

  let of_js (e : js Js.t) =
    let id = Id.Id (Js.to_string e##.id) in
    let source = Port.of_js e##.source in
    let target = Port.of_js e##.target in
    let has_value = Js.to_bool (Js.Optdef.get e##.hasValue (fun () -> Js.bool false)) in
    let ty = Option.map Js.to_string (Js.Optdef.to_option e##.ty) in
    { id; source; target; has_value; ty }

  let has_value edges id =
    match IdMap.find_opt id edges with
    | Some e -> e.has_value
    | None -> false
end

(* Parameters, variables, and hypotheses *)

module Variable = struct
  type cls = [ `Parameter | `Variable | `Hypothesis ]
  type t = { id : Id.t; name : string option; ty : string; cls : cls }

  class type js = object
    method name : Js.js_string Js.t Js.optdef Js.prop
    method ty : Js.js_string Js.t Js.prop
    method id : Js.js_string Js.t Js.prop
  end

  let of_js cls vars v =
    let id, name, ty =
      (Id.Id (Js.to_string v##.id), option_of_string_optdef v##.name, Js.to_string v##.ty) in
    vars := !vars |> IdMap.add id ({ id; name; rule = Var; value = Some ty } : Vertex.t);
    { id; name; ty; cls }
end

(* Javascript location to display a type (and possibly term): edge ID, or port identified by vertex ID with sort and label. *)

class type js_loc = object
  method isEdge : bool Js.t Js.prop
  method id : Js.js_string Js.t Js.prop
  method sort : Js.js_string Js.t Js.optdef Js.prop
  method label : Js.js_string Js.t Js.optdef Js.prop
end

(* We hack Asai's "locations" to allow them to save a list of arbitrary stringable objects.  We store these objects in the "title" of an Asai "string source", leaving the "content" to be an actual parsed string term (e.g. for a type entered by the user for an ascription node). *)

module Locable = struct
  type t = [ `Edge of Id.t | `Port of Port.t ]

  let compare : t -> t -> int = compare

  let to_string : t -> string = function
    | `Edge id -> "EDGE " ^ Id.to_string id
    | `Port port -> "PORT " ^ Port.to_string port

  let of_string (str : string) : t =
    let parts = String.split_on_char ' ' str in
    match parts with
    | [ "EDGE"; id ] -> `Edge (Id.Id id)
    | "PORT" :: data -> `Port (Port.of_strings data)
    | _ -> raise (Invalid_argument "Locable.of_string")

  let to_js : t -> js_loc Js.t = function
    | `Edge id ->
        object%js
          val mutable isEdge = Js.bool true
          val mutable id = Js.string (Id.to_string id)
          val mutable sort = Js.undefined
          val mutable label = Js.undefined
        end
    | `Port { vertex; sort; label } ->
        object%js
          val mutable isEdge = Js.bool false
          val mutable id = Js.string (Id.to_string vertex)
          val mutable sort = Js.def (Js.string (Sort.to_string sort))

          val mutable label =
            match label with
            | Some label -> Js.def (Js.string label)
            | None -> Js.undefined
        end
end

module LocableMap = Map.Make (Locable)

module Loc = struct
  type t = Asai.Range.t option

  (* Make a hacked location from a list of Locable objects. *)
  let make ?(content = "") ?(annotate = true) (objs : Locable.t list) : Asai.Range.t =
    let title =
      (if annotate then "ANNOTE/" else "NOANNOTE/")
      ^ String.concat "/" (List.map Locable.to_string objs) in
    let source : Asai.Range.source = `String { title = Some title; content } in
    let pos : Asai.Range.position = { source; offset = 0; start_of_line = 0; line_num = 1 } in
    Asai.Range.make (pos, pos)

  (* Make a location entirely non-annotating *)
  let non_annotating : t -> t =
    Option.map @@ fun loc ->
    let start, stop = Asai.Range.split loc in
    match (start.source, stop.source) with
    | ( `String { title = Some str; content = start_content },
        `String { title = _; content = stop_content } ) ->
        let title =
          Some
            (String.concat "/"
               ("NOANNOTE"
               :: List.filter
                    (fun x -> x <> "ANNOTE" && x <> "NOANNOTE")
                    (String.split_on_char '/' str))) in
        Asai.Range.make
          ( { start with source = `String { title; content = start_content } },
            { stop with source = `String { title; content = stop_content } } )
    | _ -> fatal (Anomaly "invalid source")

  (* Add a list of additional Locable objects to an existing hacked location. *)
  let append ?(annote = true) (loc : Asai.Range.t) objs =
    let start, stop = Asai.Range.split loc in
    let newtitle =
      String.concat "/"
        ((if annote then "ANNOTE" else "NOANNOTE") :: List.map Locable.to_string objs) in
    let source : Asai.Range.source =
      match start.source with
      | `File _ -> raise (Invalid_argument "Loc.append")
      | `String { title = None; content } -> `String { title = Some newtitle; content }
      | `String { title = Some title; content } ->
          `String { title = Some (title ^ "/" ^ newtitle); content } in
    Asai.Range.make ({ start with source }, { stop with source })

  let append_opt ?annote loc objs =
    match loc with
    | None -> Some (make objs)
    | Some loc -> Some (append ?annote loc objs)

  let append_to_loc ?annote ({ value; loc } : 'a Asai.Range.located) objs : 'a Asai.Range.located =
    { value; loc = append_opt ?annote loc objs }

  (* Extract the encoded Locables and the string content *)
  let locs_and_content annotation (locs : t) : Locable.t list * string =
    match locs with
    | None -> ([], "")
    | Some loc -> (
        match (fst (Asai.Range.split loc)).source with
        | `String { title = Some str; content } ->
            ( Bwd.to_list
                (fst
                   (List.fold_left
                      (fun (locs, annote) -> function
                        | "ANNOTE" -> (locs, true)
                        | "NOANNOTE" -> (locs, false)
                        | loc when annote || not annotation ->
                            (Snoc (locs, Locable.of_string loc), annote)
                        | _ -> (locs, annote))
                      (Emp, true) (String.split_on_char '/' str))),
              content )
        | _ -> raise (Invalid_argument "Loc.to_string"))

  let annotation_locs (locs : t) : Locable.t list = fst (locs_and_content true locs)

  (* Convert a location to strings and an object for returning to Javascript. *)
  let js_and_content (loc : t) : js_loc Js.t Js.js_array Js.t * string =
    let locs, content = locs_and_content false loc in
    (Js.array (Array.of_list (List.map Locable.to_js locs)), content)
end

(* A label to put on a wire connecting two ports, or a port, showing the type and possibly the value that it "carries".  (Don't confuse this kind of "label" with the label that identifies a port, which appears inside a js_loc.) *)

module Label = struct
  (* A label *without* its location(s). *)
  type t = { tm : string option; ty : string }

  class type js = object
    method loc : js_loc Js.t Js.prop
    method tm : Js.js_string Js.t Js.opt Js.prop
    method ty : Js.js_string Js.t Js.prop
  end

  let to_js (loc : Locable.t) (lbl : t) : js Js.t =
    object%js
      val mutable loc = Locable.to_js loc
      val mutable tm = Option.fold ~none:Js.null ~some:(fun x -> Js.some (Js.string x)) lbl.tm
      val mutable ty = Js.string lbl.ty
    end

  let to_js_array (labels : (Locable.t, t) Hashtbl.t) : js Js.t Js.js_array Js.t =
    let jslabels = Dynarray.create () in
    Hashtbl.fold (fun id lbl () -> Dynarray.add_last jslabels (to_js id lbl)) labels ();
    Js.array (Dynarray.to_array jslabels)
end

(* Diagnostics to return data to JavaScript *)

module Diagnostic = struct
  class type js = object
    method isfatal : bool Js.t Js.prop
    method locs : js_loc Js.t Js.js_array Js.t Js.prop
    method text : Js.js_string Js.t Js.prop
  end

  let to_js f (d : 'm Asai.Diagnostic.t) : js Js.t =
    let locs, str = Loc.js_and_content d.explanation.loc in
    let buf = Buffer.create 70 in
    Sys_js.set_channel_flusher stdout (fun s -> Buffer.add_string buf s);
    Core.Reporter.display ~use_ansi:false ~output:stdout
      (if str = "" then { d with explanation = { d.explanation with loc = None } } else d);
    Out_channel.flush stdout;
    object%js
      val mutable isfatal = Js.bool f
      val mutable locs = locs
      val mutable text = Js.string (Buffer.contents buf)
    end

  (* Add a diagnostic to a dynamic array of them, flattening multiple-error combinations. *)
  let rec add diagnostics isfatal (d : Code.t Asai.Diagnostic.t) =
    match d.message with
    | Accumulated (_, ds) -> Mbwd.miter (fun [ d ] -> add diagnostics isfatal d) [ ds ]
    | _ -> Dynarray.add_last diagnostics (to_js isfatal d)
end

(* Overall return value to JavaScript *)

class type js_checked = object
  method complete : bool Js.t Js.prop
  method error : Js.js_string Js.t Js.opt Js.prop
  method labels : Label.js Js.t Js.js_array Js.t Js.prop
  method diagnostics : Diagnostic.js Js.t Js.js_array Js.t Js.prop
end
