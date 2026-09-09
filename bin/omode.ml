(* Olorin's mode.
 *
 * Narya's modes are generated at runtime, by a generative functor application, so a mode's type is
 * normally reachable only existentially (Mode.unique ()) -- which is no good for us, since our
 * global state (the level's context and conclusion, the oracle's translation) holds values that
 * have to be at one fixed, nameable mode.  So we generate our own mode here, at module level,
 * where its type gets a name, and install the trivial theory's cells on it: Olorin's logic is
 * plain first-order logic with no modalities, so one mode and the identity modality is all of the
 * mode theory it needs.  (Narya's own test suite names a mode the same way, in
 * test/testutil/testmode.ml.)
 *
 * This is the only mode generated in the process, so Narya's `Mode.unique` sees it and every term
 * it checks is at this mode. *)

open Modal
module Olorinmode = Mode.Generate (Trivial.TestmodeGen)

(* The mode everything Olorin checks lives at. *)
type mode = Olorinmode.t

module Olorincell = Trivial.Idcell (Olorinmode)

let () = Modalcell.choose_theory (module Olorincell : Modalcell.Theory)
let mode : mode Mode.t = Olorinmode.mode
