/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module tactic.observe
! leanprover-community/mathlib commit b3f25363ae62cb169e72cd6b8b1ac97bacf21ca7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Suggest

/-!
# observe

The `observe` tactic is mainly intended for demo/educational purposes.
Calling `observe hp : p` is equivalent to `have hp : p, { library_search }`.
-/


open Tactic Tactic.Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/-- `observe hp : p` asserts the proposition `p`, and tries to prove it using `library_search`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p, { library_search }`.

If `hp` is omitted, then the placeholder `this` is used.

The variant `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
This may be particularly useful to speed up proofs. -/
unsafe def tactic.interactive.observe (trc : parse <| optional (tk "?"))
    (h : parse (parser.optional ident)) (t : parse (tk ":" *> texpr)) : tactic Unit := do
  let h' := h.getOrElse `this
  let t ← to_expr ``(($(t) : Prop))
  assert h' t
  let s ← focus1 (tactic.library_search { try_this := false }) <|> fail "observe failed"
  let s ← s.getRest "Try this: exact "
  let ppt ← pp t
  let pph : String := (h.map fun n : Name => n.toString ++ " ").getOrElse ""
  when trc <|
      ← do
        dbg_trace "Try this: have {(← pph)}: {(← ppt)} := {← s}"
#align tactic.interactive.observe tactic.interactive.observe

add_tactic_doc
  { Name := "observe"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.observe]
    tags := ["search", "Try this"] }

