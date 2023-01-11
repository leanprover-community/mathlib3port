/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module tactic.slice
! leanprover-community/mathlib commit a2d2e18906e2b62627646b5d5be856e6a642062f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Basic

open CategoryTheory

-- TODO someone might like to generalise this tactic to work with other associative structures.
namespace Tactic

unsafe def repeat_with_results {α : Type} (t : tactic α) : tactic (List α) :=
  (do
      let r ← t
      let s ← repeat_with_results
      return (r :: s)) <|>
    return []
#align tactic.repeat_with_results tactic.repeat_with_results

unsafe def repeat_count {α : Type} (t : tactic α) : tactic ℕ := do
  let r ← repeat_with_results t
  return r
#align tactic.repeat_count tactic.repeat_count

end Tactic

namespace Conv

open Tactic

unsafe def repeat_with_results {α : Type} (t : tactic α) : tactic (List α) :=
  (do
      let r ← t
      let s ← repeat_with_results
      return (r :: s)) <|>
    return []
#align conv.repeat_with_results conv.repeat_with_results

unsafe def repeat_count {α : Type} (t : tactic α) : tactic ℕ := do
  let r ← repeat_with_results t
  return r
#align conv.repeat_count conv.repeat_count

unsafe def slice (a b : ℕ) : conv Unit := do
  repeat <| to_expr ``(Category.assoc) >>= fun e => tactic.rewrite_target e { symm := ff }
  iterate_range (a - 1) (a - 1) do
      conv.congr
      conv.skip
  let k ←
    repeat_count <| to_expr ``(Category.assoc) >>= fun e => tactic.rewrite_target e { symm := true }
  iterate_range (k + 1 + a - b) (k + 1 + a - b) conv.congr
  repeat <| to_expr ``(Category.assoc) >>= fun e => tactic.rewrite_target e { symm := ff }
  rotate 1
  iterate_exactly' (k + 1 + a - b) conv.skip
#align conv.slice conv.slice

unsafe def slice_lhs (a b : ℕ) (t : conv Unit) : tactic Unit := do
  conv.interactive.to_lhs
  slice a b
  t
#align conv.slice_lhs conv.slice_lhs

unsafe def slice_rhs (a b : ℕ) (t : conv Unit) : tactic Unit := do
  conv.interactive.to_rhs
  slice a b
  t
#align conv.slice_rhs conv.slice_rhs

namespace Interactive

/-- `slice` is a conv tactic; if the current focus is a composition of several morphisms,
`slice a b` reassociates as needed, and zooms in on the `a`-th through `b`-th morphisms.

Thus if the current focus is `(a ≫ b) ≫ ((c ≫ d) ≫ e)`, then `slice 2 3` zooms to `b ≫ c`.
 -/
unsafe def slice :=
  conv.slice
#align conv.interactive.slice conv.interactive.slice

end Interactive

end Conv

namespace Tactic

open Conv

private unsafe def conv_target' (c : conv Unit) : tactic Unit := do
  let t ← target
  let (new_t, pr) ← c.convert t
  replace_target new_t pr
  try tactic.triv
  try (tactic.reflexivity reducible)
#align tactic.conv_target' tactic.conv_target'

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- `slice_lhs a b { tac }` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
unsafe def slice_lhs (a b : parse small_nat) (t : conv.interactive.itactic) : tactic Unit := do
  conv_target' ((conv.interactive.to_lhs >> slice a b) >> t)
#align tactic.interactive.slice_lhs tactic.interactive.slice_lhs

/-- `slice_rhs a b { tac }` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
unsafe def slice_rhs (a b : parse small_nat) (t : conv.interactive.itactic) : tactic Unit := do
  conv_target' ((conv.interactive.to_rhs >> slice a b) >> t)
#align tactic.interactive.slice_rhs tactic.interactive.slice_rhs

end Interactive

end Tactic

/-- `slice_lhs a b { tac }` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.

`slice_rhs a b { tac }` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
add_tactic_doc
  { Name := "slice"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.slice_lhs, `tactic.interactive.slice_rhs]
    tags := ["category theory"] }

