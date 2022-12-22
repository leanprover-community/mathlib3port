/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module tactic.simp_rw
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core

/-!
# The `simp_rw` tactic

This module defines a tactic `simp_rw` which functions as a mix of `simp` and
`rw`. Like `rw`, it applies each rewrite rule in the given order, but like
`simp` it repeatedly applies these rules and also under binders like `∀ x, ...`,
`∃ x, ...` and `λ x, ...`.

## Implementation notes

The tactic works by taking each rewrite rule in turn and applying `simp only` to
it. Arguments to `simp_rw` are of the format used by `rw` and are translated to
their equivalents for `simp`.
-/


namespace Tactic.Interactive

open Interactive Interactive.Types Tactic

/-- `simp_rw` functions as a mix of `simp` and `rw`. Like `rw`, it applies each
rewrite rule in the given order, but like `simp` it repeatedly applies these
rules and also under binders like `∀ x, ...`, `∃ x, ...` and `λ x, ...`.

Usage:
  - `simp_rw [lemma_1, ..., lemma_n]` will rewrite the goal by applying the
    lemmas in that order. A lemma preceded by `←` is applied in the reverse direction.
  - `simp_rw [lemma_1, ..., lemma_n] at h₁ ... hₙ` will rewrite the given hypotheses.
  - `simp_rw [...] at ⊢ h₁ ... hₙ` rewrites the goal as well as the given hypotheses.
  - `simp_rw [...] at *` rewrites in the whole context: all hypotheses and the goal.

Lemmas passed to `simp_rw` must be expressions that are valid arguments to `simp`.

For example, neither `simp` nor `rw` can solve the following, but `simp_rw` can:
```lean
example {α β : Type} {f : α → β} {t : set β} :
  (∀ s, f '' s ⊆ t) = ∀ s : set α, ∀ x ∈ s, x ∈ f ⁻¹' t :=
by simp_rw [set.image_subset_iff, set.subset_def]
```
-/
unsafe def simp_rw (q : parse rw_rules) (l : parse location) : tactic Unit :=
  q.rules.mmap' fun rule => do
    let simp_arg :=
      if rule.symm then simp_arg_type.symm_expr rule.rule else simp_arg_type.expr rule.rule
    save_info rule
    simp none none tt [simp_arg] [] l
#align tactic.interactive.simp_rw tactic.interactive.simp_rw

-- equivalent to `simp only [rule] at l`
add_tactic_doc
  { Name := "simp_rw"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.simp_rw]
    tags := ["simplification"] }

end Tactic.Interactive

