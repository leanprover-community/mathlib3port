/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon

! This file was ported from Lean 3 source module data.list.tfae
! leanprover-community/mathlib commit 134625f523e737f650a6ea7f0c82a6177e45e622
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic

/-!
# The Following Are Equivalent

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows to state that all propositions in a list are equivalent. It is used by
`tactic.tfae`.
`tfae l` means `∀ x ∈ l, ∀ y ∈ l, x ↔ y`. This is equivalent to `pairwise (↔) l`.
-/


namespace List

#print List.TFAE /-
/-- tfae: The Following (propositions) Are Equivalent.

The `tfae_have` and `tfae_finish` tactics can be useful in proofs with `tfae` goals.
-/
def TFAE (l : List Prop) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, x ↔ y
#align list.tfae List.TFAE
-/

#print List.tfae_nil /-
theorem tfae_nil : TFAE [] :=
  forall_mem_nil _
#align list.tfae_nil List.tfae_nil
-/

#print List.tfae_singleton /-
theorem tfae_singleton (p) : TFAE [p] := by simp [tfae, -eq_iff_iff]
#align list.tfae_singleton List.tfae_singleton
-/

#print List.tfae_cons_of_mem /-
theorem tfae_cons_of_mem {a b} {l : List Prop} (h : b ∈ l) : TFAE (a :: l) ↔ (a ↔ b) ∧ TFAE l :=
  ⟨fun H => ⟨H a (by simp) b (Or.inr h), fun p hp q hq => H _ (Or.inr hp) _ (Or.inr hq)⟩,
    by
    rintro ⟨ab, H⟩ p (rfl | hp) q (rfl | hq)
    · rfl
    · exact ab.trans (H _ h _ hq)
    · exact (ab.trans (H _ h _ hp)).symm
    · exact H _ hp _ hq⟩
#align list.tfae_cons_of_mem List.tfae_cons_of_mem
-/

#print List.tfae_cons_cons /-
theorem tfae_cons_cons {a b} {l : List Prop} : TFAE (a :: b :: l) ↔ (a ↔ b) ∧ TFAE (b :: l) :=
  tfae_cons_of_mem (Or.inl rfl)
#align list.tfae_cons_cons List.tfae_cons_cons
-/

#print List.tfae_of_forall /-
theorem tfae_of_forall (b : Prop) (l : List Prop) (h : ∀ a ∈ l, a ↔ b) : TFAE l :=
  fun a₁ h₁ a₂ h₂ => (h _ h₁).trans (h _ h₂).symm
#align list.tfae_of_forall List.tfae_of_forall
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:219:4: warning: unsupported binary notation `«->» -/
#print List.tfae_of_cycle /-
theorem tfae_of_cycle {a b} {l : List Prop} :
    List.Chain («->» · ·) a (b :: l) → (ilast' b l → a) → TFAE (a :: b :: l) :=
  by
  induction' l with c l IH generalizing a b <;>
    simp only [tfae_cons_cons, tfae_singleton, and_true_iff, chain_cons, chain.nil] at *
  · intro a b
    exact Iff.intro a b
  rintro ⟨ab, ⟨bc, ch⟩⟩ la
  have := IH ⟨bc, ch⟩ (ab ∘ la)
  exact ⟨⟨ab, la ∘ (this.2 c (Or.inl rfl) _ (ilast'_mem _ _)).1 ∘ bc⟩, this⟩
#align list.tfae_of_cycle List.tfae_of_cycle
-/

#print List.TFAE.out /-
theorem TFAE.out {l} (h : TFAE l) (n₁ n₂) {a b} (h₁ : List.get? l n₁ = some a := by rfl)
    (h₂ : List.get? l n₂ = some b := by rfl) : a ↔ b :=
  h _ (List.get?_mem h₁) _ (List.get?_mem h₂)
#align list.tfae.out List.TFAE.out
-/

end List

