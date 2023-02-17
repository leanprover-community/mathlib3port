/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module order.extension.linear
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Zorn
import Mathbin.Tactic.ByContra

/-!
# Extend a partial order to a linear order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file constructs a linear order which is an extension of the given partial order, using Zorn's
lemma.
-/


universe u

open Set Classical

open Classical

#print extend_partialOrder /-
/-- Any partial order can be extended to a linear order.
-/
theorem extend_partialOrder {α : Type u} (r : α → α → Prop) [IsPartialOrder α r] :
    ∃ (s : α → α → Prop)(_ : IsLinearOrder α s), r ≤ s :=
  by
  let S := { s | IsPartialOrder α s }
  have hS : ∀ c, c ⊆ S → IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub :=
    by
    rintro c hc₁ hc₂ s hs
    haveI := (hc₁ hs).1
    refine' ⟨Sup c, _, fun z hz => le_supₛ hz⟩
    refine'
        { refl := _
          trans := _
          antisymm := _ } <;>
      simp_rw [binary_relation_supₛ_iff]
    · intro x
      exact ⟨s, hs, refl x⟩
    · rintro x y z ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩
      haveI : IsPartialOrder _ _ := hc₁ h₁s₁
      haveI : IsPartialOrder _ _ := hc₁ h₁s₂
      cases hc₂.total h₁s₁ h₁s₂
      · exact ⟨s₂, h₁s₂, trans (h _ _ h₂s₁) h₂s₂⟩
      · exact ⟨s₁, h₁s₁, trans h₂s₁ (h _ _ h₂s₂)⟩
    · rintro x y ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩
      haveI : IsPartialOrder _ _ := hc₁ h₁s₁
      haveI : IsPartialOrder _ _ := hc₁ h₁s₂
      cases hc₂.total h₁s₁ h₁s₂
      · exact antisymm (h _ _ h₂s₁) h₂s₂
      · apply antisymm h₂s₁ (h _ _ h₂s₂)
  obtain ⟨s, hs₁ : IsPartialOrder _ _, rs, hs₂⟩ := zorn_nonempty_partialOrder₀ S hS r ‹_›
  skip
  refine' ⟨s, { Total := _ }, rs⟩
  intro x y
  by_contra' h
  let s' x' y' := s x' y' ∨ s x' x ∧ s y y'
  rw [← hs₂ s' _ fun _ _ => Or.inl] at h
  · apply h.1 (Or.inr ⟨refl _, refl _⟩)
  · refine'
      { refl := fun x => Or.inl (refl _)
        trans := _
        antisymm := _ }
    · rintro a b c (ab | ⟨ax : s a x, yb : s y b⟩) (bc | ⟨bx : s b x, yc : s y c⟩)
      · exact Or.inl (trans ab bc)
      · exact Or.inr ⟨trans ab bx, yc⟩
      · exact Or.inr ⟨ax, trans yb bc⟩
      · exact Or.inr ⟨ax, yc⟩
    · rintro a b (ab | ⟨ax : s a x, yb : s y b⟩) (ba | ⟨bx : s b x, ya : s y a⟩)
      · exact antisymm ab ba
      · exact (h.2 (trans ya (trans ab bx))).elim
      · exact (h.2 (trans yb (trans ba ax))).elim
      · exact (h.2 (trans yb bx)).elim
#align extend_partial_order extend_partialOrder
-/

#print LinearExtension /-
/-- A type alias for `α`, intended to extend a partial order on `α` to a linear order. -/
def LinearExtension (α : Type u) : Type u :=
  α
#align linear_extension LinearExtension
-/

noncomputable instance {α : Type u} [PartialOrder α] : LinearOrder (LinearExtension α)
    where
  le := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).some
  le_refl := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.some.1.1.1.1
  le_trans := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.some.1.1.2.1
  le_antisymm := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.some.1.2.1
  le_total := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.some.2.1
  decidableLe := Classical.decRel _

/- warning: to_linear_extension -> toLinearExtension is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], RelHom.{u1, u1} α (LinearExtension.{u1} α) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (LE.le.{u1} (LinearExtension.{u1} α) (Preorder.toLE.{u1} (LinearExtension.{u1} α) (PartialOrder.toPreorder.{u1} (LinearExtension.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (LinearExtension.{u1} α) (Lattice.toSemilatticeInf.{u1} (LinearExtension.{u1} α) (LinearOrder.toLattice.{u1} (LinearExtension.{u1} α) (LinearExtension.linearOrder.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], RelHom.{u1, u1} α (LinearExtension.{u1} α) (fun (x._@.Mathlib.Order.Extension.Linear._hyg.940 : α) (x._@.Mathlib.Order.Extension.Linear._hyg.942 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Order.Extension.Linear._hyg.940 x._@.Mathlib.Order.Extension.Linear._hyg.942) (fun (x._@.Mathlib.Order.Extension.Linear._hyg.964 : LinearExtension.{u1} α) (x._@.Mathlib.Order.Extension.Linear._hyg.966 : LinearExtension.{u1} α) => LE.le.{u1} (LinearExtension.{u1} α) (Preorder.toLE.{u1} (LinearExtension.{u1} α) (PartialOrder.toPreorder.{u1} (LinearExtension.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (LinearExtension.{u1} α) (Lattice.toSemilatticeInf.{u1} (LinearExtension.{u1} α) (DistribLattice.toLattice.{u1} (LinearExtension.{u1} α) (instDistribLattice.{u1} (LinearExtension.{u1} α) (instLinearOrderLinearExtension.{u1} α _inst_1))))))) x._@.Mathlib.Order.Extension.Linear._hyg.964 x._@.Mathlib.Order.Extension.Linear._hyg.966)
Case conversion may be inaccurate. Consider using '#align to_linear_extension toLinearExtensionₓ'. -/
/-- The embedding of `α` into `linear_extension α` as a relation homomorphism. -/
def toLinearExtension {α : Type u} [PartialOrder α] :
    ((· ≤ ·) : α → α → Prop) →r ((· ≤ ·) : LinearExtension α → LinearExtension α → Prop)
    where
  toFun x := x
  map_rel' a b := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.choose_spec _ _
#align to_linear_extension toLinearExtension

instance {α : Type u} [Inhabited α] : Inhabited (LinearExtension α) :=
  ⟨(default : α)⟩

