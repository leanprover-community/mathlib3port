/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.sum.interval
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sum.Order
import Mathbin.Order.LocallyFinite

/-!
# Finite intervals in a disjoint union

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for the disjoint sum of two orders.

## TODO

Do the same for the lexicographic sum of orders.
-/


open Function Sum

namespace Finset

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type _}

section SumLift₂

variable (f f₁ g₁ : α₁ → β₁ → Finset γ₁) (g f₂ g₂ : α₂ → β₂ → Finset γ₂)

#print Finset.sumLift₂ /-
/-- Lifts maps `α₁ → β₁ → finset γ₁` and `α₂ → β₂ → finset γ₂` to a map
`α₁ ⊕ α₂ → β₁ ⊕ β₂ → finset (γ₁ ⊕ γ₂)`. Could be generalized to `alternative` functors if we can
make sure to keep computability and universe polymorphism. -/
@[simp]
def sumLift₂ : ∀ (a : Sum α₁ α₂) (b : Sum β₁ β₂), Finset (Sum γ₁ γ₂)
  | inl a, inl b => (f a b).map Embedding.inl
  | inl a, inr b => ∅
  | inr a, inl b => ∅
  | inr a, inr b => (g a b).map Embedding.inr
#align finset.sum_lift₂ Finset.sumLift₂
-/

variable {f f₁ g₁ g f₂ g₂} {a : Sum α₁ α₂} {b : Sum β₁ β₂} {c : Sum γ₁ γ₂}

/- warning: finset.mem_sum_lift₂ -> Finset.mem_sumLift₂ is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} {γ₁ : Type.{u5}} {γ₂ : Type.{u6}} {f : α₁ -> β₁ -> (Finset.{u5} γ₁)} {g : α₂ -> β₂ -> (Finset.{u6} γ₂)} {a : Sum.{u1, u2} α₁ α₂} {b : Sum.{u3, u4} β₁ β₂} {c : Sum.{u5, u6} γ₁ γ₂}, Iff (Membership.Mem.{max u5 u6, max u5 u6} (Sum.{u5, u6} γ₁ γ₂) (Finset.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Finset.hasMem.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) c (Finset.sumLift₂.{u1, u2, u3, u4, u5, u6} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b)) (Or (Exists.{succ u1} α₁ (fun (a₁ : α₁) => Exists.{succ u3} β₁ (fun (b₁ : β₁) => Exists.{succ u5} γ₁ (fun (c₁ : γ₁) => And (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α₁ α₂) a (Sum.inl.{u1, u2} α₁ α₂ a₁)) (And (Eq.{max (succ u3) (succ u4)} (Sum.{u3, u4} β₁ β₂) b (Sum.inl.{u3, u4} β₁ β₂ b₁)) (And (Eq.{max (succ u5) (succ u6)} (Sum.{u5, u6} γ₁ γ₂) c (Sum.inl.{u5, u6} γ₁ γ₂ c₁)) (Membership.Mem.{u5, u5} γ₁ (Finset.{u5} γ₁) (Finset.hasMem.{u5} γ₁) c₁ (f a₁ b₁)))))))) (Exists.{succ u2} α₂ (fun (a₂ : α₂) => Exists.{succ u4} β₂ (fun (b₂ : β₂) => Exists.{succ u6} γ₂ (fun (c₂ : γ₂) => And (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α₁ α₂) a (Sum.inr.{u1, u2} α₁ α₂ a₂)) (And (Eq.{max (succ u3) (succ u4)} (Sum.{u3, u4} β₁ β₂) b (Sum.inr.{u3, u4} β₁ β₂ b₂)) (And (Eq.{max (succ u5) (succ u6)} (Sum.{u5, u6} γ₁ γ₂) c (Sum.inr.{u5, u6} γ₁ γ₂ c₂)) (Membership.Mem.{u6, u6} γ₂ (Finset.{u6} γ₂) (Finset.hasMem.{u6} γ₂) c₂ (g a₂ b₂)))))))))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} {γ₁ : Type.{u6}} {γ₂ : Type.{u5}} {f : α₁ -> β₁ -> (Finset.{u6} γ₁)} {g : α₂ -> β₂ -> (Finset.{u5} γ₂)} {a : Sum.{u4, u3} α₁ α₂} {b : Sum.{u2, u1} β₁ β₂} {c : Sum.{u6, u5} γ₁ γ₂}, Iff (Membership.mem.{max u6 u5, max u5 u6} (Sum.{u6, u5} γ₁ γ₂) (Finset.{max u5 u6} (Sum.{u6, u5} γ₁ γ₂)) (Finset.instMembershipFinset.{max u6 u5} (Sum.{u6, u5} γ₁ γ₂)) c (Finset.sumLift₂.{u4, u3, u2, u1, u6, u5} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b)) (Or (Exists.{succ u4} α₁ (fun (a₁ : α₁) => Exists.{succ u2} β₁ (fun (b₁ : β₁) => Exists.{succ u6} γ₁ (fun (c₁ : γ₁) => And (Eq.{max (succ u4) (succ u3)} (Sum.{u4, u3} α₁ α₂) a (Sum.inl.{u4, u3} α₁ α₂ a₁)) (And (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} β₁ β₂) b (Sum.inl.{u2, u1} β₁ β₂ b₁)) (And (Eq.{max (succ u6) (succ u5)} (Sum.{u6, u5} γ₁ γ₂) c (Sum.inl.{u6, u5} γ₁ γ₂ c₁)) (Membership.mem.{u6, u6} γ₁ (Finset.{u6} γ₁) (Finset.instMembershipFinset.{u6} γ₁) c₁ (f a₁ b₁)))))))) (Exists.{succ u3} α₂ (fun (a₂ : α₂) => Exists.{succ u1} β₂ (fun (b₂ : β₂) => Exists.{succ u5} γ₂ (fun (c₂ : γ₂) => And (Eq.{max (succ u4) (succ u3)} (Sum.{u4, u3} α₁ α₂) a (Sum.inr.{u4, u3} α₁ α₂ a₂)) (And (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} β₁ β₂) b (Sum.inr.{u2, u1} β₁ β₂ b₂)) (And (Eq.{max (succ u6) (succ u5)} (Sum.{u6, u5} γ₁ γ₂) c (Sum.inr.{u6, u5} γ₁ γ₂ c₂)) (Membership.mem.{u5, u5} γ₂ (Finset.{u5} γ₂) (Finset.instMembershipFinset.{u5} γ₂) c₂ (g a₂ b₂)))))))))
Case conversion may be inaccurate. Consider using '#align finset.mem_sum_lift₂ Finset.mem_sumLift₂ₓ'. -/
theorem mem_sumLift₂ :
    c ∈ sumLift₂ f g a b ↔
      (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f a₁ b₁) ∨
        ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g a₂ b₂ :=
  by
  constructor
  · cases a <;> cases b
    · rw [sum_lift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine' fun h => (not_mem_empty _ h).elim
    · refine' fun h => (not_mem_empty _ h).elim
    · rw [sum_lift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩
  · rintro (⟨a, b, c, rfl, rfl, rfl, h⟩ | ⟨a, b, c, rfl, rfl, rfl, h⟩) <;> exact mem_map_of_mem _ h
#align finset.mem_sum_lift₂ Finset.mem_sumLift₂

/- warning: finset.inl_mem_sum_lift₂ -> Finset.inl_mem_sumLift₂ is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} {γ₁ : Type.{u5}} {γ₂ : Type.{u6}} {f : α₁ -> β₁ -> (Finset.{u5} γ₁)} {g : α₂ -> β₂ -> (Finset.{u6} γ₂)} {a : Sum.{u1, u2} α₁ α₂} {b : Sum.{u3, u4} β₁ β₂} {c₁ : γ₁}, Iff (Membership.Mem.{max u5 u6, max u5 u6} (Sum.{u5, u6} γ₁ γ₂) (Finset.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Finset.hasMem.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Sum.inl.{u5, u6} γ₁ γ₂ c₁) (Finset.sumLift₂.{u1, u2, u3, u4, u5, u6} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b)) (Exists.{succ u1} α₁ (fun (a₁ : α₁) => Exists.{succ u3} β₁ (fun (b₁ : β₁) => And (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α₁ α₂) a (Sum.inl.{u1, u2} α₁ α₂ a₁)) (And (Eq.{max (succ u3) (succ u4)} (Sum.{u3, u4} β₁ β₂) b (Sum.inl.{u3, u4} β₁ β₂ b₁)) (Membership.Mem.{u5, u5} γ₁ (Finset.{u5} γ₁) (Finset.hasMem.{u5} γ₁) c₁ (f a₁ b₁))))))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} {γ₁ : Type.{u5}} {γ₂ : Type.{u6}} {f : α₁ -> β₁ -> (Finset.{u5} γ₁)} {g : α₂ -> β₂ -> (Finset.{u6} γ₂)} {a : Sum.{u4, u3} α₁ α₂} {b : Sum.{u2, u1} β₁ β₂} {c₁ : γ₁}, Iff (Membership.mem.{max u6 u5, max u6 u5} (Sum.{u5, u6} γ₁ γ₂) (Finset.{max u6 u5} (Sum.{u5, u6} γ₁ γ₂)) (Finset.instMembershipFinset.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Sum.inl.{u5, u6} γ₁ γ₂ c₁) (Finset.sumLift₂.{u4, u3, u2, u1, u5, u6} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b)) (Exists.{succ u4} α₁ (fun (a₁ : α₁) => Exists.{succ u2} β₁ (fun (b₁ : β₁) => And (Eq.{max (succ u4) (succ u3)} (Sum.{u4, u3} α₁ α₂) a (Sum.inl.{u4, u3} α₁ α₂ a₁)) (And (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} β₁ β₂) b (Sum.inl.{u2, u1} β₁ β₂ b₁)) (Membership.mem.{u5, u5} γ₁ (Finset.{u5} γ₁) (Finset.instMembershipFinset.{u5} γ₁) c₁ (f a₁ b₁))))))
Case conversion may be inaccurate. Consider using '#align finset.inl_mem_sum_lift₂ Finset.inl_mem_sumLift₂ₓ'. -/
theorem inl_mem_sumLift₂ {c₁ : γ₁} :
    inl c₁ ∈ sumLift₂ f g a b ↔ ∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f a₁ b₁ :=
  by
  rw [mem_sum_lift₂, or_iff_left]
  simp only [exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inl_ne_inr h
#align finset.inl_mem_sum_lift₂ Finset.inl_mem_sumLift₂

/- warning: finset.inr_mem_sum_lift₂ -> Finset.inr_mem_sumLift₂ is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} {γ₁ : Type.{u5}} {γ₂ : Type.{u6}} {f : α₁ -> β₁ -> (Finset.{u5} γ₁)} {g : α₂ -> β₂ -> (Finset.{u6} γ₂)} {a : Sum.{u1, u2} α₁ α₂} {b : Sum.{u3, u4} β₁ β₂} {c₂ : γ₂}, Iff (Membership.Mem.{max u5 u6, max u5 u6} (Sum.{u5, u6} γ₁ γ₂) (Finset.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Finset.hasMem.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Sum.inr.{u5, u6} γ₁ γ₂ c₂) (Finset.sumLift₂.{u1, u2, u3, u4, u5, u6} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b)) (Exists.{succ u2} α₂ (fun (a₂ : α₂) => Exists.{succ u4} β₂ (fun (b₂ : β₂) => And (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α₁ α₂) a (Sum.inr.{u1, u2} α₁ α₂ a₂)) (And (Eq.{max (succ u3) (succ u4)} (Sum.{u3, u4} β₁ β₂) b (Sum.inr.{u3, u4} β₁ β₂ b₂)) (Membership.Mem.{u6, u6} γ₂ (Finset.{u6} γ₂) (Finset.hasMem.{u6} γ₂) c₂ (g a₂ b₂))))))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} {γ₁ : Type.{u5}} {γ₂ : Type.{u6}} {f : α₁ -> β₁ -> (Finset.{u5} γ₁)} {g : α₂ -> β₂ -> (Finset.{u6} γ₂)} {a : Sum.{u4, u3} α₁ α₂} {b : Sum.{u2, u1} β₁ β₂} {c₂ : γ₂}, Iff (Membership.mem.{max u6 u5, max u6 u5} (Sum.{u5, u6} γ₁ γ₂) (Finset.{max u6 u5} (Sum.{u5, u6} γ₁ γ₂)) (Finset.instMembershipFinset.{max u6 u5} (Sum.{u5, u6} γ₁ γ₂)) (Sum.inr.{u5, u6} γ₁ γ₂ c₂) (Finset.sumLift₂.{u4, u3, u2, u1, u5, u6} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b)) (Exists.{succ u3} α₂ (fun (a₂ : α₂) => Exists.{succ u1} β₂ (fun (b₂ : β₂) => And (Eq.{max (succ u4) (succ u3)} (Sum.{u4, u3} α₁ α₂) a (Sum.inr.{u4, u3} α₁ α₂ a₂)) (And (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} β₁ β₂) b (Sum.inr.{u2, u1} β₁ β₂ b₂)) (Membership.mem.{u6, u6} γ₂ (Finset.{u6} γ₂) (Finset.instMembershipFinset.{u6} γ₂) c₂ (g a₂ b₂))))))
Case conversion may be inaccurate. Consider using '#align finset.inr_mem_sum_lift₂ Finset.inr_mem_sumLift₂ₓ'. -/
theorem inr_mem_sumLift₂ {c₂ : γ₂} :
    inr c₂ ∈ sumLift₂ f g a b ↔ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ g a₂ b₂ :=
  by
  rw [mem_sum_lift₂, or_iff_right]
  simp only [exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inr_ne_inl h
#align finset.inr_mem_sum_lift₂ Finset.inr_mem_sumLift₂

/- warning: finset.sum_lift₂_eq_empty -> Finset.sumLift₂_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} {γ₁ : Type.{u5}} {γ₂ : Type.{u6}} {f : α₁ -> β₁ -> (Finset.{u5} γ₁)} {g : α₂ -> β₂ -> (Finset.{u6} γ₂)} {a : Sum.{u1, u2} α₁ α₂} {b : Sum.{u3, u4} β₁ β₂}, Iff (Eq.{succ (max u5 u6)} (Finset.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Finset.sumLift₂.{u1, u2, u3, u4, u5, u6} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b) (EmptyCollection.emptyCollection.{max u5 u6} (Finset.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Finset.hasEmptyc.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)))) (And (forall (a₁ : α₁) (b₁ : β₁), (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α₁ α₂) a (Sum.inl.{u1, u2} α₁ α₂ a₁)) -> (Eq.{max (succ u3) (succ u4)} (Sum.{u3, u4} β₁ β₂) b (Sum.inl.{u3, u4} β₁ β₂ b₁)) -> (Eq.{succ u5} (Finset.{u5} γ₁) (f a₁ b₁) (EmptyCollection.emptyCollection.{u5} (Finset.{u5} γ₁) (Finset.hasEmptyc.{u5} γ₁)))) (forall (a₂ : α₂) (b₂ : β₂), (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α₁ α₂) a (Sum.inr.{u1, u2} α₁ α₂ a₂)) -> (Eq.{max (succ u3) (succ u4)} (Sum.{u3, u4} β₁ β₂) b (Sum.inr.{u3, u4} β₁ β₂ b₂)) -> (Eq.{succ u6} (Finset.{u6} γ₂) (g a₂ b₂) (EmptyCollection.emptyCollection.{u6} (Finset.{u6} γ₂) (Finset.hasEmptyc.{u6} γ₂)))))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} {γ₁ : Type.{u6}} {γ₂ : Type.{u5}} {f : α₁ -> β₁ -> (Finset.{u6} γ₁)} {g : α₂ -> β₂ -> (Finset.{u5} γ₂)} {a : Sum.{u4, u3} α₁ α₂} {b : Sum.{u2, u1} β₁ β₂}, Iff (Eq.{max (succ u6) (succ u5)} (Finset.{max u5 u6} (Sum.{u6, u5} γ₁ γ₂)) (Finset.sumLift₂.{u4, u3, u2, u1, u6, u5} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b) (EmptyCollection.emptyCollection.{max u6 u5} (Finset.{max u5 u6} (Sum.{u6, u5} γ₁ γ₂)) (Finset.instEmptyCollectionFinset.{max u6 u5} (Sum.{u6, u5} γ₁ γ₂)))) (And (forall (a₁ : α₁) (b₁ : β₁), (Eq.{max (succ u4) (succ u3)} (Sum.{u4, u3} α₁ α₂) a (Sum.inl.{u4, u3} α₁ α₂ a₁)) -> (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} β₁ β₂) b (Sum.inl.{u2, u1} β₁ β₂ b₁)) -> (Eq.{succ u6} (Finset.{u6} γ₁) (f a₁ b₁) (EmptyCollection.emptyCollection.{u6} (Finset.{u6} γ₁) (Finset.instEmptyCollectionFinset.{u6} γ₁)))) (forall (a₂ : α₂) (b₂ : β₂), (Eq.{max (succ u4) (succ u3)} (Sum.{u4, u3} α₁ α₂) a (Sum.inr.{u4, u3} α₁ α₂ a₂)) -> (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} β₁ β₂) b (Sum.inr.{u2, u1} β₁ β₂ b₂)) -> (Eq.{succ u5} (Finset.{u5} γ₂) (g a₂ b₂) (EmptyCollection.emptyCollection.{u5} (Finset.{u5} γ₂) (Finset.instEmptyCollectionFinset.{u5} γ₂)))))
Case conversion may be inaccurate. Consider using '#align finset.sum_lift₂_eq_empty Finset.sumLift₂_eq_emptyₓ'. -/
theorem sumLift₂_eq_empty :
    sumLift₂ f g a b = ∅ ↔
      (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅) ∧
        ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → g a₂ b₂ = ∅ :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  ·
    constructor <;>
      · rintro a b rfl rfl
        exact map_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · rfl
  · rfl
  · exact map_eq_empty.2 (h.2 _ _ rfl rfl)
#align finset.sum_lift₂_eq_empty Finset.sumLift₂_eq_empty

/- warning: finset.sum_lift₂_nonempty -> Finset.sumLift₂_nonempty is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} {γ₁ : Type.{u5}} {γ₂ : Type.{u6}} {f : α₁ -> β₁ -> (Finset.{u5} γ₁)} {g : α₂ -> β₂ -> (Finset.{u6} γ₂)} {a : Sum.{u1, u2} α₁ α₂} {b : Sum.{u3, u4} β₁ β₂}, Iff (Finset.Nonempty.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂) (Finset.sumLift₂.{u1, u2, u3, u4, u5, u6} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b)) (Or (Exists.{succ u1} α₁ (fun (a₁ : α₁) => Exists.{succ u3} β₁ (fun (b₁ : β₁) => And (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α₁ α₂) a (Sum.inl.{u1, u2} α₁ α₂ a₁)) (And (Eq.{max (succ u3) (succ u4)} (Sum.{u3, u4} β₁ β₂) b (Sum.inl.{u3, u4} β₁ β₂ b₁)) (Finset.Nonempty.{u5} γ₁ (f a₁ b₁)))))) (Exists.{succ u2} α₂ (fun (a₂ : α₂) => Exists.{succ u4} β₂ (fun (b₂ : β₂) => And (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α₁ α₂) a (Sum.inr.{u1, u2} α₁ α₂ a₂)) (And (Eq.{max (succ u3) (succ u4)} (Sum.{u3, u4} β₁ β₂) b (Sum.inr.{u3, u4} β₁ β₂ b₂)) (Finset.Nonempty.{u6} γ₂ (g a₂ b₂)))))))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} {γ₁ : Type.{u6}} {γ₂ : Type.{u5}} {f : α₁ -> β₁ -> (Finset.{u6} γ₁)} {g : α₂ -> β₂ -> (Finset.{u5} γ₂)} {a : Sum.{u4, u3} α₁ α₂} {b : Sum.{u2, u1} β₁ β₂}, Iff (Finset.Nonempty.{max u6 u5} (Sum.{u6, u5} γ₁ γ₂) (Finset.sumLift₂.{u4, u3, u2, u1, u6, u5} α₁ α₂ β₁ β₂ γ₁ γ₂ f g a b)) (Or (Exists.{succ u4} α₁ (fun (a₁ : α₁) => Exists.{succ u2} β₁ (fun (b₁ : β₁) => And (Eq.{max (succ u4) (succ u3)} (Sum.{u4, u3} α₁ α₂) a (Sum.inl.{u4, u3} α₁ α₂ a₁)) (And (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} β₁ β₂) b (Sum.inl.{u2, u1} β₁ β₂ b₁)) (Finset.Nonempty.{u6} γ₁ (f a₁ b₁)))))) (Exists.{succ u3} α₂ (fun (a₂ : α₂) => Exists.{succ u1} β₂ (fun (b₂ : β₂) => And (Eq.{max (succ u4) (succ u3)} (Sum.{u4, u3} α₁ α₂) a (Sum.inr.{u4, u3} α₁ α₂ a₂)) (And (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} β₁ β₂) b (Sum.inr.{u2, u1} β₁ β₂ b₂)) (Finset.Nonempty.{u5} γ₂ (g a₂ b₂)))))))
Case conversion may be inaccurate. Consider using '#align finset.sum_lift₂_nonempty Finset.sumLift₂_nonemptyₓ'. -/
theorem sumLift₂_nonempty :
    (sumLift₂ f g a b).Nonempty ↔
      (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).Nonempty) ∨
        ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (g a₂ b₂).Nonempty :=
  by simp [nonempty_iff_ne_empty, sum_lift₂_eq_empty, not_and_or]
#align finset.sum_lift₂_nonempty Finset.sumLift₂_nonempty

/- warning: finset.sum_lift₂_mono -> Finset.sumLift₂_mono is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} {γ₁ : Type.{u5}} {γ₂ : Type.{u6}} {f₁ : α₁ -> β₁ -> (Finset.{u5} γ₁)} {g₁ : α₁ -> β₁ -> (Finset.{u5} γ₁)} {f₂ : α₂ -> β₂ -> (Finset.{u6} γ₂)} {g₂ : α₂ -> β₂ -> (Finset.{u6} γ₂)}, (forall (a : α₁) (b : β₁), HasSubset.Subset.{u5} (Finset.{u5} γ₁) (Finset.hasSubset.{u5} γ₁) (f₁ a b) (g₁ a b)) -> (forall (a : α₂) (b : β₂), HasSubset.Subset.{u6} (Finset.{u6} γ₂) (Finset.hasSubset.{u6} γ₂) (f₂ a b) (g₂ a b)) -> (forall (a : Sum.{u1, u2} α₁ α₂) (b : Sum.{u3, u4} β₁ β₂), HasSubset.Subset.{max u5 u6} (Finset.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Finset.hasSubset.{max u5 u6} (Sum.{u5, u6} γ₁ γ₂)) (Finset.sumLift₂.{u1, u2, u3, u4, u5, u6} α₁ α₂ β₁ β₂ γ₁ γ₂ f₁ f₂ a b) (Finset.sumLift₂.{u1, u2, u3, u4, u5, u6} α₁ α₂ β₁ β₂ γ₁ γ₂ g₁ g₂ a b))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} {γ₁ : Type.{u6}} {γ₂ : Type.{u5}} {f₁ : α₁ -> β₁ -> (Finset.{u6} γ₁)} {g₁ : α₁ -> β₁ -> (Finset.{u6} γ₁)} {f₂ : α₂ -> β₂ -> (Finset.{u5} γ₂)} {g₂ : α₂ -> β₂ -> (Finset.{u5} γ₂)}, (forall (a : α₁) (b : β₁), HasSubset.Subset.{u6} (Finset.{u6} γ₁) (Finset.instHasSubsetFinset.{u6} γ₁) (f₁ a b) (g₁ a b)) -> (forall (a : α₂) (b : β₂), HasSubset.Subset.{u5} (Finset.{u5} γ₂) (Finset.instHasSubsetFinset.{u5} γ₂) (f₂ a b) (g₂ a b)) -> (forall (a : Sum.{u4, u3} α₁ α₂) (b : Sum.{u2, u1} β₁ β₂), HasSubset.Subset.{max u5 u6} (Finset.{max u5 u6} (Sum.{u6, u5} γ₁ γ₂)) (Finset.instHasSubsetFinset.{max u6 u5} (Sum.{u6, u5} γ₁ γ₂)) (Finset.sumLift₂.{u4, u3, u2, u1, u6, u5} α₁ α₂ β₁ β₂ γ₁ γ₂ f₁ f₂ a b) (Finset.sumLift₂.{u4, u3, u2, u1, u6, u5} α₁ α₂ β₁ β₂ γ₁ γ₂ g₁ g₂ a b))
Case conversion may be inaccurate. Consider using '#align finset.sum_lift₂_mono Finset.sumLift₂_monoₓ'. -/
theorem sumLift₂_mono (h₁ : ∀ a b, f₁ a b ⊆ g₁ a b) (h₂ : ∀ a b, f₂ a b ⊆ g₂ a b) :
    ∀ a b, sumLift₂ f₁ f₂ a b ⊆ sumLift₂ g₁ g₂ a b
  | inl a, inl b => map_subset_map.2 (h₁ _ _)
  | inl a, inr b => Subset.rfl
  | inr a, inl b => Subset.rfl
  | inr a, inr b => map_subset_map.2 (h₂ _ _)
#align finset.sum_lift₂_mono Finset.sumLift₂_mono

end SumLift₂

end Finset

open Finset Function

namespace Sum

variable {α β : Type _}

/-! ### Disjoint sum of orders -/


section Disjoint

variable [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]

instance : LocallyFiniteOrder (Sum α β)
    where
  finsetIcc := sumLift₂ Icc Icc
  finsetIco := sumLift₂ Ico Ico
  finsetIoc := sumLift₂ Ioc Ioc
  finsetIoo := sumLift₂ Ioo Ioo
  finset_mem_Icc := by rintro (a | a) (b | b) (x | x) <;> simp
  finset_mem_Ico := by rintro (a | a) (b | b) (x | x) <;> simp
  finset_mem_Ioc := by rintro (a | a) (b | b) (x | x) <;> simp
  finset_mem_Ioo := by rintro (a | a) (b | b) (x | x) <;> simp

variable (a₁ a₂ : α) (b₁ b₂ : β) (a b : Sum α β)

/- warning: sum.Icc_inl_inl -> Sum.Icc_inl_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₁ : α) (a₂ : α), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Icc.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u1, u2} α β a₁) (Sum.inl.{u1, u2} α β a₂)) (Finset.map.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Function.Embedding.inl.{u1, u2} α β) (Finset.Icc.{u1} α _inst_1 _inst_3 a₁ a₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₁ : α) (a₂ : α), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.Icc.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u2, u1} α β a₁) (Sum.inl.{u2, u1} α β a₂)) (Finset.map.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Function.Embedding.inl.{u2, u1} α β) (Finset.Icc.{u2} α _inst_1 _inst_3 a₁ a₂))
Case conversion may be inaccurate. Consider using '#align sum.Icc_inl_inl Sum.Icc_inl_inlₓ'. -/
theorem Icc_inl_inl : Icc (inl a₁ : Sum α β) (inl a₂) = (Icc a₁ a₂).map Embedding.inl :=
  rfl
#align sum.Icc_inl_inl Sum.Icc_inl_inl

/- warning: sum.Ico_inl_inl -> Sum.Ico_inl_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₁ : α) (a₂ : α), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ico.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u1, u2} α β a₁) (Sum.inl.{u1, u2} α β a₂)) (Finset.map.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Function.Embedding.inl.{u1, u2} α β) (Finset.Ico.{u1} α _inst_1 _inst_3 a₁ a₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₁ : α) (a₂ : α), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.Ico.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u2, u1} α β a₁) (Sum.inl.{u2, u1} α β a₂)) (Finset.map.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Function.Embedding.inl.{u2, u1} α β) (Finset.Ico.{u2} α _inst_1 _inst_3 a₁ a₂))
Case conversion may be inaccurate. Consider using '#align sum.Ico_inl_inl Sum.Ico_inl_inlₓ'. -/
theorem Ico_inl_inl : Ico (inl a₁ : Sum α β) (inl a₂) = (Ico a₁ a₂).map Embedding.inl :=
  rfl
#align sum.Ico_inl_inl Sum.Ico_inl_inl

/- warning: sum.Ioc_inl_inl -> Sum.Ioc_inl_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₁ : α) (a₂ : α), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ioc.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u1, u2} α β a₁) (Sum.inl.{u1, u2} α β a₂)) (Finset.map.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Function.Embedding.inl.{u1, u2} α β) (Finset.Ioc.{u1} α _inst_1 _inst_3 a₁ a₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₁ : α) (a₂ : α), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.Ioc.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u2, u1} α β a₁) (Sum.inl.{u2, u1} α β a₂)) (Finset.map.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Function.Embedding.inl.{u2, u1} α β) (Finset.Ioc.{u2} α _inst_1 _inst_3 a₁ a₂))
Case conversion may be inaccurate. Consider using '#align sum.Ioc_inl_inl Sum.Ioc_inl_inlₓ'. -/
theorem Ioc_inl_inl : Ioc (inl a₁ : Sum α β) (inl a₂) = (Ioc a₁ a₂).map Embedding.inl :=
  rfl
#align sum.Ioc_inl_inl Sum.Ioc_inl_inl

/- warning: sum.Ioo_inl_inl -> Sum.Ioo_inl_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₁ : α) (a₂ : α), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ioo.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u1, u2} α β a₁) (Sum.inl.{u1, u2} α β a₂)) (Finset.map.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Function.Embedding.inl.{u1, u2} α β) (Finset.Ioo.{u1} α _inst_1 _inst_3 a₁ a₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₁ : α) (a₂ : α), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.Ioo.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u2, u1} α β a₁) (Sum.inl.{u2, u1} α β a₂)) (Finset.map.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Function.Embedding.inl.{u2, u1} α β) (Finset.Ioo.{u2} α _inst_1 _inst_3 a₁ a₂))
Case conversion may be inaccurate. Consider using '#align sum.Ioo_inl_inl Sum.Ioo_inl_inlₓ'. -/
theorem Ioo_inl_inl : Ioo (inl a₁ : Sum α β) (inl a₂) = (Ioo a₁ a₂).map Embedding.inl :=
  rfl
#align sum.Ioo_inl_inl Sum.Ioo_inl_inl

/- warning: sum.Icc_inl_inr -> Sum.Icc_inl_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₁ : α) (b₂ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Icc.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u1, u2} α β a₁) (Sum.inr.{u1, u2} α β b₂)) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₁ : α) (b₂ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.Icc.{max u1 u2} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u2, u1} α β a₁) (Sum.inr.{u2, u1} α β b₂)) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align sum.Icc_inl_inr Sum.Icc_inl_inrₓ'. -/
@[simp]
theorem Icc_inl_inr : Icc (inl a₁) (inr b₂) = ∅ :=
  rfl
#align sum.Icc_inl_inr Sum.Icc_inl_inr

/- warning: sum.Ico_inl_inr -> Sum.Ico_inl_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₁ : α) (b₂ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ico.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u1, u2} α β a₁) (Sum.inr.{u1, u2} α β b₂)) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₁ : α) (b₂ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.Ico.{max u1 u2} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u2, u1} α β a₁) (Sum.inr.{u2, u1} α β b₂)) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align sum.Ico_inl_inr Sum.Ico_inl_inrₓ'. -/
@[simp]
theorem Ico_inl_inr : Ico (inl a₁) (inr b₂) = ∅ :=
  rfl
#align sum.Ico_inl_inr Sum.Ico_inl_inr

/- warning: sum.Ioc_inl_inr -> Sum.Ioc_inl_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₁ : α) (b₂ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ioc.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u1, u2} α β a₁) (Sum.inr.{u1, u2} α β b₂)) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₁ : α) (b₂ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.Ioc.{max u1 u2} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u2, u1} α β a₁) (Sum.inr.{u2, u1} α β b₂)) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align sum.Ioc_inl_inr Sum.Ioc_inl_inrₓ'. -/
@[simp]
theorem Ioc_inl_inr : Ioc (inl a₁) (inr b₂) = ∅ :=
  rfl
#align sum.Ioc_inl_inr Sum.Ioc_inl_inr

/- warning: sum.Ioo_inl_inr -> Sum.Ioo_inl_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₁ : α) (b₂ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ioo.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u1, u2} α β a₁) (Sum.inr.{u1, u2} α β b₂)) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₁ : α) (b₂ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.Ioo.{max u1 u2} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inl.{u2, u1} α β a₁) (Sum.inr.{u2, u1} α β b₂)) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align sum.Ioo_inl_inr Sum.Ioo_inl_inrₓ'. -/
@[simp]
theorem Ioo_inl_inr : Ioo (inl a₁) (inr b₂) = ∅ :=
  rfl
#align sum.Ioo_inl_inr Sum.Ioo_inl_inr

/- warning: sum.Icc_inr_inl -> Sum.Icc_inr_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₂ : α) (b₁ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Icc.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u1, u2} α β b₁) (Sum.inl.{u1, u2} α β a₂)) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₂ : α) (b₁ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.Icc.{max u1 u2} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u2, u1} α β b₁) (Sum.inl.{u2, u1} α β a₂)) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align sum.Icc_inr_inl Sum.Icc_inr_inlₓ'. -/
@[simp]
theorem Icc_inr_inl : Icc (inr b₁) (inl a₂) = ∅ :=
  rfl
#align sum.Icc_inr_inl Sum.Icc_inr_inl

/- warning: sum.Ico_inr_inl -> Sum.Ico_inr_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₂ : α) (b₁ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ico.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u1, u2} α β b₁) (Sum.inl.{u1, u2} α β a₂)) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₂ : α) (b₁ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.Ico.{max u1 u2} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u2, u1} α β b₁) (Sum.inl.{u2, u1} α β a₂)) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align sum.Ico_inr_inl Sum.Ico_inr_inlₓ'. -/
@[simp]
theorem Ico_inr_inl : Ico (inr b₁) (inl a₂) = ∅ :=
  rfl
#align sum.Ico_inr_inl Sum.Ico_inr_inl

/- warning: sum.Ioc_inr_inl -> Sum.Ioc_inr_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₂ : α) (b₁ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ioc.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u1, u2} α β b₁) (Sum.inl.{u1, u2} α β a₂)) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₂ : α) (b₁ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.Ioc.{max u1 u2} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u2, u1} α β b₁) (Sum.inl.{u2, u1} α β a₂)) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align sum.Ioc_inr_inl Sum.Ioc_inr_inlₓ'. -/
@[simp]
theorem Ioc_inr_inl : Ioc (inr b₁) (inl a₂) = ∅ :=
  rfl
#align sum.Ioc_inr_inl Sum.Ioc_inr_inl

/- warning: sum.Ioo_inr_inl -> Sum.Ioo_inr_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (a₂ : α) (b₁ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ioo.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u1, u2} α β b₁) (Sum.inl.{u1, u2} α β a₂)) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (a₂ : α) (b₁ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.Ioo.{max u1 u2} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u2, u1} α β b₁) (Sum.inl.{u2, u1} α β a₂)) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align sum.Ioo_inr_inl Sum.Ioo_inr_inlₓ'. -/
@[simp]
theorem Ioo_inr_inl : Ioo (inr b₁) (inl a₂) = ∅ :=
  rfl
#align sum.Ioo_inr_inl Sum.Ioo_inr_inl

/- warning: sum.Icc_inr_inr -> Sum.Icc_inr_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (b₁ : β) (b₂ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Icc.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u1, u2} α β b₁) (Sum.inr.{u1, u2} α β b₂)) (Finset.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Function.Embedding.inr.{u1, u2} α β) (Finset.Icc.{u2} β _inst_2 _inst_4 b₁ b₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (b₁ : β) (b₂ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.Icc.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u2, u1} α β b₁) (Sum.inr.{u2, u1} α β b₂)) (Finset.map.{u1, max u1 u2} β (Sum.{u2, u1} α β) (Function.Embedding.inr.{u2, u1} α β) (Finset.Icc.{u1} β _inst_2 _inst_4 b₁ b₂))
Case conversion may be inaccurate. Consider using '#align sum.Icc_inr_inr Sum.Icc_inr_inrₓ'. -/
theorem Icc_inr_inr : Icc (inr b₁ : Sum α β) (inr b₂) = (Icc b₁ b₂).map Embedding.inr :=
  rfl
#align sum.Icc_inr_inr Sum.Icc_inr_inr

/- warning: sum.Ico_inr_inr -> Sum.Ico_inr_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (b₁ : β) (b₂ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ico.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u1, u2} α β b₁) (Sum.inr.{u1, u2} α β b₂)) (Finset.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Function.Embedding.inr.{u1, u2} α β) (Finset.Ico.{u2} β _inst_2 _inst_4 b₁ b₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (b₁ : β) (b₂ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.Ico.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u2, u1} α β b₁) (Sum.inr.{u2, u1} α β b₂)) (Finset.map.{u1, max u1 u2} β (Sum.{u2, u1} α β) (Function.Embedding.inr.{u2, u1} α β) (Finset.Ico.{u1} β _inst_2 _inst_4 b₁ b₂))
Case conversion may be inaccurate. Consider using '#align sum.Ico_inr_inr Sum.Ico_inr_inrₓ'. -/
theorem Ico_inr_inr : Ico (inr b₁ : Sum α β) (inr b₂) = (Ico b₁ b₂).map Embedding.inr :=
  rfl
#align sum.Ico_inr_inr Sum.Ico_inr_inr

/- warning: sum.Ioc_inr_inr -> Sum.Ioc_inr_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (b₁ : β) (b₂ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ioc.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u1, u2} α β b₁) (Sum.inr.{u1, u2} α β b₂)) (Finset.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Function.Embedding.inr.{u1, u2} α β) (Finset.Ioc.{u2} β _inst_2 _inst_4 b₁ b₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (b₁ : β) (b₂ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.Ioc.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u2, u1} α β b₁) (Sum.inr.{u2, u1} α β b₂)) (Finset.map.{u1, max u1 u2} β (Sum.{u2, u1} α β) (Function.Embedding.inr.{u2, u1} α β) (Finset.Ioc.{u1} β _inst_2 _inst_4 b₁ b₂))
Case conversion may be inaccurate. Consider using '#align sum.Ioc_inr_inr Sum.Ioc_inr_inrₓ'. -/
theorem Ioc_inr_inr : Ioc (inr b₁ : Sum α β) (inr b₂) = (Ioc b₁ b₂).map Embedding.inr :=
  rfl
#align sum.Ioc_inr_inr Sum.Ioc_inr_inr

/- warning: sum.Ioo_inr_inr -> Sum.Ioo_inr_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : LocallyFiniteOrder.{u1} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u2} β _inst_2] (b₁ : β) (b₂ : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.Ioo.{max u1 u2} (Sum.{u1, u2} α β) (Sum.preorder.{u1, u2} α β _inst_1 _inst_2) (Sum.locallyFiniteOrder.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u1, u2} α β b₁) (Sum.inr.{u1, u2} α β b₂)) (Finset.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Function.Embedding.inr.{u1, u2} α β) (Finset.Ioo.{u2} β _inst_2 _inst_4 b₁ b₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : LocallyFiniteOrder.{u2} α _inst_1] [_inst_4 : LocallyFiniteOrder.{u1} β _inst_2] (b₁ : β) (b₂ : β), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.Ioo.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instPreorderSum.{u2, u1} α β _inst_1 _inst_2) (Sum.instLocallyFiniteOrderSumInstPreorderSum.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) (Sum.inr.{u2, u1} α β b₁) (Sum.inr.{u2, u1} α β b₂)) (Finset.map.{u1, max u1 u2} β (Sum.{u2, u1} α β) (Function.Embedding.inr.{u2, u1} α β) (Finset.Ioo.{u1} β _inst_2 _inst_4 b₁ b₂))
Case conversion may be inaccurate. Consider using '#align sum.Ioo_inr_inr Sum.Ioo_inr_inrₓ'. -/
theorem Ioo_inr_inr : Ioo (inr b₁ : Sum α β) (inr b₂) = (Ioo b₁ b₂).map Embedding.inr :=
  rfl
#align sum.Ioo_inr_inr Sum.Ioo_inr_inr

end Disjoint

end Sum

