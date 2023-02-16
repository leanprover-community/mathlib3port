/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.filter.lift
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Bases

/-!
# Lift filters along filter and set functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Set

open Classical Filter

namespace Filter

variable {α : Type _} {β : Type _} {γ : Type _} {ι : Sort _}

section lift

#print Filter.lift /-
/-- A variant on `bind` using a function `g` taking a set instead of a member of `α`.
This is essentially a push-forward along a function mapping each set to a filter. -/
protected def lift (f : Filter α) (g : Set α → Filter β) :=
  ⨅ s ∈ f, g s
#align filter.lift Filter.lift
-/

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Set α → Filter β}

/- warning: filter.lift_top -> Filter.lift_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (g : (Set.{u1} α) -> (Filter.{u2} β)), Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α)) g) (g (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (g : (Set.{u2} α) -> (Filter.{u1} β)), Eq.{succ u1} (Filter.{u1} β) (Filter.lift.{u2, u1} α β (Top.top.{u2} (Filter.{u2} α) (Filter.instTopFilter.{u2} α)) g) (g (Set.univ.{u2} α))
Case conversion may be inaccurate. Consider using '#align filter.lift_top Filter.lift_topₓ'. -/
@[simp]
theorem lift_top (g : Set α → Filter β) : (⊤ : Filter α).lift g = g univ := by simp [Filter.lift]
#align filter.lift_top Filter.lift_top

/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type, see `filter.has_basis.lift`.
This lemma states the corresponding `mem_iff` statement without using a sigma type. -/
theorem HasBasis.mem_lift_iff {ι} {p : ι → Prop} {s : ι → Set α} {f : Filter α}
    (hf : f.HasBasis p s) {β : ι → Type _} {pg : ∀ i, β i → Prop} {sg : ∀ i, β i → Set γ}
    {g : Set α → Filter γ} (hg : ∀ i, (g <| s i).HasBasis (pg i) (sg i)) (gm : Monotone g)
    {s : Set γ} : s ∈ f.lift g ↔ ∃ (i : ι)(hi : p i)(x : β i)(hx : pg i x), sg i x ⊆ s :=
  by
  refine' (mem_binfi_of_directed _ ⟨univ, univ_sets _⟩).trans _
  · intro t₁ ht₁ t₂ ht₂
    exact ⟨t₁ ∩ t₂, inter_mem ht₁ ht₂, gm <| inter_subset_left _ _, gm <| inter_subset_right _ _⟩
  · simp only [← (hg _).mem_iff]
    exact hf.exists_iff fun t₁ t₂ ht H => gm ht H
#align filter.has_basis.mem_lift_iff Filter.HasBasis.mem_lift_iffₓ

/- warning: filter.has_basis.lift -> Filter.HasBasis.lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} {ι : Type.{u3}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {f : Filter.{u1} α}, (Filter.HasBasis.{u1, succ u3} α ι f p s) -> (forall {β : ι -> Type.{u4}} {pg : forall (i : ι), (β i) -> Prop} {sg : forall (i : ι), (β i) -> (Set.{u2} γ)} {g : (Set.{u1} α) -> (Filter.{u2} γ)}, (forall (i : ι), Filter.HasBasis.{u2, succ u4} γ (β i) (g (s i)) (pg i) (sg i)) -> (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} γ) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} γ) (Filter.partialOrder.{u2} γ)) g) -> (Filter.HasBasis.{u2, max (succ u3) (succ u4)} γ (Sigma.{u3, u4} ι (fun (i : ι) => β i)) (Filter.lift.{u1, u2} α γ f g) (fun (i : Sigma.{u3, u4} ι (fun (i : ι) => β i)) => And (p (Sigma.fst.{u3, u4} ι (fun (i : ι) => β i) i)) (pg (Sigma.fst.{u3, u4} ι (fun (i : ι) => β i) i) (Sigma.snd.{u3, u4} ι (fun (i : ι) => β i) i))) (fun (i : Sigma.{u3, u4} ι (fun (i : ι) => β i)) => sg (Sigma.fst.{u3, u4} ι (fun (i : ι) => β i) i) (Sigma.snd.{u3, u4} ι (fun (i : ι) => β i) i))))
but is expected to have type
  forall {α : Type.{u3}} {γ : Type.{u1}} {ι : Type.{u4}} {p : ι -> Prop} {s : ι -> (Set.{u3} α)} {f : Filter.{u3} α}, (Filter.HasBasis.{u3, succ u4} α ι f p s) -> (forall {β : ι -> Type.{u2}} {pg : forall (i : ι), (β i) -> Prop} {sg : forall (i : ι), (β i) -> (Set.{u1} γ)} {g : (Set.{u3} α) -> (Filter.{u1} γ)}, (forall (i : ι), Filter.HasBasis.{u1, succ u2} γ (β i) (g (s i)) (pg i) (sg i)) -> (Monotone.{u3, u1} (Set.{u3} α) (Filter.{u1} γ) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} γ) (Filter.instPartialOrderFilter.{u1} γ)) g) -> (Filter.HasBasis.{u1, max (succ u2) (succ u4)} γ (Sigma.{u4, u2} ι (fun (i : ι) => β i)) (Filter.lift.{u3, u1} α γ f g) (fun (i : Sigma.{u4, u2} ι (fun (i : ι) => β i)) => And (p (Sigma.fst.{u4, u2} ι (fun (i : ι) => β i) i)) (pg (Sigma.fst.{u4, u2} ι (fun (i : ι) => β i) i) (Sigma.snd.{u4, u2} ι (fun (i : ι) => β i) i))) (fun (i : Sigma.{u4, u2} ι (fun (i : ι) => β i)) => sg (Sigma.fst.{u4, u2} ι (fun (i : ι) => β i) i) (Sigma.snd.{u4, u2} ι (fun (i : ι) => β i) i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.lift Filter.HasBasis.liftₓ'. -/
/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type. See also `filter.has_basis.mem_lift_iff`
for the corresponding `mem_iff` statement formulated without using a sigma type. -/
theorem HasBasis.lift {ι} {p : ι → Prop} {s : ι → Set α} {f : Filter α} (hf : f.HasBasis p s)
    {β : ι → Type _} {pg : ∀ i, β i → Prop} {sg : ∀ i, β i → Set γ} {g : Set α → Filter γ}
    (hg : ∀ i, (g <| s i).HasBasis (pg i) (sg i)) (gm : Monotone g) :
    (f.lift g).HasBasis (fun i : Σi, β i => p i.1 ∧ pg i.1 i.2) fun i : Σi, β i => sg i.1 i.2 :=
  by
  refine' ⟨fun t => (hf.mem_lift_iff hg gm).trans _⟩
  simp [Sigma.exists, and_assoc', exists_and_left]
#align filter.has_basis.lift Filter.HasBasis.lift

/- warning: filter.mem_lift_sets -> Filter.mem_lift_sets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (forall {s : Set.{u2} β}, Iff (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (Filter.lift.{u1, u2} α β f g)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (g t)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Filter.{u1} β)}, (Monotone.{u2, u1} (Set.{u2} α) (Filter.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)) g) -> (forall {s : Set.{u1} β}, Iff (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) s (Filter.lift.{u2, u1} α β f g)) (Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t f) (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) s (g t)))))
Case conversion may be inaccurate. Consider using '#align filter.mem_lift_sets Filter.mem_lift_setsₓ'. -/
theorem mem_lift_sets (hg : Monotone g) {s : Set β} : s ∈ f.lift g ↔ ∃ t ∈ f, s ∈ g t :=
  (f.basis_sets.mem_lift_iffₓ (fun s => (g s).basis_sets) hg).trans <| by
    simp only [id, exists_mem_subset_iff]
#align filter.mem_lift_sets Filter.mem_lift_sets

/- warning: filter.sInter_lift_sets -> Filter.interₛ_lift_sets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (Eq.{succ u2} (Set.{u2} β) (Set.interₛ.{u2} β (setOf.{u2} (Set.{u2} β) (fun (s : Set.{u2} β) => Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (Filter.lift.{u1, u2} α β f g)))) (Set.interᵢ.{u2, succ u1} β (Set.{u1} α) (fun (s : Set.{u1} α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => Set.interₛ.{u2} β (setOf.{u2} (Set.{u2} β) (fun (t : Set.{u2} β) => Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (g s)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Filter.{u1} β)}, (Monotone.{u2, u1} (Set.{u2} α) (Filter.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)) g) -> (Eq.{succ u1} (Set.{u1} β) (Set.interₛ.{u1} β (setOf.{u1} (Set.{u1} β) (fun (s : Set.{u1} β) => Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) s (Filter.lift.{u2, u1} α β f g)))) (Set.interᵢ.{u1, succ u2} β (Set.{u2} α) (fun (s : Set.{u2} α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) (fun (H : Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) => Set.interₛ.{u1} β (setOf.{u1} (Set.{u1} β) (fun (t : Set.{u1} β) => Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) t (g s)))))))
Case conversion may be inaccurate. Consider using '#align filter.sInter_lift_sets Filter.interₛ_lift_setsₓ'. -/
theorem interₛ_lift_sets (hg : Monotone g) :
    ⋂₀ { s | s ∈ f.lift g } = ⋂ s ∈ f, ⋂₀ { t | t ∈ g s } := by
  simp only [sInter_eq_bInter, mem_set_of_eq, Filter.mem_sets, mem_lift_sets hg, Inter_exists,
    @Inter_comm _ (Set β)]
#align filter.sInter_lift_sets Filter.interₛ_lift_sets

#print Filter.mem_lift /-
theorem mem_lift {s : Set β} {t : Set α} (ht : t ∈ f) (hs : s ∈ g t) : s ∈ f.lift g :=
  le_principal_iff.mp <|
    show f.lift g ≤ 𝓟 s from infᵢ_le_of_le t <| infᵢ_le_of_le ht <| le_principal_iff.mpr hs
#align filter.mem_lift Filter.mem_lift
-/

/- warning: filter.lift_le -> Filter.lift_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u2} β)} {h : Filter.{u2} β} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (g s) h) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift.{u1, u2} α β f g) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Filter.{u1} β)} {h : Filter.{u1} β} {s : Set.{u2} α}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (g s) h) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.lift.{u2, u1} α β f g) h)
Case conversion may be inaccurate. Consider using '#align filter.lift_le Filter.lift_leₓ'. -/
theorem lift_le {f : Filter α} {g : Set α → Filter β} {h : Filter β} {s : Set α} (hs : s ∈ f)
    (hg : g s ≤ h) : f.lift g ≤ h :=
  infᵢ₂_le_of_le s hs hg
#align filter.lift_le Filter.lift_le

/- warning: filter.le_lift -> Filter.le_lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u2} β)} {h : Filter.{u2} β}, Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) h (Filter.lift.{u1, u2} α β f g)) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) h (g s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Filter.{u1} β)} {h : Filter.{u1} β}, Iff (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) h (Filter.lift.{u2, u1} α β f g)) (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) h (g s)))
Case conversion may be inaccurate. Consider using '#align filter.le_lift Filter.le_liftₓ'. -/
theorem le_lift {f : Filter α} {g : Set α → Filter β} {h : Filter β} :
    h ≤ f.lift g ↔ ∀ s ∈ f, h ≤ g s :=
  le_infᵢ₂_iff
#align filter.le_lift Filter.le_lift

/- warning: filter.lift_mono -> Filter.lift_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {g₁ : (Set.{u1} α) -> (Filter.{u2} β)} {g₂ : (Set.{u1} α) -> (Filter.{u2} β)}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f₁ f₂) -> (LE.le.{max u1 u2} ((Set.{u1} α) -> (Filter.{u2} β)) (Pi.hasLe.{u1, u2} (Set.{u1} α) (fun (ᾰ : Set.{u1} α) => Filter.{u2} β) (fun (i : Set.{u1} α) => Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)))) g₁ g₂) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift.{u1, u2} α β f₁ g₁) (Filter.lift.{u1, u2} α β f₂ g₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f₁ : Filter.{u2} α} {f₂ : Filter.{u2} α} {g₁ : (Set.{u2} α) -> (Filter.{u1} β)} {g₂ : (Set.{u2} α) -> (Filter.{u1} β)}, (LE.le.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) f₁ f₂) -> (LE.le.{max u2 u1} ((Set.{u2} α) -> (Filter.{u1} β)) (Pi.hasLe.{u2, u1} (Set.{u2} α) (fun (ᾰ : Set.{u2} α) => Filter.{u1} β) (fun (i : Set.{u2} α) => Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)))) g₁ g₂) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.lift.{u2, u1} α β f₁ g₁) (Filter.lift.{u2, u1} α β f₂ g₂))
Case conversion may be inaccurate. Consider using '#align filter.lift_mono Filter.lift_monoₓ'. -/
theorem lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
  infᵢ_mono fun s => infᵢ_mono' fun hs => ⟨hf hs, hg s⟩
#align filter.lift_mono Filter.lift_mono

/- warning: filter.lift_mono' -> Filter.lift_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g₁ : (Set.{u1} α) -> (Filter.{u2} β)} {g₂ : (Set.{u1} α) -> (Filter.{u2} β)}, (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (g₁ s) (g₂ s))) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift.{u1, u2} α β f g₁) (Filter.lift.{u1, u2} α β f g₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g₁ : (Set.{u2} α) -> (Filter.{u1} β)} {g₂ : (Set.{u2} α) -> (Filter.{u1} β)}, (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (g₁ s) (g₂ s))) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.lift.{u2, u1} α β f g₁) (Filter.lift.{u2, u1} α β f g₂))
Case conversion may be inaccurate. Consider using '#align filter.lift_mono' Filter.lift_mono'ₓ'. -/
theorem lift_mono' (hg : ∀ s ∈ f, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ :=
  infᵢ₂_mono hg
#align filter.lift_mono' Filter.lift_mono'

#print Filter.tendsto_lift /-
theorem tendsto_lift {m : γ → β} {l : Filter γ} :
    Tendsto m l (f.lift g) ↔ ∀ s ∈ f, Tendsto m l (g s) := by simp only [Filter.lift, tendsto_infi]
#align filter.tendsto_lift Filter.tendsto_lift
-/

/- warning: filter.map_lift_eq -> Filter.map_lift_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u2} β)} {m : β -> γ}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.map.{u2, u3} β γ m (Filter.lift.{u1, u2} α β f g)) (Filter.lift.{u1, u3} α γ f (Function.comp.{succ u1, succ u2, succ u3} (Set.{u1} α) (Filter.{u2} β) (Filter.{u3} γ) (Filter.map.{u2, u3} β γ m) g)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : Filter.{u3} α} {g : (Set.{u3} α) -> (Filter.{u2} β)} {m : β -> γ}, (Monotone.{u3, u2} (Set.{u3} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β)) g) -> (Eq.{succ u1} (Filter.{u1} γ) (Filter.map.{u2, u1} β γ m (Filter.lift.{u3, u2} α β f g)) (Filter.lift.{u3, u1} α γ f (Function.comp.{succ u3, succ u2, succ u1} (Set.{u3} α) (Filter.{u2} β) (Filter.{u1} γ) (Filter.map.{u2, u1} β γ m) g)))
Case conversion may be inaccurate. Consider using '#align filter.map_lift_eq Filter.map_lift_eqₓ'. -/
theorem map_lift_eq {m : β → γ} (hg : Monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
  have : Monotone (map m ∘ g) := map_mono.comp hg
  Filter.ext fun s => by
    simp only [mem_lift_sets hg, mem_lift_sets this, exists_prop, mem_map, Function.comp_apply]
#align filter.map_lift_eq Filter.map_lift_eq

#print Filter.comap_lift_eq /-
theorem comap_lift_eq {m : γ → β} : comap m (f.lift g) = f.lift (comap m ∘ g) := by
  simp only [Filter.lift, comap_infi]
#align filter.comap_lift_eq Filter.comap_lift_eq
-/

/- warning: filter.comap_lift_eq2 -> Filter.comap_lift_eq2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {m : β -> α} {g : (Set.{u2} β) -> (Filter.{u3} γ)}, (Monotone.{u2, u3} (Set.{u2} β) (Filter.{u3} γ) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ)) g) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.lift.{u2, u3} β γ (Filter.comap.{u2, u1} β α m f) g) (Filter.lift.{u1, u3} α γ f (Function.comp.{succ u1, succ u2, succ u3} (Set.{u1} α) (Set.{u2} β) (Filter.{u3} γ) g (Set.preimage.{u2, u1} β α m))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : Filter.{u1} α} {m : β -> α} {g : (Set.{u3} β) -> (Filter.{u2} γ)}, (Monotone.{u3, u2} (Set.{u3} β) (Filter.{u2} γ) (PartialOrder.toPreorder.{u3} (Set.{u3} β) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} β) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} β) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} β) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} β) (Set.instCompleteBooleanAlgebraSet.{u3} β))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} γ) (Filter.instPartialOrderFilter.{u2} γ)) g) -> (Eq.{succ u2} (Filter.{u2} γ) (Filter.lift.{u3, u2} β γ (Filter.comap.{u3, u1} β α m f) g) (Filter.lift.{u1, u2} α γ f (Function.comp.{succ u1, succ u3, succ u2} (Set.{u1} α) (Set.{u3} β) (Filter.{u2} γ) g (Set.preimage.{u3, u1} β α m))))
Case conversion may be inaccurate. Consider using '#align filter.comap_lift_eq2 Filter.comap_lift_eq2ₓ'. -/
theorem comap_lift_eq2 {m : β → α} {g : Set β → Filter γ} (hg : Monotone g) :
    (comap m f).lift g = f.lift (g ∘ preimage m) :=
  le_antisymm (le_infᵢ₂ fun s hs => infᵢ₂_le (m ⁻¹' s) ⟨s, hs, Subset.rfl⟩)
    (le_infᵢ₂ fun s ⟨s', hs', (h_sub : m ⁻¹' s' ⊆ s)⟩ => infᵢ₂_le_of_le s' hs' <| hg h_sub)
#align filter.comap_lift_eq2 Filter.comap_lift_eq2

/- warning: filter.lift_map_le -> Filter.lift_map_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : (Set.{u2} β) -> (Filter.{u3} γ)} {m : α -> β}, LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ))) (Filter.lift.{u2, u3} β γ (Filter.map.{u1, u2} α β m f) g) (Filter.lift.{u1, u3} α γ f (Function.comp.{succ u1, succ u2, succ u3} (Set.{u1} α) (Set.{u2} β) (Filter.{u3} γ) g (Set.image.{u1, u2} α β m)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u3} β) -> (Filter.{u2} γ)} {m : α -> β}, LE.le.{u2} (Filter.{u2} γ) (Preorder.toLE.{u2} (Filter.{u2} γ) (PartialOrder.toPreorder.{u2} (Filter.{u2} γ) (Filter.instPartialOrderFilter.{u2} γ))) (Filter.lift.{u3, u2} β γ (Filter.map.{u1, u3} α β m f) g) (Filter.lift.{u1, u2} α γ f (Function.comp.{succ u1, succ u3, succ u2} (Set.{u1} α) (Set.{u3} β) (Filter.{u2} γ) g (Set.image.{u1, u3} α β m)))
Case conversion may be inaccurate. Consider using '#align filter.lift_map_le Filter.lift_map_leₓ'. -/
theorem lift_map_le {g : Set β → Filter γ} {m : α → β} : (map m f).lift g ≤ f.lift (g ∘ image m) :=
  le_lift.2 fun s hs => lift_le (image_mem_map hs) le_rfl
#align filter.lift_map_le Filter.lift_map_le

/- warning: filter.map_lift_eq2 -> Filter.map_lift_eq2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : (Set.{u2} β) -> (Filter.{u3} γ)} {m : α -> β}, (Monotone.{u2, u3} (Set.{u2} β) (Filter.{u3} γ) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ)) g) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.lift.{u2, u3} β γ (Filter.map.{u1, u2} α β m f) g) (Filter.lift.{u1, u3} α γ f (Function.comp.{succ u1, succ u2, succ u3} (Set.{u1} α) (Set.{u2} β) (Filter.{u3} γ) g (Set.image.{u1, u2} α β m))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u3} β) -> (Filter.{u2} γ)} {m : α -> β}, (Monotone.{u3, u2} (Set.{u3} β) (Filter.{u2} γ) (PartialOrder.toPreorder.{u3} (Set.{u3} β) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} β) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} β) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} β) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} β) (Set.instCompleteBooleanAlgebraSet.{u3} β))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} γ) (Filter.instPartialOrderFilter.{u2} γ)) g) -> (Eq.{succ u2} (Filter.{u2} γ) (Filter.lift.{u3, u2} β γ (Filter.map.{u1, u3} α β m f) g) (Filter.lift.{u1, u2} α γ f (Function.comp.{succ u1, succ u3, succ u2} (Set.{u1} α) (Set.{u3} β) (Filter.{u2} γ) g (Set.image.{u1, u3} α β m))))
Case conversion may be inaccurate. Consider using '#align filter.map_lift_eq2 Filter.map_lift_eq2ₓ'. -/
theorem map_lift_eq2 {g : Set β → Filter γ} {m : α → β} (hg : Monotone g) :
    (map m f).lift g = f.lift (g ∘ image m) :=
  lift_map_le.antisymm <| le_lift.2 fun s hs => lift_le hs <| hg <| image_preimage_subset _ _
#align filter.map_lift_eq2 Filter.map_lift_eq2

/- warning: filter.lift_comm -> Filter.lift_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : Filter.{u2} β} {h : (Set.{u1} α) -> (Set.{u2} β) -> (Filter.{u3} γ)}, Eq.{succ u3} (Filter.{u3} γ) (Filter.lift.{u1, u3} α γ f (fun (s : Set.{u1} α) => Filter.lift.{u2, u3} β γ g (h s))) (Filter.lift.{u2, u3} β γ g (fun (t : Set.{u2} β) => Filter.lift.{u1, u3} α γ f (fun (s : Set.{u1} α) => h s t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} {f : Filter.{u2} α} {g : Filter.{u3} β} {h : (Set.{u2} α) -> (Set.{u3} β) -> (Filter.{u1} γ)}, Eq.{succ u1} (Filter.{u1} γ) (Filter.lift.{u2, u1} α γ f (fun (s : Set.{u2} α) => Filter.lift.{u3, u1} β γ g (h s))) (Filter.lift.{u3, u1} β γ g (fun (t : Set.{u3} β) => Filter.lift.{u2, u1} α γ f (fun (s : Set.{u2} α) => h s t)))
Case conversion may be inaccurate. Consider using '#align filter.lift_comm Filter.lift_commₓ'. -/
theorem lift_comm {g : Filter β} {h : Set α → Set β → Filter γ} :
    (f.lift fun s => g.lift (h s)) = g.lift fun t => f.lift fun s => h s t :=
  le_antisymm
    (le_infᵢ fun i =>
      le_infᵢ fun hi =>
        le_infᵢ fun j =>
          le_infᵢ fun hj => infᵢ_le_of_le j <| infᵢ_le_of_le hj <| infᵢ_le_of_le i <| infᵢ_le _ hi)
    (le_infᵢ fun i =>
      le_infᵢ fun hi =>
        le_infᵢ fun j =>
          le_infᵢ fun hj => infᵢ_le_of_le j <| infᵢ_le_of_le hj <| infᵢ_le_of_le i <| infᵢ_le _ hi)
#align filter.lift_comm Filter.lift_comm

/- warning: filter.lift_assoc -> Filter.lift_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u2} β)} {h : (Set.{u2} β) -> (Filter.{u3} γ)}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.lift.{u2, u3} β γ (Filter.lift.{u1, u2} α β f g) h) (Filter.lift.{u1, u3} α γ f (fun (s : Set.{u1} α) => Filter.lift.{u2, u3} β γ (g s) h)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u3} β)} {h : (Set.{u3} β) -> (Filter.{u2} γ)}, (Monotone.{u1, u3} (Set.{u1} α) (Filter.{u3} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{u3} (Filter.{u3} β) (Filter.instPartialOrderFilter.{u3} β)) g) -> (Eq.{succ u2} (Filter.{u2} γ) (Filter.lift.{u3, u2} β γ (Filter.lift.{u1, u3} α β f g) h) (Filter.lift.{u1, u2} α γ f (fun (s : Set.{u1} α) => Filter.lift.{u3, u2} β γ (g s) h)))
Case conversion may be inaccurate. Consider using '#align filter.lift_assoc Filter.lift_assocₓ'. -/
theorem lift_assoc {h : Set β → Filter γ} (hg : Monotone g) :
    (f.lift g).lift h = f.lift fun s => (g s).lift h :=
  le_antisymm
    (le_infᵢ fun s =>
      le_infᵢ fun hs =>
        le_infᵢ fun t =>
          le_infᵢ fun ht => infᵢ_le_of_le t <| infᵢ_le _ <| (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
    (le_infᵢ fun t =>
      le_infᵢ fun ht =>
        let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht
        infᵢ_le_of_le s <| infᵢ_le_of_le hs <| infᵢ_le_of_le t <| infᵢ_le _ h')
#align filter.lift_assoc Filter.lift_assoc

/- warning: filter.lift_lift_same_le_lift -> Filter.lift_lift_same_le_lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Set.{u1} α) -> (Filter.{u2} β)}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift.{u1, u2} α β f (fun (s : Set.{u1} α) => Filter.lift.{u1, u2} α β f (g s))) (Filter.lift.{u1, u2} α β f (fun (s : Set.{u1} α) => g s s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Set.{u2} α) -> (Filter.{u1} β)}, LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.lift.{u2, u1} α β f (fun (s : Set.{u2} α) => Filter.lift.{u2, u1} α β f (g s))) (Filter.lift.{u2, u1} α β f (fun (s : Set.{u2} α) => g s s))
Case conversion may be inaccurate. Consider using '#align filter.lift_lift_same_le_lift Filter.lift_lift_same_le_liftₓ'. -/
theorem lift_lift_same_le_lift {g : Set α → Set α → Filter β} :
    (f.lift fun s => f.lift (g s)) ≤ f.lift fun s => g s s :=
  le_lift.2 fun s hs => lift_le hs <| lift_le hs le_rfl
#align filter.lift_lift_same_le_lift Filter.lift_lift_same_le_lift

/- warning: filter.lift_lift_same_eq_lift -> Filter.lift_lift_same_eq_lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Set.{u1} α) -> (Filter.{u2} β)}, (forall (s : Set.{u1} α), Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) (fun (t : Set.{u1} α) => g s t)) -> (forall (t : Set.{u1} α), Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) (fun (s : Set.{u1} α) => g s t)) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β f (fun (s : Set.{u1} α) => Filter.lift.{u1, u2} α β f (g s))) (Filter.lift.{u1, u2} α β f (fun (s : Set.{u1} α) => g s s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Set.{u2} α) -> (Filter.{u1} β)}, (forall (s : Set.{u2} α), Monotone.{u2, u1} (Set.{u2} α) (Filter.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)) (fun (t : Set.{u2} α) => g s t)) -> (forall (t : Set.{u2} α), Monotone.{u2, u1} (Set.{u2} α) (Filter.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)) (fun (s : Set.{u2} α) => g s t)) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift.{u2, u1} α β f (fun (s : Set.{u2} α) => Filter.lift.{u2, u1} α β f (g s))) (Filter.lift.{u2, u1} α β f (fun (s : Set.{u2} α) => g s s)))
Case conversion may be inaccurate. Consider using '#align filter.lift_lift_same_eq_lift Filter.lift_lift_same_eq_liftₓ'. -/
theorem lift_lift_same_eq_lift {g : Set α → Set α → Filter β} (hg₁ : ∀ s, Monotone fun t => g s t)
    (hg₂ : ∀ t, Monotone fun s => g s t) : (f.lift fun s => f.lift (g s)) = f.lift fun s => g s s :=
  lift_lift_same_le_lift.antisymm <|
    le_lift.2 fun s hs =>
      le_lift.2 fun t ht =>
        lift_le (inter_mem hs ht) <|
          calc
            g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) := hg₂ (s ∩ t) (inter_subset_left _ _)
            _ ≤ g s t := hg₁ s (inter_subset_right _ _)
            
#align filter.lift_lift_same_eq_lift Filter.lift_lift_same_eq_lift

/- warning: filter.lift_principal -> Filter.lift_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g : (Set.{u1} α) -> (Filter.{u2} β)} {s : Set.{u1} α}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β (Filter.principal.{u1} α s) g) (g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {g : (Set.{u2} α) -> (Filter.{u1} β)} {s : Set.{u2} α}, (Monotone.{u2, u1} (Set.{u2} α) (Filter.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)) g) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift.{u2, u1} α β (Filter.principal.{u2} α s) g) (g s))
Case conversion may be inaccurate. Consider using '#align filter.lift_principal Filter.lift_principalₓ'. -/
theorem lift_principal {s : Set α} (hg : Monotone g) : (𝓟 s).lift g = g s :=
  (lift_le (mem_principal_self _) le_rfl).antisymm (le_lift.2 fun t ht => hg ht)
#align filter.lift_principal Filter.lift_principal

/- warning: filter.monotone_lift -> Filter.monotone_lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u3} γ] {f : γ -> (Filter.{u1} α)} {g : γ -> (Set.{u1} α) -> (Filter.{u2} β)}, (Monotone.{u3, u1} γ (Filter.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)) f) -> (Monotone.{u3, max u1 u2} γ ((Set.{u1} α) -> (Filter.{u2} β)) _inst_1 (Pi.preorder.{u1, u2} (Set.{u1} α) (fun (ᾰ : Set.{u1} α) => Filter.{u2} β) (fun (i : Set.{u1} α) => PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) g) -> (Monotone.{u3, u2} γ (Filter.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) (fun (c : γ) => Filter.lift.{u1, u2} α β (f c) (g c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : Preorder.{u3} γ] {f : γ -> (Filter.{u2} α)} {g : γ -> (Set.{u2} α) -> (Filter.{u1} β)}, (Monotone.{u3, u2} γ (Filter.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α)) f) -> (Monotone.{u3, max u2 u1} γ ((Set.{u2} α) -> (Filter.{u1} β)) _inst_1 (Pi.preorder.{u2, u1} (Set.{u2} α) (fun (ᾰ : Set.{u2} α) => Filter.{u1} β) (fun (i : Set.{u2} α) => PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) g) -> (Monotone.{u3, u1} γ (Filter.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)) (fun (c : γ) => Filter.lift.{u2, u1} α β (f c) (g c)))
Case conversion may be inaccurate. Consider using '#align filter.monotone_lift Filter.monotone_liftₓ'. -/
theorem monotone_lift [Preorder γ] {f : γ → Filter α} {g : γ → Set α → Filter β} (hf : Monotone f)
    (hg : Monotone g) : Monotone fun c => (f c).lift (g c) := fun a b h => lift_mono (hf h) (hg h)
#align filter.monotone_lift Filter.monotone_lift

/- warning: filter.lift_ne_bot_iff -> Filter.lift_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (Iff (Filter.NeBot.{u2} β (Filter.lift.{u1, u2} α β f g)) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Filter.NeBot.{u2} β (g s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Filter.{u1} β)}, (Monotone.{u2, u1} (Set.{u2} α) (Filter.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)) g) -> (Iff (Filter.NeBot.{u1} β (Filter.lift.{u2, u1} α β f g)) (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (Filter.NeBot.{u1} β (g s))))
Case conversion may be inaccurate. Consider using '#align filter.lift_ne_bot_iff Filter.lift_neBot_iffₓ'. -/
theorem lift_neBot_iff (hm : Monotone g) : (NeBot <| f.lift g) ↔ ∀ s ∈ f, NeBot (g s) := by
  simp only [ne_bot_iff, Ne.def, ← empty_mem_iff_bot, mem_lift_sets hm, not_exists]
#align filter.lift_ne_bot_iff Filter.lift_neBot_iff

/- warning: filter.lift_const -> Filter.lift_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u2} β}, Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β f (fun (x : Set.{u1} α) => g)) g
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : Filter.{u1} β}, Eq.{succ u1} (Filter.{u1} β) (Filter.lift.{u2, u1} α β f (fun (x : Set.{u2} α) => g)) g
Case conversion may be inaccurate. Consider using '#align filter.lift_const Filter.lift_constₓ'. -/
@[simp]
theorem lift_const {f : Filter α} {g : Filter β} : (f.lift fun x => g) = g :=
  infᵢ_subtype'.trans infᵢ_const
#align filter.lift_const Filter.lift_const

/- warning: filter.lift_inf -> Filter.lift_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u2} β)} {h : (Set.{u1} α) -> (Filter.{u2} β)}, Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β f (fun (x : Set.{u1} α) => HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (g x) (h x))) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.lift.{u1, u2} α β f g) (Filter.lift.{u1, u2} α β f h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Filter.{u1} β)} {h : (Set.{u2} α) -> (Filter.{u1} β)}, Eq.{succ u1} (Filter.{u1} β) (Filter.lift.{u2, u1} α β f (fun (x : Set.{u2} α) => HasInf.inf.{u1} (Filter.{u1} β) (Filter.instHasInfFilter.{u1} β) (g x) (h x))) (HasInf.inf.{u1} (Filter.{u1} β) (Filter.instHasInfFilter.{u1} β) (Filter.lift.{u2, u1} α β f g) (Filter.lift.{u2, u1} α β f h))
Case conversion may be inaccurate. Consider using '#align filter.lift_inf Filter.lift_infₓ'. -/
@[simp]
theorem lift_inf {f : Filter α} {g h : Set α → Filter β} :
    (f.lift fun x => g x ⊓ h x) = f.lift g ⊓ f.lift h := by simp only [Filter.lift, infᵢ_inf_eq]
#align filter.lift_inf Filter.lift_inf

#print Filter.lift_principal2 /-
@[simp]
theorem lift_principal2 {f : Filter α} : f.lift 𝓟 = f :=
  le_antisymm (fun s hs => mem_lift hs (mem_principal_self s))
    (le_infᵢ fun s => le_infᵢ fun hs => by simp only [hs, le_principal_iff])
#align filter.lift_principal2 Filter.lift_principal2
-/

/- warning: filter.lift_infi_le -> Filter.lift_infᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> (Filter.{u1} α)} {g : (Set.{u1} α) -> (Filter.{u2} β)}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift.{u1, u2} α β (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f) g) (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => Filter.lift.{u1, u2} α β (f i) g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {f : ι -> (Filter.{u3} α)} {g : (Set.{u3} α) -> (Filter.{u2} β)}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.lift.{u3, u2} α β (infᵢ.{u3, u1} (Filter.{u3} α) (ConditionallyCompleteLattice.toInfSet.{u3} (Filter.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))) ι f) g) (infᵢ.{u2, u1} (Filter.{u2} β) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) ι (fun (i : ι) => Filter.lift.{u3, u2} α β (f i) g))
Case conversion may be inaccurate. Consider using '#align filter.lift_infi_le Filter.lift_infᵢ_leₓ'. -/
theorem lift_infᵢ_le {f : ι → Filter α} {g : Set α → Filter β} :
    (infᵢ f).lift g ≤ ⨅ i, (f i).lift g :=
  le_infᵢ fun i => lift_mono (infᵢ_le _ _) le_rfl
#align filter.lift_infi_le Filter.lift_infᵢ_le

/- warning: filter.lift_infi -> Filter.lift_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {f : ι -> (Filter.{u1} α)} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (forall (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u2} (Filter.{u2} β) (g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (g s) (g t))) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f) g) (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => Filter.lift.{u1, u2} α β (f i) g)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {f : ι -> (Filter.{u2} α)} {g : (Set.{u2} α) -> (Filter.{u1} β)}, (forall (s : Set.{u2} α) (t : Set.{u2} α), Eq.{succ u1} (Filter.{u1} β) (g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) (HasInf.inf.{u1} (Filter.{u1} β) (Filter.instHasInfFilter.{u1} β) (g s) (g t))) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift.{u2, u1} α β (infᵢ.{u2, u3} (Filter.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α))) ι f) g) (infᵢ.{u1, u3} (Filter.{u1} β) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} β) (Filter.instCompleteLatticeFilter.{u1} β))) ι (fun (i : ι) => Filter.lift.{u2, u1} α β (f i) g)))
Case conversion may be inaccurate. Consider using '#align filter.lift_infi Filter.lift_infᵢₓ'. -/
theorem lift_infᵢ [Nonempty ι] {f : ι → Filter α} {g : Set α → Filter β}
    (hg : ∀ s t, g (s ∩ t) = g s ⊓ g t) : (infᵢ f).lift g = ⨅ i, (f i).lift g :=
  by
  refine' lift_infi_le.antisymm fun s => _
  have H : ∀ t ∈ infᵢ f, (⨅ i, (f i).lift g) ≤ g t :=
    by
    intro t ht
    refine' infi_sets_induct ht _ fun i s t hs ht => _
    · inhabit ι
      exact infᵢ₂_le_of_le default univ (infᵢ_le _ univ_mem)
    · rw [hg]
      exact le_inf (infᵢ₂_le_of_le i s <| infᵢ_le _ hs) ht
  simp only [mem_lift_sets (Monotone.of_map_inf hg), exists_imp]
  exact fun t ht hs => H t ht hs
#align filter.lift_infi Filter.lift_infᵢ

/- warning: filter.lift_infi_of_directed -> Filter.lift_infᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {f : ι -> (Filter.{u1} α)} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (Directed.{u1, u3} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) f) -> (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f) g) (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => Filter.lift.{u1, u2} α β (f i) g)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {f : ι -> (Filter.{u2} α)} {g : (Set.{u2} α) -> (Filter.{u1} β)}, (Directed.{u2, u3} (Filter.{u2} α) ι (fun (x._@.Mathlib.Order.Filter.Lift._hyg.2699 : Filter.{u2} α) (x._@.Mathlib.Order.Filter.Lift._hyg.2701 : Filter.{u2} α) => GE.ge.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) x._@.Mathlib.Order.Filter.Lift._hyg.2699 x._@.Mathlib.Order.Filter.Lift._hyg.2701) f) -> (Monotone.{u2, u1} (Set.{u2} α) (Filter.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)) g) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift.{u2, u1} α β (infᵢ.{u2, u3} (Filter.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α))) ι f) g) (infᵢ.{u1, u3} (Filter.{u1} β) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} β) (Filter.instCompleteLatticeFilter.{u1} β))) ι (fun (i : ι) => Filter.lift.{u2, u1} α β (f i) g)))
Case conversion may be inaccurate. Consider using '#align filter.lift_infi_of_directed Filter.lift_infᵢ_of_directedₓ'. -/
theorem lift_infᵢ_of_directed [Nonempty ι] {f : ι → Filter α} {g : Set α → Filter β}
    (hf : Directed (· ≥ ·) f) (hg : Monotone g) : (infᵢ f).lift g = ⨅ i, (f i).lift g :=
  lift_infᵢ_le.antisymm fun s =>
    by
    simp only [mem_lift_sets hg, exists_imp, mem_infi_of_directed hf]
    exact fun t i ht hs => mem_infi_of_mem i <| mem_lift ht hs
#align filter.lift_infi_of_directed Filter.lift_infᵢ_of_directed

/- warning: filter.lift_infi_of_map_univ -> Filter.lift_infᵢ_of_map_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> (Filter.{u1} α)} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (forall (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u2} (Filter.{u2} β) (g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (g s) (g t))) -> (Eq.{succ u2} (Filter.{u2} β) (g (Set.univ.{u1} α)) (Top.top.{u2} (Filter.{u2} β) (Filter.hasTop.{u2} β))) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f) g) (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => Filter.lift.{u1, u2} α β (f i) g)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {f : ι -> (Filter.{u3} α)} {g : (Set.{u3} α) -> (Filter.{u2} β)}, (forall (s : Set.{u3} α) (t : Set.{u3} α), Eq.{succ u2} (Filter.{u2} β) (g (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) s t)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) (g s) (g t))) -> (Eq.{succ u2} (Filter.{u2} β) (g (Set.univ.{u3} α)) (Top.top.{u2} (Filter.{u2} β) (Filter.instTopFilter.{u2} β))) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u3, u2} α β (infᵢ.{u3, u1} (Filter.{u3} α) (ConditionallyCompleteLattice.toInfSet.{u3} (Filter.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))) ι f) g) (infᵢ.{u2, u1} (Filter.{u2} β) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) ι (fun (i : ι) => Filter.lift.{u3, u2} α β (f i) g)))
Case conversion may be inaccurate. Consider using '#align filter.lift_infi_of_map_univ Filter.lift_infᵢ_of_map_univₓ'. -/
theorem lift_infᵢ_of_map_univ {f : ι → Filter α} {g : Set α → Filter β}
    (hg : ∀ s t, g (s ∩ t) = g s ⊓ g t) (hg' : g univ = ⊤) : (infᵢ f).lift g = ⨅ i, (f i).lift g :=
  by
  cases isEmpty_or_nonempty ι
  · simp [infᵢ_of_empty, hg']
  · exact lift_infi hg
#align filter.lift_infi_of_map_univ Filter.lift_infᵢ_of_map_univ

end lift

section Lift'

#print Filter.lift' /-
/-- Specialize `lift` to functions `set α → set β`. This can be viewed as a generalization of `map`.
This is essentially a push-forward along a function mapping each set to a set. -/
protected def lift' (f : Filter α) (h : Set α → Set β) :=
  f.lift (𝓟 ∘ h)
#align filter.lift' Filter.lift'
-/

variable {f f₁ f₂ : Filter α} {h h₁ h₂ : Set α → Set β}

/- warning: filter.lift'_top -> Filter.lift'_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (h : (Set.{u1} α) -> (Set.{u2} β)), Eq.{succ u2} (Filter.{u2} β) (Filter.lift'.{u1, u2} α β (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α)) h) (Filter.principal.{u2} β (h (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (h : (Set.{u2} α) -> (Set.{u1} β)), Eq.{succ u1} (Filter.{u1} β) (Filter.lift'.{u2, u1} α β (Top.top.{u2} (Filter.{u2} α) (Filter.instTopFilter.{u2} α)) h) (Filter.principal.{u1} β (h (Set.univ.{u2} α)))
Case conversion may be inaccurate. Consider using '#align filter.lift'_top Filter.lift'_topₓ'. -/
@[simp]
theorem lift'_top (h : Set α → Set β) : (⊤ : Filter α).lift' h = 𝓟 (h univ) :=
  lift_top _
#align filter.lift'_top Filter.lift'_top

/- warning: filter.mem_lift' -> Filter.mem_lift' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (h t) (Filter.lift'.{u1, u2} α β f h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h : (Set.{u2} α) -> (Set.{u1} β)} {t : Set.{u2} α}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t f) -> (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) (h t) (Filter.lift'.{u2, u1} α β f h))
Case conversion may be inaccurate. Consider using '#align filter.mem_lift' Filter.mem_lift'ₓ'. -/
theorem mem_lift' {t : Set α} (ht : t ∈ f) : h t ∈ f.lift' h :=
  le_principal_iff.mp <| show f.lift' h ≤ 𝓟 (h t) from infᵢ_le_of_le t <| infᵢ_le_of_le ht <| le_rfl
#align filter.mem_lift' Filter.mem_lift'

#print Filter.tendsto_lift' /-
theorem tendsto_lift' {m : γ → β} {l : Filter γ} :
    Tendsto m l (f.lift' h) ↔ ∀ s ∈ f, ∀ᶠ a in l, m a ∈ h s := by
  simp only [Filter.lift', tendsto_lift, tendsto_principal]
#align filter.tendsto_lift' Filter.tendsto_lift'
-/

/- warning: filter.has_basis.lift' -> Filter.HasBasis.lift' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)} {ι : Sort.{u3}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u3} α ι f p s) -> (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) h) -> (Filter.HasBasis.{u2, u3} β ι (Filter.lift'.{u1, u2} α β f h) p (Function.comp.{u3, succ u1, succ u2} ι (Set.{u1} α) (Set.{u2} β) h s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h : (Set.{u2} α) -> (Set.{u1} β)} {ι : Sort.{u3}} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u3} α ι f p s) -> (Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) h) -> (Filter.HasBasis.{u1, u3} β ι (Filter.lift'.{u2, u1} α β f h) p (Function.comp.{u3, succ u2, succ u1} ι (Set.{u2} α) (Set.{u1} β) h s))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.lift' Filter.HasBasis.lift'ₓ'. -/
theorem HasBasis.lift' {ι} {p : ι → Prop} {s} (hf : f.HasBasis p s) (hh : Monotone h) :
    (f.lift' h).HasBasis p (h ∘ s) :=
  by
  refine' ⟨fun t => (hf.mem_lift_iff _ (monotone_principal.comp hh)).trans _⟩
  show ∀ i, (𝓟 (h (s i))).HasBasis (fun j : Unit => True) fun j : Unit => h (s i)
  exact fun i => has_basis_principal _
  simp only [exists_const]
#align filter.has_basis.lift' Filter.HasBasis.lift'

/- warning: filter.mem_lift'_sets -> Filter.mem_lift'_sets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) h) -> (forall {s : Set.{u2} β}, Iff (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (Filter.lift'.{u1, u2} α β f h)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (h t) s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h : (Set.{u2} α) -> (Set.{u1} β)}, (Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) h) -> (forall {s : Set.{u1} β}, Iff (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) s (Filter.lift'.{u2, u1} α β f h)) (Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t f) (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (h t) s))))
Case conversion may be inaccurate. Consider using '#align filter.mem_lift'_sets Filter.mem_lift'_setsₓ'. -/
theorem mem_lift'_sets (hh : Monotone h) {s : Set β} : s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ s :=
  mem_lift_sets <| monotone_principal.comp hh
#align filter.mem_lift'_sets Filter.mem_lift'_sets

/- warning: filter.eventually_lift'_iff -> Filter.eventually_lift'_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) h) -> (forall {p : β -> Prop}, Iff (Filter.Eventually.{u2} β (fun (y : β) => p y) (Filter.lift'.{u1, u2} α β f h)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (h t)) -> (p y)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h : (Set.{u2} α) -> (Set.{u1} β)}, (Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) h) -> (forall {p : β -> Prop}, Iff (Filter.Eventually.{u1} β (fun (y : β) => p y) (Filter.lift'.{u2, u1} α β f h)) (Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t f) (forall (y : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (h t)) -> (p y)))))
Case conversion may be inaccurate. Consider using '#align filter.eventually_lift'_iff Filter.eventually_lift'_iffₓ'. -/
theorem eventually_lift'_iff (hh : Monotone h) {p : β → Prop} :
    (∀ᶠ y in f.lift' h, p y) ↔ ∃ t ∈ f, ∀ y ∈ h t, p y :=
  mem_lift'_sets hh
#align filter.eventually_lift'_iff Filter.eventually_lift'_iff

/- warning: filter.sInter_lift'_sets -> Filter.interₛ_lift'_sets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) h) -> (Eq.{succ u2} (Set.{u2} β) (Set.interₛ.{u2} β (setOf.{u2} (Set.{u2} β) (fun (s : Set.{u2} β) => Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (Filter.lift'.{u1, u2} α β f h)))) (Set.interᵢ.{u2, succ u1} β (Set.{u1} α) (fun (s : Set.{u1} α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => h s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h : (Set.{u2} α) -> (Set.{u1} β)}, (Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) h) -> (Eq.{succ u1} (Set.{u1} β) (Set.interₛ.{u1} β (setOf.{u1} (Set.{u1} β) (fun (s : Set.{u1} β) => Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) s (Filter.lift'.{u2, u1} α β f h)))) (Set.interᵢ.{u1, succ u2} β (Set.{u2} α) (fun (s : Set.{u2} α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) (fun (H : Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) => h s))))
Case conversion may be inaccurate. Consider using '#align filter.sInter_lift'_sets Filter.interₛ_lift'_setsₓ'. -/
theorem interₛ_lift'_sets (hh : Monotone h) : ⋂₀ { s | s ∈ f.lift' h } = ⋂ s ∈ f, h s :=
  (interₛ_lift_sets (monotone_principal.comp hh)).trans <| interᵢ₂_congr fun s hs => cinfₛ_Ici
#align filter.sInter_lift'_sets Filter.interₛ_lift'_sets

/- warning: filter.lift'_le -> Filter.lift'_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Set.{u2} β)} {h : Filter.{u2} β} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.principal.{u2} β (g s)) h) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift'.{u1, u2} α β f g) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Set.{u1} β)} {h : Filter.{u1} β} {s : Set.{u2} α}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.principal.{u1} β (g s)) h) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.lift'.{u2, u1} α β f g) h)
Case conversion may be inaccurate. Consider using '#align filter.lift'_le Filter.lift'_leₓ'. -/
theorem lift'_le {f : Filter α} {g : Set α → Set β} {h : Filter β} {s : Set α} (hs : s ∈ f)
    (hg : 𝓟 (g s) ≤ h) : f.lift' g ≤ h :=
  lift_le hs hg
#align filter.lift'_le Filter.lift'_le

/- warning: filter.lift'_mono -> Filter.lift'_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {h₁ : (Set.{u1} α) -> (Set.{u2} β)} {h₂ : (Set.{u1} α) -> (Set.{u2} β)}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f₁ f₂) -> (LE.le.{max u1 u2} ((Set.{u1} α) -> (Set.{u2} β)) (Pi.hasLe.{u1, u2} (Set.{u1} α) (fun (ᾰ : Set.{u1} α) => Set.{u2} β) (fun (i : Set.{u1} α) => Set.hasLe.{u2} β)) h₁ h₂) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift'.{u1, u2} α β f₁ h₁) (Filter.lift'.{u1, u2} α β f₂ h₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f₁ : Filter.{u2} α} {f₂ : Filter.{u2} α} {h₁ : (Set.{u2} α) -> (Set.{u1} β)} {h₂ : (Set.{u2} α) -> (Set.{u1} β)}, (LE.le.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) f₁ f₂) -> (LE.le.{max u2 u1} ((Set.{u2} α) -> (Set.{u1} β)) (Pi.hasLe.{u2, u1} (Set.{u2} α) (fun (ᾰ : Set.{u2} α) => Set.{u1} β) (fun (i : Set.{u2} α) => Set.instLESet.{u1} β)) h₁ h₂) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.lift'.{u2, u1} α β f₁ h₁) (Filter.lift'.{u2, u1} α β f₂ h₂))
Case conversion may be inaccurate. Consider using '#align filter.lift'_mono Filter.lift'_monoₓ'. -/
theorem lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
  lift_mono hf fun s => principal_mono.mpr <| hh s
#align filter.lift'_mono Filter.lift'_mono

/- warning: filter.lift'_mono' -> Filter.lift'_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h₁ : (Set.{u1} α) -> (Set.{u2} β)} {h₂ : (Set.{u1} α) -> (Set.{u2} β)}, (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (h₁ s) (h₂ s))) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift'.{u1, u2} α β f h₁) (Filter.lift'.{u1, u2} α β f h₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h₁ : (Set.{u2} α) -> (Set.{u1} β)} {h₂ : (Set.{u2} α) -> (Set.{u1} β)}, (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (h₁ s) (h₂ s))) -> (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.lift'.{u2, u1} α β f h₁) (Filter.lift'.{u2, u1} α β f h₂))
Case conversion may be inaccurate. Consider using '#align filter.lift'_mono' Filter.lift'_mono'ₓ'. -/
theorem lift'_mono' (hh : ∀ s ∈ f, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
  infᵢ₂_mono fun s hs => principal_mono.mpr <| hh s hs
#align filter.lift'_mono' Filter.lift'_mono'

/- warning: filter.lift'_cong -> Filter.lift'_cong is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h₁ : (Set.{u1} α) -> (Set.{u2} β)} {h₂ : (Set.{u1} α) -> (Set.{u2} β)}, (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Eq.{succ u2} (Set.{u2} β) (h₁ s) (h₂ s))) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift'.{u1, u2} α β f h₁) (Filter.lift'.{u1, u2} α β f h₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h₁ : (Set.{u2} α) -> (Set.{u1} β)} {h₂ : (Set.{u2} α) -> (Set.{u1} β)}, (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (Eq.{succ u1} (Set.{u1} β) (h₁ s) (h₂ s))) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift'.{u2, u1} α β f h₁) (Filter.lift'.{u2, u1} α β f h₂))
Case conversion may be inaccurate. Consider using '#align filter.lift'_cong Filter.lift'_congₓ'. -/
theorem lift'_cong (hh : ∀ s ∈ f, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
  le_antisymm (lift'_mono' fun s hs => le_of_eq <| hh s hs)
    (lift'_mono' fun s hs => le_of_eq <| (hh s hs).symm)
#align filter.lift'_cong Filter.lift'_cong

/- warning: filter.map_lift'_eq -> Filter.map_lift'_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)} {m : β -> γ}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) h) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.map.{u2, u3} β γ m (Filter.lift'.{u1, u2} α β f h)) (Filter.lift'.{u1, u3} α γ f (Function.comp.{succ u1, succ u2, succ u3} (Set.{u1} α) (Set.{u2} β) (Set.{u3} γ) (Set.image.{u2, u3} β γ m) h)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : Filter.{u3} α} {h : (Set.{u3} α) -> (Set.{u2} β)} {m : β -> γ}, (Monotone.{u3, u2} (Set.{u3} α) (Set.{u2} β) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) h) -> (Eq.{succ u1} (Filter.{u1} γ) (Filter.map.{u2, u1} β γ m (Filter.lift'.{u3, u2} α β f h)) (Filter.lift'.{u3, u1} α γ f (Function.comp.{succ u3, succ u2, succ u1} (Set.{u3} α) (Set.{u2} β) (Set.{u1} γ) (Set.image.{u2, u1} β γ m) h)))
Case conversion may be inaccurate. Consider using '#align filter.map_lift'_eq Filter.map_lift'_eqₓ'. -/
theorem map_lift'_eq {m : β → γ} (hh : Monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
  calc
    map m (f.lift' h) = f.lift (map m ∘ 𝓟 ∘ h) := map_lift_eq <| monotone_principal.comp hh
    _ = f.lift' (image m ∘ h) := by
      simp only [(· ∘ ·), Filter.lift', map_principal, eq_self_iff_true]
    
#align filter.map_lift'_eq Filter.map_lift'_eq

/- warning: filter.lift'_map_le -> Filter.lift'_map_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : (Set.{u2} β) -> (Set.{u3} γ)} {m : α -> β}, LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ))) (Filter.lift'.{u2, u3} β γ (Filter.map.{u1, u2} α β m f) g) (Filter.lift'.{u1, u3} α γ f (Function.comp.{succ u1, succ u2, succ u3} (Set.{u1} α) (Set.{u2} β) (Set.{u3} γ) g (Set.image.{u1, u2} α β m)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u3} β) -> (Set.{u2} γ)} {m : α -> β}, LE.le.{u2} (Filter.{u2} γ) (Preorder.toLE.{u2} (Filter.{u2} γ) (PartialOrder.toPreorder.{u2} (Filter.{u2} γ) (Filter.instPartialOrderFilter.{u2} γ))) (Filter.lift'.{u3, u2} β γ (Filter.map.{u1, u3} α β m f) g) (Filter.lift'.{u1, u2} α γ f (Function.comp.{succ u1, succ u3, succ u2} (Set.{u1} α) (Set.{u3} β) (Set.{u2} γ) g (Set.image.{u1, u3} α β m)))
Case conversion may be inaccurate. Consider using '#align filter.lift'_map_le Filter.lift'_map_leₓ'. -/
theorem lift'_map_le {g : Set β → Set γ} {m : α → β} : (map m f).lift' g ≤ f.lift' (g ∘ image m) :=
  lift_map_le
#align filter.lift'_map_le Filter.lift'_map_le

/- warning: filter.map_lift'_eq2 -> Filter.map_lift'_eq2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : (Set.{u2} β) -> (Set.{u3} γ)} {m : α -> β}, (Monotone.{u2, u3} (Set.{u2} β) (Set.{u3} γ) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u3} (Set.{u3} γ) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} γ) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} γ) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} γ) (Set.completeBooleanAlgebra.{u3} γ))))))) g) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.lift'.{u2, u3} β γ (Filter.map.{u1, u2} α β m f) g) (Filter.lift'.{u1, u3} α γ f (Function.comp.{succ u1, succ u2, succ u3} (Set.{u1} α) (Set.{u2} β) (Set.{u3} γ) g (Set.image.{u1, u2} α β m))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u3} β) -> (Set.{u2} γ)} {m : α -> β}, (Monotone.{u3, u2} (Set.{u3} β) (Set.{u2} γ) (PartialOrder.toPreorder.{u3} (Set.{u3} β) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} β) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} β) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} β) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} β) (Set.instCompleteBooleanAlgebraSet.{u3} β))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} γ) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} γ) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} γ) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} γ) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} γ) (Set.instCompleteBooleanAlgebraSet.{u2} γ))))))) g) -> (Eq.{succ u2} (Filter.{u2} γ) (Filter.lift'.{u3, u2} β γ (Filter.map.{u1, u3} α β m f) g) (Filter.lift'.{u1, u2} α γ f (Function.comp.{succ u1, succ u3, succ u2} (Set.{u1} α) (Set.{u3} β) (Set.{u2} γ) g (Set.image.{u1, u3} α β m))))
Case conversion may be inaccurate. Consider using '#align filter.map_lift'_eq2 Filter.map_lift'_eq2ₓ'. -/
theorem map_lift'_eq2 {g : Set β → Set γ} {m : α → β} (hg : Monotone g) :
    (map m f).lift' g = f.lift' (g ∘ image m) :=
  map_lift_eq2 <| monotone_principal.comp hg
#align filter.map_lift'_eq2 Filter.map_lift'_eq2

#print Filter.comap_lift'_eq /-
theorem comap_lift'_eq {m : γ → β} : comap m (f.lift' h) = f.lift' (preimage m ∘ h) := by
  simp only [Filter.lift', comap_lift_eq, (· ∘ ·), comap_principal]
#align filter.comap_lift'_eq Filter.comap_lift'_eq
-/

/- warning: filter.comap_lift'_eq2 -> Filter.comap_lift'_eq2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {m : β -> α} {g : (Set.{u2} β) -> (Set.{u3} γ)}, (Monotone.{u2, u3} (Set.{u2} β) (Set.{u3} γ) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u3} (Set.{u3} γ) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} γ) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} γ) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} γ) (Set.completeBooleanAlgebra.{u3} γ))))))) g) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.lift'.{u2, u3} β γ (Filter.comap.{u2, u1} β α m f) g) (Filter.lift'.{u1, u3} α γ f (Function.comp.{succ u1, succ u2, succ u3} (Set.{u1} α) (Set.{u2} β) (Set.{u3} γ) g (Set.preimage.{u2, u1} β α m))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : Filter.{u1} α} {m : β -> α} {g : (Set.{u3} β) -> (Set.{u2} γ)}, (Monotone.{u3, u2} (Set.{u3} β) (Set.{u2} γ) (PartialOrder.toPreorder.{u3} (Set.{u3} β) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} β) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} β) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} β) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} β) (Set.instCompleteBooleanAlgebraSet.{u3} β))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} γ) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} γ) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} γ) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} γ) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} γ) (Set.instCompleteBooleanAlgebraSet.{u2} γ))))))) g) -> (Eq.{succ u2} (Filter.{u2} γ) (Filter.lift'.{u3, u2} β γ (Filter.comap.{u3, u1} β α m f) g) (Filter.lift'.{u1, u2} α γ f (Function.comp.{succ u1, succ u3, succ u2} (Set.{u1} α) (Set.{u3} β) (Set.{u2} γ) g (Set.preimage.{u3, u1} β α m))))
Case conversion may be inaccurate. Consider using '#align filter.comap_lift'_eq2 Filter.comap_lift'_eq2ₓ'. -/
theorem comap_lift'_eq2 {m : β → α} {g : Set β → Set γ} (hg : Monotone g) :
    (comap m f).lift' g = f.lift' (g ∘ preimage m) :=
  comap_lift_eq2 <| monotone_principal.comp hg
#align filter.comap_lift'_eq2 Filter.comap_lift'_eq2

/- warning: filter.lift'_principal -> Filter.lift'_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {h : (Set.{u1} α) -> (Set.{u2} β)} {s : Set.{u1} α}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) h) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift'.{u1, u2} α β (Filter.principal.{u1} α s) h) (Filter.principal.{u2} β (h s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {h : (Set.{u2} α) -> (Set.{u1} β)} {s : Set.{u2} α}, (Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) h) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift'.{u2, u1} α β (Filter.principal.{u2} α s) h) (Filter.principal.{u1} β (h s)))
Case conversion may be inaccurate. Consider using '#align filter.lift'_principal Filter.lift'_principalₓ'. -/
theorem lift'_principal {s : Set α} (hh : Monotone h) : (𝓟 s).lift' h = 𝓟 (h s) :=
  lift_principal <| monotone_principal.comp hh
#align filter.lift'_principal Filter.lift'_principal

/- warning: filter.lift'_pure -> Filter.lift'_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {h : (Set.{u1} α) -> (Set.{u2} β)} {a : α}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) h) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift'.{u1, u2} α β (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a) h) (Filter.principal.{u2} β (h (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {h : (Set.{u2} α) -> (Set.{u1} β)} {a : α}, (Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) h) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift'.{u2, u1} α β (Pure.pure.{u2, u2} Filter.{u2} Filter.instPureFilter.{u2} α a) h) (Filter.principal.{u1} β (h (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a))))
Case conversion may be inaccurate. Consider using '#align filter.lift'_pure Filter.lift'_pureₓ'. -/
theorem lift'_pure {a : α} (hh : Monotone h) : (pure a : Filter α).lift' h = 𝓟 (h {a}) := by
  rw [← principal_singleton, lift'_principal hh]
#align filter.lift'_pure Filter.lift'_pure

/- warning: filter.lift'_bot -> Filter.lift'_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {h : (Set.{u1} α) -> (Set.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) h) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift'.{u1, u2} α β (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) h) (Filter.principal.{u2} β (h (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {h : (Set.{u2} α) -> (Set.{u1} β)}, (Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) h) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift'.{u2, u1} α β (Bot.bot.{u2} (Filter.{u2} α) (CompleteLattice.toBot.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α))) h) (Filter.principal.{u1} β (h (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)))))
Case conversion may be inaccurate. Consider using '#align filter.lift'_bot Filter.lift'_botₓ'. -/
theorem lift'_bot (hh : Monotone h) : (⊥ : Filter α).lift' h = 𝓟 (h ∅) := by
  rw [← principal_empty, lift'_principal hh]
#align filter.lift'_bot Filter.lift'_bot

/- warning: filter.le_lift' -> Filter.le_lift' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)} {g : Filter.{u2} β}, Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) g (Filter.lift'.{u1, u2} α β f h)) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (h s) g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h : (Set.{u2} α) -> (Set.{u1} β)} {g : Filter.{u1} β}, Iff (LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) g (Filter.lift'.{u2, u1} α β f h)) (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) (h s) g))
Case conversion may be inaccurate. Consider using '#align filter.le_lift' Filter.le_lift'ₓ'. -/
theorem le_lift' {f : Filter α} {h : Set α → Set β} {g : Filter β} :
    g ≤ f.lift' h ↔ ∀ s ∈ f, h s ∈ g :=
  le_lift.trans <| forall₂_congr fun s hs => le_principal_iff
#align filter.le_lift' Filter.le_lift'

/- warning: filter.principal_le_lift' -> Filter.principal_le_lift' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)} {t : Set.{u2} β}, Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.principal.{u2} β t) (Filter.lift'.{u1, u2} α β f h)) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t (h s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)} {t : Set.{u2} β}, Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.principal.{u2} β t) (Filter.lift'.{u1, u2} α β f h)) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) t (h s)))
Case conversion may be inaccurate. Consider using '#align filter.principal_le_lift' Filter.principal_le_lift'ₓ'. -/
theorem principal_le_lift' {t : Set β} : 𝓟 t ≤ f.lift' h ↔ ∀ s ∈ f, t ⊆ h s :=
  le_lift'
#align filter.principal_le_lift' Filter.principal_le_lift'

/- warning: filter.monotone_lift' -> Filter.monotone_lift' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u3} γ] {f : γ -> (Filter.{u1} α)} {g : γ -> (Set.{u1} α) -> (Set.{u2} β)}, (Monotone.{u3, u1} γ (Filter.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)) f) -> (Monotone.{u3, max u1 u2} γ ((Set.{u1} α) -> (Set.{u2} β)) _inst_1 (Pi.preorder.{u1, u2} (Set.{u1} α) (fun (ᾰ : Set.{u1} α) => Set.{u2} β) (fun (i : Set.{u1} α) => PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))))) g) -> (Monotone.{u3, u2} γ (Filter.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) (fun (c : γ) => Filter.lift'.{u1, u2} α β (f c) (g c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : Preorder.{u3} γ] {f : γ -> (Filter.{u2} α)} {g : γ -> (Set.{u2} α) -> (Set.{u1} β)}, (Monotone.{u3, u2} γ (Filter.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α)) f) -> (Monotone.{u3, max u2 u1} γ ((Set.{u2} α) -> (Set.{u1} β)) _inst_1 (Pi.preorder.{u2, u1} (Set.{u2} α) (fun (ᾰ : Set.{u2} α) => Set.{u1} β) (fun (i : Set.{u2} α) => PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))))) g) -> (Monotone.{u3, u1} γ (Filter.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β)) (fun (c : γ) => Filter.lift'.{u2, u1} α β (f c) (g c)))
Case conversion may be inaccurate. Consider using '#align filter.monotone_lift' Filter.monotone_lift'ₓ'. -/
theorem monotone_lift' [Preorder γ] {f : γ → Filter α} {g : γ → Set α → Set β} (hf : Monotone f)
    (hg : Monotone g) : Monotone fun c => (f c).lift' (g c) := fun a b h => lift'_mono (hf h) (hg h)
#align filter.monotone_lift' Filter.monotone_lift'

/- warning: filter.lift_lift'_assoc -> Filter.lift_lift'_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Set.{u2} β)} {h : (Set.{u2} β) -> (Filter.{u3} γ)}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) g) -> (Monotone.{u2, u3} (Set.{u2} β) (Filter.{u3} γ) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ)) h) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.lift.{u2, u3} β γ (Filter.lift'.{u1, u2} α β f g) h) (Filter.lift.{u1, u3} α γ f (fun (s : Set.{u1} α) => h (g s))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : Filter.{u3} α} {g : (Set.{u3} α) -> (Set.{u2} β)} {h : (Set.{u2} β) -> (Filter.{u1} γ)}, (Monotone.{u3, u2} (Set.{u3} α) (Set.{u2} β) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) g) -> (Monotone.{u2, u1} (Set.{u2} β) (Filter.{u1} γ) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} γ) (Filter.instPartialOrderFilter.{u1} γ)) h) -> (Eq.{succ u1} (Filter.{u1} γ) (Filter.lift.{u2, u1} β γ (Filter.lift'.{u3, u2} α β f g) h) (Filter.lift.{u3, u1} α γ f (fun (s : Set.{u3} α) => h (g s))))
Case conversion may be inaccurate. Consider using '#align filter.lift_lift'_assoc Filter.lift_lift'_assocₓ'. -/
theorem lift_lift'_assoc {g : Set α → Set β} {h : Set β → Filter γ} (hg : Monotone g)
    (hh : Monotone h) : (f.lift' g).lift h = f.lift fun s => h (g s) :=
  calc
    (f.lift' g).lift h = f.lift fun s => (𝓟 (g s)).lift h := lift_assoc (monotone_principal.comp hg)
    _ = f.lift fun s => h (g s) := by simp only [lift_principal, hh, eq_self_iff_true]
    
#align filter.lift_lift'_assoc Filter.lift_lift'_assoc

/- warning: filter.lift'_lift'_assoc -> Filter.lift'_lift'_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Set.{u2} β)} {h : (Set.{u2} β) -> (Set.{u3} γ)}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) g) -> (Monotone.{u2, u3} (Set.{u2} β) (Set.{u3} γ) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u3} (Set.{u3} γ) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} γ) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} γ) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} γ) (Set.completeBooleanAlgebra.{u3} γ))))))) h) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.lift'.{u2, u3} β γ (Filter.lift'.{u1, u2} α β f g) h) (Filter.lift'.{u1, u3} α γ f (fun (s : Set.{u1} α) => h (g s))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : Filter.{u3} α} {g : (Set.{u3} α) -> (Set.{u2} β)} {h : (Set.{u2} β) -> (Set.{u1} γ)}, (Monotone.{u3, u2} (Set.{u3} α) (Set.{u2} β) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) g) -> (Monotone.{u2, u1} (Set.{u2} β) (Set.{u1} γ) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} γ) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} γ) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} γ) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} γ) (Set.instCompleteBooleanAlgebraSet.{u1} γ))))))) h) -> (Eq.{succ u1} (Filter.{u1} γ) (Filter.lift'.{u2, u1} β γ (Filter.lift'.{u3, u2} α β f g) h) (Filter.lift'.{u3, u1} α γ f (fun (s : Set.{u3} α) => h (g s))))
Case conversion may be inaccurate. Consider using '#align filter.lift'_lift'_assoc Filter.lift'_lift'_assocₓ'. -/
theorem lift'_lift'_assoc {g : Set α → Set β} {h : Set β → Set γ} (hg : Monotone g)
    (hh : Monotone h) : (f.lift' g).lift' h = f.lift' fun s => h (g s) :=
  lift_lift'_assoc hg (monotone_principal.comp hh)
#align filter.lift'_lift'_assoc Filter.lift'_lift'_assoc

/- warning: filter.lift'_lift_assoc -> Filter.lift'_lift_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Filter.{u2} β)} {h : (Set.{u2} β) -> (Set.{u3} γ)}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.lift'.{u2, u3} β γ (Filter.lift.{u1, u2} α β f g) h) (Filter.lift.{u1, u3} α γ f (fun (s : Set.{u1} α) => Filter.lift'.{u2, u3} β γ (g s) h)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : Filter.{u3} α} {g : (Set.{u3} α) -> (Filter.{u2} β)} {h : (Set.{u2} β) -> (Set.{u1} γ)}, (Monotone.{u3, u2} (Set.{u3} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β)) g) -> (Eq.{succ u1} (Filter.{u1} γ) (Filter.lift'.{u2, u1} β γ (Filter.lift.{u3, u2} α β f g) h) (Filter.lift.{u3, u1} α γ f (fun (s : Set.{u3} α) => Filter.lift'.{u2, u1} β γ (g s) h)))
Case conversion may be inaccurate. Consider using '#align filter.lift'_lift_assoc Filter.lift'_lift_assocₓ'. -/
theorem lift'_lift_assoc {g : Set α → Filter β} {h : Set β → Set γ} (hg : Monotone g) :
    (f.lift g).lift' h = f.lift fun s => (g s).lift' h :=
  lift_assoc hg
#align filter.lift'_lift_assoc Filter.lift'_lift_assoc

/- warning: filter.lift_lift'_same_le_lift' -> Filter.lift_lift'_same_le_lift' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Set.{u1} α) -> (Set.{u2} β)}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift.{u1, u2} α β f (fun (s : Set.{u1} α) => Filter.lift'.{u1, u2} α β f (g s))) (Filter.lift'.{u1, u2} α β f (fun (s : Set.{u1} α) => g s s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Set.{u2} α) -> (Set.{u1} β)}, LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.lift.{u2, u1} α β f (fun (s : Set.{u2} α) => Filter.lift'.{u2, u1} α β f (g s))) (Filter.lift'.{u2, u1} α β f (fun (s : Set.{u2} α) => g s s))
Case conversion may be inaccurate. Consider using '#align filter.lift_lift'_same_le_lift' Filter.lift_lift'_same_le_lift'ₓ'. -/
theorem lift_lift'_same_le_lift' {g : Set α → Set α → Set β} :
    (f.lift fun s => f.lift' (g s)) ≤ f.lift' fun s => g s s :=
  lift_lift_same_le_lift
#align filter.lift_lift'_same_le_lift' Filter.lift_lift'_same_le_lift'

/- warning: filter.lift_lift'_same_eq_lift' -> Filter.lift_lift'_same_eq_lift' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : (Set.{u1} α) -> (Set.{u1} α) -> (Set.{u2} β)}, (forall (s : Set.{u1} α), Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (t : Set.{u1} α) => g s t)) -> (forall (t : Set.{u1} α), Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (s : Set.{u1} α) => g s t)) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β f (fun (s : Set.{u1} α) => Filter.lift'.{u1, u2} α β f (g s))) (Filter.lift'.{u1, u2} α β f (fun (s : Set.{u1} α) => g s s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : (Set.{u2} α) -> (Set.{u2} α) -> (Set.{u1} β)}, (forall (s : Set.{u2} α), Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (t : Set.{u2} α) => g s t)) -> (forall (t : Set.{u2} α), Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (s : Set.{u2} α) => g s t)) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift.{u2, u1} α β f (fun (s : Set.{u2} α) => Filter.lift'.{u2, u1} α β f (g s))) (Filter.lift'.{u2, u1} α β f (fun (s : Set.{u2} α) => g s s)))
Case conversion may be inaccurate. Consider using '#align filter.lift_lift'_same_eq_lift' Filter.lift_lift'_same_eq_lift'ₓ'. -/
theorem lift_lift'_same_eq_lift' {g : Set α → Set α → Set β} (hg₁ : ∀ s, Monotone fun t => g s t)
    (hg₂ : ∀ t, Monotone fun s => g s t) :
    (f.lift fun s => f.lift' (g s)) = f.lift' fun s => g s s :=
  lift_lift_same_eq_lift (fun s => monotone_principal.comp (hg₁ s)) fun t =>
    monotone_principal.comp (hg₂ t)
#align filter.lift_lift'_same_eq_lift' Filter.lift_lift'_same_eq_lift'

/- warning: filter.lift'_inf_principal_eq -> Filter.lift'_inf_principal_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)} {s : Set.{u2} β}, Eq.{succ u2} (Filter.{u2} β) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.lift'.{u1, u2} α β f h) (Filter.principal.{u2} β s)) (Filter.lift'.{u1, u2} α β f (fun (t : Set.{u1} α) => Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (h t) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h : (Set.{u2} α) -> (Set.{u1} β)} {s : Set.{u1} β}, Eq.{succ u1} (Filter.{u1} β) (HasInf.inf.{u1} (Filter.{u1} β) (Filter.instHasInfFilter.{u1} β) (Filter.lift'.{u2, u1} α β f h) (Filter.principal.{u1} β s)) (Filter.lift'.{u2, u1} α β f (fun (t : Set.{u2} α) => Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (h t) s))
Case conversion may be inaccurate. Consider using '#align filter.lift'_inf_principal_eq Filter.lift'_inf_principal_eqₓ'. -/
theorem lift'_inf_principal_eq {h : Set α → Set β} {s : Set β} :
    f.lift' h ⊓ 𝓟 s = f.lift' fun t => h t ∩ s := by
  simp only [Filter.lift', Filter.lift, (· ∘ ·), ← inf_principal, infᵢ_subtype', ← infᵢ_inf]
#align filter.lift'_inf_principal_eq Filter.lift'_inf_principal_eq

/- warning: filter.lift'_ne_bot_iff -> Filter.lift'_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {h : (Set.{u1} α) -> (Set.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) h) -> (Iff (Filter.NeBot.{u2} β (Filter.lift'.{u1, u2} α β f h)) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Set.Nonempty.{u2} β (h s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {h : (Set.{u2} α) -> (Set.{u1} β)}, (Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) h) -> (Iff (Filter.NeBot.{u1} β (Filter.lift'.{u2, u1} α β f h)) (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (Set.Nonempty.{u1} β (h s))))
Case conversion may be inaccurate. Consider using '#align filter.lift'_ne_bot_iff Filter.lift'_neBot_iffₓ'. -/
theorem lift'_neBot_iff (hh : Monotone h) : NeBot (f.lift' h) ↔ ∀ s ∈ f, (h s).Nonempty :=
  calc
    NeBot (f.lift' h) ↔ ∀ s ∈ f, NeBot (𝓟 (h s)) := lift_neBot_iff (monotone_principal.comp hh)
    _ ↔ ∀ s ∈ f, (h s).Nonempty := by simp only [principal_ne_bot_iff]
    
#align filter.lift'_ne_bot_iff Filter.lift'_neBot_iff

#print Filter.lift'_id /-
@[simp]
theorem lift'_id {f : Filter α} : f.lift' id = f :=
  lift_principal2
#align filter.lift'_id Filter.lift'_id
-/

/- warning: filter.lift'_infi -> Filter.lift'_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {f : ι -> (Filter.{u1} α)} {g : (Set.{u1} α) -> (Set.{u2} β)}, (forall (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (g s) (g t))) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift'.{u1, u2} α β (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f) g) (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => Filter.lift'.{u1, u2} α β (f i) g)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {f : ι -> (Filter.{u2} α)} {g : (Set.{u2} α) -> (Set.{u1} β)}, (forall (s : Set.{u2} α) (t : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (g s) (g t))) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift'.{u2, u1} α β (infᵢ.{u2, u3} (Filter.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α))) ι f) g) (infᵢ.{u1, u3} (Filter.{u1} β) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} β) (Filter.instCompleteLatticeFilter.{u1} β))) ι (fun (i : ι) => Filter.lift'.{u2, u1} α β (f i) g)))
Case conversion may be inaccurate. Consider using '#align filter.lift'_infi Filter.lift'_infᵢₓ'. -/
theorem lift'_infᵢ [Nonempty ι] {f : ι → Filter α} {g : Set α → Set β}
    (hg : ∀ s t, g (s ∩ t) = g s ∩ g t) : (infᵢ f).lift' g = ⨅ i, (f i).lift' g :=
  lift_infᵢ fun s t => by rw [inf_principal, (· ∘ ·), ← hg]
#align filter.lift'_infi Filter.lift'_infᵢ

/- warning: filter.lift'_infi_of_map_univ -> Filter.lift'_infᵢ_of_map_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> (Filter.{u1} α)} {g : (Set.{u1} α) -> (Set.{u2} β)}, (forall {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u2} (Set.{u2} β) (g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (g s) (g t))) -> (Eq.{succ u2} (Set.{u2} β) (g (Set.univ.{u1} α)) (Set.univ.{u2} β)) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift'.{u1, u2} α β (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f) g) (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => Filter.lift'.{u1, u2} α β (f i) g)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {f : ι -> (Filter.{u3} α)} {g : (Set.{u3} α) -> (Set.{u2} β)}, (forall {s : Set.{u3} α} {t : Set.{u3} α}, Eq.{succ u2} (Set.{u2} β) (g (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (g s) (g t))) -> (Eq.{succ u2} (Set.{u2} β) (g (Set.univ.{u3} α)) (Set.univ.{u2} β)) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift'.{u3, u2} α β (infᵢ.{u3, u1} (Filter.{u3} α) (ConditionallyCompleteLattice.toInfSet.{u3} (Filter.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))) ι f) g) (infᵢ.{u2, u1} (Filter.{u2} β) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) ι (fun (i : ι) => Filter.lift'.{u3, u2} α β (f i) g)))
Case conversion may be inaccurate. Consider using '#align filter.lift'_infi_of_map_univ Filter.lift'_infᵢ_of_map_univₓ'. -/
theorem lift'_infᵢ_of_map_univ {f : ι → Filter α} {g : Set α → Set β}
    (hg : ∀ {s t}, g (s ∩ t) = g s ∩ g t) (hg' : g univ = univ) :
    (infᵢ f).lift' g = ⨅ i, (f i).lift' g :=
  lift_infᵢ_of_map_univ (fun s t => by rw [inf_principal, (· ∘ ·), ← hg])
    (by rw [Function.comp_apply, hg', principal_univ])
#align filter.lift'_infi_of_map_univ Filter.lift'_infᵢ_of_map_univ

/- warning: filter.lift'_inf -> Filter.lift'_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Filter.{u1} α) (g : Filter.{u1} α) {s : (Set.{u1} α) -> (Set.{u2} β)}, (forall (t₁ : Set.{u1} α) (t₂ : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t₁ t₂)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (s t₁) (s t₂))) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift'.{u1, u2} α β (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g) s) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.lift'.{u1, u2} α β f s) (Filter.lift'.{u1, u2} α β g s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Filter.{u2} α) (g : Filter.{u2} α) {s : (Set.{u2} α) -> (Set.{u1} β)}, (forall (t₁ : Set.{u2} α) (t₂ : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (s (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (s t₁) (s t₂))) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.lift'.{u2, u1} α β (HasInf.inf.{u2} (Filter.{u2} α) (Filter.instHasInfFilter.{u2} α) f g) s) (HasInf.inf.{u1} (Filter.{u1} β) (Filter.instHasInfFilter.{u1} β) (Filter.lift'.{u2, u1} α β f s) (Filter.lift'.{u2, u1} α β g s)))
Case conversion may be inaccurate. Consider using '#align filter.lift'_inf Filter.lift'_infₓ'. -/
theorem lift'_inf (f g : Filter α) {s : Set α → Set β} (hs : ∀ t₁ t₂, s (t₁ ∩ t₂) = s t₁ ∩ s t₂) :
    (f ⊓ g).lift' s = f.lift' s ⊓ g.lift' s :=
  by
  have : (⨅ b : Bool, cond b f g).lift' s = ⨅ b : Bool, (cond b f g).lift' s := lift'_infᵢ @hs
  simpa only [infᵢ_bool_eq]
#align filter.lift'_inf Filter.lift'_inf

/- warning: filter.lift'_inf_le -> Filter.lift'_inf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Filter.{u1} α) (g : Filter.{u1} α) (s : (Set.{u1} α) -> (Set.{u2} β)), LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift'.{u1, u2} α β (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g) s) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.lift'.{u1, u2} α β f s) (Filter.lift'.{u1, u2} α β g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Filter.{u2} α) (g : Filter.{u2} α) (s : (Set.{u2} α) -> (Set.{u1} β)), LE.le.{u1} (Filter.{u1} β) (Preorder.toLE.{u1} (Filter.{u1} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} β) (Filter.instPartialOrderFilter.{u1} β))) (Filter.lift'.{u2, u1} α β (HasInf.inf.{u2} (Filter.{u2} α) (Filter.instHasInfFilter.{u2} α) f g) s) (HasInf.inf.{u1} (Filter.{u1} β) (Filter.instHasInfFilter.{u1} β) (Filter.lift'.{u2, u1} α β f s) (Filter.lift'.{u2, u1} α β g s))
Case conversion may be inaccurate. Consider using '#align filter.lift'_inf_le Filter.lift'_inf_leₓ'. -/
theorem lift'_inf_le (f g : Filter α) (s : Set α → Set β) :
    (f ⊓ g).lift' s ≤ f.lift' s ⊓ g.lift' s :=
  le_inf (lift'_mono inf_le_left le_rfl) (lift'_mono inf_le_right le_rfl)
#align filter.lift'_inf_le Filter.lift'_inf_le

#print Filter.comap_eq_lift' /-
theorem comap_eq_lift' {f : Filter β} {m : α → β} : comap m f = f.lift' (preimage m) :=
  Filter.ext fun s => (mem_lift'_sets monotone_preimage).symm
#align filter.comap_eq_lift' Filter.comap_eq_lift'
-/

end Lift'

section Prod

variable {f : Filter α}

/- warning: filter.prod_def -> Filter.prod_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u2} β}, Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.prod.{u1, u2} α β f g) (Filter.lift.{u1, max u1 u2} α (Prod.{u1, u2} α β) f (fun (s : Set.{u1} α) => Filter.lift'.{u2, max u1 u2} β (Prod.{u1, u2} α β) g (fun (t : Set.{u2} β) => Set.prod.{u1, u2} α β s t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : Filter.{u1} β}, Eq.{max (succ u2) (succ u1)} (Filter.{max u1 u2} (Prod.{u2, u1} α β)) (Filter.prod.{u2, u1} α β f g) (Filter.lift.{u2, max u1 u2} α (Prod.{u2, u1} α β) f (fun (s : Set.{u2} α) => Filter.lift'.{u1, max u1 u2} β (Prod.{u2, u1} α β) g (fun (t : Set.{u1} β) => Set.prod.{u2, u1} α β s t)))
Case conversion may be inaccurate. Consider using '#align filter.prod_def Filter.prod_defₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_def {f : Filter α} {g : Filter β} : f ×ᶠ g = f.lift fun s => g.lift' fun t => s ×ˢ t :=
  by
  have : ∀ (s : Set α) (t : Set β), 𝓟 (s ×ˢ t) = (𝓟 s).comap Prod.fst ⊓ (𝓟 t).comap Prod.snd := by
    simp only [principal_eq_iff_eq, comap_principal, inf_principal] <;> intros <;> rfl
  simp only [Filter.lift', Function.comp, this, lift_inf, lift_const, lift_inf]
  rw [← comap_lift_eq, ← comap_lift_eq]
  simp only [Filter.prod, lift_principal2]
#align filter.prod_def Filter.prod_def

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Filter.prod_same_eq /-
theorem prod_same_eq : f ×ᶠ f = f.lift' fun t : Set α => t ×ˢ t :=
  prod_def.trans <|
    lift_lift'_same_eq_lift' (fun s => monotone_const.set_prod monotone_id) fun t =>
      monotone_id.set_prod monotone_const
#align filter.prod_same_eq Filter.prod_same_eq
-/

/- warning: filter.mem_prod_same_iff -> Filter.mem_prod_same_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (Filter.prod.{u1, u1} α α f f)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α t t) s)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (Filter.prod.{u1, u1} α α f f)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α t t) s)))
Case conversion may be inaccurate. Consider using '#align filter.mem_prod_same_iff Filter.mem_prod_same_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_prod_same_iff {s : Set (α × α)} : s ∈ f ×ᶠ f ↔ ∃ t ∈ f, t ×ˢ t ⊆ s :=
  by
  rw [prod_same_eq, mem_lift'_sets]
  exact monotone_id.set_prod monotone_id
#align filter.mem_prod_same_iff Filter.mem_prod_same_iff

/- warning: filter.tendsto_prod_self_iff -> Filter.tendsto_prod_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : (Prod.{u1, u1} α α) -> β} {x : Filter.{u1} α} {y : Filter.{u2} β}, Iff (Filter.Tendsto.{u1, u2} (Prod.{u1, u1} α α) β f (Filter.prod.{u1, u1} α α x x) y) (forall (W : Set.{u2} β), (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) W y) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U x) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U x) => forall (x : α) (x' : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x U) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x' U) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f (Prod.mk.{u1, u1} α α x x')) W)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : (Prod.{u2, u2} α α) -> β} {x : Filter.{u2} α} {y : Filter.{u1} β}, Iff (Filter.Tendsto.{u2, u1} (Prod.{u2, u2} α α) β f (Filter.prod.{u2, u2} α α x x) y) (forall (W : Set.{u1} β), (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) W y) -> (Exists.{succ u2} (Set.{u2} α) (fun (U : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) U x) (forall (x : α) (x' : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x U) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x' U) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f (Prod.mk.{u2, u2} α α x x')) W)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_prod_self_iff Filter.tendsto_prod_self_iffₓ'. -/
theorem tendsto_prod_self_iff {f : α × α → β} {x : Filter α} {y : Filter β} :
    Filter.Tendsto f (x ×ᶠ x) y ↔ ∀ W ∈ y, ∃ U ∈ x, ∀ x x' : α, x ∈ U → x' ∈ U → f (x, x') ∈ W := by
  simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff, exists_prop, iff_self_iff]
#align filter.tendsto_prod_self_iff Filter.tendsto_prod_self_iff

variable {α₁ : Type _} {α₂ : Type _} {β₁ : Type _} {β₂ : Type _}

/- warning: filter.prod_lift_lift -> Filter.prod_lift_lift is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} {f₁ : Filter.{u1} α₁} {f₂ : Filter.{u2} α₂} {g₁ : (Set.{u1} α₁) -> (Filter.{u3} β₁)} {g₂ : (Set.{u2} α₂) -> (Filter.{u4} β₂)}, (Monotone.{u1, u3} (Set.{u1} α₁) (Filter.{u3} β₁) (PartialOrder.toPreorder.{u1} (Set.{u1} α₁) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α₁) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α₁) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α₁) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α₁) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α₁) (Set.completeBooleanAlgebra.{u1} α₁))))))) (PartialOrder.toPreorder.{u3} (Filter.{u3} β₁) (Filter.partialOrder.{u3} β₁)) g₁) -> (Monotone.{u2, u4} (Set.{u2} α₂) (Filter.{u4} β₂) (PartialOrder.toPreorder.{u2} (Set.{u2} α₂) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α₂) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α₂) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α₂) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α₂) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α₂) (Set.completeBooleanAlgebra.{u2} α₂))))))) (PartialOrder.toPreorder.{u4} (Filter.{u4} β₂) (Filter.partialOrder.{u4} β₂)) g₂) -> (Eq.{succ (max u3 u4)} (Filter.{max u3 u4} (Prod.{u3, u4} β₁ β₂)) (Filter.prod.{u3, u4} β₁ β₂ (Filter.lift.{u1, u3} α₁ β₁ f₁ g₁) (Filter.lift.{u2, u4} α₂ β₂ f₂ g₂)) (Filter.lift.{u1, max u3 u4} α₁ (Prod.{u3, u4} β₁ β₂) f₁ (fun (s : Set.{u1} α₁) => Filter.lift.{u2, max u3 u4} α₂ (Prod.{u3, u4} β₁ β₂) f₂ (fun (t : Set.{u2} α₂) => Filter.prod.{u3, u4} β₁ β₂ (g₁ s) (g₂ t)))))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} {f₁ : Filter.{u4} α₁} {f₂ : Filter.{u3} α₂} {g₁ : (Set.{u4} α₁) -> (Filter.{u2} β₁)} {g₂ : (Set.{u3} α₂) -> (Filter.{u1} β₂)}, (Monotone.{u4, u2} (Set.{u4} α₁) (Filter.{u2} β₁) (PartialOrder.toPreorder.{u4} (Set.{u4} α₁) (CompleteSemilatticeInf.toPartialOrder.{u4} (Set.{u4} α₁) (CompleteLattice.toCompleteSemilatticeInf.{u4} (Set.{u4} α₁) (Order.Coframe.toCompleteLattice.{u4} (Set.{u4} α₁) (CompleteDistribLattice.toCoframe.{u4} (Set.{u4} α₁) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u4} (Set.{u4} α₁) (Set.instCompleteBooleanAlgebraSet.{u4} α₁))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β₁) (Filter.instPartialOrderFilter.{u2} β₁)) g₁) -> (Monotone.{u3, u1} (Set.{u3} α₂) (Filter.{u1} β₂) (PartialOrder.toPreorder.{u3} (Set.{u3} α₂) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α₂) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α₂) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α₂) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α₂) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α₂) (Set.instCompleteBooleanAlgebraSet.{u3} α₂))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} β₂) (Filter.instPartialOrderFilter.{u1} β₂)) g₂) -> (Eq.{max (succ u2) (succ u1)} (Filter.{max u1 u2} (Prod.{u2, u1} β₁ β₂)) (Filter.prod.{u2, u1} β₁ β₂ (Filter.lift.{u4, u2} α₁ β₁ f₁ g₁) (Filter.lift.{u3, u1} α₂ β₂ f₂ g₂)) (Filter.lift.{u4, max u1 u2} α₁ (Prod.{u2, u1} β₁ β₂) f₁ (fun (s : Set.{u4} α₁) => Filter.lift.{u3, max u1 u2} α₂ (Prod.{u2, u1} β₁ β₂) f₂ (fun (t : Set.{u3} α₂) => Filter.prod.{u2, u1} β₁ β₂ (g₁ s) (g₂ t)))))
Case conversion may be inaccurate. Consider using '#align filter.prod_lift_lift Filter.prod_lift_liftₓ'. -/
theorem prod_lift_lift {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ → Filter β₁}
    {g₂ : Set α₂ → Filter β₂} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift g₁ ×ᶠ f₂.lift g₂ = f₁.lift fun s => f₂.lift fun t => g₁ s ×ᶠ g₂ t :=
  by
  simp only [prod_def, lift_assoc hg₁]
  apply congr_arg; funext x
  rw [lift_comm]
  apply congr_arg; funext y
  apply lift'_lift_assoc hg₂
#align filter.prod_lift_lift Filter.prod_lift_lift

/- warning: filter.prod_lift'_lift' -> Filter.prod_lift'_lift' is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} {f₁ : Filter.{u1} α₁} {f₂ : Filter.{u2} α₂} {g₁ : (Set.{u1} α₁) -> (Set.{u3} β₁)} {g₂ : (Set.{u2} α₂) -> (Set.{u4} β₂)}, (Monotone.{u1, u3} (Set.{u1} α₁) (Set.{u3} β₁) (PartialOrder.toPreorder.{u1} (Set.{u1} α₁) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α₁) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α₁) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α₁) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α₁) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α₁) (Set.completeBooleanAlgebra.{u1} α₁))))))) (PartialOrder.toPreorder.{u3} (Set.{u3} β₁) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} β₁) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} β₁) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} β₁) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} β₁) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} β₁) (Set.completeBooleanAlgebra.{u3} β₁))))))) g₁) -> (Monotone.{u2, u4} (Set.{u2} α₂) (Set.{u4} β₂) (PartialOrder.toPreorder.{u2} (Set.{u2} α₂) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α₂) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α₂) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α₂) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α₂) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α₂) (Set.completeBooleanAlgebra.{u2} α₂))))))) (PartialOrder.toPreorder.{u4} (Set.{u4} β₂) (CompleteSemilatticeInf.toPartialOrder.{u4} (Set.{u4} β₂) (CompleteLattice.toCompleteSemilatticeInf.{u4} (Set.{u4} β₂) (Order.Coframe.toCompleteLattice.{u4} (Set.{u4} β₂) (CompleteDistribLattice.toCoframe.{u4} (Set.{u4} β₂) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u4} (Set.{u4} β₂) (Set.completeBooleanAlgebra.{u4} β₂))))))) g₂) -> (Eq.{succ (max u3 u4)} (Filter.{max u3 u4} (Prod.{u3, u4} β₁ β₂)) (Filter.prod.{u3, u4} β₁ β₂ (Filter.lift'.{u1, u3} α₁ β₁ f₁ g₁) (Filter.lift'.{u2, u4} α₂ β₂ f₂ g₂)) (Filter.lift.{u1, max u3 u4} α₁ (Prod.{u3, u4} β₁ β₂) f₁ (fun (s : Set.{u1} α₁) => Filter.lift'.{u2, max u3 u4} α₂ (Prod.{u3, u4} β₁ β₂) f₂ (fun (t : Set.{u2} α₂) => Set.prod.{u3, u4} β₁ β₂ (g₁ s) (g₂ t)))))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} {f₁ : Filter.{u4} α₁} {f₂ : Filter.{u3} α₂} {g₁ : (Set.{u4} α₁) -> (Set.{u2} β₁)} {g₂ : (Set.{u3} α₂) -> (Set.{u1} β₂)}, (Monotone.{u4, u2} (Set.{u4} α₁) (Set.{u2} β₁) (PartialOrder.toPreorder.{u4} (Set.{u4} α₁) (CompleteSemilatticeInf.toPartialOrder.{u4} (Set.{u4} α₁) (CompleteLattice.toCompleteSemilatticeInf.{u4} (Set.{u4} α₁) (Order.Coframe.toCompleteLattice.{u4} (Set.{u4} α₁) (CompleteDistribLattice.toCoframe.{u4} (Set.{u4} α₁) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u4} (Set.{u4} α₁) (Set.instCompleteBooleanAlgebraSet.{u4} α₁))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β₁) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β₁) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β₁) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β₁) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β₁) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β₁) (Set.instCompleteBooleanAlgebraSet.{u2} β₁))))))) g₁) -> (Monotone.{u3, u1} (Set.{u3} α₂) (Set.{u1} β₂) (PartialOrder.toPreorder.{u3} (Set.{u3} α₂) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α₂) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α₂) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α₂) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α₂) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α₂) (Set.instCompleteBooleanAlgebraSet.{u3} α₂))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β₂) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β₂) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β₂) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β₂) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β₂) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β₂) (Set.instCompleteBooleanAlgebraSet.{u1} β₂))))))) g₂) -> (Eq.{max (succ u2) (succ u1)} (Filter.{max u1 u2} (Prod.{u2, u1} β₁ β₂)) (Filter.prod.{u2, u1} β₁ β₂ (Filter.lift'.{u4, u2} α₁ β₁ f₁ g₁) (Filter.lift'.{u3, u1} α₂ β₂ f₂ g₂)) (Filter.lift.{u4, max u1 u2} α₁ (Prod.{u2, u1} β₁ β₂) f₁ (fun (s : Set.{u4} α₁) => Filter.lift'.{u3, max u1 u2} α₂ (Prod.{u2, u1} β₁ β₂) f₂ (fun (t : Set.{u3} α₂) => Set.prod.{u2, u1} β₁ β₂ (g₁ s) (g₂ t)))))
Case conversion may be inaccurate. Consider using '#align filter.prod_lift'_lift' Filter.prod_lift'_lift'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_lift'_lift' {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ → Set β₁}
    {g₂ : Set α₂ → Set β₂} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift' g₁ ×ᶠ f₂.lift' g₂ = f₁.lift fun s => f₂.lift' fun t => g₁ s ×ˢ g₂ t :=
  calc
    f₁.lift' g₁ ×ᶠ f₂.lift' g₂ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s) ×ᶠ 𝓟 (g₂ t) :=
      prod_lift_lift (monotone_principal.comp hg₁) (monotone_principal.comp hg₂)
    _ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s ×ˢ g₂ t) := by
      simp only [prod_principal_principal]
    
#align filter.prod_lift'_lift' Filter.prod_lift'_lift'

end Prod

end Filter

