/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov

! This file was ported from Lean 3 source module order.filter.cofinite
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.AtTopBot
import Mathbin.Order.Filter.Pi

/-!
# The cofinite filter

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define

`cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `at_top`.

## TODO

Define filters for other cardinalities of the complement.
-/


open Set Function

open Classical

variable {ι α β : Type _} {l : Filter α}

namespace Filter

#print Filter.cofinite /-
/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : Filter α where
  sets := { s | sᶜ.Finite }
  univ_sets := by simp only [compl_univ, finite_empty, mem_set_of_eq]
  sets_of_superset s t (hs : sᶜ.Finite) (st : s ⊆ t) := hs.Subset <| compl_subset_compl.2 st
  inter_sets s t (hs : sᶜ.Finite) (ht : tᶜ.Finite) := by
    simp only [compl_inter, finite.union, ht, hs, mem_set_of_eq]
#align filter.cofinite Filter.cofinite
-/

/- warning: filter.mem_cofinite -> Filter.mem_cofinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (Filter.cofinite.{u1} α)) (Set.Finite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (Filter.cofinite.{u1} α)) (Set.Finite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align filter.mem_cofinite Filter.mem_cofiniteₓ'. -/
@[simp]
theorem mem_cofinite {s : Set α} : s ∈ @cofinite α ↔ sᶜ.Finite :=
  Iff.rfl
#align filter.mem_cofinite Filter.mem_cofinite

#print Filter.eventually_cofinite /-
@[simp]
theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite :=
  Iff.rfl
#align filter.eventually_cofinite Filter.eventually_cofinite
-/

/- warning: filter.has_basis_cofinite -> Filter.hasBasis_cofinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Filter.HasBasis.{u1, succ u1} α (Set.{u1} α) (Filter.cofinite.{u1} α) (fun (s : Set.{u1} α) => Set.Finite.{u1} α s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Filter.HasBasis.{u1, succ u1} α (Set.{u1} α) (Filter.cofinite.{u1} α) (fun (s : Set.{u1} α) => Set.Finite.{u1} α s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_cofinite Filter.hasBasis_cofiniteₓ'. -/
theorem hasBasis_cofinite : HasBasis cofinite (fun s : Set α => s.Finite) compl :=
  ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).Subset⟩, fun ⟨t, htf, hts⟩ =>
      htf.Subset <| compl_subset_comm.2 hts⟩⟩
#align filter.has_basis_cofinite Filter.hasBasis_cofinite

#print Filter.cofinite_neBot /-
instance cofinite_neBot [Infinite α] : NeBot (@cofinite α) :=
  hasBasis_cofinite.ne_bot_iff.2 fun s hs => hs.infinite_compl.Nonempty
#align filter.cofinite_ne_bot Filter.cofinite_neBot
-/

#print Filter.frequently_cofinite_iff_infinite /-
theorem frequently_cofinite_iff_infinite {p : α → Prop} :
    (∃ᶠ x in cofinite, p x) ↔ Set.Infinite { x | p x } := by
  simp only [Filter.Frequently, Filter.Eventually, mem_cofinite, compl_set_of, Classical.not_not,
    Set.Infinite]
#align filter.frequently_cofinite_iff_infinite Filter.frequently_cofinite_iff_infinite
-/

/- warning: set.finite.compl_mem_cofinite -> Set.Finite.compl_mem_cofinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (Filter.cofinite.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (Filter.cofinite.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.finite.compl_mem_cofinite Set.Finite.compl_mem_cofiniteₓ'. -/
theorem Set.Finite.compl_mem_cofinite {s : Set α} (hs : s.Finite) : sᶜ ∈ @cofinite α :=
  mem_cofinite.2 <| (compl_compl s).symm ▸ hs
#align set.finite.compl_mem_cofinite Set.Finite.compl_mem_cofinite

#print Set.Finite.eventually_cofinite_nmem /-
theorem Set.Finite.eventually_cofinite_nmem {s : Set α} (hs : s.Finite) : ∀ᶠ x in cofinite, x ∉ s :=
  hs.compl_mem_cofinite
#align set.finite.eventually_cofinite_nmem Set.Finite.eventually_cofinite_nmem
-/

#print Finset.eventually_cofinite_nmem /-
theorem Finset.eventually_cofinite_nmem (s : Finset α) : ∀ᶠ x in cofinite, x ∉ s :=
  s.finite_to_set.eventually_cofinite_nmem
#align finset.eventually_cofinite_nmem Finset.eventually_cofinite_nmem
-/

#print Set.infinite_iff_frequently_cofinite /-
theorem Set.infinite_iff_frequently_cofinite {s : Set α} :
    Set.Infinite s ↔ ∃ᶠ x in cofinite, x ∈ s :=
  frequently_cofinite_iff_infinite.symm
#align set.infinite_iff_frequently_cofinite Set.infinite_iff_frequently_cofinite
-/

#print Filter.eventually_cofinite_ne /-
theorem eventually_cofinite_ne (x : α) : ∀ᶠ a in cofinite, a ≠ x :=
  (Set.finite_singleton x).eventually_cofinite_nmem
#align filter.eventually_cofinite_ne Filter.eventually_cofinite_ne
-/

/- warning: filter.le_cofinite_iff_compl_singleton_mem -> Filter.le_cofinite_iff_compl_singleton_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l (Filter.cofinite.{u1} α)) (forall (x : α), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) l)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l (Filter.cofinite.{u1} α)) (forall (x : α), Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) l)
Case conversion may be inaccurate. Consider using '#align filter.le_cofinite_iff_compl_singleton_mem Filter.le_cofinite_iff_compl_singleton_memₓ'. -/
theorem le_cofinite_iff_compl_singleton_mem : l ≤ cofinite ↔ ∀ x, {x}ᶜ ∈ l :=
  by
  refine' ⟨fun h x => h (finite_singleton x).compl_mem_cofinite, fun h s (hs : sᶜ.Finite) => _⟩
  rw [← compl_compl s, ← bUnion_of_singleton (sᶜ), compl_Union₂, Filter.binterᵢ_mem hs]
  exact fun x _ => h x
#align filter.le_cofinite_iff_compl_singleton_mem Filter.le_cofinite_iff_compl_singleton_mem

/- warning: filter.le_cofinite_iff_eventually_ne -> Filter.le_cofinite_iff_eventually_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l (Filter.cofinite.{u1} α)) (forall (x : α), Filter.Eventually.{u1} α (fun (y : α) => Ne.{succ u1} α y x) l)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l (Filter.cofinite.{u1} α)) (forall (x : α), Filter.Eventually.{u1} α (fun (y : α) => Ne.{succ u1} α y x) l)
Case conversion may be inaccurate. Consider using '#align filter.le_cofinite_iff_eventually_ne Filter.le_cofinite_iff_eventually_neₓ'. -/
theorem le_cofinite_iff_eventually_ne : l ≤ cofinite ↔ ∀ x, ∀ᶠ y in l, y ≠ x :=
  le_cofinite_iff_compl_singleton_mem
#align filter.le_cofinite_iff_eventually_ne Filter.le_cofinite_iff_eventually_ne

/- warning: filter.at_top_le_cofinite -> Filter.atTop_le_cofinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.atTop.{u1} α _inst_1) (Filter.cofinite.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.atTop.{u1} α _inst_1) (Filter.cofinite.{u1} α)
Case conversion may be inaccurate. Consider using '#align filter.at_top_le_cofinite Filter.atTop_le_cofiniteₓ'. -/
/-- If `α` is a preorder with no maximal element, then `at_top ≤ cofinite`. -/
theorem atTop_le_cofinite [Preorder α] [NoMaxOrder α] : (atTop : Filter α) ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr eventually_ne_atTop
#align filter.at_top_le_cofinite Filter.atTop_le_cofinite

/- warning: filter.comap_cofinite_le -> Filter.comap_cofinite_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.comap.{u1, u2} α β f (Filter.cofinite.{u2} β)) (Filter.cofinite.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), LE.le.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) (Filter.comap.{u2, u1} α β f (Filter.cofinite.{u1} β)) (Filter.cofinite.{u2} α)
Case conversion may be inaccurate. Consider using '#align filter.comap_cofinite_le Filter.comap_cofinite_leₓ'. -/
theorem comap_cofinite_le (f : α → β) : comap f cofinite ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr fun x =>
    mem_comap.2 ⟨{f x}ᶜ, (finite_singleton _).compl_mem_cofinite, fun y => ne_of_apply_ne f⟩
#align filter.comap_cofinite_le Filter.comap_cofinite_le

/- warning: filter.coprod_cofinite -> Filter.coprod_cofinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.coprod.{u1, u2} α β (Filter.cofinite.{u1} α) (Filter.cofinite.{u2} β)) (Filter.cofinite.{max u1 u2} (Prod.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Filter.{max u1 u2} (Prod.{u2, u1} α β)) (Filter.coprod.{u2, u1} α β (Filter.cofinite.{u2} α) (Filter.cofinite.{u1} β)) (Filter.cofinite.{max u2 u1} (Prod.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align filter.coprod_cofinite Filter.coprod_cofiniteₓ'. -/
/-- The coproduct of the cofinite filters on two types is the cofinite filter on their product. -/
theorem coprod_cofinite : (cofinite : Filter α).coprod (cofinite : Filter β) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_coprod, mem_cofinite, compl_compl, finite_image_fst_and_snd_iff]
#align filter.coprod_cofinite Filter.coprod_cofinite

#print Filter.coprodᵢ_cofinite /-
/-- Finite product of finite sets is finite -/
theorem coprodᵢ_cofinite {α : ι → Type _} [Finite ι] :
    (Filter.coprodᵢ fun i => (cofinite : Filter (α i))) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_Coprod, mem_cofinite, compl_compl, forall_finite_image_eval_iff]
#align filter.Coprod_cofinite Filter.coprodᵢ_cofinite
-/

/- warning: filter.disjoint_cofinite_left -> Filter.disjoint_cofinite_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Filter.cofinite.{u1} α) l) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) => Set.Finite.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Filter.cofinite.{u1} α) l) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l) (Set.Finite.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align filter.disjoint_cofinite_left Filter.disjoint_cofinite_leftₓ'. -/
@[simp]
theorem disjoint_cofinite_left : Disjoint cofinite l ↔ ∃ s ∈ l, Set.Finite s :=
  by
  simp only [has_basis_cofinite.disjoint_iff l.basis_sets, id, disjoint_compl_left_iff_subset]
  exact
    ⟨fun ⟨s, hs, t, ht, hts⟩ => ⟨t, ht, hs.Subset hts⟩, fun ⟨s, hs, hsf⟩ =>
      ⟨s, hsf, s, hs, subset.rfl⟩⟩
#align filter.disjoint_cofinite_left Filter.disjoint_cofinite_left

/- warning: filter.disjoint_cofinite_right -> Filter.disjoint_cofinite_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) l (Filter.cofinite.{u1} α)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) => Set.Finite.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) l (Filter.cofinite.{u1} α)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l) (Set.Finite.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align filter.disjoint_cofinite_right Filter.disjoint_cofinite_rightₓ'. -/
@[simp]
theorem disjoint_cofinite_right : Disjoint l cofinite ↔ ∃ s ∈ l, Set.Finite s :=
  disjoint_comm.trans disjoint_cofinite_left
#align filter.disjoint_cofinite_right Filter.disjoint_cofinite_right

end Filter

open Filter

#print Nat.cofinite_eq_atTop /-
/-- For natural numbers the filters `cofinite` and `at_top` coincide. -/
theorem Nat.cofinite_eq_atTop : @cofinite ℕ = at_top :=
  by
  refine' le_antisymm _ at_top_le_cofinite
  refine' at_top_basis.ge_iff.2 fun N hN => _
  simpa only [mem_cofinite, compl_Ici] using finite_lt_nat N
#align nat.cofinite_eq_at_top Nat.cofinite_eq_atTop
-/

#print Nat.frequently_atTop_iff_infinite /-
theorem Nat.frequently_atTop_iff_infinite {p : ℕ → Prop} :
    (∃ᶠ n in at_top, p n) ↔ Set.Infinite { n | p n } := by
  rw [← Nat.cofinite_eq_atTop, frequently_cofinite_iff_infinite]
#align nat.frequently_at_top_iff_infinite Nat.frequently_atTop_iff_infinite
-/

/- warning: filter.tendsto.exists_within_forall_le -> Filter.Tendsto.exists_within_forall_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {f : α -> β}, (Filter.Tendsto.{u1, u2} α β f (Filter.cofinite.{u1} α) (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))))) -> (Exists.{succ u1} α (fun (a₀ : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a₀ s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a₀ s) => forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a₀) (f a))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (forall {f : α -> β}, (Filter.Tendsto.{u2, u1} α β f (Filter.cofinite.{u2} α) (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))))) -> (Exists.{succ u2} α (fun (a₀ : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a₀ s) (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f a₀) (f a))))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.exists_within_forall_le Filter.Tendsto.exists_within_forall_leₓ'. -/
theorem Filter.Tendsto.exists_within_forall_le {α β : Type _} [LinearOrder β] {s : Set α}
    (hs : s.Nonempty) {f : α → β} (hf : Filter.Tendsto f Filter.cofinite Filter.atTop) :
    ∃ a₀ ∈ s, ∀ a ∈ s, f a₀ ≤ f a :=
  by
  rcases em (∃ y ∈ s, ∃ x, f y < x) with (⟨y, hys, x, hx⟩ | not_all_top)
  · -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    have : { y | ¬x ≤ f y }.Finite := filter.eventually_cofinite.mp (tendsto_at_top.1 hf x)
    simp only [not_le] at this
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ :=
      exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
    refine' ⟨a₀, ha₀s, fun a has => (lt_or_le (f a) x).elim _ (le_trans ha₀.le)⟩
    exact fun h => others_bigger a ⟨h, has⟩
  · -- in this case, f is constant because all values are at top
    push_neg  at not_all_top
    obtain ⟨a₀, ha₀s⟩ := hs
    exact ⟨a₀, ha₀s, fun a ha => not_all_top a ha (f a₀)⟩
#align filter.tendsto.exists_within_forall_le Filter.Tendsto.exists_within_forall_le

/- warning: filter.tendsto.exists_forall_le -> Filter.Tendsto.exists_forall_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β}, (Filter.Tendsto.{u1, u2} α β f (Filter.cofinite.{u1} α) (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) -> (Exists.{succ u1} α (fun (a₀ : α) => forall (a : α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (f a₀) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Nonempty.{succ u2} α] [_inst_2 : LinearOrder.{u1} β] {f : α -> β}, (Filter.Tendsto.{u2, u1} α β f (Filter.cofinite.{u2} α) (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))))) -> (Exists.{succ u2} α (fun (a₀ : α) => forall (a : α), LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2)))))) (f a₀) (f a)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.exists_forall_le Filter.Tendsto.exists_forall_leₓ'. -/
theorem Filter.Tendsto.exists_forall_le [Nonempty α] [LinearOrder β] {f : α → β}
    (hf : Tendsto f cofinite atTop) : ∃ a₀, ∀ a, f a₀ ≤ f a :=
  let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩
#align filter.tendsto.exists_forall_le Filter.Tendsto.exists_forall_le

/- warning: filter.tendsto.exists_within_forall_ge -> Filter.Tendsto.exists_within_forall_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {f : α -> β}, (Filter.Tendsto.{u1, u2} α β f (Filter.cofinite.{u1} α) (Filter.atBot.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))))) -> (Exists.{succ u1} α (fun (a₀ : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a₀ s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a₀ s) => forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a) (f a₀))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {f : α -> β}, (Filter.Tendsto.{u1, u2} α β f (Filter.cofinite.{u1} α) (Filter.atBot.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1))))))) -> (Exists.{succ u1} α (fun (a₀ : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a₀ s) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (f a) (f a₀))))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.exists_within_forall_ge Filter.Tendsto.exists_within_forall_geₓ'. -/
theorem Filter.Tendsto.exists_within_forall_ge [LinearOrder β] {s : Set α} (hs : s.Nonempty)
    {f : α → β} (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) :
    ∃ a₀ ∈ s, ∀ a ∈ s, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_within_forall_le _ βᵒᵈ _ _ hs _ hf
#align filter.tendsto.exists_within_forall_ge Filter.Tendsto.exists_within_forall_ge

/- warning: filter.tendsto.exists_forall_ge -> Filter.Tendsto.exists_forall_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β}, (Filter.Tendsto.{u1, u2} α β f (Filter.cofinite.{u1} α) (Filter.atBot.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) -> (Exists.{succ u1} α (fun (a₀ : α) => forall (a : α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (f a) (f a₀)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Nonempty.{succ u2} α] [_inst_2 : LinearOrder.{u1} β] {f : α -> β}, (Filter.Tendsto.{u2, u1} α β f (Filter.cofinite.{u2} α) (Filter.atBot.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))))) -> (Exists.{succ u2} α (fun (a₀ : α) => forall (a : α), LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2)))))) (f a) (f a₀)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.exists_forall_ge Filter.Tendsto.exists_forall_geₓ'. -/
theorem Filter.Tendsto.exists_forall_ge [Nonempty α] [LinearOrder β] {f : α → β}
    (hf : Tendsto f cofinite atBot) : ∃ a₀, ∀ a, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_forall_le _ βᵒᵈ _ _ _ hf
#align filter.tendsto.exists_forall_ge Filter.Tendsto.exists_forall_ge

/- warning: function.injective.tendsto_cofinite -> Function.Injective.tendsto_cofinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Filter.Tendsto.{u1, u2} α β f (Filter.cofinite.{u1} α) (Filter.cofinite.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Filter.Tendsto.{u2, u1} α β f (Filter.cofinite.{u2} α) (Filter.cofinite.{u1} β))
Case conversion may be inaccurate. Consider using '#align function.injective.tendsto_cofinite Function.Injective.tendsto_cofiniteₓ'. -/
/-- For an injective function `f`, inverse images of finite sets are finite. See also
`filter.comap_cofinite_le` and `function.injective.comap_cofinite_eq`. -/
theorem Function.Injective.tendsto_cofinite {f : α → β} (hf : Injective f) :
    Tendsto f cofinite cofinite := fun s h => h.Preimage (hf.InjOn _)
#align function.injective.tendsto_cofinite Function.Injective.tendsto_cofinite

/- warning: function.injective.comap_cofinite_eq -> Function.Injective.comap_cofinite_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β f (Filter.cofinite.{u2} β)) (Filter.cofinite.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Eq.{succ u2} (Filter.{u2} α) (Filter.comap.{u2, u1} α β f (Filter.cofinite.{u1} β)) (Filter.cofinite.{u2} α))
Case conversion may be inaccurate. Consider using '#align function.injective.comap_cofinite_eq Function.Injective.comap_cofinite_eqₓ'. -/
/-- The pullback of the `filter.cofinite` under an injective function is equal to `filter.cofinite`.
See also `filter.comap_cofinite_le` and `function.injective.tendsto_cofinite`. -/
theorem Function.Injective.comap_cofinite_eq {f : α → β} (hf : Injective f) :
    comap f cofinite = cofinite :=
  (comap_cofinite_le f).antisymm hf.tendsto_cofinite.le_comap
#align function.injective.comap_cofinite_eq Function.Injective.comap_cofinite_eq

#print Function.Injective.nat_tendsto_atTop /-
/-- An injective sequence `f : ℕ → ℕ` tends to infinity at infinity. -/
theorem Function.Injective.nat_tendsto_atTop {f : ℕ → ℕ} (hf : Injective f) :
    Tendsto f atTop atTop :=
  Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite
#align function.injective.nat_tendsto_at_top Function.Injective.nat_tendsto_atTop
-/

