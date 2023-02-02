/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.continuous_on
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Constructions

/-!
# Neighborhoods and continuity relative to a subset

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines relative versions

* `nhds_within`           of `nhds`
* `continuous_on`         of `continuous`
* `continuous_within_at`  of `continuous_at`

and proves their basic properties, including the relationships between
these restricted notions and the corresponding notions for the subtype
equipped with the subspace topology.

## Notation

* `𝓝 x`: the filter of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhds_within x s` of neighborhoods of a point `x` within a set `s`.

-/


open Set Filter Function

open Topology Filter

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable [TopologicalSpace α]

#print nhds_bind_nhdsWithin /-
@[simp]
theorem nhds_bind_nhdsWithin {a : α} {s : Set α} : ((𝓝 a).bind fun x => 𝓝[s] x) = 𝓝[s] a :=
  bind_inf_principal.trans <| congr_arg₂ _ nhds_bind_nhds rfl
#align nhds_bind_nhds_within nhds_bind_nhdsWithin
-/

#print eventually_nhds_nhdsWithin /-
@[simp]
theorem eventually_nhds_nhdsWithin {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝[s] y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x :=
  Filter.ext_iff.1 nhds_bind_nhdsWithin { x | p x }
#align eventually_nhds_nhds_within eventually_nhds_nhdsWithin
-/

#print eventually_nhdsWithin_iff /-
theorem eventually_nhdsWithin_iff {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ x in 𝓝[s] a, p x) ↔ ∀ᶠ x in 𝓝 a, x ∈ s → p x :=
  eventually_inf_principal
#align eventually_nhds_within_iff eventually_nhdsWithin_iff
-/

#print frequently_nhdsWithin_iff /-
theorem frequently_nhdsWithin_iff {z : α} {s : Set α} {p : α → Prop} :
    (∃ᶠ x in 𝓝[s] z, p x) ↔ ∃ᶠ x in 𝓝 z, p x ∧ x ∈ s :=
  Iff.not (by simp [eventually_nhdsWithin_iff, not_and'])
#align frequently_nhds_within_iff frequently_nhdsWithin_iff
-/

/- warning: mem_closure_ne_iff_frequently_within -> mem_closure_ne_iff_frequently_within is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {z : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z (closure.{u1} α _inst_1 (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) z)))) (Filter.Frequently.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (nhdsWithin.{u1} α _inst_1 z (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) z))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {z : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z (closure.{u1} α _inst_1 (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) z)))) (Filter.Frequently.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (nhdsWithin.{u1} α _inst_1 z (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) z))))
Case conversion may be inaccurate. Consider using '#align mem_closure_ne_iff_frequently_within mem_closure_ne_iff_frequently_withinₓ'. -/
theorem mem_closure_ne_iff_frequently_within {z : α} {s : Set α} :
    z ∈ closure (s \ {z}) ↔ ∃ᶠ x in 𝓝[≠] z, x ∈ s := by
  simp [mem_closure_iff_frequently, frequently_nhdsWithin_iff]
#align mem_closure_ne_iff_frequently_within mem_closure_ne_iff_frequently_within

#print eventually_nhdsWithin_nhdsWithin /-
@[simp]
theorem eventually_nhdsWithin_nhdsWithin {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ y in 𝓝[s] a, ∀ᶠ x in 𝓝[s] y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x :=
  by
  refine' ⟨fun h => _, fun h => (eventually_nhds_nhdsWithin.2 h).filter_mono inf_le_left⟩
  simp only [eventually_nhdsWithin_iff] at h⊢
  exact h.mono fun x hx hxs => (hx hxs).self_of_nhds hxs
#align eventually_nhds_within_nhds_within eventually_nhdsWithin_nhdsWithin
-/

/- warning: nhds_within_eq -> nhdsWithin_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Set.{u1} α) (fun (t : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t (setOf.{u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (IsOpen.{u1} α _inst_1 t)))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t (setOf.{u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (IsOpen.{u1} α _inst_1 t)))) => Filter.principal.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Set.{u1} α) (fun (t : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t (setOf.{u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) (IsOpen.{u1} α _inst_1 t)))) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t (setOf.{u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) (IsOpen.{u1} α _inst_1 t)))) => Filter.principal.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s))))
Case conversion may be inaccurate. Consider using '#align nhds_within_eq nhdsWithin_eqₓ'. -/
theorem nhdsWithin_eq (a : α) (s : Set α) :
    𝓝[s] a = ⨅ t ∈ { t : Set α | a ∈ t ∧ IsOpen t }, 𝓟 (t ∩ s) :=
  ((nhds_basis_opens a).inf_principal s).eq_binfᵢ
#align nhds_within_eq nhdsWithin_eq

#print nhdsWithin_univ /-
theorem nhdsWithin_univ (a : α) : 𝓝[Set.univ] a = 𝓝 a := by
  rw [nhdsWithin, principal_univ, inf_top_eq]
#align nhds_within_univ nhdsWithin_univ
-/

/- warning: nhds_within_has_basis -> nhdsWithin_hasBasis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {p : β -> Prop} {s : β -> (Set.{u1} α)} {a : α}, (Filter.HasBasis.{u1, succ u2} α β (nhds.{u1} α _inst_1 a) p s) -> (forall (t : Set.{u1} α), Filter.HasBasis.{u1, succ u2} α β (nhdsWithin.{u1} α _inst_1 a t) p (fun (i : β) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s i) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {p : β -> Prop} {s : β -> (Set.{u2} α)} {a : α}, (Filter.HasBasis.{u2, succ u1} α β (nhds.{u2} α _inst_1 a) p s) -> (forall (t : Set.{u2} α), Filter.HasBasis.{u2, succ u1} α β (nhdsWithin.{u2} α _inst_1 a t) p (fun (i : β) => Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (s i) t))
Case conversion may be inaccurate. Consider using '#align nhds_within_has_basis nhdsWithin_hasBasisₓ'. -/
theorem nhdsWithin_hasBasis {p : β → Prop} {s : β → Set α} {a : α} (h : (𝓝 a).HasBasis p s)
    (t : Set α) : (𝓝[t] a).HasBasis p fun i => s i ∩ t :=
  h.inf_principal t
#align nhds_within_has_basis nhdsWithin_hasBasis

/- warning: nhds_within_basis_open -> nhdsWithin_basis_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (t : Set.{u1} α), Filter.HasBasis.{u1, succ u1} α (Set.{u1} α) (nhdsWithin.{u1} α _inst_1 a t) (fun (u : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a u) (IsOpen.{u1} α _inst_1 u)) (fun (u : Set.{u1} α) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (t : Set.{u1} α), Filter.HasBasis.{u1, succ u1} α (Set.{u1} α) (nhdsWithin.{u1} α _inst_1 a t) (fun (u : Set.{u1} α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a u) (IsOpen.{u1} α _inst_1 u)) (fun (u : Set.{u1} α) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u t)
Case conversion may be inaccurate. Consider using '#align nhds_within_basis_open nhdsWithin_basis_openₓ'. -/
theorem nhdsWithin_basis_open (a : α) (t : Set α) :
    (𝓝[t] a).HasBasis (fun u => a ∈ u ∧ IsOpen u) fun u => u ∩ t :=
  nhdsWithin_hasBasis (nhds_basis_opens a) t
#align nhds_within_basis_open nhdsWithin_basis_open

/- warning: mem_nhds_within -> mem_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {t : Set.{u1} α} {a : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhdsWithin.{u1} α _inst_1 a s)) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (IsOpen.{u1} α _inst_1 u) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a u) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s) t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {t : Set.{u1} α} {a : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhdsWithin.{u1} α _inst_1 a s)) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (IsOpen.{u1} α _inst_1 u) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a u) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u s) t))))
Case conversion may be inaccurate. Consider using '#align mem_nhds_within mem_nhdsWithinₓ'. -/
theorem mem_nhdsWithin {t : Set α} {a : α} {s : Set α} :
    t ∈ 𝓝[s] a ↔ ∃ u, IsOpen u ∧ a ∈ u ∧ u ∩ s ⊆ t := by
  simpa only [exists_prop, and_assoc', and_comm'] using (nhdsWithin_basis_open a s).mem_iff
#align mem_nhds_within mem_nhdsWithin

/- warning: mem_nhds_within_iff_exists_mem_nhds_inter -> mem_nhdsWithin_iff_exists_mem_nhds_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {t : Set.{u1} α} {a : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhdsWithin.{u1} α _inst_1 a s)) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhds.{u1} α _inst_1 a)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhds.{u1} α _inst_1 a)) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {t : Set.{u1} α} {a : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhdsWithin.{u1} α _inst_1 a s)) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u (nhds.{u1} α _inst_1 a)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u s) t)))
Case conversion may be inaccurate. Consider using '#align mem_nhds_within_iff_exists_mem_nhds_inter mem_nhdsWithin_iff_exists_mem_nhds_interₓ'. -/
theorem mem_nhdsWithin_iff_exists_mem_nhds_inter {t : Set α} {a : α} {s : Set α} :
    t ∈ 𝓝[s] a ↔ ∃ u ∈ 𝓝 a, u ∩ s ⊆ t :=
  (nhdsWithin_hasBasis (𝓝 a).basis_sets s).mem_iff
#align mem_nhds_within_iff_exists_mem_nhds_inter mem_nhdsWithin_iff_exists_mem_nhds_inter

/- warning: diff_mem_nhds_within_compl -> diff_mem_nhdsWithin_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 x)) -> (forall (t : Set.{u1} α), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α _inst_1 x)) -> (forall (t : Set.{u1} α), Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)))
Case conversion may be inaccurate. Consider using '#align diff_mem_nhds_within_compl diff_mem_nhdsWithin_complₓ'. -/
theorem diff_mem_nhdsWithin_compl {x : α} {s : Set α} (hs : s ∈ 𝓝 x) (t : Set α) :
    s \ t ∈ 𝓝[tᶜ] x :=
  diff_mem_inf_principal_compl hs t
#align diff_mem_nhds_within_compl diff_mem_nhdsWithin_compl

/- warning: diff_mem_nhds_within_diff -> diff_mem_nhdsWithin_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhdsWithin.{u1} α _inst_1 x t)) -> (forall (t' : Set.{u1} α), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t') (nhdsWithin.{u1} α _inst_1 x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t t')))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhdsWithin.{u1} α _inst_1 x t)) -> (forall (t' : Set.{u1} α), Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t') (nhdsWithin.{u1} α _inst_1 x (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t t')))
Case conversion may be inaccurate. Consider using '#align diff_mem_nhds_within_diff diff_mem_nhdsWithin_diffₓ'. -/
theorem diff_mem_nhdsWithin_diff {x : α} {s t : Set α} (hs : s ∈ 𝓝[t] x) (t' : Set α) :
    s \ t' ∈ 𝓝[t \ t'] x :=
  by
  rw [nhdsWithin, diff_eq, diff_eq, ← inf_principal, ← inf_assoc]
  exact inter_mem_inf hs (mem_principal_self _)
#align diff_mem_nhds_within_diff diff_mem_nhdsWithin_diff

#print nhds_of_nhdsWithin_of_nhds /-
theorem nhds_of_nhdsWithin_of_nhds {s t : Set α} {a : α} (h1 : s ∈ 𝓝 a) (h2 : t ∈ 𝓝[s] a) :
    t ∈ 𝓝 a :=
  by
  rcases mem_nhds_within_iff_exists_mem_nhds_inter.mp h2 with ⟨_, Hw, hw⟩
  exact (nhds a).sets_of_superset ((nhds a).inter_sets Hw h1) hw
#align nhds_of_nhds_within_of_nhds nhds_of_nhdsWithin_of_nhds
-/

#print mem_nhdsWithin_iff_eventually /-
theorem mem_nhdsWithin_iff_eventually {s t : Set α} {x : α} :
    t ∈ 𝓝[s] x ↔ ∀ᶠ y in 𝓝 x, y ∈ s → y ∈ t :=
  by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  constructor
  · rintro ⟨u, hu, hut⟩
    exact eventually_of_mem hu fun x hxu hxs => hut ⟨hxu, hxs⟩
  · refine' fun h => ⟨_, h, fun y hy => hy.1 hy.2⟩
#align mem_nhds_within_iff_eventually mem_nhdsWithin_iff_eventually
-/

/- warning: mem_nhds_within_iff_eventually_eq -> mem_nhdsWithin_iff_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhdsWithin.{u1} α _inst_1 x s)) (Filter.EventuallyEq.{u1, 0} α Prop (nhds.{u1} α _inst_1 x) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhdsWithin.{u1} α _inst_1 x s)) (Filter.EventuallyEq.{u1, 0} α Prop (nhds.{u1} α _inst_1 x) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align mem_nhds_within_iff_eventually_eq mem_nhdsWithin_iff_eventuallyEqₓ'. -/
theorem mem_nhdsWithin_iff_eventuallyEq {s t : Set α} {x : α} :
    t ∈ 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s ∩ t : Set α) := by
  simp_rw [mem_nhdsWithin_iff_eventually, eventually_eq_set, mem_inter_iff, iff_self_and]
#align mem_nhds_within_iff_eventually_eq mem_nhdsWithin_iff_eventuallyEq

#print nhdsWithin_eq_iff_eventuallyEq /-
theorem nhdsWithin_eq_iff_eventuallyEq {s t : Set α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t :=
  by
  simp_rw [Filter.ext_iff, mem_nhdsWithin_iff_eventually, eventually_eq_set]
  constructor
  · intro h
    filter_upwards [(h t).mpr (eventually_of_forall fun x => id),
      (h s).mp (eventually_of_forall fun x => id)]
    exact fun x => Iff.intro
  · refine' fun h u => eventually_congr (h.mono fun x h => _)
    rw [h]
#align nhds_within_eq_iff_eventually_eq nhdsWithin_eq_iff_eventuallyEq
-/

/- warning: nhds_within_le_iff -> nhdsWithin_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhdsWithin.{u1} α _inst_1 x s) (nhdsWithin.{u1} α _inst_1 x t)) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhdsWithin.{u1} α _inst_1 x s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhdsWithin.{u1} α _inst_1 x s) (nhdsWithin.{u1} α _inst_1 x t)) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhdsWithin.{u1} α _inst_1 x s))
Case conversion may be inaccurate. Consider using '#align nhds_within_le_iff nhdsWithin_le_iffₓ'. -/
theorem nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x ≤ 𝓝[t] x ↔ t ∈ 𝓝[s] x :=
  by
  simp_rw [Filter.le_def, mem_nhdsWithin_iff_eventually]
  constructor
  · exact fun h => (h t <| eventually_of_forall fun x => id).mono fun x => id
  · exact fun h u hu => (h.And hu).mono fun x hx h => hx.2 <| hx.1 h
#align nhds_within_le_iff nhdsWithin_le_iff

theorem preimage_nhdsWithin_coinduced' {π : α → β} {s : Set β} {t : Set α} {a : α} (h : a ∈ t)
    (ht : IsOpen t)
    (hs :
      s ∈ @nhds β (TopologicalSpace.coinduced (fun x : t => π x) Subtype.topologicalSpace) (π a)) :
    π ⁻¹' s ∈ 𝓝[t] a :=
  by
  letI := TopologicalSpace.coinduced (fun x : t => π x) Subtype.topologicalSpace
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  refine'
    mem_nhds_within_iff_exists_mem_nhds_inter.mpr
      ⟨π ⁻¹' V, mem_nhds_iff.mpr ⟨t ∩ π ⁻¹' V, inter_subset_right t (π ⁻¹' V), _, mem_sep h mem_V⟩,
        subset.trans (inter_subset_left _ _) (preimage_mono hVs)⟩
  obtain ⟨u, hu1, hu2⟩ := is_open_induced_iff.mp (isOpen_coinduced.1 V_op)
  rw [preimage_comp] at hu2
  rw [Set.inter_comm, ← subtype.preimage_coe_eq_preimage_coe_iff.mp hu2]
  exact hu1.inter ht
#align preimage_nhds_within_coinduced' preimage_nhdsWithin_coinduced'ₓ

#print mem_nhdsWithin_of_mem_nhds /-
theorem mem_nhdsWithin_of_mem_nhds {s t : Set α} {a : α} (h : s ∈ 𝓝 a) : s ∈ 𝓝[t] a :=
  mem_inf_of_left h
#align mem_nhds_within_of_mem_nhds mem_nhdsWithin_of_mem_nhds
-/

#print self_mem_nhdsWithin /-
theorem self_mem_nhdsWithin {a : α} {s : Set α} : s ∈ 𝓝[s] a :=
  mem_inf_of_right (mem_principal_self s)
#align self_mem_nhds_within self_mem_nhdsWithin
-/

#print eventually_mem_nhdsWithin /-
theorem eventually_mem_nhdsWithin {a : α} {s : Set α} : ∀ᶠ x in 𝓝[s] a, x ∈ s :=
  self_mem_nhdsWithin
#align eventually_mem_nhds_within eventually_mem_nhdsWithin
-/

/- warning: inter_mem_nhds_within -> inter_mem_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) {t : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhds.{u1} α _inst_1 a)) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (nhdsWithin.{u1} α _inst_1 a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) {t : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhds.{u1} α _inst_1 a)) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (nhdsWithin.{u1} α _inst_1 a s))
Case conversion may be inaccurate. Consider using '#align inter_mem_nhds_within inter_mem_nhdsWithinₓ'. -/
theorem inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : α} (h : t ∈ 𝓝 a) : s ∩ t ∈ 𝓝[s] a :=
  inter_mem self_mem_nhdsWithin (mem_inf_of_left h)
#align inter_mem_nhds_within inter_mem_nhdsWithin

/- warning: nhds_within_mono -> nhdsWithin_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a t))
Case conversion may be inaccurate. Consider using '#align nhds_within_mono nhdsWithin_monoₓ'. -/
theorem nhdsWithin_mono (a : α) {s t : Set α} (h : s ⊆ t) : 𝓝[s] a ≤ 𝓝[t] a :=
  inf_le_inf_left _ (principal_mono.mpr h)
#align nhds_within_mono nhdsWithin_mono

/- warning: pure_le_nhds_within -> pure_le_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a) (nhdsWithin.{u1} α _inst_1 a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a) (nhdsWithin.{u1} α _inst_1 a s))
Case conversion may be inaccurate. Consider using '#align pure_le_nhds_within pure_le_nhdsWithinₓ'. -/
theorem pure_le_nhdsWithin {a : α} {s : Set α} (ha : a ∈ s) : pure a ≤ 𝓝[s] a :=
  le_inf (pure_le_nhds a) (le_principal_iff.2 ha)
#align pure_le_nhds_within pure_le_nhdsWithin

#print mem_of_mem_nhdsWithin /-
theorem mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha : a ∈ s) (ht : t ∈ 𝓝[s] a) : a ∈ t :=
  pure_le_nhdsWithin ha ht
#align mem_of_mem_nhds_within mem_of_mem_nhdsWithin
-/

#print Filter.Eventually.self_of_nhdsWithin /-
theorem Filter.Eventually.self_of_nhdsWithin {p : α → Prop} {s : Set α} {x : α}
    (h : ∀ᶠ y in 𝓝[s] x, p y) (hx : x ∈ s) : p x :=
  mem_of_mem_nhdsWithin hx h
#align filter.eventually.self_of_nhds_within Filter.Eventually.self_of_nhdsWithin
-/

#print tendsto_const_nhdsWithin /-
theorem tendsto_const_nhdsWithin {l : Filter β} {s : Set α} {a : α} (ha : a ∈ s) :
    Tendsto (fun x : β => a) l (𝓝[s] a) :=
  tendsto_const_pure.mono_right <| pure_le_nhdsWithin ha
#align tendsto_const_nhds_within tendsto_const_nhdsWithin
-/

/- warning: nhds_within_restrict'' -> nhdsWithin_restrict'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} (s : Set.{u1} α) {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhdsWithin.{u1} α _inst_1 a s)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} (s : Set.{u1} α) {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhdsWithin.{u1} α _inst_1 a s)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align nhds_within_restrict'' nhdsWithin_restrict''ₓ'. -/
theorem nhdsWithin_restrict'' {a : α} (s : Set α) {t : Set α} (h : t ∈ 𝓝[s] a) :
    𝓝[s] a = 𝓝[s ∩ t] a :=
  le_antisymm (le_inf inf_le_left (le_principal_iff.mpr (inter_mem self_mem_nhdsWithin h)))
    (inf_le_inf_left _ (principal_mono.mpr (Set.inter_subset_left _ _)))
#align nhds_within_restrict'' nhdsWithin_restrict''

/- warning: nhds_within_restrict' -> nhdsWithin_restrict' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} (s : Set.{u1} α) {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhds.{u1} α _inst_1 a)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} (s : Set.{u1} α) {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhds.{u1} α _inst_1 a)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align nhds_within_restrict' nhdsWithin_restrict'ₓ'. -/
theorem nhdsWithin_restrict' {a : α} (s : Set α) {t : Set α} (h : t ∈ 𝓝 a) : 𝓝[s] a = 𝓝[s ∩ t] a :=
  nhdsWithin_restrict'' s <| mem_inf_of_left h
#align nhds_within_restrict' nhdsWithin_restrict'

/- warning: nhds_within_restrict -> nhdsWithin_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} (s : Set.{u1} α) {t : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) -> (IsOpen.{u1} α _inst_1 t) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} (s : Set.{u1} α) {t : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) -> (IsOpen.{u1} α _inst_1 t) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align nhds_within_restrict nhdsWithin_restrictₓ'. -/
theorem nhdsWithin_restrict {a : α} (s : Set α) {t : Set α} (h₀ : a ∈ t) (h₁ : IsOpen t) :
    𝓝[s] a = 𝓝[s ∩ t] a :=
  nhdsWithin_restrict' s (IsOpen.mem_nhds h₁ h₀)
#align nhds_within_restrict nhdsWithin_restrict

/- warning: nhds_within_le_of_mem -> nhdsWithin_le_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhdsWithin.{u1} α _inst_1 a t)) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhdsWithin.{u1} α _inst_1 a t) (nhdsWithin.{u1} α _inst_1 a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhdsWithin.{u1} α _inst_1 a t)) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhdsWithin.{u1} α _inst_1 a t) (nhdsWithin.{u1} α _inst_1 a s))
Case conversion may be inaccurate. Consider using '#align nhds_within_le_of_mem nhdsWithin_le_of_memₓ'. -/
theorem nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s ∈ 𝓝[t] a) : 𝓝[t] a ≤ 𝓝[s] a :=
  nhdsWithin_le_iff.mpr h
#align nhds_within_le_of_mem nhdsWithin_le_of_mem

/- warning: nhds_within_le_nhds -> nhdsWithin_le_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhdsWithin.{u1} α _inst_1 a s) (nhds.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhdsWithin.{u1} α _inst_1 a s) (nhds.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align nhds_within_le_nhds nhdsWithin_le_nhdsₓ'. -/
theorem nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a ≤ 𝓝 a :=
  by
  rw [← nhdsWithin_univ]
  apply nhdsWithin_le_of_mem
  exact univ_mem
#align nhds_within_le_nhds nhdsWithin_le_nhds

/- warning: nhds_within_eq_nhds_within' -> nhdsWithin_eq_nhds_within' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 a)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a t) (nhdsWithin.{u1} α _inst_1 a u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α _inst_1 a)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u s)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a t) (nhdsWithin.{u1} α _inst_1 a u))
Case conversion may be inaccurate. Consider using '#align nhds_within_eq_nhds_within' nhdsWithin_eq_nhds_within'ₓ'. -/
theorem nhdsWithin_eq_nhds_within' {a : α} {s t u : Set α} (hs : s ∈ 𝓝 a) (h₂ : t ∩ s = u ∩ s) :
    𝓝[t] a = 𝓝[u] a := by rw [nhdsWithin_restrict' t hs, nhdsWithin_restrict' u hs, h₂]
#align nhds_within_eq_nhds_within' nhdsWithin_eq_nhds_within'

/- warning: nhds_within_eq_nhds_within -> nhdsWithin_eq_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (IsOpen.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a t) (nhdsWithin.{u1} α _inst_1 a u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (IsOpen.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u s)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a t) (nhdsWithin.{u1} α _inst_1 a u))
Case conversion may be inaccurate. Consider using '#align nhds_within_eq_nhds_within nhdsWithin_eq_nhdsWithinₓ'. -/
theorem nhdsWithin_eq_nhdsWithin {a : α} {s t u : Set α} (h₀ : a ∈ s) (h₁ : IsOpen s)
    (h₂ : t ∩ s = u ∩ s) : 𝓝[t] a = 𝓝[u] a := by
  rw [nhdsWithin_restrict t h₀ h₁, nhdsWithin_restrict u h₀ h₁, h₂]
#align nhds_within_eq_nhds_within nhdsWithin_eq_nhdsWithin

#print IsOpen.nhdsWithin_eq /-
theorem IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOpen s) (ha : a ∈ s) : 𝓝[s] a = 𝓝 a :=
  inf_eq_left.2 <| le_principal_iff.2 <| IsOpen.mem_nhds h ha
#align is_open.nhds_within_eq IsOpen.nhdsWithin_eq
-/

#print preimage_nhds_within_coinduced /-
theorem preimage_nhds_within_coinduced {π : α → β} {s : Set β} {t : Set α} {a : α} (h : a ∈ t)
    (ht : IsOpen t)
    (hs :
      s ∈ @nhds β (TopologicalSpace.coinduced (fun x : t => π x) Subtype.topologicalSpace) (π a)) :
    π ⁻¹' s ∈ 𝓝 a := by
  rw [← ht.nhds_within_eq h]
  exact preimage_nhdsWithin_coinduced' h ht hs
#align preimage_nhds_within_coinduced preimage_nhds_within_coinduced
-/

/- warning: nhds_within_empty -> nhdsWithin_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align nhds_within_empty nhdsWithin_emptyₓ'. -/
@[simp]
theorem nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥ := by rw [nhdsWithin, principal_empty, inf_bot_eq]
#align nhds_within_empty nhdsWithin_empty

/- warning: nhds_within_union -> nhdsWithin_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a t))
Case conversion may be inaccurate. Consider using '#align nhds_within_union nhdsWithin_unionₓ'. -/
theorem nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s ∪ t] a = 𝓝[s] a ⊔ 𝓝[t] a :=
  by
  delta nhdsWithin
  rw [← inf_sup_left, sup_principal]
#align nhds_within_union nhdsWithin_union

/- warning: nhds_within_inter -> nhdsWithin_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (nhdsWithin.{u1} α _inst_1 a t))
Case conversion may be inaccurate. Consider using '#align nhds_within_inter nhdsWithin_interₓ'. -/
theorem nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s ∩ t] a = 𝓝[s] a ⊓ 𝓝[t] a :=
  by
  delta nhdsWithin
  rw [inf_left_comm, inf_assoc, inf_principal, ← inf_assoc, inf_idem]
#align nhds_within_inter nhdsWithin_inter

/- warning: nhds_within_inter' -> nhdsWithin_inter' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (Filter.principal.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (nhdsWithin.{u1} α _inst_1 a s) (Filter.principal.{u1} α t))
Case conversion may be inaccurate. Consider using '#align nhds_within_inter' nhdsWithin_inter'ₓ'. -/
theorem nhdsWithin_inter' (a : α) (s t : Set α) : 𝓝[s ∩ t] a = 𝓝[s] a ⊓ 𝓟 t :=
  by
  delta nhdsWithin
  rw [← inf_principal, inf_assoc]
#align nhds_within_inter' nhdsWithin_inter'

/- warning: nhds_within_inter_of_mem -> nhdsWithin_inter_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhdsWithin.{u1} α _inst_1 a t)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (nhdsWithin.{u1} α _inst_1 a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhdsWithin.{u1} α _inst_1 a t)) -> (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (nhdsWithin.{u1} α _inst_1 a t))
Case conversion may be inaccurate. Consider using '#align nhds_within_inter_of_mem nhdsWithin_inter_of_memₓ'. -/
theorem nhdsWithin_inter_of_mem {a : α} {s t : Set α} (h : s ∈ 𝓝[t] a) : 𝓝[s ∩ t] a = 𝓝[t] a :=
  by
  rw [nhdsWithin_inter, inf_eq_right]
  exact nhdsWithin_le_of_mem h
#align nhds_within_inter_of_mem nhdsWithin_inter_of_mem

#print nhdsWithin_singleton /-
@[simp]
theorem nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a := by
  rw [nhdsWithin, principal_singleton, inf_eq_right.2 (pure_le_nhds a)]
#align nhds_within_singleton nhdsWithin_singleton
-/

/- warning: nhds_within_insert -> nhdsWithin_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a) (nhdsWithin.{u1} α _inst_1 a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (s : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 a (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a) (nhdsWithin.{u1} α _inst_1 a s))
Case conversion may be inaccurate. Consider using '#align nhds_within_insert nhdsWithin_insertₓ'. -/
@[simp]
theorem nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s] a = pure a ⊔ 𝓝[s] a := by
  rw [← singleton_union, nhdsWithin_union, nhdsWithin_singleton]
#align nhds_within_insert nhdsWithin_insert

#print mem_nhdsWithin_insert /-
theorem mem_nhdsWithin_insert {a : α} {s t : Set α} : t ∈ 𝓝[insert a s] a ↔ a ∈ t ∧ t ∈ 𝓝[s] a := by
  simp
#align mem_nhds_within_insert mem_nhdsWithin_insert
-/

#print insert_mem_nhdsWithin_insert /-
theorem insert_mem_nhdsWithin_insert {a : α} {s t : Set α} (h : t ∈ 𝓝[s] a) :
    insert a t ∈ 𝓝[insert a s] a := by simp [mem_of_superset h]
#align insert_mem_nhds_within_insert insert_mem_nhdsWithin_insert
-/

/- warning: insert_mem_nhds_iff -> insert_mem_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) (nhds.{u1} α _inst_1 a)) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) (nhds.{u1} α _inst_1 a)) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))))
Case conversion may be inaccurate. Consider using '#align insert_mem_nhds_iff insert_mem_nhds_iffₓ'. -/
theorem insert_mem_nhds_iff {a : α} {s : Set α} : insert a s ∈ 𝓝 a ↔ s ∈ 𝓝[≠] a := by
  simp only [nhdsWithin, mem_inf_principal, mem_compl_iff, mem_singleton_iff, or_iff_not_imp_left,
    insert_def]
#align insert_mem_nhds_iff insert_mem_nhds_iff

/- warning: nhds_within_compl_singleton_sup_pure -> nhdsWithin_compl_singleton_sup_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a)) (nhds.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a)) (nhds.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align nhds_within_compl_singleton_sup_pure nhdsWithin_compl_singleton_sup_pureₓ'. -/
@[simp]
theorem nhdsWithin_compl_singleton_sup_pure (a : α) : 𝓝[≠] a ⊔ pure a = 𝓝 a := by
  rw [← nhdsWithin_singleton, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ]
#align nhds_within_compl_singleton_sup_pure nhdsWithin_compl_singleton_sup_pure

/- warning: nhds_within_prod_eq -> nhdsWithin_prod_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} β] (a : α) (b : β) (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (nhdsWithin.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_2 _inst_3) (Prod.mk.{u1, u2} α β a b) (Set.prod.{u1, u2} α β s t)) (Filter.prod.{u1, u2} α β (nhdsWithin.{u1} α _inst_2 a s) (nhdsWithin.{u2} β _inst_3 b t))
but is expected to have type
  forall {α : Type.{u1}} {_inst_2 : Type.{u2}} [β : TopologicalSpace.{u1} α] [_inst_3 : TopologicalSpace.{u2} _inst_2] (a : α) (b : _inst_2) (s : Set.{u1} α) (t : Set.{u2} _inst_2), Eq.{max (succ u1) (succ u2)} (Filter.{max u2 u1} (Prod.{u1, u2} α _inst_2)) (nhdsWithin.{max u2 u1} (Prod.{u1, u2} α _inst_2) (instTopologicalSpaceProd.{u1, u2} α _inst_2 β _inst_3) (Prod.mk.{u1, u2} α _inst_2 a b) (Set.prod.{u1, u2} α _inst_2 s t)) (Filter.prod.{u1, u2} α _inst_2 (nhdsWithin.{u1} α β a s) (nhdsWithin.{u2} _inst_2 _inst_3 b t))
Case conversion may be inaccurate. Consider using '#align nhds_within_prod_eq nhdsWithin_prod_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem nhdsWithin_prod_eq {α : Type _} [TopologicalSpace α] {β : Type _} [TopologicalSpace β]
    (a : α) (b : β) (s : Set α) (t : Set β) : 𝓝[s ×ˢ t] (a, b) = 𝓝[s] a ×ᶠ 𝓝[t] b :=
  by
  delta nhdsWithin
  rw [nhds_prod_eq, ← Filter.prod_inf_prod, Filter.prod_principal_principal]
#align nhds_within_prod_eq nhdsWithin_prod_eq

/- warning: nhds_within_prod -> nhdsWithin_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {u : Set.{u1} α} {t : Set.{u2} β} {v : Set.{u2} β} {a : α} {b : β}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhdsWithin.{u1} α _inst_2 a s)) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) v (nhdsWithin.{u2} β _inst_3 b t)) -> (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β u v) (nhdsWithin.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_2 _inst_3) (Prod.mk.{u1, u2} α β a b) (Set.prod.{u1, u2} α β s t)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {u : Set.{u2} α} {t : Set.{u1} β} {v : Set.{u1} β} {a : α} {b : β}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) u (nhdsWithin.{u2} α _inst_2 a s)) -> (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) v (nhdsWithin.{u1} β _inst_3 b t)) -> (Membership.mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Filter.{max u1 u2} (Prod.{u2, u1} α β)) (instMembershipSetFilter.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β u v) (nhdsWithin.{max u1 u2} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_2 _inst_3) (Prod.mk.{u2, u1} α β a b) (Set.prod.{u2, u1} α β s t)))
Case conversion may be inaccurate. Consider using '#align nhds_within_prod nhdsWithin_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem nhdsWithin_prod {α : Type _} [TopologicalSpace α] {β : Type _} [TopologicalSpace β]
    {s u : Set α} {t v : Set β} {a : α} {b : β} (hu : u ∈ 𝓝[s] a) (hv : v ∈ 𝓝[t] b) :
    u ×ˢ v ∈ 𝓝[s ×ˢ t] (a, b) := by
  rw [nhdsWithin_prod_eq]
  exact prod_mem_prod hu hv
#align nhds_within_prod nhdsWithin_prod

/- warning: nhds_within_pi_eq' -> nhdsWithin_pi_eq' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (α i)] {I : Set.{u1} ι}, (Set.Finite.{u1} ι I) -> (forall (s : forall (i : ι), Set.{u2} (α i)) (x : forall (i : ι), α i), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (nhdsWithin.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) x (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s)) (infᵢ.{max u1 u2, succ u1} (Filter.{max u1 u2} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i)))) ι (fun (i : ι) => Filter.comap.{max u1 u2, u2} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.hasInf.{u2} (α i)) (nhds.{u2} (α i) (_inst_2 i) (x i)) (infᵢ.{u2, 0} (Filter.{u2} (α i)) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} (α i)) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} (α i)) (Filter.completeLattice.{u2} (α i)))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) (fun (hi : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) => Filter.principal.{u2} (α i) (s i)))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (α i)] {I : Set.{u2} ι}, (Set.Finite.{u2} ι I) -> (forall (s : forall (i : ι), Set.{u1} (α i)) (x : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), α i)) (nhdsWithin.{max u2 u1} (forall (i : ι), α i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) x (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I s)) (infᵢ.{max u2 u1, succ u2} (Filter.{max u2 u1} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i)))) ι (fun (i : ι) => Filter.comap.{max u2 u1, u1} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (HasInf.inf.{u1} (Filter.{u1} (α i)) (Filter.instHasInfFilter.{u1} (α i)) (nhds.{u1} (α i) (_inst_2 i) (x i)) (infᵢ.{u1, 0} (Filter.{u1} (α i)) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} (α i)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (α i)) (Filter.instCompleteLatticeFilter.{u1} (α i)))) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) (fun (hi : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) => Filter.principal.{u1} (α i) (s i)))))))
Case conversion may be inaccurate. Consider using '#align nhds_within_pi_eq' nhdsWithin_pi_eq'ₓ'. -/
theorem nhdsWithin_pi_eq' {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    (hI : I.Finite) (s : ∀ i, Set (α i)) (x : ∀ i, α i) :
    𝓝[pi I s] x = ⨅ i, comap (fun x => x i) (𝓝 (x i) ⊓ ⨅ hi : i ∈ I, 𝓟 (s i)) := by
  simp only [nhdsWithin, nhds_pi, Filter.pi, comap_inf, comap_infi, pi_def, comap_principal, ←
    infi_principal_finite hI, ← infᵢ_inf_eq]
#align nhds_within_pi_eq' nhdsWithin_pi_eq'

/- warning: nhds_within_pi_eq -> nhdsWithin_pi_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (α i)] {I : Set.{u1} ι}, (Set.Finite.{u1} ι I) -> (forall (s : forall (i : ι), Set.{u2} (α i)) (x : forall (i : ι), α i), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (nhdsWithin.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) x (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s)) (HasInf.inf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasInf.{max u1 u2} (forall (i : ι), α i)) (infᵢ.{max u1 u2, succ u1} (Filter.{max u1 u2} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i)))) ι (fun (i : ι) => infᵢ.{max u1 u2, 0} (Filter.{max u1 u2} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i)))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) => Filter.comap.{max u1 u2, u2} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (nhdsWithin.{u2} (α i) (_inst_2 i) (x i) (s i))))) (infᵢ.{max u1 u2, succ u1} (Filter.{max u1 u2} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i)))) ι (fun (i : ι) => infᵢ.{max u1 u2, 0} (Filter.{max u1 u2} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i)))) (Not (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I)) (fun (H : Not (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I)) => Filter.comap.{max u1 u2, u2} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (nhds.{u2} (α i) (_inst_2 i) (x i)))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (α i)] {I : Set.{u2} ι}, (Set.Finite.{u2} ι I) -> (forall (s : forall (i : ι), Set.{u1} (α i)) (x : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), α i)) (nhdsWithin.{max u2 u1} (forall (i : ι), α i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) x (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I s)) (HasInf.inf.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instHasInfFilter.{max u2 u1} (forall (i : ι), α i)) (infᵢ.{max u2 u1, succ u2} (Filter.{max u2 u1} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i)))) ι (fun (i : ι) => infᵢ.{max u2 u1, 0} (Filter.{max u2 u1} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i)))) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) => Filter.comap.{max u2 u1, u1} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (nhdsWithin.{u1} (α i) (_inst_2 i) (x i) (s i))))) (infᵢ.{max u2 u1, succ u2} (Filter.{max u2 u1} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i)))) ι (fun (i : ι) => infᵢ.{max u2 u1, 0} (Filter.{max u2 u1} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i)))) (Not (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I)) (fun (H : Not (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I)) => Filter.comap.{max u2 u1, u1} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (nhds.{u1} (α i) (_inst_2 i) (x i)))))))
Case conversion may be inaccurate. Consider using '#align nhds_within_pi_eq nhdsWithin_pi_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (i «expr ∉ » I) -/
theorem nhdsWithin_pi_eq {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    (hI : I.Finite) (s : ∀ i, Set (α i)) (x : ∀ i, α i) :
    𝓝[pi I s] x =
      (⨅ i ∈ I, comap (fun x => x i) (𝓝[s i] x i)) ⊓
        ⨅ (i) (_ : i ∉ I), comap (fun x => x i) (𝓝 (x i)) :=
  by
  simp only [nhdsWithin, nhds_pi, Filter.pi, pi_def, ← infi_principal_finite hI, comap_inf,
    comap_principal, eval]
  rw [infᵢ_split _ fun i => i ∈ I, inf_right_comm]
  simp only [infᵢ_inf_eq]
#align nhds_within_pi_eq nhdsWithin_pi_eq

/- warning: nhds_within_pi_univ_eq -> nhdsWithin_pi_univ_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_2 : Finite.{succ u1} ι] [_inst_3 : forall (i : ι), TopologicalSpace.{u2} (α i)] (s : forall (i : ι), Set.{u2} (α i)) (x : forall (i : ι), α i), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (nhdsWithin.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_3 a)) x (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) s)) (infᵢ.{max u1 u2, succ u1} (Filter.{max u1 u2} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i)))) ι (fun (i : ι) => Filter.comap.{max u1 u2, u2} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (nhdsWithin.{u2} (α i) (_inst_3 i) (x i) (s i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_2 : Finite.{succ u2} ι] [_inst_3 : forall (i : ι), TopologicalSpace.{u1} (α i)] (s : forall (i : ι), Set.{u1} (α i)) (x : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), α i)) (nhdsWithin.{max u2 u1} (forall (i : ι), α i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_3 a)) x (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) s)) (infᵢ.{max u2 u1, succ u2} (Filter.{max u2 u1} (forall (i : ι), α i)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i)))) ι (fun (i : ι) => Filter.comap.{max u2 u1, u1} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (nhdsWithin.{u1} (α i) (_inst_3 i) (x i) (s i))))
Case conversion may be inaccurate. Consider using '#align nhds_within_pi_univ_eq nhdsWithin_pi_univ_eqₓ'. -/
theorem nhdsWithin_pi_univ_eq {ι : Type _} {α : ι → Type _} [Finite ι] [∀ i, TopologicalSpace (α i)]
    (s : ∀ i, Set (α i)) (x : ∀ i, α i) : 𝓝[pi univ s] x = ⨅ i, comap (fun x => x i) (𝓝[s i] x i) :=
  by simpa [nhdsWithin] using nhdsWithin_pi_eq finite_univ s x
#align nhds_within_pi_univ_eq nhdsWithin_pi_univ_eq

/- warning: nhds_within_pi_eq_bot -> nhdsWithin_pi_eq_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (α i)] {I : Set.{u1} ι} {s : forall (i : ι), Set.{u2} (α i)} {x : forall (i : ι), α i}, Iff (Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (nhdsWithin.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) x (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s)) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toHasBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i))))) (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) => Eq.{succ u2} (Filter.{u2} (α i)) (nhdsWithin.{u2} (α i) (_inst_2 i) (x i) (s i)) (Bot.bot.{u2} (Filter.{u2} (α i)) (CompleteLattice.toHasBot.{u2} (Filter.{u2} (α i)) (Filter.completeLattice.{u2} (α i)))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (α i)] {I : Set.{u2} ι} {s : forall (i : ι), Set.{u1} (α i)} {x : forall (i : ι), α i}, Iff (Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), α i)) (nhdsWithin.{max u2 u1} (forall (i : ι), α i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) x (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I s)) (Bot.bot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toBot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i))))) (Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) (Eq.{succ u1} (Filter.{u1} (α i)) (nhdsWithin.{u1} (α i) (_inst_2 i) (x i) (s i)) (Bot.bot.{u1} (Filter.{u1} (α i)) (CompleteLattice.toBot.{u1} (Filter.{u1} (α i)) (Filter.instCompleteLatticeFilter.{u1} (α i)))))))
Case conversion may be inaccurate. Consider using '#align nhds_within_pi_eq_bot nhdsWithin_pi_eq_botₓ'. -/
theorem nhdsWithin_pi_eq_bot {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    {s : ∀ i, Set (α i)} {x : ∀ i, α i} : 𝓝[pi I s] x = ⊥ ↔ ∃ i ∈ I, 𝓝[s i] x i = ⊥ := by
  simp only [nhdsWithin, nhds_pi, pi_inf_principal_pi_eq_bot]
#align nhds_within_pi_eq_bot nhdsWithin_pi_eq_bot

/- warning: nhds_within_pi_ne_bot -> nhdsWithin_pi_neBot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (α i)] {I : Set.{u1} ι} {s : forall (i : ι), Set.{u2} (α i)} {x : forall (i : ι), α i}, Iff (Filter.NeBot.{max u1 u2} (forall (i : ι), α i) (nhdsWithin.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) x (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) -> (Filter.NeBot.{u2} (α i) (nhdsWithin.{u2} (α i) (_inst_2 i) (x i) (s i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (α i)] {I : Set.{u2} ι} {s : forall (i : ι), Set.{u1} (α i)} {x : forall (i : ι), α i}, Iff (Filter.NeBot.{max u2 u1} (forall (i : ι), α i) (nhdsWithin.{max u2 u1} (forall (i : ι), α i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) x (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I s))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) -> (Filter.NeBot.{u1} (α i) (nhdsWithin.{u1} (α i) (_inst_2 i) (x i) (s i))))
Case conversion may be inaccurate. Consider using '#align nhds_within_pi_ne_bot nhdsWithin_pi_neBotₓ'. -/
theorem nhdsWithin_pi_neBot {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    {s : ∀ i, Set (α i)} {x : ∀ i, α i} : (𝓝[pi I s] x).ne_bot ↔ ∀ i ∈ I, (𝓝[s i] x i).ne_bot := by
  simp [ne_bot_iff, nhdsWithin_pi_eq_bot]
#align nhds_within_pi_ne_bot nhdsWithin_pi_neBot

/- warning: filter.tendsto.piecewise_nhds_within -> Filter.Tendsto.piecewise_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> β} {g : α -> β} {t : Set.{u1} α} [_inst_2 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)] {a : α} {s : Set.{u1} α} {l : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) l) -> (Filter.Tendsto.{u1, u2} α β g (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))) l) -> (Filter.Tendsto.{u1, u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_2 j)) (nhdsWithin.{u1} α _inst_1 a s) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : α -> β} {g : α -> β} {t : Set.{u2} α} [_inst_2 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t)] {a : α} {s : Set.{u2} α} {l : Filter.{u1} β}, (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) l) -> (Filter.Tendsto.{u2, u1} α β g (nhdsWithin.{u2} α _inst_1 a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) t))) l) -> (Filter.Tendsto.{u2, u1} α β (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_2 j)) (nhdsWithin.{u2} α _inst_1 a s) l)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.piecewise_nhds_within Filter.Tendsto.piecewise_nhdsWithinₓ'. -/
theorem Filter.Tendsto.piecewise_nhdsWithin {f g : α → β} {t : Set α} [∀ x, Decidable (x ∈ t)]
    {a : α} {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s ∩ t] a) l)
    (h₁ : Tendsto g (𝓝[s ∩ tᶜ] a) l) : Tendsto (piecewise t f g) (𝓝[s] a) l := by
  apply tendsto.piecewise <;> rwa [← nhdsWithin_inter']
#align filter.tendsto.piecewise_nhds_within Filter.Tendsto.piecewise_nhdsWithin

/- warning: filter.tendsto.if_nhds_within -> Filter.Tendsto.if_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> β} {g : α -> β} {p : α -> Prop} [_inst_2 : DecidablePred.{succ u1} α p] {a : α} {s : Set.{u1} α} {l : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (x : α) => p x)))) l) -> (Filter.Tendsto.{u1, u2} α β g (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (x : α) => Not (p x))))) l) -> (Filter.Tendsto.{u1, u2} α β (fun (x : α) => ite.{succ u2} β (p x) (_inst_2 x) (f x) (g x)) (nhdsWithin.{u1} α _inst_1 a s) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : α -> β} {g : α -> β} {p : α -> Prop} [_inst_2 : DecidablePred.{succ u2} α p] {a : α} {s : Set.{u2} α} {l : Filter.{u1} β}, (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (setOf.{u2} α (fun (x : α) => p x)))) l) -> (Filter.Tendsto.{u2, u1} α β g (nhdsWithin.{u2} α _inst_1 a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (setOf.{u2} α (fun (x : α) => Not (p x))))) l) -> (Filter.Tendsto.{u2, u1} α β (fun (x : α) => ite.{succ u1} β (p x) (_inst_2 x) (f x) (g x)) (nhdsWithin.{u2} α _inst_1 a s) l)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.if_nhds_within Filter.Tendsto.if_nhdsWithinₓ'. -/
theorem Filter.Tendsto.if_nhdsWithin {f g : α → β} {p : α → Prop} [DecidablePred p] {a : α}
    {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s ∩ { x | p x }] a) l)
    (h₁ : Tendsto g (𝓝[s ∩ { x | ¬p x }] a) l) :
    Tendsto (fun x => if p x then f x else g x) (𝓝[s] a) l :=
  h₀.piecewise_nhdsWithin h₁
#align filter.tendsto.if_nhds_within Filter.Tendsto.if_nhdsWithin

/- warning: map_nhds_within -> map_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] (f : α -> β) (a : α) (s : Set.{u1} α), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s)) (infᵢ.{u2, succ u1} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) (Set.{u1} α) (fun (t : Set.{u1} α) => infᵢ.{u2, 0} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t (setOf.{u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (IsOpen.{u1} α _inst_1 t)))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t (setOf.{u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (IsOpen.{u1} α _inst_1 t)))) => Filter.principal.{u2} β (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] (f : α -> β) (a : α) (s : Set.{u2} α), Eq.{succ u1} (Filter.{u1} β) (Filter.map.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a s)) (infᵢ.{u1, succ u2} (Filter.{u1} β) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} β) (Filter.instCompleteLatticeFilter.{u1} β))) (Set.{u2} α) (fun (t : Set.{u2} α) => infᵢ.{u1, 0} (Filter.{u1} β) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} β) (Filter.instCompleteLatticeFilter.{u1} β))) (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) t (setOf.{u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a t) (IsOpen.{u2} α _inst_1 t)))) (fun (H : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) t (setOf.{u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a t) (IsOpen.{u2} α _inst_1 t)))) => Filter.principal.{u1} β (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) t s)))))
Case conversion may be inaccurate. Consider using '#align map_nhds_within map_nhdsWithinₓ'. -/
theorem map_nhdsWithin (f : α → β) (a : α) (s : Set α) :
    map f (𝓝[s] a) = ⨅ t ∈ { t : Set α | a ∈ t ∧ IsOpen t }, 𝓟 (f '' (t ∩ s)) :=
  ((nhdsWithin_basis_open a s).map f).eq_binfᵢ
#align map_nhds_within map_nhdsWithin

/- warning: tendsto_nhds_within_mono_left -> tendsto_nhdsWithin_mono_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> β} {a : α} {s : Set.{u1} α} {t : Set.{u1} α} {l : Filter.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a t) l) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : α -> β} {a : α} {s : Set.{u2} α} {t : Set.{u2} α} {l : Filter.{u1} β}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a t) l) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a s) l)
Case conversion may be inaccurate. Consider using '#align tendsto_nhds_within_mono_left tendsto_nhdsWithin_mono_leftₓ'. -/
theorem tendsto_nhdsWithin_mono_left {f : α → β} {a : α} {s t : Set α} {l : Filter β} (hst : s ⊆ t)
    (h : Tendsto f (𝓝[t] a) l) : Tendsto f (𝓝[s] a) l :=
  h.mono_left <| nhdsWithin_mono a hst
#align tendsto_nhds_within_mono_left tendsto_nhdsWithin_mono_left

#print tendsto_nhdsWithin_mono_right /-
theorem tendsto_nhdsWithin_mono_right {f : β → α} {l : Filter β} {a : α} {s t : Set α} (hst : s ⊆ t)
    (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝[t] a) :=
  h.mono_right (nhdsWithin_mono a hst)
#align tendsto_nhds_within_mono_right tendsto_nhdsWithin_mono_right
-/

/- warning: tendsto_nhds_within_of_tendsto_nhds -> tendsto_nhdsWithin_of_tendsto_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> β} {a : α} {s : Set.{u1} α} {l : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f (nhds.{u1} α _inst_1 a) l) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : α -> β} {a : α} {s : Set.{u2} α} {l : Filter.{u1} β}, (Filter.Tendsto.{u2, u1} α β f (nhds.{u2} α _inst_1 a) l) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a s) l)
Case conversion may be inaccurate. Consider using '#align tendsto_nhds_within_of_tendsto_nhds tendsto_nhdsWithin_of_tendsto_nhdsₓ'. -/
theorem tendsto_nhdsWithin_of_tendsto_nhds {f : α → β} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f (𝓝 a) l) : Tendsto f (𝓝[s] a) l :=
  h.mono_left inf_le_left
#align tendsto_nhds_within_of_tendsto_nhds tendsto_nhdsWithin_of_tendsto_nhds

/- warning: eventually_mem_of_tendsto_nhds_within -> eventually_mem_of_tendsto_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {s : Set.{u1} α} {l : Filter.{u2} β}, (Filter.Tendsto.{u2, u1} β α f l (nhdsWithin.{u1} α _inst_1 a s)) -> (Filter.Eventually.{u2} β (fun (i : β) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f i) s) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : β -> α} {a : α} {s : Set.{u2} α} {l : Filter.{u1} β}, (Filter.Tendsto.{u1, u2} β α f l (nhdsWithin.{u2} α _inst_1 a s)) -> (Filter.Eventually.{u1} β (fun (i : β) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (f i) s) l)
Case conversion may be inaccurate. Consider using '#align eventually_mem_of_tendsto_nhds_within eventually_mem_of_tendsto_nhdsWithinₓ'. -/
theorem eventually_mem_of_tendsto_nhdsWithin {f : β → α} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f l (𝓝[s] a)) : ∀ᶠ i in l, f i ∈ s :=
  by
  simp_rw [nhdsWithin_eq, tendsto_infi, mem_set_of_eq, tendsto_principal, mem_inter_iff,
    eventually_and] at h
  exact (h univ ⟨mem_univ a, isOpen_univ⟩).2
#align eventually_mem_of_tendsto_nhds_within eventually_mem_of_tendsto_nhdsWithin

/- warning: tendsto_nhds_of_tendsto_nhds_within -> tendsto_nhds_of_tendsto_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {s : Set.{u1} α} {l : Filter.{u2} β}, (Filter.Tendsto.{u2, u1} β α f l (nhdsWithin.{u1} α _inst_1 a s)) -> (Filter.Tendsto.{u2, u1} β α f l (nhds.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : β -> α} {a : α} {s : Set.{u2} α} {l : Filter.{u1} β}, (Filter.Tendsto.{u1, u2} β α f l (nhdsWithin.{u2} α _inst_1 a s)) -> (Filter.Tendsto.{u1, u2} β α f l (nhds.{u2} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align tendsto_nhds_of_tendsto_nhds_within tendsto_nhds_of_tendsto_nhdsWithinₓ'. -/
theorem tendsto_nhds_of_tendsto_nhdsWithin {f : β → α} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝 a) :=
  h.mono_right nhdsWithin_le_nhds
#align tendsto_nhds_of_tendsto_nhds_within tendsto_nhds_of_tendsto_nhdsWithin

#print principal_subtype /-
theorem principal_subtype {α : Type _} (s : Set α) (t : Set { x // x ∈ s }) :
    𝓟 t = comap coe (𝓟 ((coe : s → α) '' t)) := by
  rw [comap_principal, Set.preimage_image_eq _ Subtype.coe_injective]
#align principal_subtype principal_subtype
-/

#print nhdsWithin_neBot_of_mem /-
theorem nhdsWithin_neBot_of_mem {s : Set α} {x : α} (hx : x ∈ s) : NeBot (𝓝[s] x) :=
  mem_closure_iff_nhdsWithin_neBot.1 <| subset_closure hx
#align nhds_within_ne_bot_of_mem nhdsWithin_neBot_of_mem
-/

#print IsClosed.mem_of_nhdsWithin_neBot /-
theorem IsClosed.mem_of_nhdsWithin_neBot {s : Set α} (hs : IsClosed s) {x : α}
    (hx : NeBot <| 𝓝[s] x) : x ∈ s := by
  simpa only [hs.closure_eq] using mem_closure_iff_nhdsWithin_neBot.2 hx
#align is_closed.mem_of_nhds_within_ne_bot IsClosed.mem_of_nhdsWithin_neBot
-/

#print DenseRange.nhdsWithin_neBot /-
theorem DenseRange.nhdsWithin_neBot {ι : Type _} {f : ι → α} (h : DenseRange f) (x : α) :
    NeBot (𝓝[range f] x) :=
  mem_closure_iff_clusterPt.1 (h x)
#align dense_range.nhds_within_ne_bot DenseRange.nhdsWithin_neBot
-/

/- warning: mem_closure_pi -> mem_closure_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (α i)] {I : Set.{u1} ι} {s : forall (i : ι), Set.{u2} (α i)} {x : forall (i : ι), α i}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) x (closure.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) -> (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) (x i) (closure.{u2} (α i) (_inst_2 i) (s i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (α i)] {I : Set.{u2} ι} {s : forall (i : ι), Set.{u1} (α i)} {x : forall (i : ι), α i}, Iff (Membership.mem.{max u2 u1, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) x (closure.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I s))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) -> (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) (x i) (closure.{u1} (α i) (_inst_2 i) (s i))))
Case conversion may be inaccurate. Consider using '#align mem_closure_pi mem_closure_piₓ'. -/
theorem mem_closure_pi {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    {s : ∀ i, Set (α i)} {x : ∀ i, α i} : x ∈ closure (pi I s) ↔ ∀ i ∈ I, x i ∈ closure (s i) := by
  simp only [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_pi_neBot]
#align mem_closure_pi mem_closure_pi

/- warning: closure_pi_set -> closure_pi_set is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (α i)] (I : Set.{u1} ι) (s : forall (i : ι), Set.{u2} (α i)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (closure.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I (fun (i : ι) => closure.{u2} (α i) (_inst_2 i) (s i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (α i)] (I : Set.{u2} ι) (s : forall (i : ι), Set.{u1} (α i)), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (forall (i : ι), α i)) (closure.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I s)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I (fun (i : ι) => closure.{u1} (α i) (_inst_2 i) (s i)))
Case conversion may be inaccurate. Consider using '#align closure_pi_set closure_pi_setₓ'. -/
theorem closure_pi_set {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] (I : Set ι)
    (s : ∀ i, Set (α i)) : closure (pi I s) = pi I fun i => closure (s i) :=
  Set.ext fun x => mem_closure_pi
#align closure_pi_set closure_pi_set

/- warning: dense_pi -> dense_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (α i)] {s : forall (i : ι), Set.{u2} (α i)} (I : Set.{u1} ι), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) -> (Dense.{u2} (α i) (_inst_2 i) (s i))) -> (Dense.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (α i)] {s : forall (i : ι), Set.{u1} (α i)} (I : Set.{u2} ι), (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) -> (Dense.{u1} (α i) (_inst_2 i) (s i))) -> (Dense.{max u1 u2} (forall (i : ι), α i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I s))
Case conversion may be inaccurate. Consider using '#align dense_pi dense_piₓ'. -/
theorem dense_pi {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {s : ∀ i, Set (α i)}
    (I : Set ι) (hs : ∀ i ∈ I, Dense (s i)) : Dense (pi I s) := by
  simp only [dense_iff_closure_eq, closure_pi_set, pi_congr rfl fun i hi => (hs i hi).closure_eq,
    pi_univ]
#align dense_pi dense_pi

/- warning: eventually_eq_nhds_within_iff -> eventuallyEq_nhdsWithin_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> β} {g : α -> β} {s : Set.{u1} α} {a : α}, Iff (Filter.EventuallyEq.{u1, u2} α β (nhdsWithin.{u1} α _inst_1 a s) f g) (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u2} β (f x) (g x))) (nhds.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : α -> β} {g : α -> β} {s : Set.{u2} α} {a : α}, Iff (Filter.EventuallyEq.{u2, u1} α β (nhdsWithin.{u2} α _inst_1 a s) f g) (Filter.Eventually.{u2} α (fun (x : α) => (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Eq.{succ u1} β (f x) (g x))) (nhds.{u2} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align eventually_eq_nhds_within_iff eventuallyEq_nhdsWithin_iffₓ'. -/
theorem eventuallyEq_nhdsWithin_iff {f g : α → β} {s : Set α} {a : α} :
    f =ᶠ[𝓝[s] a] g ↔ ∀ᶠ x in 𝓝 a, x ∈ s → f x = g x :=
  mem_inf_principal
#align eventually_eq_nhds_within_iff eventuallyEq_nhdsWithin_iff

/- warning: eventually_eq_nhds_within_of_eq_on -> eventuallyEq_nhdsWithin_of_eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> β} {g : α -> β} {s : Set.{u1} α} {a : α}, (Set.EqOn.{u1, u2} α β f g s) -> (Filter.EventuallyEq.{u1, u2} α β (nhdsWithin.{u1} α _inst_1 a s) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : α -> β} {g : α -> β} {s : Set.{u2} α} {a : α}, (Set.EqOn.{u2, u1} α β f g s) -> (Filter.EventuallyEq.{u2, u1} α β (nhdsWithin.{u2} α _inst_1 a s) f g)
Case conversion may be inaccurate. Consider using '#align eventually_eq_nhds_within_of_eq_on eventuallyEq_nhdsWithin_of_eqOnₓ'. -/
theorem eventuallyEq_nhdsWithin_of_eqOn {f g : α → β} {s : Set α} {a : α} (h : EqOn f g s) :
    f =ᶠ[𝓝[s] a] g :=
  mem_inf_of_right h
#align eventually_eq_nhds_within_of_eq_on eventuallyEq_nhdsWithin_of_eqOn

/- warning: set.eq_on.eventually_eq_nhds_within -> Set.EqOn.eventuallyEq_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> β} {g : α -> β} {s : Set.{u1} α} {a : α}, (Set.EqOn.{u1, u2} α β f g s) -> (Filter.EventuallyEq.{u1, u2} α β (nhdsWithin.{u1} α _inst_1 a s) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : α -> β} {g : α -> β} {s : Set.{u2} α} {a : α}, (Set.EqOn.{u2, u1} α β f g s) -> (Filter.EventuallyEq.{u2, u1} α β (nhdsWithin.{u2} α _inst_1 a s) f g)
Case conversion may be inaccurate. Consider using '#align set.eq_on.eventually_eq_nhds_within Set.EqOn.eventuallyEq_nhdsWithinₓ'. -/
theorem Set.EqOn.eventuallyEq_nhdsWithin {f g : α → β} {s : Set α} {a : α} (h : EqOn f g s) :
    f =ᶠ[𝓝[s] a] g :=
  eventuallyEq_nhdsWithin_of_eqOn h
#align set.eq_on.eventually_eq_nhds_within Set.EqOn.eventuallyEq_nhdsWithin

/- warning: tendsto_nhds_within_congr -> tendsto_nhdsWithin_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> β} {g : α -> β} {s : Set.{u1} α} {a : α} {l : Filter.{u2} β}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u2} β (f x) (g x))) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s) l) -> (Filter.Tendsto.{u1, u2} α β g (nhdsWithin.{u1} α _inst_1 a s) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {f : α -> β} {g : α -> β} {s : Set.{u2} α} {a : α} {l : Filter.{u1} β}, (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Eq.{succ u1} β (f x) (g x))) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a s) l) -> (Filter.Tendsto.{u2, u1} α β g (nhdsWithin.{u2} α _inst_1 a s) l)
Case conversion may be inaccurate. Consider using '#align tendsto_nhds_within_congr tendsto_nhdsWithin_congrₓ'. -/
theorem tendsto_nhdsWithin_congr {f g : α → β} {s : Set α} {a : α} {l : Filter β}
    (hfg : ∀ x ∈ s, f x = g x) (hf : Tendsto f (𝓝[s] a) l) : Tendsto g (𝓝[s] a) l :=
  (tendsto_congr' <| eventuallyEq_nhdsWithin_of_eqOn hfg).1 hf
#align tendsto_nhds_within_congr tendsto_nhdsWithin_congr

#print eventually_nhdsWithin_of_forall /-
theorem eventually_nhdsWithin_of_forall {s : Set α} {a : α} {p : α → Prop} (h : ∀ x ∈ s, p x) :
    ∀ᶠ x in 𝓝[s] a, p x :=
  mem_inf_of_right h
#align eventually_nhds_within_of_forall eventually_nhdsWithin_of_forall
-/

#print tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within /-
theorem tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α}
    (f : β → α) (h1 : Tendsto f l (𝓝 a)) (h2 : ∀ᶠ x in l, f x ∈ s) : Tendsto f l (𝓝[s] a) :=
  tendsto_inf.2 ⟨h1, tendsto_principal.2 h2⟩
#align tendsto_nhds_within_of_tendsto_nhds_of_eventually_within tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
-/

#print tendsto_nhdsWithin_iff /-
theorem tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s : Set α} {f : β → α} :
    Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ ∀ᶠ n in l, f n ∈ s :=
  ⟨fun h => ⟨tendsto_nhds_of_tendsto_nhdsWithin h, eventually_mem_of_tendsto_nhdsWithin h⟩, fun h =>
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h.1 h.2⟩
#align tendsto_nhds_within_iff tendsto_nhdsWithin_iff
-/

#print tendsto_nhdsWithin_range /-
@[simp]
theorem tendsto_nhdsWithin_range {a : α} {l : Filter β} {f : β → α} :
    Tendsto f l (𝓝[range f] a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => h.mono_right inf_le_left, fun h =>
    tendsto_inf.2 ⟨h, tendsto_principal.2 <| eventually_of_forall mem_range_self⟩⟩
#align tendsto_nhds_within_range tendsto_nhdsWithin_range
-/

/- warning: filter.eventually_eq.eq_of_nhds_within -> Filter.EventuallyEq.eq_of_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {f : α -> β} {g : α -> β} {a : α}, (Filter.EventuallyEq.{u1, u2} α β (nhdsWithin.{u1} α _inst_1 a s) f g) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Eq.{succ u2} β (f a) (g a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {f : α -> β} {g : α -> β} {a : α}, (Filter.EventuallyEq.{u2, u1} α β (nhdsWithin.{u2} α _inst_1 a s) f g) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Eq.{succ u1} β (f a) (g a))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.eq_of_nhds_within Filter.EventuallyEq.eq_of_nhdsWithinₓ'. -/
theorem Filter.EventuallyEq.eq_of_nhdsWithin {s : Set α} {f g : α → β} {a : α} (h : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : f a = g a :=
  h.self_of_nhdsWithin hmem
#align filter.eventually_eq.eq_of_nhds_within Filter.EventuallyEq.eq_of_nhdsWithin

#print eventually_nhdsWithin_of_eventually_nhds /-
theorem eventually_nhdsWithin_of_eventually_nhds {α : Type _} [TopologicalSpace α] {s : Set α}
    {a : α} {p : α → Prop} (h : ∀ᶠ x in 𝓝 a, p x) : ∀ᶠ x in 𝓝[s] a, p x :=
  mem_nhdsWithin_of_mem_nhds h
#align eventually_nhds_within_of_eventually_nhds eventually_nhdsWithin_of_eventually_nhds
-/

/-!
### `nhds_within` and subtypes
-/


#print mem_nhdsWithin_subtype /-
theorem mem_nhdsWithin_subtype {s : Set α} {a : { x // x ∈ s }} {t u : Set { x // x ∈ s }} :
    t ∈ 𝓝[u] a ↔ t ∈ comap (coe : s → α) (𝓝[coe '' u] a) := by
  rw [nhdsWithin, nhds_subtype, principal_subtype, ← comap_inf, ← nhdsWithin]
#align mem_nhds_within_subtype mem_nhdsWithin_subtype
-/

#print nhdsWithin_subtype /-
theorem nhdsWithin_subtype (s : Set α) (a : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    𝓝[t] a = comap (coe : s → α) (𝓝[coe '' t] a) :=
  Filter.ext fun u => mem_nhdsWithin_subtype
#align nhds_within_subtype nhdsWithin_subtype
-/

#print nhdsWithin_eq_map_subtype_coe /-
theorem nhdsWithin_eq_map_subtype_coe {s : Set α} {a : α} (h : a ∈ s) :
    𝓝[s] a = map (coe : s → α) (𝓝 ⟨a, h⟩) := by
  simpa only [Subtype.range_coe] using (embedding_subtype_coe.map_nhds_eq ⟨a, h⟩).symm
#align nhds_within_eq_map_subtype_coe nhdsWithin_eq_map_subtype_coe
-/

#print mem_nhds_subtype_iff_nhdsWithin /-
theorem mem_nhds_subtype_iff_nhdsWithin {s : Set α} {a : s} {t : Set s} :
    t ∈ 𝓝 a ↔ coe '' t ∈ 𝓝[s] (a : α) := by
  rw [nhdsWithin_eq_map_subtype_coe a.coe_prop, mem_map, preimage_image_eq _ Subtype.coe_injective,
    Subtype.coe_eta]
#align mem_nhds_subtype_iff_nhds_within mem_nhds_subtype_iff_nhdsWithin
-/

#print preimage_coe_mem_nhds_subtype /-
theorem preimage_coe_mem_nhds_subtype {s t : Set α} {a : s} : coe ⁻¹' t ∈ 𝓝 a ↔ t ∈ 𝓝[s] ↑a := by
  simp only [mem_nhds_subtype_iff_nhdsWithin, Subtype.image_preimage_coe, inter_mem_iff,
    self_mem_nhdsWithin, and_true_iff]
#align preimage_coe_mem_nhds_subtype preimage_coe_mem_nhds_subtype
-/

/- warning: tendsto_nhds_within_iff_subtype -> tendsto_nhdsWithin_iff_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {a : α} (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (f : α -> β) (l : Filter.{u2} β), Iff (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s) l) (Filter.Tendsto.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f) (nhds.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) a h)) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {a : α} (h : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (f : α -> β) (l : Filter.{u1} β), Iff (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a s) l) (Filter.Tendsto.{u2, u1} (Set.Elem.{u2} α s) β (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f) (nhds.{u2} (Set.Elem.{u2} α s) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a h)) l)
Case conversion may be inaccurate. Consider using '#align tendsto_nhds_within_iff_subtype tendsto_nhdsWithin_iff_subtypeₓ'. -/
theorem tendsto_nhdsWithin_iff_subtype {s : Set α} {a : α} (h : a ∈ s) (f : α → β) (l : Filter β) :
    Tendsto f (𝓝[s] a) l ↔ Tendsto (s.restrict f) (𝓝 ⟨a, h⟩) l := by
  simp only [tendsto, nhdsWithin_eq_map_subtype_coe h, Filter.map_map, restrict]
#align tendsto_nhds_within_iff_subtype tendsto_nhdsWithin_iff_subtype

variable [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

#print ContinuousWithinAt /-
/-- A function between topological spaces is continuous at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while staying within `s`. -/
def ContinuousWithinAt (f : α → β) (s : Set α) (x : α) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))
#align continuous_within_at ContinuousWithinAt
-/

/- warning: continuous_within_at.tendsto -> ContinuousWithinAt.tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 x s) (nhds.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 x s) (nhds.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.tendsto ContinuousWithinAt.tendstoₓ'. -/
/-- If a function is continuous within `s` at `x`, then it tends to `f x` within `s` by definition.
We register this fact for use with the dot notation, especially to use `tendsto.comp` as
`continuous_within_at.comp` will have a different meaning. -/
theorem ContinuousWithinAt.tendsto {f : α → β} {s : Set α} {x : α} (h : ContinuousWithinAt f s x) :
    Tendsto f (𝓝[s] x) (𝓝 (f x)) :=
  h
#align continuous_within_at.tendsto ContinuousWithinAt.tendsto

#print ContinuousOn /-
/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
def ContinuousOn (f : α → β) (s : Set α) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x
#align continuous_on ContinuousOn
-/

/- warning: continuous_on.continuous_within_at -> ContinuousOn.continuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align continuous_on.continuous_within_at ContinuousOn.continuousWithinAtₓ'. -/
theorem ContinuousOn.continuousWithinAt {f : α → β} {s : Set α} {x : α} (hf : ContinuousOn f s)
    (hx : x ∈ s) : ContinuousWithinAt f s x :=
  hf x hx
#align continuous_on.continuous_within_at ContinuousOn.continuousWithinAt

/- warning: continuous_within_at_univ -> continuousWithinAt_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : α -> β) (x : α), Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (Set.univ.{u1} α) x) (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : α -> β) (x : α), Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (Set.univ.{u2} α) x) (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at_univ continuousWithinAt_univₓ'. -/
theorem continuousWithinAt_univ (f : α → β) (x : α) :
    ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x := by
  rw [ContinuousAt, ContinuousWithinAt, nhdsWithin_univ]
#align continuous_within_at_univ continuousWithinAt_univ

/- warning: continuous_within_at_iff_continuous_at_restrict -> continuousWithinAt_iff_continuousAt_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : α -> β) {x : α} {s : Set.{u1} α} (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s), Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) (ContinuousAt.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2 (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : α -> β) {x : α} {s : Set.{u2} α} (h : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s), Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) (ContinuousAt.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2 (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f) (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x h))
Case conversion may be inaccurate. Consider using '#align continuous_within_at_iff_continuous_at_restrict continuousWithinAt_iff_continuousAt_restrictₓ'. -/
theorem continuousWithinAt_iff_continuousAt_restrict (f : α → β) {x : α} {s : Set α} (h : x ∈ s) :
    ContinuousWithinAt f s x ↔ ContinuousAt (s.restrict f) ⟨x, h⟩ :=
  tendsto_nhdsWithin_iff_subtype h f _
#align continuous_within_at_iff_continuous_at_restrict continuousWithinAt_iff_continuousAt_restrict

/- warning: continuous_within_at.tendsto_nhds_within -> ContinuousWithinAt.tendsto_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 x s) (nhdsWithin.{u2} β _inst_2 (f x) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α} {t : Set.{u1} β}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Set.MapsTo.{u2, u1} α β f s t) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 x s) (nhdsWithin.{u1} β _inst_2 (f x) t))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.tendsto_nhds_within ContinuousWithinAt.tendsto_nhdsWithinₓ'. -/
theorem ContinuousWithinAt.tendsto_nhdsWithin {f : α → β} {x : α} {s : Set α} {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f (𝓝[s] x) (𝓝[t] f x) :=
  tendsto_inf.2 ⟨h, tendsto_principal.2 <| mem_inf_of_right <| mem_principal.2 <| ht⟩
#align continuous_within_at.tendsto_nhds_within ContinuousWithinAt.tendsto_nhdsWithin

/- warning: continuous_within_at.tendsto_nhds_within_image -> ContinuousWithinAt.tendsto_nhdsWithin_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 x s) (nhdsWithin.{u2} β _inst_2 (f x) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 x s) (nhdsWithin.{u1} β _inst_2 (f x) (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.tendsto_nhds_within_image ContinuousWithinAt.tendsto_nhdsWithin_imageₓ'. -/
theorem ContinuousWithinAt.tendsto_nhdsWithin_image {f : α → β} {x : α} {s : Set α}
    (h : ContinuousWithinAt f s x) : Tendsto f (𝓝[s] x) (𝓝[f '' s] f x) :=
  h.tendsto_nhdsWithin (mapsTo_image _ _)
#align continuous_within_at.tendsto_nhds_within_image ContinuousWithinAt.tendsto_nhdsWithin_image

/- warning: continuous_within_at.prod_map -> ContinuousWithinAt.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> γ} {g : β -> δ} {s : Set.{u1} α} {t : Set.{u2} β} {x : α} {y : β}, (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 f s x) -> (ContinuousWithinAt.{u2, u4} β δ _inst_2 _inst_4 g t y) -> (ContinuousWithinAt.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u3, u4} γ δ _inst_3 _inst_4) (Prod.map.{u1, u3, u2, u4} α γ β δ f g) (Set.prod.{u1, u2} α β s t) (Prod.mk.{u1, u2} α β x y))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> γ} {g : β -> δ} {s : Set.{u4} α} {t : Set.{u3} β} {x : α} {y : β}, (ContinuousWithinAt.{u4, u2} α γ _inst_1 _inst_3 f s x) -> (ContinuousWithinAt.{u3, u1} β δ _inst_2 _inst_4 g t y) -> (ContinuousWithinAt.{max u3 u4, max u1 u2} (Prod.{u4, u3} α β) (Prod.{u2, u1} γ δ) (instTopologicalSpaceProd.{u4, u3} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u2, u1} γ δ _inst_3 _inst_4) (Prod.map.{u4, u2, u3, u1} α γ β δ f g) (Set.prod.{u4, u3} α β s t) (Prod.mk.{u4, u3} α β x y))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.prod_map ContinuousWithinAt.prod_mapₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ContinuousWithinAt.prod_map {f : α → γ} {g : β → δ} {s : Set α} {t : Set β} {x : α} {y : β}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g t y) :
    ContinuousWithinAt (Prod.map f g) (s ×ˢ t) (x, y) :=
  by
  unfold ContinuousWithinAt at *
  rw [nhdsWithin_prod_eq, Prod.map, nhds_prod_eq]
  exact hf.prod_map hg
#align continuous_within_at.prod_map ContinuousWithinAt.prod_map

/- warning: continuous_within_at_pi -> continuousWithinAt_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_5 : forall (i : ι), TopologicalSpace.{u3} (π i)] {f : α -> (forall (i : ι), π i)} {s : Set.{u1} α} {x : α}, Iff (ContinuousWithinAt.{u1, max u2 u3} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_5 a)) f s x) (forall (i : ι), ContinuousWithinAt.{u1, u3} α (π i) _inst_1 (_inst_5 i) (fun (y : α) => f y i) s x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u3}} {π : ι -> Type.{u2}} [_inst_5 : forall (i : ι), TopologicalSpace.{u2} (π i)] {f : α -> (forall (i : ι), π i)} {s : Set.{u1} α} {x : α}, Iff (ContinuousWithinAt.{u1, max u3 u2} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u3, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_5 a)) f s x) (forall (i : ι), ContinuousWithinAt.{u1, u2} α (π i) _inst_1 (_inst_5 i) (fun (y : α) => f y i) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at_pi continuousWithinAt_piₓ'. -/
theorem continuousWithinAt_pi {ι : Type _} {π : ι → Type _} [∀ i, TopologicalSpace (π i)]
    {f : α → ∀ i, π i} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔ ∀ i, ContinuousWithinAt (fun y => f y i) s x :=
  tendsto_pi_nhds
#align continuous_within_at_pi continuousWithinAt_pi

/- warning: continuous_on_pi -> continuousOn_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_5 : forall (i : ι), TopologicalSpace.{u3} (π i)] {f : α -> (forall (i : ι), π i)} {s : Set.{u1} α}, Iff (ContinuousOn.{u1, max u2 u3} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_5 a)) f s) (forall (i : ι), ContinuousOn.{u1, u3} α (π i) _inst_1 (_inst_5 i) (fun (y : α) => f y i) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u3}} {π : ι -> Type.{u2}} [_inst_5 : forall (i : ι), TopologicalSpace.{u2} (π i)] {f : α -> (forall (i : ι), π i)} {s : Set.{u1} α}, Iff (ContinuousOn.{u1, max u3 u2} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u3, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_5 a)) f s) (forall (i : ι), ContinuousOn.{u1, u2} α (π i) _inst_1 (_inst_5 i) (fun (y : α) => f y i) s)
Case conversion may be inaccurate. Consider using '#align continuous_on_pi continuousOn_piₓ'. -/
theorem continuousOn_pi {ι : Type _} {π : ι → Type _} [∀ i, TopologicalSpace (π i)]
    {f : α → ∀ i, π i} {s : Set α} : ContinuousOn f s ↔ ∀ i, ContinuousOn (fun y => f y i) s :=
  ⟨fun h i x hx => tendsto_pi_nhds.1 (h x hx) i, fun h x hx => tendsto_pi_nhds.2 fun i => h i x hx⟩
#align continuous_on_pi continuousOn_pi

/- warning: continuous_within_at.fin_insert_nth -> ContinuousWithinAt.fin_insertNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u2}} [_inst_5 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), TopologicalSpace.{u2} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) {f : α -> (π i)} {a : α} {s : Set.{u1} α}, (ContinuousWithinAt.{u1, u2} α (π i) _inst_1 (_inst_5 i) f s a) -> (forall {g : α -> (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j))}, (ContinuousWithinAt.{u1, u2} α (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin n) (fun (j : Fin n) => π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (fun (a : Fin n) => _inst_5 (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) a))) g s a) -> (ContinuousWithinAt.{u1, u2} α (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), π j) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => _inst_5 a)) (fun (a : α) => Fin.insertNth.{u2} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π i) i (f a) (g a)) s a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u2}} [_inst_5 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), TopologicalSpace.{u2} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) {f : α -> (π i)} {a : α} {s : Set.{u1} α}, (ContinuousWithinAt.{u1, u2} α (π i) _inst_1 (_inst_5 i) f s a) -> (forall {g : α -> (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j))}, (ContinuousWithinAt.{u1, u2} α (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin n) (fun (j : Fin n) => π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) (fun (a : Fin n) => _inst_5 (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) a))) g s a) -> (ContinuousWithinAt.{u1, u2} α (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), π j) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => _inst_5 a)) (fun (a : α) => Fin.insertNth.{u2} n π i (f a) (g a)) s a))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.fin_insert_nth ContinuousWithinAt.fin_insertNthₓ'. -/
theorem ContinuousWithinAt.fin_insertNth {n} {π : Fin (n + 1) → Type _}
    [∀ i, TopologicalSpace (π i)] (i : Fin (n + 1)) {f : α → π i} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) {g : α → ∀ j : Fin n, π (i.succAbove j)}
    (hg : ContinuousWithinAt g s a) : ContinuousWithinAt (fun a => i.insertNth (f a) (g a)) s a :=
  hf.fin_insertNth i hg
#align continuous_within_at.fin_insert_nth ContinuousWithinAt.fin_insertNth

/- warning: continuous_on.fin_insert_nth -> ContinuousOn.fin_insertNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u2}} [_inst_5 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), TopologicalSpace.{u2} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) {f : α -> (π i)} {s : Set.{u1} α}, (ContinuousOn.{u1, u2} α (π i) _inst_1 (_inst_5 i) f s) -> (forall {g : α -> (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j))}, (ContinuousOn.{u1, u2} α (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin n) (fun (j : Fin n) => π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (fun (a : Fin n) => _inst_5 (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) a))) g s) -> (ContinuousOn.{u1, u2} α (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), π j) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => _inst_5 a)) (fun (a : α) => Fin.insertNth.{u2} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π i) i (f a) (g a)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u2}} [_inst_5 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), TopologicalSpace.{u2} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) {f : α -> (π i)} {s : Set.{u1} α}, (ContinuousOn.{u1, u2} α (π i) _inst_1 (_inst_5 i) f s) -> (forall {g : α -> (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j))}, (ContinuousOn.{u1, u2} α (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin n) (fun (j : Fin n) => π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) (fun (a : Fin n) => _inst_5 (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) a))) g s) -> (ContinuousOn.{u1, u2} α (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), π j) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => _inst_5 a)) (fun (a : α) => Fin.insertNth.{u2} n π i (f a) (g a)) s))
Case conversion may be inaccurate. Consider using '#align continuous_on.fin_insert_nth ContinuousOn.fin_insertNthₓ'. -/
theorem ContinuousOn.fin_insertNth {n} {π : Fin (n + 1) → Type _} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : α → π i} {s : Set α} (hf : ContinuousOn f s)
    {g : α → ∀ j : Fin n, π (i.succAbove j)} (hg : ContinuousOn g s) :
    ContinuousOn (fun a => i.insertNth (f a) (g a)) s := fun a ha =>
  (hf a ha).fin_insertNth i (hg a ha)
#align continuous_on.fin_insert_nth ContinuousOn.fin_insertNth

/- warning: continuous_on_iff -> continuousOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (t : Set.{u2} β), (IsOpen.{u2} β _inst_2 t) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (IsOpen.{u1} α _inst_1 u) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x u) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s) (Set.preimage.{u1, u2} α β f t)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, Iff (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (t : Set.{u1} β), (IsOpen.{u1} β _inst_2 t) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) t) -> (Exists.{succ u2} (Set.{u2} α) (fun (u : Set.{u2} α) => And (IsOpen.{u2} α _inst_1 u) (And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x u) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) u s) (Set.preimage.{u2, u1} α β f t)))))))
Case conversion may be inaccurate. Consider using '#align continuous_on_iff continuousOn_iffₓ'. -/
theorem continuousOn_iff {f : α → β} {s : Set α} :
    ContinuousOn f s ↔
      ∀ x ∈ s, ∀ t : Set β, IsOpen t → f x ∈ t → ∃ u, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ f ⁻¹' t :=
  by simp only [ContinuousOn, ContinuousWithinAt, tendsto_nhds, mem_nhdsWithin]
#align continuous_on_iff continuousOn_iff

/- warning: continuous_on_iff_continuous_restrict -> continuousOn_iff_continuous_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) (Continuous.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2 (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, Iff (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) (Continuous.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2 (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f))
Case conversion may be inaccurate. Consider using '#align continuous_on_iff_continuous_restrict continuousOn_iff_continuous_restrictₓ'. -/
theorem continuousOn_iff_continuous_restrict {f : α → β} {s : Set α} :
    ContinuousOn f s ↔ Continuous (s.restrict f) :=
  by
  rw [ContinuousOn, continuous_iff_continuousAt]; constructor
  · rintro h ⟨x, xs⟩
    exact (continuousWithinAt_iff_continuousAt_restrict f xs).mp (h x xs)
  intro h x xs
  exact (continuousWithinAt_iff_continuousAt_restrict f xs).mpr (h ⟨x, xs⟩)
#align continuous_on_iff_continuous_restrict continuousOn_iff_continuous_restrict

/- warning: continuous_on_iff' -> continuousOn_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) (forall (t : Set.{u2} β), (IsOpen.{u2} β _inst_2 t) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (IsOpen.{u1} α _inst_1 u) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, u2} α β f t) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, Iff (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) (forall (t : Set.{u1} β), (IsOpen.{u1} β _inst_2 t) -> (Exists.{succ u2} (Set.{u2} α) (fun (u : Set.{u2} α) => And (IsOpen.{u2} α _inst_1 u) (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Set.preimage.{u2, u1} α β f t) s) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) u s)))))
Case conversion may be inaccurate. Consider using '#align continuous_on_iff' continuousOn_iff'ₓ'. -/
theorem continuousOn_iff' {f : α → β} {s : Set α} :
    ContinuousOn f s ↔ ∀ t : Set β, IsOpen t → ∃ u, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s :=
  by
  have : ∀ t, IsOpen (s.restrict f ⁻¹' t) ↔ ∃ u : Set α, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s :=
    by
    intro t
    rw [isOpen_induced_iff, Set.restrict_eq, Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff]
    constructor <;>
      · rintro ⟨u, ou, useq⟩
        exact ⟨u, ou, useq.symm⟩
  rw [continuousOn_iff_continuous_restrict, continuous_def] <;> simp only [this]
#align continuous_on_iff' continuousOn_iff'

/- warning: continuous_on.mono_dom -> ContinuousOn.mono_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β}, (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t₂ t₁) -> (forall {s : Set.{u1} α} {f : α -> β}, (ContinuousOn.{u1, u2} α β t₁ t₃ f s) -> (ContinuousOn.{u1, u2} α β t₂ t₃ f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t₁ : TopologicalSpace.{u2} α} {t₂ : TopologicalSpace.{u2} α} {t₃ : TopologicalSpace.{u1} β}, (LE.le.{u2} (TopologicalSpace.{u2} α) (Preorder.toLE.{u2} (TopologicalSpace.{u2} α) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u2} α))) t₂ t₁) -> (forall {s : Set.{u2} α} {f : α -> β}, (ContinuousOn.{u2, u1} α β t₁ t₃ f s) -> (ContinuousOn.{u2, u1} α β t₂ t₃ f s))
Case conversion may be inaccurate. Consider using '#align continuous_on.mono_dom ContinuousOn.mono_domₓ'. -/
/-- If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any finer topology on the source space. -/
theorem ContinuousOn.mono_dom {α β : Type _} {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β}
    (h₁ : t₂ ≤ t₁) {s : Set α} {f : α → β} (h₂ : @ContinuousOn α β t₁ t₃ f s) :
    @ContinuousOn α β t₂ t₃ f s := by
  rw [continuousOn_iff'] at h₂⊢
  intro t ht
  rcases h₂ t ht with ⟨u, hu, h'u⟩
  exact ⟨u, h₁ u hu, h'u⟩
#align continuous_on.mono_dom ContinuousOn.mono_dom

/- warning: continuous_on.mono_rng -> ContinuousOn.mono_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u2} β} {t₃ : TopologicalSpace.{u2} β}, (LE.le.{u2} (TopologicalSpace.{u2} β) (Preorder.toLE.{u2} (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.partialOrder.{u2} β))) t₂ t₃) -> (forall {s : Set.{u1} α} {f : α -> β}, (ContinuousOn.{u1, u2} α β t₁ t₂ f s) -> (ContinuousOn.{u1, u2} α β t₁ t₃ f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t₁ : TopologicalSpace.{u2} α} {t₂ : TopologicalSpace.{u1} β} {t₃ : TopologicalSpace.{u1} β}, (LE.le.{u1} (TopologicalSpace.{u1} β) (Preorder.toLE.{u1} (TopologicalSpace.{u1} β) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} β))) t₂ t₃) -> (forall {s : Set.{u2} α} {f : α -> β}, (ContinuousOn.{u2, u1} α β t₁ t₂ f s) -> (ContinuousOn.{u2, u1} α β t₁ t₃ f s))
Case conversion may be inaccurate. Consider using '#align continuous_on.mono_rng ContinuousOn.mono_rngₓ'. -/
/-- If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any coarser topology on the target space. -/
theorem ContinuousOn.mono_rng {α β : Type _} {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β}
    (h₁ : t₂ ≤ t₃) {s : Set α} {f : α → β} (h₂ : @ContinuousOn α β t₁ t₂ f s) :
    @ContinuousOn α β t₁ t₃ f s := by
  rw [continuousOn_iff'] at h₂⊢
  intro t ht
  exact h₂ t (h₁ t ht)
#align continuous_on.mono_rng ContinuousOn.mono_rng

/- warning: continuous_on_iff_is_closed -> continuousOn_iff_isClosed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) (forall (t : Set.{u2} β), (IsClosed.{u2} β _inst_2 t) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (IsClosed.{u1} α _inst_1 u) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, u2} α β f t) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, Iff (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) (forall (t : Set.{u1} β), (IsClosed.{u1} β _inst_2 t) -> (Exists.{succ u2} (Set.{u2} α) (fun (u : Set.{u2} α) => And (IsClosed.{u2} α _inst_1 u) (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Set.preimage.{u2, u1} α β f t) s) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) u s)))))
Case conversion may be inaccurate. Consider using '#align continuous_on_iff_is_closed continuousOn_iff_isClosedₓ'. -/
theorem continuousOn_iff_isClosed {f : α → β} {s : Set α} :
    ContinuousOn f s ↔ ∀ t : Set β, IsClosed t → ∃ u, IsClosed u ∧ f ⁻¹' t ∩ s = u ∩ s :=
  by
  have : ∀ t, IsClosed (s.restrict f ⁻¹' t) ↔ ∃ u : Set α, IsClosed u ∧ f ⁻¹' t ∩ s = u ∩ s :=
    by
    intro t
    rw [isClosed_induced_iff, Set.restrict_eq, Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]
  rw [continuousOn_iff_continuous_restrict, continuous_iff_isClosed] <;> simp only [this]
#align continuous_on_iff_is_closed continuousOn_iff_isClosed

/- warning: continuous_on.prod_map -> ContinuousOn.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> γ} {g : β -> δ} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousOn.{u1, u3} α γ _inst_1 _inst_3 f s) -> (ContinuousOn.{u2, u4} β δ _inst_2 _inst_4 g t) -> (ContinuousOn.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u3, u4} γ δ _inst_3 _inst_4) (Prod.map.{u1, u3, u2, u4} α γ β δ f g) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> γ} {g : β -> δ} {s : Set.{u4} α} {t : Set.{u3} β}, (ContinuousOn.{u4, u2} α γ _inst_1 _inst_3 f s) -> (ContinuousOn.{u3, u1} β δ _inst_2 _inst_4 g t) -> (ContinuousOn.{max u3 u4, max u1 u2} (Prod.{u4, u3} α β) (Prod.{u2, u1} γ δ) (instTopologicalSpaceProd.{u4, u3} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u2, u1} γ δ _inst_3 _inst_4) (Prod.map.{u4, u2, u3, u1} α γ β δ f g) (Set.prod.{u4, u3} α β s t))
Case conversion may be inaccurate. Consider using '#align continuous_on.prod_map ContinuousOn.prod_mapₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ContinuousOn.prod_map {f : α → γ} {g : β → δ} {s : Set α} {t : Set β}
    (hf : ContinuousOn f s) (hg : ContinuousOn g t) : ContinuousOn (Prod.map f g) (s ×ˢ t) :=
  fun ⟨x, y⟩ ⟨hx, hy⟩ => ContinuousWithinAt.prod_map (hf x hx) (hg y hy)
#align continuous_on.prod_map ContinuousOn.prod_map

/- warning: continuous_on_empty -> continuousOn_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : α -> β), ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : α -> β), ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))
Case conversion may be inaccurate. Consider using '#align continuous_on_empty continuousOn_emptyₓ'. -/
theorem continuousOn_empty (f : α → β) : ContinuousOn f ∅ := fun x => False.elim
#align continuous_on_empty continuousOn_empty

/- warning: continuous_on_singleton -> continuousOn_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : α -> β) (a : α), ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : α -> β) (a : α), ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a)
Case conversion may be inaccurate. Consider using '#align continuous_on_singleton continuousOn_singletonₓ'. -/
theorem continuousOn_singleton (f : α → β) (a : α) : ContinuousOn f {a} :=
  forall_eq.2 <| by
    simpa only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_left] using fun s =>
      mem_of_mem_nhds
#align continuous_on_singleton continuousOn_singleton

/- warning: set.subsingleton.continuous_on -> Set.Subsingleton.continuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (forall (f : α -> β), ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α}, (Set.Subsingleton.{u2} α s) -> (forall (f : α -> β), ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s)
Case conversion may be inaccurate. Consider using '#align set.subsingleton.continuous_on Set.Subsingleton.continuousOnₓ'. -/
theorem Set.Subsingleton.continuousOn {s : Set α} (hs : s.Subsingleton) (f : α → β) :
    ContinuousOn f s :=
  hs.inductionOn (continuousOn_empty f) (continuousOn_singleton f)
#align set.subsingleton.continuous_on Set.Subsingleton.continuousOn

/- warning: nhds_within_le_comap -> nhdsWithin_le_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {x : α} {s : Set.{u1} α} {f : α -> β}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhdsWithin.{u1} α _inst_1 x s) (Filter.comap.{u1, u2} α β f (nhdsWithin.{u2} β _inst_2 (f x) (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {x : α} {s : Set.{u2} α} {f : α -> β}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (LE.le.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) (nhdsWithin.{u2} α _inst_1 x s) (Filter.comap.{u2, u1} α β f (nhdsWithin.{u1} β _inst_2 (f x) (Set.image.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align nhds_within_le_comap nhdsWithin_le_comapₓ'. -/
theorem nhdsWithin_le_comap {x : α} {s : Set α} {f : α → β} (ctsf : ContinuousWithinAt f s x) :
    𝓝[s] x ≤ comap f (𝓝[f '' s] f x) :=
  ctsf.tendsto_nhdsWithin_image.le_comap
#align nhds_within_le_comap nhdsWithin_le_comap

#print comap_nhdsWithin_range /-
@[simp]
theorem comap_nhdsWithin_range {α} (f : α → β) (y : β) : comap f (𝓝[range f] y) = comap f (𝓝 y) :=
  comap_inf_principal_range
#align comap_nhds_within_range comap_nhdsWithin_range
-/

/- warning: continuous_iff_continuous_on_univ -> continuous_iff_continuousOn_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, Iff (Continuous.{u1, u2} α β _inst_1 _inst_2 f) (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, Iff (Continuous.{u2, u1} α β _inst_1 _inst_2 f) (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (Set.univ.{u2} α))
Case conversion may be inaccurate. Consider using '#align continuous_iff_continuous_on_univ continuous_iff_continuousOn_univₓ'. -/
theorem continuous_iff_continuousOn_univ {f : α → β} : Continuous f ↔ ContinuousOn f univ := by
  simp [continuous_iff_continuousAt, ContinuousOn, ContinuousAt, ContinuousWithinAt,
    nhdsWithin_univ]
#align continuous_iff_continuous_on_univ continuous_iff_continuousOn_univ

/- warning: continuous_within_at.mono -> ContinuousWithinAt.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f t x) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f t x) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.mono ContinuousWithinAt.monoₓ'. -/
theorem ContinuousWithinAt.mono {f : α → β} {s t : Set α} {x : α} (h : ContinuousWithinAt f t x)
    (hs : s ⊆ t) : ContinuousWithinAt f s x :=
  h.mono_left (nhdsWithin_mono x hs)
#align continuous_within_at.mono ContinuousWithinAt.mono

/- warning: continuous_within_at.mono_of_mem -> ContinuousWithinAt.mono_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f t x) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhdsWithin.{u1} α _inst_1 x s)) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f t x) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t (nhdsWithin.{u2} α _inst_1 x s)) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.mono_of_mem ContinuousWithinAt.mono_of_memₓ'. -/
theorem ContinuousWithinAt.mono_of_mem {f : α → β} {s t : Set α} {x : α}
    (h : ContinuousWithinAt f t x) (hs : t ∈ 𝓝[s] x) : ContinuousWithinAt f s x :=
  h.mono_left (nhdsWithin_le_of_mem hs)
#align continuous_within_at.mono_of_mem ContinuousWithinAt.mono_of_mem

/- warning: continuous_within_at_inter' -> continuousWithinAt_inter' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhdsWithin.{u1} α _inst_1 x s)) -> (Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) x) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α} {x : α}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t (nhdsWithin.{u2} α _inst_1 x s)) -> (Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t) x) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x))
Case conversion may be inaccurate. Consider using '#align continuous_within_at_inter' continuousWithinAt_inter'ₓ'. -/
theorem continuousWithinAt_inter' {f : α → β} {s t : Set α} {x : α} (h : t ∈ 𝓝[s] x) :
    ContinuousWithinAt f (s ∩ t) x ↔ ContinuousWithinAt f s x := by
  simp [ContinuousWithinAt, nhdsWithin_restrict'' s h]
#align continuous_within_at_inter' continuousWithinAt_inter'

/- warning: continuous_within_at_inter -> continuousWithinAt_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhds.{u1} α _inst_1 x)) -> (Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) x) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α} {x : α}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t (nhds.{u2} α _inst_1 x)) -> (Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t) x) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x))
Case conversion may be inaccurate. Consider using '#align continuous_within_at_inter continuousWithinAt_interₓ'. -/
theorem continuousWithinAt_inter {f : α → β} {s t : Set α} {x : α} (h : t ∈ 𝓝 x) :
    ContinuousWithinAt f (s ∩ t) x ↔ ContinuousWithinAt f s x := by
  simp [ContinuousWithinAt, nhdsWithin_restrict' s h]
#align continuous_within_at_inter continuousWithinAt_inter

/- warning: continuous_within_at_union -> continuousWithinAt_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) x) (And (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f t x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α} {x : α}, Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t) x) (And (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f t x))
Case conversion may be inaccurate. Consider using '#align continuous_within_at_union continuousWithinAt_unionₓ'. -/
theorem continuousWithinAt_union {f : α → β} {s t : Set α} {x : α} :
    ContinuousWithinAt f (s ∪ t) x ↔ ContinuousWithinAt f s x ∧ ContinuousWithinAt f t x := by
  simp only [ContinuousWithinAt, nhdsWithin_union, tendsto_sup]
#align continuous_within_at_union continuousWithinAt_union

/- warning: continuous_within_at.union -> ContinuousWithinAt.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f t x) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f t x) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t) x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.union ContinuousWithinAt.unionₓ'. -/
theorem ContinuousWithinAt.union {f : α → β} {s t : Set α} {x : α} (hs : ContinuousWithinAt f s x)
    (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s ∪ t) x :=
  continuousWithinAt_union.2 ⟨hs, ht⟩
#align continuous_within_at.union ContinuousWithinAt.union

/- warning: continuous_within_at.mem_closure_image -> ContinuousWithinAt.mem_closure_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α _inst_1 s)) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (closure.{u2} α _inst_1 s)) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.mem_closure_image ContinuousWithinAt.mem_closure_imageₓ'. -/
theorem ContinuousWithinAt.mem_closure_image {f : α → β} {s : Set α} {x : α}
    (h : ContinuousWithinAt f s x) (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hx
  mem_closure_of_tendsto h <| mem_of_superset self_mem_nhdsWithin (subset_preimage_image f s)
#align continuous_within_at.mem_closure_image ContinuousWithinAt.mem_closure_image

/- warning: continuous_within_at.mem_closure -> ContinuousWithinAt.mem_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α} {A : Set.{u2} β}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α _inst_1 s)) -> (Set.MapsTo.{u1, u2} α β f s A) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) (closure.{u2} β _inst_2 A))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α} {A : Set.{u1} β}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (closure.{u2} α _inst_1 s)) -> (Set.MapsTo.{u2, u1} α β f s A) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) (closure.{u1} β _inst_2 A))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.mem_closure ContinuousWithinAt.mem_closureₓ'. -/
theorem ContinuousWithinAt.mem_closure {f : α → β} {s : Set α} {x : α} {A : Set β}
    (h : ContinuousWithinAt f s x) (hx : x ∈ closure s) (hA : MapsTo f s A) : f x ∈ closure A :=
  closure_mono (image_subset_iff.2 hA) (h.mem_closure_image hx)
#align continuous_within_at.mem_closure ContinuousWithinAt.mem_closure

/- warning: set.maps_to.closure_of_continuous_within_at -> Set.MapsTo.closure_of_continuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.MapsTo.{u1, u2} α β f s t) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α _inst_1 s)) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)) -> (Set.MapsTo.{u1, u2} α β f (closure.{u1} α _inst_1 s) (closure.{u2} β _inst_2 t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.MapsTo.{u2, u1} α β f s t) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (closure.{u2} α _inst_1 s)) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)) -> (Set.MapsTo.{u2, u1} α β f (closure.{u2} α _inst_1 s) (closure.{u1} β _inst_2 t))
Case conversion may be inaccurate. Consider using '#align set.maps_to.closure_of_continuous_within_at Set.MapsTo.closure_of_continuousWithinAtₓ'. -/
theorem Set.MapsTo.closure_of_continuousWithinAt {f : α → β} {s : Set α} {t : Set β}
    (h : MapsTo f s t) (hc : ∀ x ∈ closure s, ContinuousWithinAt f s x) :
    MapsTo f (closure s) (closure t) := fun x hx => (hc x hx).mem_closure hx h
#align set.maps_to.closure_of_continuous_within_at Set.MapsTo.closure_of_continuousWithinAt

/- warning: set.maps_to.closure_of_continuous_on -> Set.MapsTo.closure_of_continuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.MapsTo.{u1, u2} α β f s t) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (closure.{u1} α _inst_1 s)) -> (Set.MapsTo.{u1, u2} α β f (closure.{u1} α _inst_1 s) (closure.{u2} β _inst_2 t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.MapsTo.{u2, u1} α β f s t) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (closure.{u2} α _inst_1 s)) -> (Set.MapsTo.{u2, u1} α β f (closure.{u2} α _inst_1 s) (closure.{u1} β _inst_2 t))
Case conversion may be inaccurate. Consider using '#align set.maps_to.closure_of_continuous_on Set.MapsTo.closure_of_continuousOnₓ'. -/
theorem Set.MapsTo.closure_of_continuousOn {f : α → β} {s : Set α} {t : Set β} (h : MapsTo f s t)
    (hc : ContinuousOn f (closure s)) : MapsTo f (closure s) (closure t) :=
  h.closure_of_continuousWithinAt fun x hx => (hc x hx).mono subset_closure
#align set.maps_to.closure_of_continuous_on Set.MapsTo.closure_of_continuousOn

/- warning: continuous_within_at.image_closure -> ContinuousWithinAt.image_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α _inst_1 s)) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f (closure.{u1} α _inst_1 s)) (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (closure.{u2} α _inst_1 s)) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f (closure.{u2} α _inst_1 s)) (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.image_closure ContinuousWithinAt.image_closureₓ'. -/
theorem ContinuousWithinAt.image_closure {f : α → β} {s : Set α}
    (hf : ∀ x ∈ closure s, ContinuousWithinAt f s x) : f '' closure s ⊆ closure (f '' s) :=
  mapsTo'.1 <| (mapsTo_image f s).closure_of_continuousWithinAt hf
#align continuous_within_at.image_closure ContinuousWithinAt.image_closure

/- warning: continuous_on.image_closure -> ContinuousOn.image_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (closure.{u1} α _inst_1 s)) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f (closure.{u1} α _inst_1 s)) (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (closure.{u2} α _inst_1 s)) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f (closure.{u2} α _inst_1 s)) (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align continuous_on.image_closure ContinuousOn.image_closureₓ'. -/
theorem ContinuousOn.image_closure {f : α → β} {s : Set α} (hf : ContinuousOn f (closure s)) :
    f '' closure s ⊆ closure (f '' s) :=
  ContinuousWithinAt.image_closure fun x hx => (hf x hx).mono subset_closure
#align continuous_on.image_closure ContinuousOn.image_closure

/- warning: continuous_within_at_singleton -> continuousWithinAt_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α}, ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α}, ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x) x
Case conversion may be inaccurate. Consider using '#align continuous_within_at_singleton continuousWithinAt_singletonₓ'. -/
@[simp]
theorem continuousWithinAt_singleton {f : α → β} {x : α} : ContinuousWithinAt f {x} x := by
  simp only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_nhds]
#align continuous_within_at_singleton continuousWithinAt_singleton

/- warning: continuous_within_at_insert_self -> continuousWithinAt_insert_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α}, Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s) x) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α}, Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) x s) x) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at_insert_self continuousWithinAt_insert_selfₓ'. -/
@[simp]
theorem continuousWithinAt_insert_self {f : α → β} {x : α} {s : Set α} :
    ContinuousWithinAt f (insert x s) x ↔ ContinuousWithinAt f s x := by
  simp only [← singleton_union, continuousWithinAt_union, continuousWithinAt_singleton,
    true_and_iff]
#align continuous_within_at_insert_self continuousWithinAt_insert_self

/- warning: continuous_within_at.insert_self -> ContinuousWithinAt.insert_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) x s) x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.insert_self ContinuousWithinAt.insert_selfₓ'. -/
alias continuousWithinAt_insert_self ↔ _ ContinuousWithinAt.insert_self
#align continuous_within_at.insert_self ContinuousWithinAt.insert_self

/- warning: continuous_within_at.diff_iff -> ContinuousWithinAt.diff_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f t x) -> (Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) x) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f t x) -> (Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s t) x) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.diff_iff ContinuousWithinAt.diff_iffₓ'. -/
theorem ContinuousWithinAt.diff_iff {f : α → β} {s t : Set α} {x : α}
    (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s \ t) x ↔ ContinuousWithinAt f s x :=
  ⟨fun h => (h.union ht).mono <| by simp only [diff_union_self, subset_union_left], fun h =>
    h.mono (diff_subset _ _)⟩
#align continuous_within_at.diff_iff ContinuousWithinAt.diff_iff

/- warning: continuous_within_at_diff_self -> continuousWithinAt_diff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) x) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x)) x) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at_diff_self continuousWithinAt_diff_selfₓ'. -/
@[simp]
theorem continuousWithinAt_diff_self {f : α → β} {s : Set α} {x : α} :
    ContinuousWithinAt f (s \ {x}) x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_singleton.diff_iff
#align continuous_within_at_diff_self continuousWithinAt_diff_self

/- warning: continuous_within_at_compl_self -> continuousWithinAt_compl_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {a : α}, Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) a) (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {a : α}, Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a)) a) (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at_compl_self continuousWithinAt_compl_selfₓ'. -/
@[simp]
theorem continuousWithinAt_compl_self {f : α → β} {a : α} :
    ContinuousWithinAt f ({a}ᶜ) a ↔ ContinuousAt f a := by
  rw [compl_eq_univ_diff, continuousWithinAt_diff_self, continuousWithinAt_univ]
#align continuous_within_at_compl_self continuousWithinAt_compl_self

/- warning: continuous_within_at_update_same -> continuousWithinAt_update_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : DecidableEq.{succ u1} α] {f : α -> β} {s : Set.{u1} α} {x : α} {y : β}, Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 (Function.update.{succ u1, succ u2} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_5 a b) f x y) s x) (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))) (nhds.{u2} β _inst_2 y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : DecidableEq.{succ u2} α] {f : α -> β} {s : Set.{u2} α} {x : α} {y : β}, Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 (Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_5 a b) f x y) s x) (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 x (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x))) (nhds.{u1} β _inst_2 y))
Case conversion may be inaccurate. Consider using '#align continuous_within_at_update_same continuousWithinAt_update_sameₓ'. -/
@[simp]
theorem continuousWithinAt_update_same [DecidableEq α] {f : α → β} {s : Set α} {x : α} {y : β} :
    ContinuousWithinAt (update f x y) s x ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
  calc
    ContinuousWithinAt (update f x y) s x ↔ Tendsto (update f x y) (𝓝[s \ {x}] x) (𝓝 y) := by
      rw [← continuousWithinAt_diff_self, ContinuousWithinAt, Function.update_same]
    _ ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
      tendsto_congr' <|
        eventually_nhdsWithin_iff.2 <| eventually_of_forall fun z hz => update_noteq hz.2 _ _
    
#align continuous_within_at_update_same continuousWithinAt_update_same

/- warning: continuous_at_update_same -> continuousAt_update_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : DecidableEq.{succ u1} α] {f : α -> β} {x : α} {y : β}, Iff (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 (Function.update.{succ u1, succ u2} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_5 a b) f x y) x) (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))) (nhds.{u2} β _inst_2 y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : DecidableEq.{succ u2} α] {f : α -> β} {x : α} {y : β}, Iff (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 (Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_5 a b) f x y) x) (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x))) (nhds.{u1} β _inst_2 y))
Case conversion may be inaccurate. Consider using '#align continuous_at_update_same continuousAt_update_sameₓ'. -/
@[simp]
theorem continuousAt_update_same [DecidableEq α] {f : α → β} {x : α} {y : β} :
    ContinuousAt (Function.update f x y) x ↔ Tendsto f (𝓝[≠] x) (𝓝 y) := by
  rw [← continuousWithinAt_univ, continuousWithinAt_update_same, compl_eq_univ_diff]
#align continuous_at_update_same continuousAt_update_same

/- warning: is_open_map.continuous_on_image_of_left_inv_on -> IsOpenMap.continuousOn_image_of_leftInvOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (IsOpenMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2 (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f)) -> (forall {finv : β -> α}, (Set.LeftInvOn.{u1, u2} α β finv f s) -> (ContinuousOn.{u2, u1} β α _inst_2 _inst_1 finv (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (IsOpenMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2 (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f)) -> (forall {finv : β -> α}, (Set.LeftInvOn.{u2, u1} α β finv f s) -> (ContinuousOn.{u1, u2} β α _inst_2 _inst_1 finv (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align is_open_map.continuous_on_image_of_left_inv_on IsOpenMap.continuousOn_image_of_leftInvOnₓ'. -/
theorem IsOpenMap.continuousOn_image_of_leftInvOn {f : α → β} {s : Set α}
    (h : IsOpenMap (s.restrict f)) {finv : β → α} (hleft : LeftInvOn finv f s) :
    ContinuousOn finv (f '' s) :=
  by
  refine' continuousOn_iff'.2 fun t ht => ⟨f '' (t ∩ s), _, _⟩
  · rw [← image_restrict]
    exact h _ (ht.preimage continuous_subtype_val)
  · rw [inter_eq_self_of_subset_left (image_subset f (inter_subset_right t s)), hleft.image_inter']
#align is_open_map.continuous_on_image_of_left_inv_on IsOpenMap.continuousOn_image_of_leftInvOn

/- warning: is_open_map.continuous_on_range_of_left_inverse -> IsOpenMap.continuousOn_range_of_leftInverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (IsOpenMap.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {finv : β -> α}, (Function.LeftInverse.{succ u1, succ u2} α β finv f) -> (ContinuousOn.{u2, u1} β α _inst_2 _inst_1 finv (Set.range.{u2, succ u1} β α f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (IsOpenMap.{u2, u1} α β _inst_1 _inst_2 f) -> (forall {finv : β -> α}, (Function.LeftInverse.{succ u2, succ u1} α β finv f) -> (ContinuousOn.{u1, u2} β α _inst_2 _inst_1 finv (Set.range.{u1, succ u2} β α f)))
Case conversion may be inaccurate. Consider using '#align is_open_map.continuous_on_range_of_left_inverse IsOpenMap.continuousOn_range_of_leftInverseₓ'. -/
theorem IsOpenMap.continuousOn_range_of_leftInverse {f : α → β} (hf : IsOpenMap f) {finv : β → α}
    (hleft : Function.LeftInverse finv f) : ContinuousOn finv (range f) :=
  by
  rw [← image_univ]
  exact (hf.restrict isOpen_univ).continuousOn_image_of_leftInvOn fun x _ => hleft x
#align is_open_map.continuous_on_range_of_left_inverse IsOpenMap.continuousOn_range_of_leftInverse

/- warning: continuous_on.congr_mono -> ContinuousOn.congr_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α} {s₁ : Set.{u1} α}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Set.EqOn.{u1, u2} α β g f s₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 g s₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α} {s₁ : Set.{u2} α}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (Set.EqOn.{u2, u1} α β g f s₁) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s₁ s) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 g s₁)
Case conversion may be inaccurate. Consider using '#align continuous_on.congr_mono ContinuousOn.congr_monoₓ'. -/
theorem ContinuousOn.congr_mono {f g : α → β} {s s₁ : Set α} (h : ContinuousOn f s)
    (h' : EqOn g f s₁) (h₁ : s₁ ⊆ s) : ContinuousOn g s₁ :=
  by
  intro x hx
  unfold ContinuousWithinAt
  have A := (h x (h₁ hx)).mono h₁
  unfold ContinuousWithinAt at A
  rw [← h' hx] at A
  exact A.congr' h'.eventually_eq_nhds_within.symm
#align continuous_on.congr_mono ContinuousOn.congr_mono

/- warning: continuous_on.congr -> ContinuousOn.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Set.EqOn.{u1, u2} α β g f s) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 g s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (Set.EqOn.{u2, u1} α β g f s) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 g s)
Case conversion may be inaccurate. Consider using '#align continuous_on.congr ContinuousOn.congrₓ'. -/
theorem ContinuousOn.congr {f g : α → β} {s : Set α} (h : ContinuousOn f s) (h' : EqOn g f s) :
    ContinuousOn g s :=
  h.congr_mono h' (Subset.refl _)
#align continuous_on.congr ContinuousOn.congr

/- warning: continuous_on_congr -> continuousOn_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (Set.EqOn.{u1, u2} α β g f s) -> (Iff (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 g s) (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (Set.EqOn.{u2, u1} α β g f s) -> (Iff (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 g s) (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s))
Case conversion may be inaccurate. Consider using '#align continuous_on_congr continuousOn_congrₓ'. -/
theorem continuousOn_congr {f g : α → β} {s : Set α} (h' : EqOn g f s) :
    ContinuousOn g s ↔ ContinuousOn f s :=
  ⟨fun h => ContinuousOn.congr h h'.symm, fun h => h.congr h'⟩
#align continuous_on_congr continuousOn_congr

/- warning: continuous_at.continuous_within_at -> ContinuousAt.continuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align continuous_at.continuous_within_at ContinuousAt.continuousWithinAtₓ'. -/
theorem ContinuousAt.continuousWithinAt {f : α → β} {s : Set α} {x : α} (h : ContinuousAt f x) :
    ContinuousWithinAt f s x :=
  ContinuousWithinAt.mono ((continuousWithinAt_univ f x).2 h) (subset_univ _)
#align continuous_at.continuous_within_at ContinuousAt.continuousWithinAt

/- warning: continuous_within_at_iff_continuous_at -> continuousWithinAt_iff_continuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 x)) -> (Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_1 x)) -> (Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x))
Case conversion may be inaccurate. Consider using '#align continuous_within_at_iff_continuous_at continuousWithinAt_iff_continuousAtₓ'. -/
theorem continuousWithinAt_iff_continuousAt {f : α → β} {s : Set α} {x : α} (h : s ∈ 𝓝 x) :
    ContinuousWithinAt f s x ↔ ContinuousAt f x := by
  rw [← univ_inter s, continuousWithinAt_inter h, continuousWithinAt_univ]
#align continuous_within_at_iff_continuous_at continuousWithinAt_iff_continuousAt

/- warning: continuous_within_at.continuous_at -> ContinuousWithinAt.continuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 x)) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_1 x)) -> (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.continuous_at ContinuousWithinAt.continuousAtₓ'. -/
theorem ContinuousWithinAt.continuousAt {f : α → β} {s : Set α} {x : α}
    (h : ContinuousWithinAt f s x) (hs : s ∈ 𝓝 x) : ContinuousAt f x :=
  (continuousWithinAt_iff_continuousAt hs).mp h
#align continuous_within_at.continuous_at ContinuousWithinAt.continuousAt

/- warning: is_open.continuous_on_iff -> IsOpen.continuousOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (Iff (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) (forall {{a : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (IsOpen.{u2} α _inst_1 s) -> (Iff (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) (forall {{a : α}}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f a)))
Case conversion may be inaccurate. Consider using '#align is_open.continuous_on_iff IsOpen.continuousOn_iffₓ'. -/
theorem IsOpen.continuousOn_iff {f : α → β} {s : Set α} (hs : IsOpen s) :
    ContinuousOn f s ↔ ∀ ⦃a⦄, a ∈ s → ContinuousAt f a :=
  ball_congr fun _ => continuousWithinAt_iff_continuousAt ∘ hs.mem_nhds
#align is_open.continuous_on_iff IsOpen.continuousOn_iff

/- warning: continuous_on.continuous_at -> ContinuousOn.continuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 x)) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_1 x)) -> (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align continuous_on.continuous_at ContinuousOn.continuousAtₓ'. -/
theorem ContinuousOn.continuousAt {f : α → β} {s : Set α} {x : α} (h : ContinuousOn f s)
    (hx : s ∈ 𝓝 x) : ContinuousAt f x :=
  (h x (mem_of_mem_nhds hx)).ContinuousAt hx
#align continuous_on.continuous_at ContinuousOn.continuousAt

/- warning: continuous_at.continuous_on -> ContinuousAt.continuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x)) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x)) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s)
Case conversion may be inaccurate. Consider using '#align continuous_at.continuous_on ContinuousAt.continuousOnₓ'. -/
theorem ContinuousAt.continuousOn {f : α → β} {s : Set α} (hcont : ∀ x ∈ s, ContinuousAt f x) :
    ContinuousOn f s := fun x hx => (hcont x hx).ContinuousWithinAt
#align continuous_at.continuous_on ContinuousAt.continuousOn

/- warning: continuous_within_at.comp -> ContinuousWithinAt.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β} {x : α}, (ContinuousWithinAt.{u2, u3} β γ _inst_2 _inst_3 g t (f x)) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Set.MapsTo.{u1, u2} α β f s t) -> (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α} {t : Set.{u2} β} {x : α}, (ContinuousWithinAt.{u2, u1} β γ _inst_2 _inst_3 g t (f x)) -> (ContinuousWithinAt.{u3, u2} α β _inst_1 _inst_2 f s x) -> (Set.MapsTo.{u3, u2} α β f s t) -> (ContinuousWithinAt.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.comp ContinuousWithinAt.compₓ'. -/
theorem ContinuousWithinAt.comp {g : β → γ} {f : α → β} {s : Set α} {t : Set β} {x : α}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t) :
    ContinuousWithinAt (g ∘ f) s x :=
  hg.Tendsto.comp (hf.tendsto_nhdsWithin h)
#align continuous_within_at.comp ContinuousWithinAt.comp

/- warning: continuous_within_at.comp' -> ContinuousWithinAt.comp' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β} {x : α}, (ContinuousWithinAt.{u2, u3} β γ _inst_2 _inst_3 g t (f x)) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f t)) x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α} {t : Set.{u2} β} {x : α}, (ContinuousWithinAt.{u2, u1} β γ _inst_2 _inst_3 g t (f x)) -> (ContinuousWithinAt.{u3, u2} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) s (Set.preimage.{u3, u2} α β f t)) x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.comp' ContinuousWithinAt.comp'ₓ'. -/
theorem ContinuousWithinAt.comp' {g : β → γ} {f : α → β} {s : Set α} {t : Set β} {x : α}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)
#align continuous_within_at.comp' ContinuousWithinAt.comp'

/- warning: continuous_at.comp_continuous_within_at -> ContinuousAt.comp_continuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α} {x : α}, (ContinuousAt.{u2, u3} β γ _inst_2 _inst_3 g (f x)) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α} {x : α}, (ContinuousAt.{u2, u1} β γ _inst_2 _inst_3 g (f x)) -> (ContinuousWithinAt.{u3, u2} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) s x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_continuous_within_at ContinuousAt.comp_continuousWithinAtₓ'. -/
theorem ContinuousAt.comp_continuousWithinAt {g : β → γ} {f : α → β} {s : Set α} {x : α}
    (hg : ContinuousAt g (f x)) (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (g ∘ f) s x :=
  hg.ContinuousWithinAt.comp hf (mapsTo_univ _ _)
#align continuous_at.comp_continuous_within_at ContinuousAt.comp_continuousWithinAt

/- warning: continuous_on.comp -> ContinuousOn.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousOn.{u2, u3} β γ _inst_2 _inst_3 g t) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (ContinuousOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α} {t : Set.{u2} β}, (ContinuousOn.{u2, u1} β γ _inst_2 _inst_3 g t) -> (ContinuousOn.{u3, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u3, u2} α β f s t) -> (ContinuousOn.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.comp ContinuousOn.compₓ'. -/
theorem ContinuousOn.comp {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) s := fun x hx =>
  ContinuousWithinAt.comp (hg _ (h hx)) (hf x hx) h
#align continuous_on.comp ContinuousOn.comp

/- warning: continuous_on.mono -> ContinuousOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) t s) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f t)
Case conversion may be inaccurate. Consider using '#align continuous_on.mono ContinuousOn.monoₓ'. -/
theorem ContinuousOn.mono {f : α → β} {s t : Set α} (hf : ContinuousOn f s) (h : t ⊆ s) :
    ContinuousOn f t := fun x hx => (hf x (h hx)).mono_left (nhdsWithin_mono _ h)
#align continuous_on.mono ContinuousOn.mono

/- warning: antitone_continuous_on -> antitone_continuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, Antitone.{u1, 0} (Set.{u1} α) Prop (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, Antitone.{u2, 0} (Set.{u2} α) Prop (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align antitone_continuous_on antitone_continuousOnₓ'. -/
theorem antitone_continuousOn {f : α → β} : Antitone (ContinuousOn f) := fun s t hst hf =>
  hf.mono hst
#align antitone_continuous_on antitone_continuousOn

/- warning: continuous_on.comp' -> ContinuousOn.comp' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousOn.{u2, u3} β γ _inst_2 _inst_3 g t) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (ContinuousOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α} {t : Set.{u2} β}, (ContinuousOn.{u2, u1} β γ _inst_2 _inst_3 g t) -> (ContinuousOn.{u3, u2} α β _inst_1 _inst_2 f s) -> (ContinuousOn.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) s (Set.preimage.{u3, u2} α β f t)))
Case conversion may be inaccurate. Consider using '#align continuous_on.comp' ContinuousOn.comp'ₓ'. -/
theorem ContinuousOn.comp' {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)
#align continuous_on.comp' ContinuousOn.comp'

/- warning: continuous.continuous_on -> Continuous.continuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s)
Case conversion may be inaccurate. Consider using '#align continuous.continuous_on Continuous.continuousOnₓ'. -/
theorem Continuous.continuousOn {f : α → β} {s : Set α} (h : Continuous f) : ContinuousOn f s :=
  by
  rw [continuous_iff_continuousOn_univ] at h
  exact h.mono (subset_univ _)
#align continuous.continuous_on Continuous.continuousOn

/- warning: continuous.continuous_within_at -> Continuous.continuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align continuous.continuous_within_at Continuous.continuousWithinAtₓ'. -/
theorem Continuous.continuousWithinAt {f : α → β} {s : Set α} {x : α} (h : Continuous f) :
    ContinuousWithinAt f s x :=
  h.ContinuousAt.ContinuousWithinAt
#align continuous.continuous_within_at Continuous.continuousWithinAt

/- warning: continuous.comp_continuous_on -> Continuous.comp_continuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α}, (Continuous.{u2, u3} β γ _inst_2 _inst_3 g) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (ContinuousOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α}, (Continuous.{u2, u1} β γ _inst_2 _inst_3 g) -> (ContinuousOn.{u3, u2} α β _inst_1 _inst_2 f s) -> (ContinuousOn.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) s)
Case conversion may be inaccurate. Consider using '#align continuous.comp_continuous_on Continuous.comp_continuousOnₓ'. -/
theorem Continuous.comp_continuousOn {g : β → γ} {f : α → β} {s : Set α} (hg : Continuous g)
    (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) s :=
  hg.ContinuousOn.comp hf (mapsTo_univ _ _)
#align continuous.comp_continuous_on Continuous.comp_continuousOn

/- warning: continuous_on.comp_continuous -> ContinuousOn.comp_continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u2} β}, (ContinuousOn.{u2, u3} β γ _inst_2 _inst_3 g s) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (x : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) s) -> (Continuous.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} β}, (ContinuousOn.{u3, u2} β γ _inst_2 _inst_3 g s) -> (Continuous.{u1, u3} α β _inst_1 _inst_2 f) -> (forall (x : α), Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) (f x) s) -> (Continuous.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f))
Case conversion may be inaccurate. Consider using '#align continuous_on.comp_continuous ContinuousOn.comp_continuousₓ'. -/
theorem ContinuousOn.comp_continuous {g : β → γ} {f : α → β} {s : Set β} (hg : ContinuousOn g s)
    (hf : Continuous f) (hs : ∀ x, f x ∈ s) : Continuous (g ∘ f) :=
  by
  rw [continuous_iff_continuousOn_univ] at *
  exact hg.comp hf fun x _ => hs x
#align continuous_on.comp_continuous ContinuousOn.comp_continuous

/- warning: continuous_within_at.preimage_mem_nhds_within -> ContinuousWithinAt.preimage_mem_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 (f x))) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Set.preimage.{u1, u2} α β f t) (nhdsWithin.{u1} α _inst_1 x s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α} {t : Set.{u1} β}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) t (nhds.{u1} β _inst_2 (f x))) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (Set.preimage.{u2, u1} α β f t) (nhdsWithin.{u2} α _inst_1 x s))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.preimage_mem_nhds_within ContinuousWithinAt.preimage_mem_nhdsWithinₓ'. -/
theorem ContinuousWithinAt.preimage_mem_nhdsWithin {f : α → β} {x : α} {s : Set α} {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝[s] x :=
  h ht
#align continuous_within_at.preimage_mem_nhds_within ContinuousWithinAt.preimage_mem_nhdsWithin

#print Set.LeftInvOn.map_nhdsWithin_eq /-
theorem Set.LeftInvOn.map_nhdsWithin_eq {f : α → β} {g : β → α} {x : β} {s : Set β}
    (h : LeftInvOn f g s) (hx : f (g x) = x) (hf : ContinuousWithinAt f (g '' s) (g x))
    (hg : ContinuousWithinAt g s x) : map g (𝓝[s] x) = 𝓝[g '' s] g x :=
  by
  apply le_antisymm
  · exact hg.tendsto_nhds_within (maps_to_image _ _)
  · have A : g ∘ f =ᶠ[𝓝[g '' s] g x] id :=
      h.right_inv_on_image.eq_on.eventually_eq_of_mem self_mem_nhdsWithin
    refine' le_map_of_right_inverse A _
    simpa only [hx] using hf.tendsto_nhds_within (h.maps_to (surj_on_image _ _))
#align set.left_inv_on.map_nhds_within_eq Set.LeftInvOn.map_nhdsWithin_eq
-/

#print Function.LeftInverse.map_nhds_eq /-
theorem Function.LeftInverse.map_nhds_eq {f : α → β} {g : β → α} {x : β}
    (h : Function.LeftInverse f g) (hf : ContinuousWithinAt f (range g) (g x))
    (hg : ContinuousAt g x) : map g (𝓝 x) = 𝓝[range g] g x := by
  simpa only [nhdsWithin_univ, image_univ] using
    (h.left_inv_on univ).map_nhdsWithin_eq (h x) (by rwa [image_univ]) hg.continuous_within_at
#align function.left_inverse.map_nhds_eq Function.LeftInverse.map_nhds_eq
-/

/- warning: continuous_within_at.preimage_mem_nhds_within' -> ContinuousWithinAt.preimage_mem_nhds_within' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhdsWithin.{u2} β _inst_2 (f x) (Set.image.{u1, u2} α β f s))) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Set.preimage.{u1, u2} α β f t) (nhdsWithin.{u1} α _inst_1 x s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α} {t : Set.{u1} β}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) t (nhdsWithin.{u1} β _inst_2 (f x) (Set.image.{u2, u1} α β f s))) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (Set.preimage.{u2, u1} α β f t) (nhdsWithin.{u2} α _inst_1 x s))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.preimage_mem_nhds_within' ContinuousWithinAt.preimage_mem_nhds_within'ₓ'. -/
theorem ContinuousWithinAt.preimage_mem_nhds_within' {f : α → β} {x : α} {s : Set α} {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t ∈ 𝓝[f '' s] f x) : f ⁻¹' t ∈ 𝓝[s] x :=
  h.tendsto_nhdsWithin (mapsTo_image _ _) ht
#align continuous_within_at.preimage_mem_nhds_within' ContinuousWithinAt.preimage_mem_nhds_within'

/- warning: filter.eventually_eq.congr_continuous_within_at -> Filter.EventuallyEq.congr_continuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α} {x : α}, (Filter.EventuallyEq.{u1, u2} α β (nhdsWithin.{u1} α _inst_1 x s) f g) -> (Eq.{succ u2} β (f x) (g x)) -> (Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 g s x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α} {x : α}, (Filter.EventuallyEq.{u2, u1} α β (nhdsWithin.{u2} α _inst_1 x s) f g) -> (Eq.{succ u1} β (f x) (g x)) -> (Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 g s x))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.congr_continuous_within_at Filter.EventuallyEq.congr_continuousWithinAtₓ'. -/
theorem Filter.EventuallyEq.congr_continuousWithinAt {f g : α → β} {s : Set α} {x : α}
    (h : f =ᶠ[𝓝[s] x] g) (hx : f x = g x) : ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x :=
  by rw [ContinuousWithinAt, hx, tendsto_congr' h, ContinuousWithinAt]
#align filter.eventually_eq.congr_continuous_within_at Filter.EventuallyEq.congr_continuousWithinAt

/- warning: continuous_within_at.congr_of_eventually_eq -> ContinuousWithinAt.congr_of_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {f₁ : α -> β} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Filter.EventuallyEq.{u1, u2} α β (nhdsWithin.{u1} α _inst_1 x s) f₁ f) -> (Eq.{succ u2} β (f₁ x) (f x)) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f₁ s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {f₁ : α -> β} {s : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Filter.EventuallyEq.{u2, u1} α β (nhdsWithin.{u2} α _inst_1 x s) f₁ f) -> (Eq.{succ u1} β (f₁ x) (f x)) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f₁ s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.congr_of_eventually_eq ContinuousWithinAt.congr_of_eventuallyEqₓ'. -/
theorem ContinuousWithinAt.congr_of_eventuallyEq {f f₁ : α → β} {s : Set α} {x : α}
    (h : ContinuousWithinAt f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContinuousWithinAt f₁ s x :=
  (h₁.congr_continuousWithinAt hx).2 h
#align continuous_within_at.congr_of_eventually_eq ContinuousWithinAt.congr_of_eventuallyEq

/- warning: continuous_within_at.congr -> ContinuousWithinAt.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {f₁ : α -> β} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Eq.{succ u2} β (f₁ y) (f y))) -> (Eq.{succ u2} β (f₁ x) (f x)) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f₁ s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {f₁ : α -> β} {s : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Eq.{succ u1} β (f₁ y) (f y))) -> (Eq.{succ u1} β (f₁ x) (f x)) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f₁ s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.congr ContinuousWithinAt.congrₓ'. -/
theorem ContinuousWithinAt.congr {f f₁ : α → β} {s : Set α} {x : α} (h : ContinuousWithinAt f s x)
    (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) : ContinuousWithinAt f₁ s x :=
  h.congr_of_eventuallyEq (mem_of_superset self_mem_nhdsWithin h₁) hx
#align continuous_within_at.congr ContinuousWithinAt.congr

/- warning: continuous_within_at.congr_mono -> ContinuousWithinAt.congr_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α} {s₁ : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (Set.EqOn.{u1, u2} α β g f s₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s) -> (Eq.{succ u2} β (g x) (f x)) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 g s₁ x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α} {s₁ : Set.{u2} α} {x : α}, (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x) -> (Set.EqOn.{u2, u1} α β g f s₁) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s₁ s) -> (Eq.{succ u1} β (g x) (f x)) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 g s₁ x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.congr_mono ContinuousWithinAt.congr_monoₓ'. -/
theorem ContinuousWithinAt.congr_mono {f g : α → β} {s s₁ : Set α} {x : α}
    (h : ContinuousWithinAt f s x) (h' : EqOn g f s₁) (h₁ : s₁ ⊆ s) (hx : g x = f x) :
    ContinuousWithinAt g s₁ x :=
  (h.mono h₁).congr h' hx
#align continuous_within_at.congr_mono ContinuousWithinAt.congr_mono

/- warning: continuous_on_const -> continuousOn_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {c : β}, ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (fun (x : α) => c) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {c : β}, ContinuousOn.{u2, u1} α β _inst_1 _inst_2 (fun (x : α) => c) s
Case conversion may be inaccurate. Consider using '#align continuous_on_const continuousOn_constₓ'. -/
theorem continuousOn_const {s : Set α} {c : β} : ContinuousOn (fun x => c) s :=
  continuous_const.ContinuousOn
#align continuous_on_const continuousOn_const

/- warning: continuous_within_at_const -> continuousWithinAt_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {b : β} {s : Set.{u1} α} {x : α}, ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 (fun (_x : α) => b) s x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {b : β} {s : Set.{u2} α} {x : α}, ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 (fun (_x : α) => b) s x
Case conversion may be inaccurate. Consider using '#align continuous_within_at_const continuousWithinAt_constₓ'. -/
theorem continuousWithinAt_const {b : β} {s : Set α} {x : α} :
    ContinuousWithinAt (fun _ : α => b) s x :=
  continuous_const.ContinuousWithinAt
#align continuous_within_at_const continuousWithinAt_const

#print continuousOn_id /-
theorem continuousOn_id {s : Set α} : ContinuousOn id s :=
  continuous_id.ContinuousOn
#align continuous_on_id continuousOn_id
-/

#print continuousWithinAt_id /-
theorem continuousWithinAt_id {s : Set α} {x : α} : ContinuousWithinAt id s x :=
  continuous_id.ContinuousWithinAt
#align continuous_within_at_id continuousWithinAt_id
-/

/- warning: continuous_on_open_iff -> continuousOn_open_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (Iff (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) (forall (t : Set.{u2} β), (IsOpen.{u2} β _inst_2 t) -> (IsOpen.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f t)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (IsOpen.{u2} α _inst_1 s) -> (Iff (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) (forall (t : Set.{u1} β), (IsOpen.{u1} β _inst_2 t) -> (IsOpen.{u2} α _inst_1 (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.preimage.{u2, u1} α β f t)))))
Case conversion may be inaccurate. Consider using '#align continuous_on_open_iff continuousOn_open_iffₓ'. -/
theorem continuousOn_open_iff {f : α → β} {s : Set α} (hs : IsOpen s) :
    ContinuousOn f s ↔ ∀ t, IsOpen t → IsOpen (s ∩ f ⁻¹' t) :=
  by
  rw [continuousOn_iff']
  constructor
  · intro h t ht
    rcases h t ht with ⟨u, u_open, hu⟩
    rw [inter_comm, hu]
    apply IsOpen.inter u_open hs
  · intro h t ht
    refine' ⟨s ∩ f ⁻¹' t, h t ht, _⟩
    rw [@inter_comm _ s (f ⁻¹' t), inter_assoc, inter_self]
#align continuous_on_open_iff continuousOn_open_iff

/- warning: continuous_on.preimage_open_of_open -> ContinuousOn.preimage_open_of_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u2} β _inst_2 t) -> (IsOpen.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u1} β}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (IsOpen.{u2} α _inst_1 s) -> (IsOpen.{u1} β _inst_2 t) -> (IsOpen.{u2} α _inst_1 (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.preimage.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align continuous_on.preimage_open_of_open ContinuousOn.preimage_open_of_openₓ'. -/
theorem ContinuousOn.preimage_open_of_open {f : α → β} {s : Set α} {t : Set β}
    (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ f ⁻¹' t) :=
  (continuousOn_open_iff hs).1 hf t ht
#align continuous_on.preimage_open_of_open ContinuousOn.preimage_open_of_open

/- warning: continuous_on.is_open_preimage -> ContinuousOn.isOpen_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (IsOpen.{u1} α _inst_1 s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.preimage.{u1, u2} α β f t) s) -> (IsOpen.{u2} β _inst_2 t) -> (IsOpen.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u1} β}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (IsOpen.{u2} α _inst_1 s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.preimage.{u2, u1} α β f t) s) -> (IsOpen.{u1} β _inst_2 t) -> (IsOpen.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align continuous_on.is_open_preimage ContinuousOn.isOpen_preimageₓ'. -/
theorem ContinuousOn.isOpen_preimage {f : α → β} {s : Set α} {t : Set β} (h : ContinuousOn f s)
    (hs : IsOpen s) (hp : f ⁻¹' t ⊆ s) (ht : IsOpen t) : IsOpen (f ⁻¹' t) :=
  by
  convert (continuousOn_open_iff hs).mp h t ht
  rw [inter_comm, inter_eq_self_of_subset_left hp]
#align continuous_on.is_open_preimage ContinuousOn.isOpen_preimage

/- warning: continuous_on.preimage_closed_of_closed -> ContinuousOn.preimage_closed_of_closed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (IsClosed.{u1} α _inst_1 s) -> (IsClosed.{u2} β _inst_2 t) -> (IsClosed.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u1} β}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (IsClosed.{u2} α _inst_1 s) -> (IsClosed.{u1} β _inst_2 t) -> (IsClosed.{u2} α _inst_1 (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.preimage.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align continuous_on.preimage_closed_of_closed ContinuousOn.preimage_closed_of_closedₓ'. -/
theorem ContinuousOn.preimage_closed_of_closed {f : α → β} {s : Set α} {t : Set β}
    (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∩ f ⁻¹' t) :=
  by
  rcases continuousOn_iff_isClosed.1 hf t ht with ⟨u, hu⟩
  rw [inter_comm, hu.2]
  apply IsClosed.inter hu.1 hs
#align continuous_on.preimage_closed_of_closed ContinuousOn.preimage_closed_of_closed

/- warning: continuous_on.preimage_interior_subset_interior_preimage -> ContinuousOn.preimage_interior_subset_interior_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (IsOpen.{u1} α _inst_1 s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f (interior.{u2} β _inst_2 t))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (interior.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f t))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u1} β}, (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (IsOpen.{u2} α _inst_1 s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.preimage.{u2, u1} α β f (interior.{u1} β _inst_2 t))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (interior.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f t))))
Case conversion may be inaccurate. Consider using '#align continuous_on.preimage_interior_subset_interior_preimage ContinuousOn.preimage_interior_subset_interior_preimageₓ'. -/
theorem ContinuousOn.preimage_interior_subset_interior_preimage {f : α → β} {s : Set α} {t : Set β}
    (hf : ContinuousOn f s) (hs : IsOpen s) : s ∩ f ⁻¹' interior t ⊆ s ∩ interior (f ⁻¹' t) :=
  calc
    s ∩ f ⁻¹' interior t ⊆ interior (s ∩ f ⁻¹' t) :=
      interior_maximal (inter_subset_inter (Subset.refl _) (preimage_mono interior_subset))
        (hf.preimage_open_of_open hs isOpen_interior)
    _ = s ∩ interior (f ⁻¹' t) := by rw [interior_inter, hs.interior_eq]
    
#align continuous_on.preimage_interior_subset_interior_preimage ContinuousOn.preimage_interior_subset_interior_preimage

/- warning: continuous_on_of_locally_continuous_on -> continuousOn_of_locally_continuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (IsOpen.{u1} α _inst_1 t) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (IsOpen.{u2} α _inst_1 t) (And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)))))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s)
Case conversion may be inaccurate. Consider using '#align continuous_on_of_locally_continuous_on continuousOn_of_locally_continuousOnₓ'. -/
theorem continuousOn_of_locally_continuousOn {f : α → β} {s : Set α}
    (h : ∀ x ∈ s, ∃ t, IsOpen t ∧ x ∈ t ∧ ContinuousOn f (s ∩ t)) : ContinuousOn f s :=
  by
  intro x xs
  rcases h x xs with ⟨t, open_t, xt, ct⟩
  have := ct x ⟨xs, xt⟩
  rwa [ContinuousWithinAt, ← nhdsWithin_restrict _ xt open_t] at this
#align continuous_on_of_locally_continuous_on continuousOn_of_locally_continuousOn

theorem continuousOn_open_of_generateFrom {β : Type _} {s : Set α} {T : Set (Set β)} {f : α → β}
    (hs : IsOpen s) (h : ∀ t ∈ T, IsOpen (s ∩ f ⁻¹' t)) :
    @ContinuousOn α β _ (TopologicalSpace.generateFrom T) f s :=
  by
  rw [continuousOn_open_iff]
  intro t ht
  induction' ht with u hu u v Tu Tv hu hv U hU hU'
  · exact h u hu
  · simp only [preimage_univ, inter_univ]
    exact hs
  · have : s ∩ f ⁻¹' (u ∩ v) = s ∩ f ⁻¹' u ∩ (s ∩ f ⁻¹' v) := by
      rw [preimage_inter, inter_assoc, inter_left_comm _ s, ← inter_assoc s s, inter_self]
    rw [this]
    exact hu.inter hv
  · rw [preimage_sUnion, inter_Union₂]
    exact isOpen_bunionᵢ hU'
  · exact hs
#align continuous_on_open_of_generate_from continuousOn_open_of_generateFromₓ

/- warning: continuous_within_at.prod -> ContinuousWithinAt.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : α -> γ} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 g s x) -> (ContinuousWithinAt.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u3} β γ (f x) (g x)) s x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β} {g : α -> γ} {s : Set.{u3} α} {x : α}, (ContinuousWithinAt.{u3, u2} α β _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u3, u1} α γ _inst_1 _inst_3 g s x) -> (ContinuousWithinAt.{u3, max u1 u2} α (Prod.{u2, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u2, u1} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u1} β γ (f x) (g x)) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.prod ContinuousWithinAt.prodₓ'. -/
theorem ContinuousWithinAt.prod {f : α → β} {g : α → γ} {s : Set α} {x : α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => (f x, g x)) s x :=
  hf.prod_mk_nhds hg
#align continuous_within_at.prod ContinuousWithinAt.prod

/- warning: continuous_on.prod -> ContinuousOn.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : α -> γ} {s : Set.{u1} α}, (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (ContinuousOn.{u1, u3} α γ _inst_1 _inst_3 g s) -> (ContinuousOn.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u3} β γ (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β} {g : α -> γ} {s : Set.{u3} α}, (ContinuousOn.{u3, u2} α β _inst_1 _inst_2 f s) -> (ContinuousOn.{u3, u1} α γ _inst_1 _inst_3 g s) -> (ContinuousOn.{u3, max u1 u2} α (Prod.{u2, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u2, u1} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u1} β γ (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.prod ContinuousOn.prodₓ'. -/
theorem ContinuousOn.prod {f : α → β} {g : α → γ} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (f x, g x)) s := fun x hx =>
  ContinuousWithinAt.prod (hf x hx) (hg x hx)
#align continuous_on.prod ContinuousOn.prod

/- warning: inducing.continuous_within_at_iff -> Inducing.continuousWithinAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : β -> γ}, (Inducing.{u2, u3} β γ _inst_2 _inst_3 g) -> (forall {s : Set.{u1} α} {x : α}, Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x) (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : α -> β} {g : β -> γ}, (Inducing.{u3, u2} β γ _inst_2 _inst_3 g) -> (forall {s : Set.{u1} α} {x : α}, Iff (ContinuousWithinAt.{u1, u3} α β _inst_1 _inst_2 f s x) (ContinuousWithinAt.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) s x))
Case conversion may be inaccurate. Consider using '#align inducing.continuous_within_at_iff Inducing.continuousWithinAt_iffₓ'. -/
theorem Inducing.continuousWithinAt_iff {f : α → β} {g : β → γ} (hg : Inducing g) {s : Set α}
    {x : α} : ContinuousWithinAt f s x ↔ ContinuousWithinAt (g ∘ f) s x := by
  simp_rw [ContinuousWithinAt, Inducing.tendsto_nhds_iff hg]
#align inducing.continuous_within_at_iff Inducing.continuousWithinAt_iff

/- warning: inducing.continuous_on_iff -> Inducing.continuousOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : β -> γ}, (Inducing.{u2, u3} β γ _inst_2 _inst_3 g) -> (forall {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) (ContinuousOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : α -> β} {g : β -> γ}, (Inducing.{u3, u2} β γ _inst_2 _inst_3 g) -> (forall {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u3} α β _inst_1 _inst_2 f s) (ContinuousOn.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) s))
Case conversion may be inaccurate. Consider using '#align inducing.continuous_on_iff Inducing.continuousOn_iffₓ'. -/
theorem Inducing.continuousOn_iff {f : α → β} {g : β → γ} (hg : Inducing g) {s : Set α} :
    ContinuousOn f s ↔ ContinuousOn (g ∘ f) s := by
  simp_rw [ContinuousOn, hg.continuous_within_at_iff]
#align inducing.continuous_on_iff Inducing.continuousOn_iff

/- warning: embedding.continuous_on_iff -> Embedding.continuousOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : β -> γ}, (Embedding.{u2, u3} β γ _inst_2 _inst_3 g) -> (forall {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) (ContinuousOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : α -> β} {g : β -> γ}, (Embedding.{u3, u2} β γ _inst_2 _inst_3 g) -> (forall {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u3} α β _inst_1 _inst_2 f s) (ContinuousOn.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) s))
Case conversion may be inaccurate. Consider using '#align embedding.continuous_on_iff Embedding.continuousOn_iffₓ'. -/
theorem Embedding.continuousOn_iff {f : α → β} {g : β → γ} (hg : Embedding g) {s : Set α} :
    ContinuousOn f s ↔ ContinuousOn (g ∘ f) s :=
  Inducing.continuousOn_iff hg.1
#align embedding.continuous_on_iff Embedding.continuousOn_iff

/- warning: embedding.map_nhds_within_eq -> Embedding.map_nhdsWithin_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Embedding.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u1} α) (x : α), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 x s)) (nhdsWithin.{u2} β _inst_2 (f x) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (Embedding.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u2} α) (x : α), Eq.{succ u1} (Filter.{u1} β) (Filter.map.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 x s)) (nhdsWithin.{u1} β _inst_2 (f x) (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align embedding.map_nhds_within_eq Embedding.map_nhdsWithin_eqₓ'. -/
theorem Embedding.map_nhdsWithin_eq {f : α → β} (hf : Embedding f) (s : Set α) (x : α) :
    map f (𝓝[s] x) = 𝓝[f '' s] f x := by
  rw [nhdsWithin, map_inf hf.inj, hf.map_nhds_eq, map_principal, ← nhdsWithin_inter',
    inter_eq_self_of_subset_right (image_subset_range _ _)]
#align embedding.map_nhds_within_eq Embedding.map_nhdsWithin_eq

/- warning: open_embedding.map_nhds_within_preimage_eq -> OpenEmbedding.map_nhdsWithin_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (OpenEmbedding.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u2} β) (x : α), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 x (Set.preimage.{u1, u2} α β f s))) (nhdsWithin.{u2} β _inst_2 (f x) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (OpenEmbedding.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u1} β) (x : α), Eq.{succ u1} (Filter.{u1} β) (Filter.map.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 x (Set.preimage.{u2, u1} α β f s))) (nhdsWithin.{u1} β _inst_2 (f x) s))
Case conversion may be inaccurate. Consider using '#align open_embedding.map_nhds_within_preimage_eq OpenEmbedding.map_nhdsWithin_preimage_eqₓ'. -/
theorem OpenEmbedding.map_nhdsWithin_preimage_eq {f : α → β} (hf : OpenEmbedding f) (s : Set β)
    (x : α) : map f (𝓝[f ⁻¹' s] x) = 𝓝[s] f x :=
  by
  rw [hf.to_embedding.map_nhds_within_eq, image_preimage_eq_inter_range]
  apply nhdsWithin_eq_nhdsWithin (mem_range_self _) hf.open_range
  rw [inter_assoc, inter_self]
#align open_embedding.map_nhds_within_preimage_eq OpenEmbedding.map_nhdsWithin_preimage_eq

/- warning: continuous_within_at_of_not_mem_closure -> continuousWithinAt_of_not_mem_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {x : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α _inst_1 s))) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {x : α}, (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (closure.{u2} α _inst_1 s))) -> (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at_of_not_mem_closure continuousWithinAt_of_not_mem_closureₓ'. -/
theorem continuousWithinAt_of_not_mem_closure {f : α → β} {s : Set α} {x : α} :
    x ∉ closure s → ContinuousWithinAt f s x :=
  by
  intro hx
  rw [mem_closure_iff_nhdsWithin_neBot, ne_bot_iff, Classical.not_not] at hx
  rw [ContinuousWithinAt, hx]
  exact tendsto_bot
#align continuous_within_at_of_not_mem_closure continuousWithinAt_of_not_mem_closure

/- warning: continuous_on.piecewise' -> ContinuousOn.piecewise' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t)], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t))) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (nhds.{u2} β _inst_2 (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_5 j) a)))) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t))) -> (Filter.Tendsto.{u1, u2} α β g (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))) (nhds.{u2} β _inst_2 (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_5 j) a)))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_5 j)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {t : Set.{u2} α} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a t)], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_1 t))) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) (nhds.{u1} β _inst_2 (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_5 j) a)))) -> (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_1 t))) -> (Filter.Tendsto.{u2, u1} α β g (nhdsWithin.{u2} α _inst_1 a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) t))) (nhds.{u1} β _inst_2 (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_5 j) a)))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) t))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_5 j)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.piecewise' ContinuousOn.piecewise'ₓ'. -/
theorem ContinuousOn.piecewise' {s t : Set α} {f g : α → β} [∀ a, Decidable (a ∈ t)]
    (hpf : ∀ a ∈ s ∩ frontier t, Tendsto f (𝓝[s ∩ t] a) (𝓝 (piecewise t f g a)))
    (hpg : ∀ a ∈ s ∩ frontier t, Tendsto g (𝓝[s ∩ tᶜ] a) (𝓝 (piecewise t f g a)))
    (hf : ContinuousOn f <| s ∩ t) (hg : ContinuousOn g <| s ∩ tᶜ) :
    ContinuousOn (piecewise t f g) s := by
  intro x hx
  by_cases hx' : x ∈ frontier t
  · exact (hpf x ⟨hx, hx'⟩).piecewise_nhdsWithin (hpg x ⟨hx, hx'⟩)
  · rw [← inter_univ s, ← union_compl_self t, inter_union_distrib_left] at hx⊢
    cases hx
    · apply ContinuousWithinAt.union
      ·
        exact
          (hf x hx).congr (fun y hy => piecewise_eq_of_mem _ _ _ hy.2)
            (piecewise_eq_of_mem _ _ _ hx.2)
      · have : x ∉ closure (tᶜ) := fun h => hx' ⟨subset_closure hx.2, by rwa [closure_compl] at h⟩
        exact
          continuousWithinAt_of_not_mem_closure fun h =>
            this (closure_inter_subset_inter_closure _ _ h).2
    · apply ContinuousWithinAt.union
      · have : x ∉ closure t := fun h =>
          hx' ⟨h, fun h' : x ∈ interior t => hx.2 (interior_subset h')⟩
        exact
          continuousWithinAt_of_not_mem_closure fun h =>
            this (closure_inter_subset_inter_closure _ _ h).2
      ·
        exact
          (hg x hx).congr (fun y hy => piecewise_eq_of_not_mem _ _ _ hy.2)
            (piecewise_eq_of_not_mem _ _ _ hx.2)
#align continuous_on.piecewise' ContinuousOn.piecewise'

/- warning: continuous_on.if' -> ContinuousOn.if' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {p : α -> Prop} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (p a)], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 (setOf.{u1} α (fun (a : α) => p a))))) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (a : α) => p a)))) (nhds.{u2} β _inst_2 (ite.{succ u2} β (p a) (_inst_5 a) (f a) (g a))))) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 (setOf.{u1} α (fun (a : α) => p a))))) -> (Filter.Tendsto.{u1, u2} α β g (nhdsWithin.{u1} α _inst_1 a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (a : α) => Not (p a))))) (nhds.{u2} β _inst_2 (ite.{succ u2} β (p a) (_inst_5 a) (f a) (g a))))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (a : α) => p a)))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (a : α) => Not (p a))))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u2} β (p a) (_inst_5 a) (f a) (g a)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {p : α -> Prop} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (p a)], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_1 (setOf.{u2} α (fun (a : α) => p a))))) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (setOf.{u2} α (fun (a : α) => p a)))) (nhds.{u1} β _inst_2 (ite.{succ u1} β (p a) (_inst_5 a) (f a) (g a))))) -> (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_1 (setOf.{u2} α (fun (a : α) => p a))))) -> (Filter.Tendsto.{u2, u1} α β g (nhdsWithin.{u2} α _inst_1 a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (setOf.{u2} α (fun (a : α) => Not (p a))))) (nhds.{u1} β _inst_2 (ite.{succ u1} β (p a) (_inst_5 a) (f a) (g a))))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (setOf.{u2} α (fun (a : α) => p a)))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (setOf.{u2} α (fun (a : α) => Not (p a))))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u1} β (p a) (_inst_5 a) (f a) (g a)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.if' ContinuousOn.if'ₓ'. -/
theorem ContinuousOn.if' {s : Set α} {p : α → Prop} {f g : α → β} [∀ a, Decidable (p a)]
    (hpf :
      ∀ a ∈ s ∩ frontier { a | p a },
        Tendsto f (𝓝[s ∩ { a | p a }] a) (𝓝 <| if p a then f a else g a))
    (hpg :
      ∀ a ∈ s ∩ frontier { a | p a },
        Tendsto g (𝓝[s ∩ { a | ¬p a }] a) (𝓝 <| if p a then f a else g a))
    (hf : ContinuousOn f <| s ∩ { a | p a }) (hg : ContinuousOn g <| s ∩ { a | ¬p a }) :
    ContinuousOn (fun a => if p a then f a else g a) s :=
  hf.piecewise' hpf hpg hg
#align continuous_on.if' ContinuousOn.if'

/- warning: continuous_on.if -> ContinuousOn.if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} α] [_inst_6 : TopologicalSpace.{u2} β] {p : α -> Prop} [_inst_7 : forall (a : α), Decidable (p a)] {s : Set.{u1} α} {f : α -> β} {g : α -> β}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_5 (setOf.{u1} α (fun (a : α) => p a))))) -> (Eq.{succ u2} β (f a) (g a))) -> (ContinuousOn.{u1, u2} α β _inst_5 _inst_6 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (closure.{u1} α _inst_5 (setOf.{u1} α (fun (a : α) => p a))))) -> (ContinuousOn.{u1, u2} α β _inst_5 _inst_6 g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (closure.{u1} α _inst_5 (setOf.{u1} α (fun (a : α) => Not (p a)))))) -> (ContinuousOn.{u1, u2} α β _inst_5 _inst_6 (fun (a : α) => ite.{succ u2} β (p a) (_inst_7 a) (f a) (g a)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_5 : TopologicalSpace.{u2} α] [_inst_6 : TopologicalSpace.{u1} β] {p : α -> Prop} [_inst_7 : forall (a : α), Decidable (p a)] {s : Set.{u2} α} {f : α -> β} {g : α -> β}, (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_5 (setOf.{u2} α (fun (a : α) => p a))))) -> (Eq.{succ u1} β (f a) (g a))) -> (ContinuousOn.{u2, u1} α β _inst_5 _inst_6 f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (closure.{u2} α _inst_5 (setOf.{u2} α (fun (a : α) => p a))))) -> (ContinuousOn.{u2, u1} α β _inst_5 _inst_6 g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (closure.{u2} α _inst_5 (setOf.{u2} α (fun (a : α) => Not (p a)))))) -> (ContinuousOn.{u2, u1} α β _inst_5 _inst_6 (fun (a : α) => ite.{succ u1} β (p a) (_inst_7 a) (f a) (g a)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.if ContinuousOn.ifₓ'. -/
theorem ContinuousOn.if {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {p : α → Prop}
    [∀ a, Decidable (p a)] {s : Set α} {f g : α → β}
    (hp : ∀ a ∈ s ∩ frontier { a | p a }, f a = g a)
    (hf : ContinuousOn f <| s ∩ closure { a | p a })
    (hg : ContinuousOn g <| s ∩ closure { a | ¬p a }) :
    ContinuousOn (fun a => if p a then f a else g a) s :=
  by
  apply ContinuousOn.if'
  · rintro a ha
    simp only [← hp a ha, if_t_t]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inter_right s subset_closure)
    exact hf a ⟨ha.1, ha.2.1⟩
  · rintro a ha
    simp only [hp a ha, if_t_t]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inter_right s subset_closure)
    rcases ha with ⟨has, ⟨_, ha⟩⟩
    rw [← mem_compl_iff, ← closure_compl] at ha
    apply hg a ⟨has, ha⟩
  · exact hf.mono (inter_subset_inter_right s subset_closure)
  · exact hg.mono (inter_subset_inter_right s subset_closure)
#align continuous_on.if ContinuousOn.if

/- warning: continuous_on.piecewise -> ContinuousOn.piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t)], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t))) -> (Eq.{succ u2} β (f a) (g a))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (closure.{u1} α _inst_1 t))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_5 j)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {t : Set.{u2} α} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a t)], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_1 t))) -> (Eq.{succ u1} β (f a) (g a))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (closure.{u2} α _inst_1 t))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (closure.{u2} α _inst_1 (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) t)))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) t f g (fun (j : α) => _inst_5 j)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.piecewise ContinuousOn.piecewiseₓ'. -/
theorem ContinuousOn.piecewise {s t : Set α} {f g : α → β} [∀ a, Decidable (a ∈ t)]
    (ht : ∀ a ∈ s ∩ frontier t, f a = g a) (hf : ContinuousOn f <| s ∩ closure t)
    (hg : ContinuousOn g <| s ∩ closure (tᶜ)) : ContinuousOn (piecewise t f g) s :=
  hf.if ht hg
#align continuous_on.piecewise ContinuousOn.piecewise

/- warning: continuous_if' -> continuous_if' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : α -> Prop} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (p a)], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (frontier.{u1} α _inst_1 (setOf.{u1} α (fun (x : α) => p x)))) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a (setOf.{u1} α (fun (x : α) => p x))) (nhds.{u2} β _inst_2 (ite.{succ u2} β (p a) (_inst_5 a) (f a) (g a))))) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (frontier.{u1} α _inst_1 (setOf.{u1} α (fun (x : α) => p x)))) -> (Filter.Tendsto.{u1, u2} α β g (nhdsWithin.{u1} α _inst_1 a (setOf.{u1} α (fun (x : α) => Not (p x)))) (nhds.{u2} β _inst_2 (ite.{succ u2} β (p a) (_inst_5 a) (f a) (g a))))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (setOf.{u1} α (fun (x : α) => p x))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 g (setOf.{u1} α (fun (x : α) => Not (p x)))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u2} β (p a) (_inst_5 a) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {p : α -> Prop} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (p a)], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (frontier.{u2} α _inst_1 (setOf.{u2} α (fun (x : α) => p x)))) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a (setOf.{u2} α (fun (x : α) => p x))) (nhds.{u1} β _inst_2 (ite.{succ u1} β (p a) (_inst_5 a) (f a) (g a))))) -> (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (frontier.{u2} α _inst_1 (setOf.{u2} α (fun (x : α) => p x)))) -> (Filter.Tendsto.{u2, u1} α β g (nhdsWithin.{u2} α _inst_1 a (setOf.{u2} α (fun (x : α) => Not (p x)))) (nhds.{u1} β _inst_2 (ite.{succ u1} β (p a) (_inst_5 a) (f a) (g a))))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (setOf.{u2} α (fun (x : α) => p x))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 g (setOf.{u2} α (fun (x : α) => Not (p x)))) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u1} β (p a) (_inst_5 a) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align continuous_if' continuous_if'ₓ'. -/
theorem continuous_if' {p : α → Prop} {f g : α → β} [∀ a, Decidable (p a)]
    (hpf : ∀ a ∈ frontier { x | p x }, Tendsto f (𝓝[{ x | p x }] a) (𝓝 <| ite (p a) (f a) (g a)))
    (hpg : ∀ a ∈ frontier { x | p x }, Tendsto g (𝓝[{ x | ¬p x }] a) (𝓝 <| ite (p a) (f a) (g a)))
    (hf : ContinuousOn f { x | p x }) (hg : ContinuousOn g { x | ¬p x }) :
    Continuous fun a => ite (p a) (f a) (g a) :=
  by
  rw [continuous_iff_continuousOn_univ]
  apply ContinuousOn.if' <;> simp [*] <;> assumption
#align continuous_if' continuous_if'

/- warning: continuous_if -> continuous_if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : α -> Prop} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (p a)], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (frontier.{u1} α _inst_1 (setOf.{u1} α (fun (x : α) => p x)))) -> (Eq.{succ u2} β (f a) (g a))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (closure.{u1} α _inst_1 (setOf.{u1} α (fun (x : α) => p x)))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 g (closure.{u1} α _inst_1 (setOf.{u1} α (fun (x : α) => Not (p x))))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u2} β (p a) (_inst_5 a) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {p : α -> Prop} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (p a)], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (frontier.{u2} α _inst_1 (setOf.{u2} α (fun (x : α) => p x)))) -> (Eq.{succ u1} β (f a) (g a))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (closure.{u2} α _inst_1 (setOf.{u2} α (fun (x : α) => p x)))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 g (closure.{u2} α _inst_1 (setOf.{u2} α (fun (x : α) => Not (p x))))) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u1} β (p a) (_inst_5 a) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align continuous_if continuous_ifₓ'. -/
theorem continuous_if {p : α → Prop} {f g : α → β} [∀ a, Decidable (p a)]
    (hp : ∀ a ∈ frontier { x | p x }, f a = g a) (hf : ContinuousOn f (closure { x | p x }))
    (hg : ContinuousOn g (closure { x | ¬p x })) : Continuous fun a => if p a then f a else g a :=
  by
  rw [continuous_iff_continuousOn_univ]
  apply ContinuousOn.if <;> simp <;> assumption
#align continuous_if continuous_if

/- warning: continuous.if -> Continuous.if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : α -> Prop} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (p a)], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (frontier.{u1} α _inst_1 (setOf.{u1} α (fun (x : α) => p x)))) -> (Eq.{succ u2} β (f a) (g a))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 g) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u2} β (p a) (_inst_5 a) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {p : α -> Prop} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (p a)], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (frontier.{u2} α _inst_1 (setOf.{u2} α (fun (x : α) => p x)))) -> (Eq.{succ u1} β (f a) (g a))) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 g) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u1} β (p a) (_inst_5 a) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align continuous.if Continuous.ifₓ'. -/
theorem Continuous.if {p : α → Prop} {f g : α → β} [∀ a, Decidable (p a)]
    (hp : ∀ a ∈ frontier { x | p x }, f a = g a) (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => if p a then f a else g a :=
  continuous_if hp hf.ContinuousOn hg.ContinuousOn
#align continuous.if Continuous.if

/- warning: continuous_if_const -> continuous_if_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (p : Prop) {f : α -> β} {g : α -> β} [_inst_5 : Decidable p], (p -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f)) -> ((Not p) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 g)) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u2} β p _inst_5 (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (p : Prop) {f : α -> β} {g : α -> β} [_inst_5 : Decidable p], (p -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f)) -> ((Not p) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 g)) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u1} β p _inst_5 (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align continuous_if_const continuous_if_constₓ'. -/
theorem continuous_if_const (p : Prop) {f g : α → β} [Decidable p] (hf : p → Continuous f)
    (hg : ¬p → Continuous g) : Continuous fun a => if p then f a else g a :=
  by
  split_ifs
  exact hf h
  exact hg h
#align continuous_if_const continuous_if_const

/- warning: continuous.if_const -> Continuous.if_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (p : Prop) {f : α -> β} {g : α -> β} [_inst_5 : Decidable p], (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 g) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u2} β p _inst_5 (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (p : Prop) {f : α -> β} {g : α -> β} [_inst_5 : Decidable p], (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 g) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => ite.{succ u1} β p _inst_5 (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align continuous.if_const Continuous.if_constₓ'. -/
theorem Continuous.if_const (p : Prop) {f g : α → β} [Decidable p] (hf : Continuous f)
    (hg : Continuous g) : Continuous fun a => if p then f a else g a :=
  continuous_if_const p (fun _ => hf) fun _ => hg
#align continuous.if_const Continuous.if_const

/- warning: continuous_piecewise -> continuous_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (frontier.{u1} α _inst_1 s)) -> (Eq.{succ u2} β (f a) (g a))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (closure.{u1} α _inst_1 s)) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 g (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_5 j)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (frontier.{u2} α _inst_1 s)) -> (Eq.{succ u1} β (f a) (g a))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (closure.{u2} α _inst_1 s)) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 g (closure.{u2} α _inst_1 (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s))) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_5 j)))
Case conversion may be inaccurate. Consider using '#align continuous_piecewise continuous_piecewiseₓ'. -/
theorem continuous_piecewise {s : Set α} {f g : α → β} [∀ a, Decidable (a ∈ s)]
    (hs : ∀ a ∈ frontier s, f a = g a) (hf : ContinuousOn f (closure s))
    (hg : ContinuousOn g (closure (sᶜ))) : Continuous (piecewise s f g) :=
  continuous_if hs hf hg
#align continuous_piecewise continuous_piecewise

/- warning: continuous.piecewise -> Continuous.piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (frontier.{u1} α _inst_1 s)) -> (Eq.{succ u2} β (f a) (g a))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 g) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_5 j)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {f : α -> β} {g : α -> β} [_inst_5 : forall (a : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (frontier.{u2} α _inst_1 s)) -> (Eq.{succ u1} β (f a) (g a))) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 g) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_5 j)))
Case conversion may be inaccurate. Consider using '#align continuous.piecewise Continuous.piecewiseₓ'. -/
theorem Continuous.piecewise {s : Set α} {f g : α → β} [∀ a, Decidable (a ∈ s)]
    (hs : ∀ a ∈ frontier s, f a = g a) (hf : Continuous f) (hg : Continuous g) :
    Continuous (piecewise s f g) :=
  hf.if hs hg
#align continuous.piecewise Continuous.piecewise

#print IsOpen.ite' /-
theorem IsOpen.ite' {s s' t : Set α} (hs : IsOpen s) (hs' : IsOpen s')
    (ht : ∀ x ∈ frontier t, x ∈ s ↔ x ∈ s') : IsOpen (t.ite s s') := by
  classical
    simp only [isOpen_iff_continuous_mem, Set.ite] at *
    convert continuous_piecewise (fun x hx => propext (ht x hx)) hs.continuous_on hs'.continuous_on
    ext x
    by_cases hx : x ∈ t <;> simp [hx]
#align is_open.ite' IsOpen.ite'
-/

/- warning: is_open.ite -> IsOpen.ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 s') -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s' (frontier.{u1} α _inst_1 t))) -> (IsOpen.{u1} α _inst_1 (Set.ite.{u1} α t s s'))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 s') -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (frontier.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s' (frontier.{u1} α _inst_1 t))) -> (IsOpen.{u1} α _inst_1 (Set.ite.{u1} α t s s'))
Case conversion may be inaccurate. Consider using '#align is_open.ite IsOpen.iteₓ'. -/
theorem IsOpen.ite {s s' t : Set α} (hs : IsOpen s) (hs' : IsOpen s')
    (ht : s ∩ frontier t = s' ∩ frontier t) : IsOpen (t.ite s s') :=
  hs.ite' hs' fun x hx => by simpa [hx] using ext_iff.1 ht x
#align is_open.ite IsOpen.ite

/- warning: ite_inter_closure_eq_of_inter_frontier_eq -> ite_inter_closure_eq_of_inter_frontier_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u1} α}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s' (frontier.{u1} α _inst_1 t))) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.ite.{u1} α t s s') (closure.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (closure.{u1} α _inst_1 t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u1} α}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (frontier.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s' (frontier.{u1} α _inst_1 t))) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.ite.{u1} α t s s') (closure.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (closure.{u1} α _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align ite_inter_closure_eq_of_inter_frontier_eq ite_inter_closure_eq_of_inter_frontier_eqₓ'. -/
theorem ite_inter_closure_eq_of_inter_frontier_eq {s s' t : Set α}
    (ht : s ∩ frontier t = s' ∩ frontier t) : t.ite s s' ∩ closure t = s ∩ closure t := by
  rw [closure_eq_self_union_frontier, inter_union_distrib_left, inter_union_distrib_left,
    ite_inter_self, ite_inter_of_inter_eq _ ht]
#align ite_inter_closure_eq_of_inter_frontier_eq ite_inter_closure_eq_of_inter_frontier_eq

/- warning: ite_inter_closure_compl_eq_of_inter_frontier_eq -> ite_inter_closure_compl_eq_of_inter_frontier_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u1} α}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s' (frontier.{u1} α _inst_1 t))) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.ite.{u1} α t s s') (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s' (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u1} α}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (frontier.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s' (frontier.{u1} α _inst_1 t))) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.ite.{u1} α t s s') (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s' (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))))
Case conversion may be inaccurate. Consider using '#align ite_inter_closure_compl_eq_of_inter_frontier_eq ite_inter_closure_compl_eq_of_inter_frontier_eqₓ'. -/
theorem ite_inter_closure_compl_eq_of_inter_frontier_eq {s s' t : Set α}
    (ht : s ∩ frontier t = s' ∩ frontier t) : t.ite s s' ∩ closure (tᶜ) = s' ∩ closure (tᶜ) :=
  by
  rw [← ite_compl, ite_inter_closure_eq_of_inter_frontier_eq]
  rwa [frontier_compl, eq_comm]
#align ite_inter_closure_compl_eq_of_inter_frontier_eq ite_inter_closure_compl_eq_of_inter_frontier_eq

/- warning: continuous_on_piecewise_ite' -> continuousOn_piecewise_ite' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u1} α} {f : α -> β} {f' : α -> β} [_inst_5 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)], (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (closure.{u1} α _inst_1 t))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f' (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s' (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)))) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s' (frontier.{u1} α _inst_1 t))) -> (Set.EqOn.{u1, u2} α β f f' (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) t f f' (fun (j : α) => _inst_5 j)) (Set.ite.{u1} α t s s'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {s' : Set.{u2} α} {t : Set.{u2} α} {f : α -> β} {f' : α -> β} [_inst_5 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t)], (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (closure.{u2} α _inst_1 t))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f' (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s' (closure.{u2} α _inst_1 (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) t)))) -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_1 t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s' (frontier.{u2} α _inst_1 t))) -> (Set.EqOn.{u2, u1} α β f f' (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_1 t))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) t f f' (fun (j : α) => _inst_5 j)) (Set.ite.{u2} α t s s'))
Case conversion may be inaccurate. Consider using '#align continuous_on_piecewise_ite' continuousOn_piecewise_ite'ₓ'. -/
theorem continuousOn_piecewise_ite' {s s' t : Set α} {f f' : α → β} [∀ x, Decidable (x ∈ t)]
    (h : ContinuousOn f (s ∩ closure t)) (h' : ContinuousOn f' (s' ∩ closure (tᶜ)))
    (H : s ∩ frontier t = s' ∩ frontier t) (Heq : EqOn f f' (s ∩ frontier t)) :
    ContinuousOn (t.piecewise f f') (t.ite s s') :=
  by
  apply ContinuousOn.piecewise
  · rwa [ite_inter_of_inter_eq _ H]
  · rwa [ite_inter_closure_eq_of_inter_frontier_eq H]
  · rwa [ite_inter_closure_compl_eq_of_inter_frontier_eq H]
#align continuous_on_piecewise_ite' continuousOn_piecewise_ite'

/- warning: continuous_on_piecewise_ite -> continuousOn_piecewise_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u1} α} {f : α -> β} {f' : α -> β} [_inst_5 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)], (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 f' s') -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s' (frontier.{u1} α _inst_1 t))) -> (Set.EqOn.{u1, u2} α β f f' (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 t))) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) t f f' (fun (j : α) => _inst_5 j)) (Set.ite.{u1} α t s s'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {s' : Set.{u2} α} {t : Set.{u2} α} {f : α -> β} {f' : α -> β} [_inst_5 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t)], (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 f' s') -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_1 t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s' (frontier.{u2} α _inst_1 t))) -> (Set.EqOn.{u2, u1} α β f f' (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (frontier.{u2} α _inst_1 t))) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_2 (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) t f f' (fun (j : α) => _inst_5 j)) (Set.ite.{u2} α t s s'))
Case conversion may be inaccurate. Consider using '#align continuous_on_piecewise_ite continuousOn_piecewise_iteₓ'. -/
theorem continuousOn_piecewise_ite {s s' t : Set α} {f f' : α → β} [∀ x, Decidable (x ∈ t)]
    (h : ContinuousOn f s) (h' : ContinuousOn f' s') (H : s ∩ frontier t = s' ∩ frontier t)
    (Heq : EqOn f f' (s ∩ frontier t)) : ContinuousOn (t.piecewise f f') (t.ite s s') :=
  continuousOn_piecewise_ite' (h.mono (inter_subset_left _ _)) (h'.mono (inter_subset_left _ _)) H
    Heq
#align continuous_on_piecewise_ite continuousOn_piecewise_ite

/- warning: frontier_inter_open_inter -> frontier_inter_open_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (frontier.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (frontier.{u1} α _inst_1 s) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (frontier.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (frontier.{u1} α _inst_1 s) t))
Case conversion may be inaccurate. Consider using '#align frontier_inter_open_inter frontier_inter_open_interₓ'. -/
theorem frontier_inter_open_inter {s t : Set α} (ht : IsOpen t) :
    frontier (s ∩ t) ∩ t = frontier s ∩ t := by
  simp only [← Subtype.preimage_coe_eq_preimage_coe_iff,
    ht.is_open_map_subtype_coe.preimage_frontier_eq_frontier_preimage continuous_subtype_val,
    Subtype.preimage_coe_inter_self]
#align frontier_inter_open_inter frontier_inter_open_inter

/- warning: continuous_on_fst -> continuousOn_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u1 u2} (Prod.{u1, u2} α β)}, ContinuousOn.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β) s
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u2 u1} (Prod.{u1, u2} α β)}, ContinuousOn.{max u2 u1, u1} (Prod.{u1, u2} α β) α (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β) s
Case conversion may be inaccurate. Consider using '#align continuous_on_fst continuousOn_fstₓ'. -/
theorem continuousOn_fst {s : Set (α × β)} : ContinuousOn Prod.fst s :=
  continuous_fst.ContinuousOn
#align continuous_on_fst continuousOn_fst

/- warning: continuous_within_at_fst -> continuousWithinAt_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u1 u2} (Prod.{u1, u2} α β)} {p : Prod.{u1, u2} α β}, ContinuousWithinAt.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β) s p
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u2 u1} (Prod.{u1, u2} α β)} {p : Prod.{u1, u2} α β}, ContinuousWithinAt.{max u2 u1, u1} (Prod.{u1, u2} α β) α (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β) s p
Case conversion may be inaccurate. Consider using '#align continuous_within_at_fst continuousWithinAt_fstₓ'. -/
theorem continuousWithinAt_fst {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.fst s p :=
  continuous_fst.ContinuousWithinAt
#align continuous_within_at_fst continuousWithinAt_fst

/- warning: continuous_on.fst -> ContinuousOn.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> (Prod.{u2, u3} β γ)} {s : Set.{u1} α}, (ContinuousOn.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) f s) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (fun (x : α) => Prod.fst.{u2, u3} β γ (f x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : α -> (Prod.{u3, u2} β γ)} {s : Set.{u1} α}, (ContinuousOn.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u2} β γ _inst_2 _inst_3) f s) -> (ContinuousOn.{u1, u3} α β _inst_1 _inst_2 (fun (x : α) => Prod.fst.{u3, u2} β γ (f x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.fst ContinuousOn.fstₓ'. -/
theorem ContinuousOn.fst {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).1) s :=
  continuous_fst.comp_continuousOn hf
#align continuous_on.fst ContinuousOn.fst

/- warning: continuous_within_at.fst -> ContinuousWithinAt.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> (Prod.{u2, u3} β γ)} {s : Set.{u1} α} {a : α}, (ContinuousWithinAt.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) f s a) -> (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 (fun (x : α) => Prod.fst.{u2, u3} β γ (f x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : α -> (Prod.{u3, u2} β γ)} {s : Set.{u1} α} {a : α}, (ContinuousWithinAt.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u2} β γ _inst_2 _inst_3) f s a) -> (ContinuousWithinAt.{u1, u3} α β _inst_1 _inst_2 (fun (x : α) => Prod.fst.{u3, u2} β γ (f x)) s a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.fst ContinuousWithinAt.fstₓ'. -/
theorem ContinuousWithinAt.fst {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).fst) s a :=
  continuousAt_fst.comp_continuousWithinAt h
#align continuous_within_at.fst ContinuousWithinAt.fst

/- warning: continuous_on_snd -> continuousOn_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u1 u2} (Prod.{u1, u2} α β)}, ContinuousOn.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β) s
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u2 u1} (Prod.{u1, u2} α β)}, ContinuousOn.{max u2 u1, u2} (Prod.{u1, u2} α β) β (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β) s
Case conversion may be inaccurate. Consider using '#align continuous_on_snd continuousOn_sndₓ'. -/
theorem continuousOn_snd {s : Set (α × β)} : ContinuousOn Prod.snd s :=
  continuous_snd.ContinuousOn
#align continuous_on_snd continuousOn_snd

/- warning: continuous_within_at_snd -> continuousWithinAt_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u1 u2} (Prod.{u1, u2} α β)} {p : Prod.{u1, u2} α β}, ContinuousWithinAt.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β) s p
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u2 u1} (Prod.{u1, u2} α β)} {p : Prod.{u1, u2} α β}, ContinuousWithinAt.{max u2 u1, u2} (Prod.{u1, u2} α β) β (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β) s p
Case conversion may be inaccurate. Consider using '#align continuous_within_at_snd continuousWithinAt_sndₓ'. -/
theorem continuousWithinAt_snd {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.snd s p :=
  continuous_snd.ContinuousWithinAt
#align continuous_within_at_snd continuousWithinAt_snd

/- warning: continuous_on.snd -> ContinuousOn.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> (Prod.{u2, u3} β γ)} {s : Set.{u1} α}, (ContinuousOn.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) f s) -> (ContinuousOn.{u1, u3} α γ _inst_1 _inst_3 (fun (x : α) => Prod.snd.{u2, u3} β γ (f x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : α -> (Prod.{u3, u2} β γ)} {s : Set.{u1} α}, (ContinuousOn.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u2} β γ _inst_2 _inst_3) f s) -> (ContinuousOn.{u1, u2} α γ _inst_1 _inst_3 (fun (x : α) => Prod.snd.{u3, u2} β γ (f x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.snd ContinuousOn.sndₓ'. -/
theorem ContinuousOn.snd {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).2) s :=
  continuous_snd.comp_continuousOn hf
#align continuous_on.snd ContinuousOn.snd

/- warning: continuous_within_at.snd -> ContinuousWithinAt.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> (Prod.{u2, u3} β γ)} {s : Set.{u1} α} {a : α}, (ContinuousWithinAt.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) f s a) -> (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 (fun (x : α) => Prod.snd.{u2, u3} β γ (f x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : α -> (Prod.{u3, u2} β γ)} {s : Set.{u1} α} {a : α}, (ContinuousWithinAt.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u2} β γ _inst_2 _inst_3) f s a) -> (ContinuousWithinAt.{u1, u2} α γ _inst_1 _inst_3 (fun (x : α) => Prod.snd.{u3, u2} β γ (f x)) s a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.snd ContinuousWithinAt.sndₓ'. -/
theorem ContinuousWithinAt.snd {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).snd) s a :=
  continuousAt_snd.comp_continuousWithinAt h
#align continuous_within_at.snd ContinuousWithinAt.snd

/- warning: continuous_within_at_prod_iff -> continuousWithinAt_prod_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> (Prod.{u2, u3} β γ)} {s : Set.{u1} α} {x : α}, Iff (ContinuousWithinAt.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) f s x) (And (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_2 (Function.comp.{succ u1, max (succ u2) (succ u3), succ u2} α (Prod.{u2, u3} β γ) β (Prod.fst.{u2, u3} β γ) f) s x) (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, max (succ u2) (succ u3), succ u3} α (Prod.{u2, u3} β γ) γ (Prod.snd.{u2, u3} β γ) f) s x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : α -> (Prod.{u3, u2} β γ)} {s : Set.{u1} α} {x : α}, Iff (ContinuousWithinAt.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u2} β γ _inst_2 _inst_3) f s x) (And (ContinuousWithinAt.{u1, u3} α β _inst_1 _inst_2 (Function.comp.{succ u1, max (succ u2) (succ u3), succ u3} α (Prod.{u3, u2} β γ) β (Prod.fst.{u3, u2} β γ) f) s x) (ContinuousWithinAt.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, max (succ u2) (succ u3), succ u2} α (Prod.{u3, u2} β γ) γ (Prod.snd.{u3, u2} β γ) f) s x))
Case conversion may be inaccurate. Consider using '#align continuous_within_at_prod_iff continuousWithinAt_prod_iffₓ'. -/
theorem continuousWithinAt_prod_iff {f : α → β × γ} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔
      ContinuousWithinAt (Prod.fst ∘ f) s x ∧ ContinuousWithinAt (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, by
    rintro ⟨h1, h2⟩
    convert h1.prod h2
    ext
    rfl
    rfl⟩
#align continuous_within_at_prod_iff continuousWithinAt_prod_iff

