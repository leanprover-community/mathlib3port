/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module group_theory.group_action.fixing_subgroup
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.GroupTheory.GroupAction.Basic

/-!

# Fixing submonoid, fixing subgroup of an action

In the presence of of an action of a monoid or a group,
this file defines the fixing submonoid or the fixing subgroup,
and relates it to the set of fixed points via a Galois connection.

## Main definitions

* `fixing_submonoid M s` : in the presence of `mul_action M α` (with `monoid M`)
  it is the `submonoid M` consisting of elements which fix `s : set α` pointwise.

* `fixing_submonoid_fixed_points_gc M α` is the `galois_connection`
  that relates `fixing_submonoid` with `fixed_points`.

* `fixing_subgroup M s` : in the presence of `mul_action M α` (with `group M`)
  it is the `subgroup M` consisting of elements which fix `s : set α` pointwise.

* `fixing_subgroup_fixed_points_gc M α` is the `galois_connection`
  that relates `fixing_subgroup` with `fixed_points`.

TODO :

* Maybe other lemmas are useful

* Treat semigroups ?

-/


section Monoid

open MulAction

variable (M : Type _) {α : Type _} [Monoid M] [MulAction M α]

/-- The submonoid fixing a set under a `mul_action`. -/
@[to_additive " The additive submonoid fixing a set under an `add_action`. "]
def fixingSubmonoid (s : Set α) : Submonoid M
    where
  carrier := { ϕ : M | ∀ x : s, ϕ • (x : α) = x }
  one_mem' _ := one_smul _ _
  mul_mem' x y hx hy z := by rw [mul_smul, hy z, hx z]
#align fixing_submonoid fixingSubmonoid

theorem mem_fixing_submonoid_iff {s : Set α} {m : M} :
    m ∈ fixingSubmonoid M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩
#align mem_fixing_submonoid_iff mem_fixing_submonoid_iff

variable (α)

/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
theorem fixing_submonoid_fixed_points_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubmonoid M)
      ((fun P : Submonoid M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun s P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩
#align fixing_submonoid_fixed_points_gc fixing_submonoid_fixed_points_gc

theorem fixing_submonoid_antitone : Antitone fun s : Set α => fixingSubmonoid M s :=
  (fixing_submonoid_fixed_points_gc M α).monotone_l
#align fixing_submonoid_antitone fixing_submonoid_antitone

theorem fixed_points_antitone : Antitone fun P : Submonoid M => fixedPoints P α :=
  (fixing_submonoid_fixed_points_gc M α).monotone_u.dual_left
#align fixed_points_antitone fixed_points_antitone

/-- Fixing submonoid of union is intersection -/
theorem fixing_submonoid_union {s t : Set α} :
    fixingSubmonoid M (s ∪ t) = fixingSubmonoid M s ⊓ fixingSubmonoid M t :=
  (fixing_submonoid_fixed_points_gc M α).l_sup
#align fixing_submonoid_union fixing_submonoid_union

/-- Fixing submonoid of Union is intersection -/
theorem fixing_submonoid_Union {ι : Sort _} {s : ι → Set α} :
    fixingSubmonoid M (⋃ i, s i) = ⨅ i, fixingSubmonoid M (s i) :=
  (fixing_submonoid_fixed_points_gc M α).l_supr
#align fixing_submonoid_Union fixing_submonoid_Union

/-- Fixed points of sup of submonoids is intersection -/
theorem fixed_points_submonoid_sup {P Q : Submonoid M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixing_submonoid_fixed_points_gc M α).u_inf
#align fixed_points_submonoid_sup fixed_points_submonoid_sup

/-- Fixed points of supr of submonoids is intersection -/
theorem fixed_points_submonoid_supr {ι : Sort _} {P : ι → Submonoid M} :
    fixedPoints (↥(supᵢ P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixing_submonoid_fixed_points_gc M α).u_infi
#align fixed_points_submonoid_supr fixed_points_submonoid_supr

end Monoid

section Group

open MulAction

variable (M : Type _) {α : Type _} [Group M] [MulAction M α]

/-- The subgroup fixing a set under a `mul_action`. -/
@[to_additive " The additive subgroup fixing a set under an `add_action`. "]
def fixingSubgroup (s : Set α) : Subgroup M :=
  { fixingSubmonoid M s with inv_mem' := fun _ hx z => by rw [inv_smul_eq_iff, hx z] }
#align fixing_subgroup fixingSubgroup

theorem mem_fixing_subgroup_iff {s : Set α} {m : M} : m ∈ fixingSubgroup M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩
#align mem_fixing_subgroup_iff mem_fixing_subgroup_iff

variable (α)

/-- The Galois connection between fixing subgroups and fixed points of a group action -/
theorem fixing_subgroup_fixed_points_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubgroup M)
      ((fun P : Subgroup M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun s P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩
#align fixing_subgroup_fixed_points_gc fixing_subgroup_fixed_points_gc

theorem fixing_subgroup_antitone : Antitone (fixingSubgroup M : Set α → Subgroup M) :=
  (fixing_subgroup_fixed_points_gc M α).monotone_l
#align fixing_subgroup_antitone fixing_subgroup_antitone

theorem fixed_points_subgroup_antitone : Antitone fun P : Subgroup M => fixedPoints P α :=
  (fixing_subgroup_fixed_points_gc M α).monotone_u.dual_left
#align fixed_points_subgroup_antitone fixed_points_subgroup_antitone

/-- Fixing subgroup of union is intersection -/
theorem fixing_subgroup_union {s t : Set α} :
    fixingSubgroup M (s ∪ t) = fixingSubgroup M s ⊓ fixingSubgroup M t :=
  (fixing_subgroup_fixed_points_gc M α).l_sup
#align fixing_subgroup_union fixing_subgroup_union

/-- Fixing subgroup of Union is intersection -/
theorem fixing_subgroup_Union {ι : Sort _} {s : ι → Set α} :
    fixingSubgroup M (⋃ i, s i) = ⨅ i, fixingSubgroup M (s i) :=
  (fixing_subgroup_fixed_points_gc M α).l_supr
#align fixing_subgroup_Union fixing_subgroup_Union

/-- Fixed points of sup of subgroups is intersection -/
theorem fixed_points_subgroup_sup {P Q : Subgroup M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixing_subgroup_fixed_points_gc M α).u_inf
#align fixed_points_subgroup_sup fixed_points_subgroup_sup

/-- Fixed points of supr of subgroups is intersection -/
theorem fixed_points_subgroup_supr {ι : Sort _} {P : ι → Subgroup M} :
    fixedPoints (↥(supᵢ P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixing_subgroup_fixed_points_gc M α).u_infi
#align fixed_points_subgroup_supr fixed_points_subgroup_supr

end Group

