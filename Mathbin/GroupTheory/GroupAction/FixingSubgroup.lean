/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathbin.GroupTheory.Subgroup.Actions
import Mathbin.GroupTheory.GroupAction.Basic

#align_import group_theory.group_action.fixing_subgroup from "leanprover-community/mathlib"@"fac369018417f980cec5fcdafc766a69f88d8cfe"

/-!

# Fixing submonoid, fixing subgroup of an action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print fixingSubmonoid /-
/-- The submonoid fixing a set under a `mul_action`. -/
@[to_additive " The additive submonoid fixing a set under an `add_action`. "]
def fixingSubmonoid (s : Set α) : Submonoid M
    where
  carrier := {ϕ : M | ∀ x : s, ϕ • (x : α) = x}
  one_mem' _ := one_smul _ _
  hMul_mem' x y hx hy z := by rw [mul_smul, hy z, hx z]
#align fixing_submonoid fixingSubmonoid
#align fixing_add_submonoid fixingAddSubmonoid
-/

#print mem_fixingSubmonoid_iff /-
theorem mem_fixingSubmonoid_iff {s : Set α} {m : M} :
    m ∈ fixingSubmonoid M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩
#align mem_fixing_submonoid_iff mem_fixingSubmonoid_iff
-/

variable (α)

#print fixingSubmonoid_fixedPoints_gc /-
/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
theorem fixingSubmonoid_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubmonoid M)
      ((fun P : Submonoid M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun s P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩
#align fixing_submonoid_fixed_points_gc fixingSubmonoid_fixedPoints_gc
-/

#print fixingSubmonoid_antitone /-
theorem fixingSubmonoid_antitone : Antitone fun s : Set α => fixingSubmonoid M s :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_l
#align fixing_submonoid_antitone fixingSubmonoid_antitone
-/

#print fixedPoints_antitone /-
theorem fixedPoints_antitone : Antitone fun P : Submonoid M => fixedPoints P α :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_u.dual_left
#align fixed_points_antitone fixedPoints_antitone
-/

#print fixingSubmonoid_union /-
/-- Fixing submonoid of union is intersection -/
theorem fixingSubmonoid_union {s t : Set α} :
    fixingSubmonoid M (s ∪ t) = fixingSubmonoid M s ⊓ fixingSubmonoid M t :=
  (fixingSubmonoid_fixedPoints_gc M α).l_sup
#align fixing_submonoid_union fixingSubmonoid_union
-/

#print fixingSubmonoid_iUnion /-
/-- Fixing submonoid of Union is intersection -/
theorem fixingSubmonoid_iUnion {ι : Sort _} {s : ι → Set α} :
    fixingSubmonoid M (⋃ i, s i) = ⨅ i, fixingSubmonoid M (s i) :=
  (fixingSubmonoid_fixedPoints_gc M α).l_iSup
#align fixing_submonoid_Union fixingSubmonoid_iUnion
-/

#print fixedPoints_submonoid_sup /-
/-- Fixed points of sup of submonoids is intersection -/
theorem fixedPoints_submonoid_sup {P Q : Submonoid M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_inf
#align fixed_points_submonoid_sup fixedPoints_submonoid_sup
-/

#print fixedPoints_submonoid_iSup /-
/-- Fixed points of supr of submonoids is intersection -/
theorem fixedPoints_submonoid_iSup {ι : Sort _} {P : ι → Submonoid M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_iInf
#align fixed_points_submonoid_supr fixedPoints_submonoid_iSup
-/

end Monoid

section Group

open MulAction

variable (M : Type _) {α : Type _} [Group M] [MulAction M α]

#print fixingSubgroup /-
/-- The subgroup fixing a set under a `mul_action`. -/
@[to_additive " The additive subgroup fixing a set under an `add_action`. "]
def fixingSubgroup (s : Set α) : Subgroup M :=
  { fixingSubmonoid M s with inv_mem' := fun _ hx z => by rw [inv_smul_eq_iff, hx z] }
#align fixing_subgroup fixingSubgroup
#align fixing_add_subgroup fixingAddSubgroup
-/

#print mem_fixingSubgroup_iff /-
theorem mem_fixingSubgroup_iff {s : Set α} {m : M} : m ∈ fixingSubgroup M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩
#align mem_fixing_subgroup_iff mem_fixingSubgroup_iff
-/

variable (α)

#print fixingSubgroup_fixedPoints_gc /-
/-- The Galois connection between fixing subgroups and fixed points of a group action -/
theorem fixingSubgroup_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubgroup M)
      ((fun P : Subgroup M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun s P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩
#align fixing_subgroup_fixed_points_gc fixingSubgroup_fixedPoints_gc
-/

#print fixingSubgroup_antitone /-
theorem fixingSubgroup_antitone : Antitone (fixingSubgroup M : Set α → Subgroup M) :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_l
#align fixing_subgroup_antitone fixingSubgroup_antitone
-/

#print fixedPoints_subgroup_antitone /-
theorem fixedPoints_subgroup_antitone : Antitone fun P : Subgroup M => fixedPoints P α :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_u.dual_left
#align fixed_points_subgroup_antitone fixedPoints_subgroup_antitone
-/

#print fixingSubgroup_union /-
/-- Fixing subgroup of union is intersection -/
theorem fixingSubgroup_union {s t : Set α} :
    fixingSubgroup M (s ∪ t) = fixingSubgroup M s ⊓ fixingSubgroup M t :=
  (fixingSubgroup_fixedPoints_gc M α).l_sup
#align fixing_subgroup_union fixingSubgroup_union
-/

#print fixingSubgroup_iUnion /-
/-- Fixing subgroup of Union is intersection -/
theorem fixingSubgroup_iUnion {ι : Sort _} {s : ι → Set α} :
    fixingSubgroup M (⋃ i, s i) = ⨅ i, fixingSubgroup M (s i) :=
  (fixingSubgroup_fixedPoints_gc M α).l_iSup
#align fixing_subgroup_Union fixingSubgroup_iUnion
-/

#print fixedPoints_subgroup_sup /-
/-- Fixed points of sup of subgroups is intersection -/
theorem fixedPoints_subgroup_sup {P Q : Subgroup M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubgroup_fixedPoints_gc M α).u_inf
#align fixed_points_subgroup_sup fixedPoints_subgroup_sup
-/

#print fixedPoints_subgroup_iSup /-
/-- Fixed points of supr of subgroups is intersection -/
theorem fixedPoints_subgroup_iSup {ι : Sort _} {P : ι → Subgroup M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubgroup_fixedPoints_gc M α).u_iInf
#align fixed_points_subgroup_supr fixedPoints_subgroup_iSup
-/

end Group

