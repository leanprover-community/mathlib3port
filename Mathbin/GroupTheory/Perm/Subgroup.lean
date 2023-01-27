/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.perm.subgroup
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Perm.Basic
import Mathbin.Data.Fintype.Perm
import Mathbin.GroupTheory.Subgroup.Finite

/-!
# Lemmas about subgroups within the permutations (self-equivalences) of a type `α`

This file provides extra lemmas about some `subgroup`s that exist within `equiv.perm α`.
`group_theory.subgroup` depends on `group_theory.perm.basic`, so these need to be in a separate
file.

It also provides decidable instances on membership in these subgroups, since
`monoid_hom.decidable_mem_range` cannot be inferred without the help of a lambda.
The presence of these instances induces a `fintype` instance on the `quotient_group.quotient` of
these subgroups.
-/


namespace Equiv

namespace Perm

universe u

instance sumCongrHom.decidableMemRange {α β : Type _} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] : DecidablePred (· ∈ (sumCongrHom α β).range) := fun x => inferInstance
#align equiv.perm.sum_congr_hom.decidable_mem_range Equiv.Perm.sumCongrHom.decidableMemRange

@[simp]
theorem sumCongrHom.card_range {α β : Type _} [Fintype (sumCongrHom α β).range]
    [Fintype (Perm α × Perm β)] :
    Fintype.card (sumCongrHom α β).range = Fintype.card (Perm α × Perm β) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sumCongrHom α β) sumCongrHom_injective).symm⟩
#align equiv.perm.sum_congr_hom.card_range Equiv.Perm.sumCongrHom.card_range

instance sigmaCongrRightHom.decidableMemRange {α : Type _} {β : α → Type _} [DecidableEq α]
    [∀ a, DecidableEq (β a)] [Fintype α] [∀ a, Fintype (β a)] :
    DecidablePred (· ∈ (sigmaCongrRightHom β).range) := fun x => inferInstance
#align equiv.perm.sigma_congr_right_hom.decidable_mem_range Equiv.Perm.sigmaCongrRightHom.decidableMemRange

@[simp]
theorem sigmaCongrRightHom.card_range {α : Type _} {β : α → Type _}
    [Fintype (sigmaCongrRightHom β).range] [Fintype (∀ a, Perm (β a))] :
    Fintype.card (sigmaCongrRightHom β).range = Fintype.card (∀ a, Perm (β a)) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sigmaCongrRightHom β) sigmaCongrRightHom_injective).symm⟩
#align equiv.perm.sigma_congr_right_hom.card_range Equiv.Perm.sigmaCongrRightHom.card_range

instance subtypeCongrHom.decidableMemRange {α : Type _} (p : α → Prop) [DecidablePred p]
    [Fintype (Perm { a // p a } × Perm { a // ¬p a })] [DecidableEq (Perm α)] :
    DecidablePred (· ∈ (subtypeCongrHom p).range) := fun x => inferInstance
#align equiv.perm.subtype_congr_hom.decidable_mem_range Equiv.Perm.subtypeCongrHom.decidableMemRange

@[simp]
theorem subtypeCongrHom.card_range {α : Type _} (p : α → Prop) [DecidablePred p]
    [Fintype (subtypeCongrHom p).range] [Fintype (Perm { a // p a } × Perm { a // ¬p a })] :
    Fintype.card (subtypeCongrHom p).range =
      Fintype.card (Perm { a // p a } × Perm { a // ¬p a }) :=
  Fintype.card_eq.mpr ⟨(ofInjective (subtypeCongrHom p) (subtypeCongrHom_injective p)).symm⟩
#align equiv.perm.subtype_congr_hom.card_range Equiv.Perm.subtypeCongrHom.card_range

/-- **Cayley's theorem**: Every group G is isomorphic to a subgroup of the symmetric group acting on
`G`. Note that we generalize this to an arbitrary "faithful" group action by `G`. Setting `H = G`
recovers the usual statement of Cayley's theorem via `right_cancel_monoid.to_has_faithful_smul` -/
noncomputable def subgroupOfMulAction (G H : Type _) [Group G] [MulAction G H] [FaithfulSMul G H] :
    G ≃* (MulAction.toPermHom G H).range :=
  MulEquiv.ofLeftInverse' _ (Classical.choose_spec MulAction.toPerm_injective.HasLeftInverse)
#align equiv.perm.subgroup_of_mul_action Equiv.Perm.subgroupOfMulAction

end Perm

end Equiv

