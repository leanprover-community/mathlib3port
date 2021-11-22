import Mathbin.GroupTheory.Perm.Basic 
import Mathbin.Data.Fintype.Basic 
import Mathbin.GroupTheory.Subgroup.Basic

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

instance sum_congr_hom.decidable_mem_range {α β : Type _} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
  DecidablePred (· ∈ (sum_congr_hom α β).range) :=
  fun x => inferInstance

@[simp]
theorem sum_congr_hom.card_range {α β : Type _} [Fintype (sum_congr_hom α β).range] [Fintype (perm α × perm β)] :
  Fintype.card (sum_congr_hom α β).range = Fintype.card (perm α × perm β) :=
  Fintype.card_eq.mpr ⟨(of_injective (sum_congr_hom α β) sum_congr_hom_injective).symm⟩

instance sigma_congr_right_hom.decidable_mem_range {α : Type _} {β : α → Type _} [DecidableEq α]
  [∀ a, DecidableEq (β a)] [Fintype α] [∀ a, Fintype (β a)] : DecidablePred (· ∈ (sigma_congr_right_hom β).range) :=
  fun x => inferInstance

@[simp]
theorem sigma_congr_right_hom.card_range {α : Type _} {β : α → Type _} [Fintype (sigma_congr_right_hom β).range]
  [Fintype (∀ a, perm (β a))] : Fintype.card (sigma_congr_right_hom β).range = Fintype.card (∀ a, perm (β a)) :=
  Fintype.card_eq.mpr ⟨(of_injective (sigma_congr_right_hom β) sigma_congr_right_hom_injective).symm⟩

instance subtype_congr_hom.decidable_mem_range {α : Type _} (p : α → Prop) [DecidablePred p]
  [Fintype (perm { a // p a } × perm { a // ¬p a })] [DecidableEq (perm α)] :
  DecidablePred (· ∈ (subtype_congr_hom p).range) :=
  fun x => inferInstance

@[simp]
theorem subtype_congr_hom.card_range {α : Type _} (p : α → Prop) [DecidablePred p] [Fintype (subtype_congr_hom p).range]
  [Fintype (perm { a // p a } × perm { a // ¬p a })] :
  Fintype.card (subtype_congr_hom p).range = Fintype.card (perm { a // p a } × perm { a // ¬p a }) :=
  Fintype.card_eq.mpr ⟨(of_injective (subtype_congr_hom p) (subtype_congr_hom_injective p)).symm⟩

/-- **Cayley's theorem**: Every group G is isomorphic to a subgroup of the symmetric group acting on
`G`. Note that we generalize this to an arbitrary "faithful" group action by `G`. Setting `H = G`
recovers the usual statement of Cayley's theorem via `right_cancel_monoid.to_has_faithful_scalar` -/
noncomputable def subgroup_of_mul_action (G H : Type _) [Groupₓ G] [MulAction G H] [HasFaithfulScalar G H] :
  G ≃* (MulAction.toPermHom G H).range :=
  MulEquiv.ofLeftInverse' _ (Classical.some_spec MulAction.to_perm_injective.HasLeftInverse)

end Perm

end Equiv

