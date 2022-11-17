/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.Data.Zmod.Quotient

/-!
# Complements

In this file we define the complement of a subgroup.

## Main definitions

- `is_complement S T` where `S` and `T` are subsets of `G` states that every `g : G` can be
  written uniquely as a product `s * t` for `s ∈ S`, `t ∈ T`.
- `left_transversals T` where `T` is a subset of `G` is the set of all left-complements of `T`,
  i.e. the set of all `S : set G` that contain exactly one element of each left coset of `T`.
- `right_transversals S` where `S` is a subset of `G` is the set of all right-complements of `S`,
  i.e. the set of all `T : set G` that contain exactly one element of each right coset of `S`.
- `transfer_transversal H g` is a specific `left_transversal` of `H` that is used in the
  computation of the transfer homomorphism evaluated at an element `g : G`.

## Main results

- `is_complement_of_coprime` : Subgroups of coprime order are complements.
-/


open BigOperators Pointwise

namespace Subgroup

variable {G : Type _} [Group G] (H K : Subgroup G) (S T : Set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
  This notion generalizes left transversals, right transversals, and complementary subgroups. -/
@[to_additive "`S` and `T` are complements if `(*) : S × T → G` is a bijection"]
def IsComplement : Prop :=
  Function.Bijective fun x : S × T => x.1.1 * x.2.1
#align subgroup.is_complement Subgroup.IsComplement

/-- `H` and `K` are complements if `(*) : H × K → G` is a bijection -/
@[to_additive "`H` and `K` are complements if `(*) : H × K → G` is a bijection"]
abbrev IsComplement' :=
  IsComplement (H : Set G) (K : Set G)
#align subgroup.is_complement' Subgroup.IsComplement'

/-- The set of left-complements of `T : set G` -/
@[to_additive "The set of left-complements of `T : set G`"]
def leftTransversals : Set (Set G) :=
  { S : Set G | IsComplement S T }
#align subgroup.left_transversals Subgroup.leftTransversals

/-- The set of right-complements of `S : set G` -/
@[to_additive "The set of right-complements of `S : set G`"]
def rightTransversals : Set (Set G) :=
  { T : Set G | IsComplement S T }
#align subgroup.right_transversals Subgroup.rightTransversals

variable {H K S T}

@[to_additive]
theorem is_complement'_def : IsComplement' H K ↔ IsComplement (H : Set G) (K : Set G) :=
  Iff.rfl
#align subgroup.is_complement'_def Subgroup.is_complement'_def

@[to_additive]
theorem is_complement_iff_exists_unique : IsComplement S T ↔ ∀ g : G, ∃! x : S × T, x.1.1 * x.2.1 = g :=
  Function.bijective_iff_existsUnique _
#align subgroup.is_complement_iff_exists_unique Subgroup.is_complement_iff_exists_unique

@[to_additive]
theorem IsComplement.exists_unique (h : IsComplement S T) (g : G) : ∃! x : S × T, x.1.1 * x.2.1 = g :=
  is_complement_iff_exists_unique.mp h g
#align subgroup.is_complement.exists_unique Subgroup.IsComplement.exists_unique

@[to_additive]
theorem IsComplement'.symm (h : IsComplement' H K) : IsComplement' K H := by
  let ϕ : H × K ≃ K × H :=
    Equiv.mk (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => Prod.ext (inv_inv _) (inv_inv _)) fun x =>
      Prod.ext (inv_inv _) (inv_inv _)
  let ψ : G ≃ G := Equiv.mk (fun g : G => g⁻¹) (fun g : G => g⁻¹) inv_inv inv_inv
  suffices (ψ ∘ fun x : H × K => x.1.1 * x.2.1) = (fun x : K × H => x.1.1 * x.2.1) ∘ ϕ by
    rwa [is_complement'_def, is_complement, ← Equiv.bijective_comp, ← this, Equiv.comp_bijective]
  exact funext fun x => mul_inv_rev _ _
#align subgroup.is_complement'.symm Subgroup.IsComplement'.symm

@[to_additive]
theorem is_complement'_comm : IsComplement' H K ↔ IsComplement' K H :=
  ⟨IsComplement'.symm, IsComplement'.symm⟩
#align subgroup.is_complement'_comm Subgroup.is_complement'_comm

@[to_additive]
theorem is_complement_top_singleton {g : G} : IsComplement (⊤ : Set G) {g} :=
  ⟨fun ⟨x, _, rfl⟩ ⟨y, _, rfl⟩ h => Prod.ext (Subtype.ext (mul_right_cancel h)) rfl, fun x =>
    ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩
#align subgroup.is_complement_top_singleton Subgroup.is_complement_top_singleton

@[to_additive]
theorem is_complement_singleton_top {g : G} : IsComplement ({g} : Set G) ⊤ :=
  ⟨fun ⟨⟨_, rfl⟩, x⟩ ⟨⟨_, rfl⟩, y⟩ h => Prod.ext rfl (Subtype.ext (mul_left_cancel h)), fun x =>
    ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩
#align subgroup.is_complement_singleton_top Subgroup.is_complement_singleton_top

@[to_additive]
theorem is_complement_singleton_left {g : G} : IsComplement {g} S ↔ S = ⊤ := by
  refine' ⟨fun h => top_le_iff.mp fun x hx => _, fun h => (congr_arg _ h).mpr is_complement_singleton_top⟩
  obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x)
  rwa [← mul_left_cancel hy]
#align subgroup.is_complement_singleton_left Subgroup.is_complement_singleton_left

@[to_additive]
theorem is_complement_singleton_right {g : G} : IsComplement S {g} ↔ S = ⊤ := by
  refine' ⟨fun h => top_le_iff.mp fun x hx => _, fun h => (congr_arg _ h).mpr is_complement_top_singleton⟩
  obtain ⟨y, hy⟩ := h.2 (x * g)
  conv_rhs at hy => rw [← show y.2.1 = g from y.2.2]
  rw [← mul_right_cancel hy]
  exact y.1.2
#align subgroup.is_complement_singleton_right Subgroup.is_complement_singleton_right

@[to_additive]
theorem is_complement_top_left : IsComplement ⊤ S ↔ ∃ g : G, S = {g} := by
  refine' ⟨fun h => set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, fun a ha b hb => _⟩, _⟩
  · obtain ⟨a, ha⟩ := h.2 1
    exact ⟨a.2.1, a.2.2⟩
    
  · have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : Set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
      h.1 ((inv_mul_self a).trans (inv_mul_self b).symm)
    exact subtype.ext_iff.mp (prod.ext_iff.mp this).2
    
  · rintro ⟨g, rfl⟩
    exact is_complement_top_singleton
    
#align subgroup.is_complement_top_left Subgroup.is_complement_top_left

@[to_additive]
theorem is_complement_top_right : IsComplement S ⊤ ↔ ∃ g : G, S = {g} := by
  refine' ⟨fun h => set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, fun a ha b hb => _⟩, _⟩
  · obtain ⟨a, ha⟩ := h.2 1
    exact ⟨a.1.1, a.1.2⟩
    
  · have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : Set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
      h.1 ((mul_inv_self a).trans (mul_inv_self b).symm)
    exact subtype.ext_iff.mp (prod.ext_iff.mp this).1
    
  · rintro ⟨g, rfl⟩
    exact is_complement_singleton_top
    
#align subgroup.is_complement_top_right Subgroup.is_complement_top_right

@[to_additive]
theorem is_complement'_top_bot : IsComplement' (⊤ : Subgroup G) ⊥ :=
  is_complement_top_singleton
#align subgroup.is_complement'_top_bot Subgroup.is_complement'_top_bot

@[to_additive]
theorem is_complement'_bot_top : IsComplement' (⊥ : Subgroup G) ⊤ :=
  is_complement_singleton_top
#align subgroup.is_complement'_bot_top Subgroup.is_complement'_bot_top

@[simp, to_additive]
theorem is_complement'_bot_left : IsComplement' ⊥ H ↔ H = ⊤ :=
  is_complement_singleton_left.trans coe_eq_univ
#align subgroup.is_complement'_bot_left Subgroup.is_complement'_bot_left

@[simp, to_additive]
theorem is_complement'_bot_right : IsComplement' H ⊥ ↔ H = ⊤ :=
  is_complement_singleton_right.trans coe_eq_univ
#align subgroup.is_complement'_bot_right Subgroup.is_complement'_bot_right

@[simp, to_additive]
theorem is_complement'_top_left : IsComplement' ⊤ H ↔ H = ⊥ :=
  is_complement_top_left.trans coe_eq_singleton
#align subgroup.is_complement'_top_left Subgroup.is_complement'_top_left

@[simp, to_additive]
theorem is_complement'_top_right : IsComplement' H ⊤ ↔ H = ⊥ :=
  is_complement_top_right.trans coe_eq_singleton
#align subgroup.is_complement'_top_right Subgroup.is_complement'_top_right

@[to_additive]
theorem mem_left_transversals_iff_exists_unique_inv_mul_mem :
    S ∈ leftTransversals T ↔ ∀ g : G, ∃! s : S, (s : G)⁻¹ * g ∈ T := by
  rw [left_transversals, Set.mem_set_of_eq, is_complement_iff_exists_unique]
  refine' ⟨fun h g => _, fun h g => _⟩
  · obtain ⟨x, h1, h2⟩ := h g
    exact
      ⟨x.1, (congr_arg (· ∈ T) (eq_inv_mul_of_mul_eq h1)).mp x.2.2, fun y hy =>
        (prod.ext_iff.mp (h2 ⟨y, y⁻¹ * g, hy⟩ (mul_inv_cancel_left y g))).1⟩
    
  · obtain ⟨x, h1, h2⟩ := h g
    refine' ⟨⟨x, x⁻¹ * g, h1⟩, mul_inv_cancel_left x g, fun y hy => _⟩
    have := h2 y.1 ((congr_arg (· ∈ T) (eq_inv_mul_of_mul_eq hy)).mp y.2.2)
    exact Prod.ext this (Subtype.ext (eq_inv_mul_of_mul_eq ((congr_arg _ this).mp hy)))
    
#align
  subgroup.mem_left_transversals_iff_exists_unique_inv_mul_mem Subgroup.mem_left_transversals_iff_exists_unique_inv_mul_mem

@[to_additive]
theorem mem_right_transversals_iff_exists_unique_mul_inv_mem :
    S ∈ rightTransversals T ↔ ∀ g : G, ∃! s : S, g * (s : G)⁻¹ ∈ T := by
  rw [right_transversals, Set.mem_set_of_eq, is_complement_iff_exists_unique]
  refine' ⟨fun h g => _, fun h g => _⟩
  · obtain ⟨x, h1, h2⟩ := h g
    exact
      ⟨x.2, (congr_arg (· ∈ T) (eq_mul_inv_of_mul_eq h1)).mp x.1.2, fun y hy =>
        (prod.ext_iff.mp (h2 ⟨⟨g * y⁻¹, hy⟩, y⟩ (inv_mul_cancel_right g y))).2⟩
    
  · obtain ⟨x, h1, h2⟩ := h g
    refine' ⟨⟨⟨g * x⁻¹, h1⟩, x⟩, inv_mul_cancel_right g x, fun y hy => _⟩
    have := h2 y.2 ((congr_arg (· ∈ T) (eq_mul_inv_of_mul_eq hy)).mp y.1.2)
    exact Prod.ext (Subtype.ext (eq_mul_inv_of_mul_eq ((congr_arg _ this).mp hy))) this
    
#align
  subgroup.mem_right_transversals_iff_exists_unique_mul_inv_mem Subgroup.mem_right_transversals_iff_exists_unique_mul_inv_mem

@[to_additive]
theorem mem_left_transversals_iff_exists_unique_quotient_mk'_eq :
    S ∈ leftTransversals (H : Set G) ↔ ∀ q : Quotient (QuotientGroup.leftRel H), ∃! s : S, Quotient.mk' s.1 = q := by
  simp_rw [mem_left_transversals_iff_exists_unique_inv_mul_mem, SetLike.mem_coe, ← QuotientGroup.eq']
  exact ⟨fun h q => Quotient.inductionOn' q h, fun h g => h (Quotient.mk' g)⟩
#align
  subgroup.mem_left_transversals_iff_exists_unique_quotient_mk'_eq Subgroup.mem_left_transversals_iff_exists_unique_quotient_mk'_eq

@[to_additive]
theorem mem_right_transversals_iff_exists_unique_quotient_mk'_eq :
    S ∈ rightTransversals (H : Set G) ↔ ∀ q : Quotient (QuotientGroup.rightRel H), ∃! s : S, Quotient.mk' s.1 = q := by
  simp_rw [mem_right_transversals_iff_exists_unique_mul_inv_mem, SetLike.mem_coe, ← QuotientGroup.right_rel_apply, ←
    Quotient.eq']
  exact ⟨fun h q => Quotient.inductionOn' q h, fun h g => h (Quotient.mk' g)⟩
#align
  subgroup.mem_right_transversals_iff_exists_unique_quotient_mk'_eq Subgroup.mem_right_transversals_iff_exists_unique_quotient_mk'_eq

@[to_additive]
theorem mem_left_transversals_iff_bijective :
    S ∈ leftTransversals (H : Set G) ↔
      Function.Bijective (S.restrict (Quotient.mk' : G → Quotient (QuotientGroup.leftRel H))) :=
  mem_left_transversals_iff_exists_unique_quotient_mk'_eq.trans
    (Function.bijective_iff_existsUnique (S.restrict Quotient.mk')).symm
#align subgroup.mem_left_transversals_iff_bijective Subgroup.mem_left_transversals_iff_bijective

@[to_additive]
theorem mem_right_transversals_iff_bijective :
    S ∈ rightTransversals (H : Set G) ↔
      Function.Bijective (S.restrict (Quotient.mk' : G → Quotient (QuotientGroup.rightRel H))) :=
  mem_right_transversals_iff_exists_unique_quotient_mk'_eq.trans
    (Function.bijective_iff_existsUnique (S.restrict Quotient.mk')).symm
#align subgroup.mem_right_transversals_iff_bijective Subgroup.mem_right_transversals_iff_bijective

@[to_additive]
theorem card_left_transversal (h : S ∈ leftTransversals (H : Set G)) : Nat.card S = H.index :=
  Nat.card_congr $ Equiv.ofBijective _ $ mem_left_transversals_iff_bijective.mp h
#align subgroup.card_left_transversal Subgroup.card_left_transversal

@[to_additive]
theorem card_right_transversal (h : S ∈ rightTransversals (H : Set G)) : Nat.card S = H.index :=
  Nat.card_congr $
    (Equiv.ofBijective _ $ mem_right_transversals_iff_bijective.mp h).trans $
      QuotientGroup.quotientRightRelEquivQuotientLeftRel H
#align subgroup.card_right_transversal Subgroup.card_right_transversal

@[to_additive]
theorem range_mem_left_transversals {f : G ⧸ H → G} (hf : ∀ q, ↑(f q) = q) :
    Set.range f ∈ leftTransversals (H : Set G) :=
  mem_left_transversals_iff_bijective.mpr
    ⟨by rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h <;> exact congr_arg _ (((hf q₁).symm.trans h).trans (hf q₂)), fun q =>
      ⟨⟨f q, q, rfl⟩, hf q⟩⟩
#align subgroup.range_mem_left_transversals Subgroup.range_mem_left_transversals

@[to_additive]
theorem range_mem_right_transversals {f : Quotient (QuotientGroup.rightRel H) → G} (hf : ∀ q, Quotient.mk' (f q) = q) :
    Set.range f ∈ rightTransversals (H : Set G) :=
  mem_right_transversals_iff_bijective.mpr
    ⟨by rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h <;> exact congr_arg _ (((hf q₁).symm.trans h).trans (hf q₂)), fun q =>
      ⟨⟨f q, q, rfl⟩, hf q⟩⟩
#align subgroup.range_mem_right_transversals Subgroup.range_mem_right_transversals

@[to_additive]
theorem exists_left_transversal (g : G) : ∃ S ∈ leftTransversals (H : Set G), g ∈ S := by classical
  refine'
    ⟨Set.range (Function.update Quotient.out' (↑g) g), range_mem_left_transversals fun q => _, g,
      Function.update_same g g Quotient.out'⟩
  by_cases hq:q = g
  · exact hq.symm ▸ congr_arg _ (Function.update_same g g Quotient.out')
    
  · exact Eq.trans (congr_arg _ (Function.update_noteq hq g Quotient.out')) q.out_eq'
    
#align subgroup.exists_left_transversal Subgroup.exists_left_transversal

@[to_additive]
theorem exists_right_transversal (g : G) : ∃ S ∈ rightTransversals (H : Set G), g ∈ S := by classical
  refine'
    ⟨Set.range (Function.update Quotient.out' _ g), range_mem_right_transversals fun q => _, Quotient.mk' g,
      Function.update_same (Quotient.mk' g) g Quotient.out'⟩
  by_cases hq:q = Quotient.mk' g
  · exact hq.symm ▸ congr_arg _ (Function.update_same (Quotient.mk' g) g Quotient.out')
    
  · exact Eq.trans (congr_arg _ (Function.update_noteq hq g Quotient.out')) q.out_eq'
    
#align subgroup.exists_right_transversal Subgroup.exists_right_transversal

namespace MemLeftTransversals

/-- A left transversal is in bijection with left cosets. -/
@[to_additive "A left transversal is in bijection with left cosets."]
noncomputable def toEquiv (hS : S ∈ Subgroup.leftTransversals (H : Set G)) : G ⧸ H ≃ S :=
  (Equiv.ofBijective _ (Subgroup.mem_left_transversals_iff_bijective.mp hS)).symm
#align subgroup.mem_left_transversals.to_equiv Subgroup.MemLeftTransversals.toEquiv

@[to_additive]
theorem mk'_to_equiv (hS : S ∈ Subgroup.leftTransversals (H : Set G)) (q : G ⧸ H) :
    Quotient.mk' (toEquiv hS q : G) = q :=
  (toEquiv hS).symm_apply_apply q
#align subgroup.mem_left_transversals.mk'_to_equiv Subgroup.MemLeftTransversals.mk'_to_equiv

@[to_additive]
theorem to_equiv_apply {f : G ⧸ H → G} (hf : ∀ q, (f q : G ⧸ H) = q) (q : G ⧸ H) :
    (toEquiv (range_mem_left_transversals hf) q : G) = f q := by
  refine' (subtype.ext_iff.mp _).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (to_equiv (range_mem_left_transversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm
#align subgroup.mem_left_transversals.to_equiv_apply Subgroup.MemLeftTransversals.to_equiv_apply

/-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/
@[to_additive
      "A left transversal can be viewed as a function mapping each element of the group\n  to the chosen representative from that left coset."]
noncomputable def toFun (hS : S ∈ Subgroup.leftTransversals (H : Set G)) : G → S :=
  toEquiv hS ∘ Quotient.mk'
#align subgroup.mem_left_transversals.to_fun Subgroup.MemLeftTransversals.toFun

@[to_additive]
theorem inv_to_fun_mul_mem (hS : S ∈ Subgroup.leftTransversals (H : Set G)) (g : G) : (toFun hS g : G)⁻¹ * g ∈ H :=
  QuotientGroup.left_rel_apply.mp $ Quotient.exact' $ mk'_to_equiv _ _
#align subgroup.mem_left_transversals.inv_to_fun_mul_mem Subgroup.MemLeftTransversals.inv_to_fun_mul_mem

@[to_additive]
theorem inv_mul_to_fun_mem (hS : S ∈ Subgroup.leftTransversals (H : Set G)) (g : G) : g⁻¹ * toFun hS g ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (inv_to_fun_mul_mem hS g))
#align subgroup.mem_left_transversals.inv_mul_to_fun_mem Subgroup.MemLeftTransversals.inv_mul_to_fun_mem

end MemLeftTransversals

namespace MemRightTransversals

/-- A right transversal is in bijection with right cosets. -/
@[to_additive "A right transversal is in bijection with right cosets."]
noncomputable def toEquiv (hS : S ∈ Subgroup.rightTransversals (H : Set G)) : Quotient (QuotientGroup.rightRel H) ≃ S :=
  (Equiv.ofBijective _ (Subgroup.mem_right_transversals_iff_bijective.mp hS)).symm
#align subgroup.mem_right_transversals.to_equiv Subgroup.MemRightTransversals.toEquiv

@[to_additive]
theorem mk'_to_equiv (hS : S ∈ Subgroup.rightTransversals (H : Set G)) (q : Quotient (QuotientGroup.rightRel H)) :
    Quotient.mk' (toEquiv hS q : G) = q :=
  (toEquiv hS).symm_apply_apply q
#align subgroup.mem_right_transversals.mk'_to_equiv Subgroup.MemRightTransversals.mk'_to_equiv

@[to_additive]
theorem to_equiv_apply {f : Quotient (QuotientGroup.rightRel H) → G} (hf : ∀ q, Quotient.mk' (f q) = q)
    (q : Quotient (QuotientGroup.rightRel H)) : (toEquiv (range_mem_right_transversals hf) q : G) = f q := by
  refine' (subtype.ext_iff.mp _).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (to_equiv (range_mem_right_transversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm
#align subgroup.mem_right_transversals.to_equiv_apply Subgroup.MemRightTransversals.to_equiv_apply

/-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/
@[to_additive
      "A right transversal can be viewed as a function mapping each element of the group\n  to the chosen representative from that right coset."]
noncomputable def toFun (hS : S ∈ Subgroup.rightTransversals (H : Set G)) : G → S :=
  toEquiv hS ∘ Quotient.mk'
#align subgroup.mem_right_transversals.to_fun Subgroup.MemRightTransversals.toFun

@[to_additive]
theorem mul_inv_to_fun_mem (hS : S ∈ Subgroup.rightTransversals (H : Set G)) (g : G) : g * (toFun hS g : G)⁻¹ ∈ H :=
  QuotientGroup.right_rel_apply.mp $ Quotient.exact' $ mk'_to_equiv _ _
#align subgroup.mem_right_transversals.mul_inv_to_fun_mem Subgroup.MemRightTransversals.mul_inv_to_fun_mem

@[to_additive]
theorem to_fun_mul_inv_mem (hS : S ∈ Subgroup.rightTransversals (H : Set G)) (g : G) : (toFun hS g : G) * g⁻¹ ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (mul_inv_to_fun_mem hS g))
#align subgroup.mem_right_transversals.to_fun_mul_inv_mem Subgroup.MemRightTransversals.to_fun_mul_inv_mem

end MemRightTransversals

section Action

open Pointwise

open MulAction MemLeftTransversals

variable {F : Type _} [Group F] [MulAction F G] [QuotientAction F H]

@[to_additive]
instance : MulAction F (leftTransversals (H : Set G)) where
  smul f T :=
    ⟨f • T, by
      refine' mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr fun g => _
      obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (f⁻¹ • g)
      refine' ⟨⟨f • t, Set.smul_mem_smul_set t.2⟩, _, _⟩
      · exact (congr_arg _ (smul_inv_smul f g)).mp (quotient_action.inv_mul_mem f ht1)
        
      · rintro ⟨-, t', ht', rfl⟩ h
        replace h := quotient_action.inv_mul_mem f⁻¹ h
        simp only [Subtype.ext_iff, Subtype.coe_mk, smul_left_cancel_iff, inv_smul_smul] at h⊢
        exact subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)
        ⟩
  one_smul T := Subtype.ext (one_smul F T)
  mul_smul f₁ f₂ T := Subtype.ext (mul_smul f₁ f₂ T)

@[to_additive]
theorem smul_to_fun (f : F) (T : leftTransversals (H : Set G)) (g : G) :
    (f • toFun T.2 g : G) = toFun (f • T).2 (f • g) :=
  Subtype.ext_iff.mp $
    @ExistsUnique.unique (↥(f • T)) (fun s => (↑s)⁻¹ * f • g ∈ H)
      (mem_left_transversals_iff_exists_unique_inv_mul_mem.mp (f • T).2 (f • g))
      ⟨f • toFun T.2 g, Set.smul_mem_smul_set (Subtype.coe_prop _)⟩ (toFun (f • T).2 (f • g))
      (QuotientAction.inv_mul_mem f (inv_to_fun_mul_mem T.2 g)) (inv_to_fun_mul_mem (f • T).2 (f • g))
#align subgroup.smul_to_fun Subgroup.smul_to_fun

@[to_additive]
theorem smul_to_equiv (f : F) (T : leftTransversals (H : Set G)) (q : G ⧸ H) :
    f • (toEquiv T.2 q : G) = toEquiv (f • T).2 (f • q) :=
  Quotient.inductionOn' q fun g => smul_to_fun f T g
#align subgroup.smul_to_equiv Subgroup.smul_to_equiv

@[to_additive]
theorem smul_apply_eq_smul_apply_inv_smul (f : F) (T : leftTransversals (H : Set G)) (q : G ⧸ H) :
    (toEquiv (f • T).2 q : G) = f • (toEquiv T.2 (f⁻¹ • q) : G) := by rw [smul_to_equiv, smul_inv_smul]
#align subgroup.smul_apply_eq_smul_apply_inv_smul Subgroup.smul_apply_eq_smul_apply_inv_smul

end Action

@[to_additive]
instance : Inhabited (leftTransversals (H : Set G)) :=
  ⟨⟨Set.range Quotient.out', range_mem_left_transversals Quotient.out_eq'⟩⟩

@[to_additive]
instance : Inhabited (rightTransversals (H : Set G)) :=
  ⟨⟨Set.range Quotient.out', range_mem_right_transversals Quotient.out_eq'⟩⟩

theorem IsComplement'.is_compl (h : IsComplement' H K) : IsCompl H K := by
  refine'
    ⟨disjoint_iff_inf_le.mpr $ fun g ⟨p, q⟩ =>
        let x : H × K := ⟨⟨g, p⟩, 1⟩
        let y : H × K := ⟨1, g, q⟩
        subtype.ext_iff.mp (prod.ext_iff.mp (show x = y from h.1 ((mul_one g).trans (one_mul g).symm))).1,
      codisjoint_iff_le_sup.mpr $ fun g _ => _⟩
  obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g
  exact Subgroup.mul_mem_sup h.2 k.2
#align subgroup.is_complement'.is_compl Subgroup.IsComplement'.is_compl

theorem IsComplement'.sup_eq_top (h : IsComplement' H K) : H ⊔ K = ⊤ :=
  h.IsCompl.sup_eq_top
#align subgroup.is_complement'.sup_eq_top Subgroup.IsComplement'.sup_eq_top

theorem IsComplement'.disjoint (h : IsComplement' H K) : Disjoint H K :=
  h.IsCompl.Disjoint
#align subgroup.is_complement'.disjoint Subgroup.IsComplement'.disjoint

theorem IsComplement'.index_eq_card (h : IsComplement' H K) : K.index = Nat.card H :=
  (card_left_transversal h).symm
#align subgroup.is_complement'.index_eq_card Subgroup.IsComplement'.index_eq_card

theorem IsComplement.card_mul [Fintype G] [Fintype S] [Fintype T] (h : IsComplement S T) :
    Fintype.card S * Fintype.card T = Fintype.card G :=
  (Fintype.card_prod _ _).symm.trans (Fintype.card_of_bijective h)
#align subgroup.is_complement.card_mul Subgroup.IsComplement.card_mul

theorem IsComplement'.card_mul [Fintype G] [Fintype H] [Fintype K] (h : IsComplement' H K) :
    Fintype.card H * Fintype.card K = Fintype.card G :=
  h.card_mul
#align subgroup.is_complement'.card_mul Subgroup.IsComplement'.card_mul

theorem is_complement'_of_disjoint_and_mul_eq_univ (h1 : Disjoint H K) (h2 : ↑H * ↑K = (Set.univ : Set G)) :
    IsComplement' H K := by
  refine' ⟨mul_injective_of_disjoint h1, fun g => _⟩
  obtain ⟨h, k, hh, hk, hg⟩ := set.eq_univ_iff_forall.mp h2 g
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hg⟩
#align subgroup.is_complement'_of_disjoint_and_mul_eq_univ Subgroup.is_complement'_of_disjoint_and_mul_eq_univ

theorem is_complement'_of_card_mul_and_disjoint [Fintype G] [Fintype H] [Fintype K]
    (h1 : Fintype.card H * Fintype.card K = Fintype.card G) (h2 : Disjoint H K) : IsComplement' H K :=
  (Fintype.bijective_iff_injective_and_card _).mpr ⟨mul_injective_of_disjoint h2, (Fintype.card_prod H K).trans h1⟩
#align subgroup.is_complement'_of_card_mul_and_disjoint Subgroup.is_complement'_of_card_mul_and_disjoint

theorem is_complement'_iff_card_mul_and_disjoint [Fintype G] [Fintype H] [Fintype K] :
    IsComplement' H K ↔ Fintype.card H * Fintype.card K = Fintype.card G ∧ Disjoint H K :=
  ⟨fun h => ⟨h.card_mul, h.Disjoint⟩, fun h => is_complement'_of_card_mul_and_disjoint h.1 h.2⟩
#align subgroup.is_complement'_iff_card_mul_and_disjoint Subgroup.is_complement'_iff_card_mul_and_disjoint

theorem is_complement'_of_coprime [Fintype G] [Fintype H] [Fintype K]
    (h1 : Fintype.card H * Fintype.card K = Fintype.card G) (h2 : Nat.Coprime (Fintype.card H) (Fintype.card K)) :
    IsComplement' H K :=
  is_complement'_of_card_mul_and_disjoint h1 (disjoint_iff.mpr (inf_eq_bot_of_coprime h2))
#align subgroup.is_complement'_of_coprime Subgroup.is_complement'_of_coprime

theorem is_complement'_stabilizer {α : Type _} [MulAction G α] (a : α) (h1 : ∀ h : H, h • a = a → h = 1)
    (h2 : ∀ g : G, ∃ h : H, h • g • a = a) : IsComplement' H (MulAction.stabilizer G a) := by
  refine' is_complement_iff_exists_unique.mpr fun g => _
  obtain ⟨h, hh⟩ := h2 g
  have hh' : (↑h * g) • a = a := by rwa [mul_smul]
  refine' ⟨⟨h⁻¹, h * g, hh'⟩, inv_mul_cancel_left h g, _⟩
  rintro ⟨h', g, hg : g • a = a⟩ rfl
  specialize h1 (h * h') (by rwa [mul_smul, smul_def h', ← hg, ← mul_smul, hg])
  refine' Prod.ext (eq_inv_of_mul_eq_one_right h1) (Subtype.ext _)
  rwa [Subtype.ext_iff, coe_one, coe_mul, ← self_eq_mul_left, mul_assoc (↑h) (↑h') g] at h1
#align subgroup.is_complement'_stabilizer Subgroup.is_complement'_stabilizer

end Subgroup

namespace Subgroup

open Equiv Function MemLeftTransversals MulAction MulAction.quotient Zmod

universe u

variable {G : Type u} [Group G] (H : Subgroup G) (g : G)

/-- Partition `G ⧸ H` into orbits of the action of `g : G`. -/
noncomputable def quotientEquivSigmaZmod :
    G ⧸ H ≃ Σ q : orbitRel.Quotient (zpowers g) (G ⧸ H), Zmod (minimalPeriod ((· • ·) g) q.out') :=
  (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)).trans (sigmaCongrRight fun q => orbitZpowersEquiv g q.out')
#align subgroup.quotient_equiv_sigma_zmod Subgroup.quotientEquivSigmaZmod

theorem quotient_equiv_sigma_zmod_symm_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : Zmod (minimalPeriod ((· • ·) g) q.out')) : (quotientEquivSigmaZmod H g).symm ⟨q, k⟩ = g ^ (k : ℤ) • q.out' :=
  rfl
#align subgroup.quotient_equiv_sigma_zmod_symm_apply Subgroup.quotient_equiv_sigma_zmod_symm_apply

theorem quotient_equiv_sigma_zmod_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : ℤ) :
    quotientEquivSigmaZmod H g (g ^ k • q.out') = ⟨q, k⟩ := by
  rw [apply_eq_iff_eq_symm_apply, quotient_equiv_sigma_zmod_symm_apply, Zmod.coe_int_cast, zpow_smul_mod_minimal_period]
#align subgroup.quotient_equiv_sigma_zmod_apply Subgroup.quotient_equiv_sigma_zmod_apply

/-- The transfer transversal as a function. Given a `⟨g⟩`-orbit `q₀, g • q₀, ..., g ^ (m - 1) • q₀`
  in `G ⧸ H`, an element `g ^ k • q₀` is mapped to `g ^ k • g₀` for a fixed choice of
  representative `g₀` of `q₀`. -/
noncomputable def transferFunction : G ⧸ H → G := fun q =>
  g ^ ((quotientEquivSigmaZmod H g q).2 : ℤ) * (quotientEquivSigmaZmod H g q).1.out'.out'
#align subgroup.transfer_function Subgroup.transferFunction

theorem transfer_function_apply (q : G ⧸ H) :
    transferFunction H g q = g ^ ((quotientEquivSigmaZmod H g q).2 : ℤ) * (quotientEquivSigmaZmod H g q).1.out'.out' :=
  rfl
#align subgroup.transfer_function_apply Subgroup.transfer_function_apply

theorem coe_transfer_function (q : G ⧸ H) : ↑(transferFunction H g q) = q := by
  rw [transfer_function_apply, ← smul_eq_mul, coe_smul_out', ← quotient_equiv_sigma_zmod_symm_apply, Sigma.eta,
    symm_apply_apply]
#align subgroup.coe_transfer_function Subgroup.coe_transfer_function

/-- The transfer transversal as a set. Contains elements of the form `g ^ k • g₀` for fixed choices
  of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transferSet : Set G :=
  Set.range (transferFunction H g)
#align subgroup.transfer_set Subgroup.transferSet

theorem mem_transfer_set (q : G ⧸ H) : transferFunction H g q ∈ transferSet H g :=
  ⟨q, rfl⟩
#align subgroup.mem_transfer_set Subgroup.mem_transfer_set

/-- The transfer transversal. Contains elements of the form `g ^ k • g₀` for fixed choices
  of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transferTransversal : leftTransversals (H : Set G) :=
  ⟨transferSet H g, range_mem_left_transversals (coe_transfer_function H g)⟩
#align subgroup.transfer_transversal Subgroup.transferTransversal

theorem transfer_transversal_apply (q : G ⧸ H) : ↑(toEquiv (transferTransversal H g).2 q) = transferFunction H g q :=
  to_equiv_apply (coe_transfer_function H g) q
#align subgroup.transfer_transversal_apply Subgroup.transfer_transversal_apply

theorem transfer_transversal_apply' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : Zmod (minimalPeriod ((· • ·) g) q.out')) :
    ↑(toEquiv (transferTransversal H g).2 (g ^ (k : ℤ) • q.out')) = g ^ (k : ℤ) * q.out'.out' := by
  rw [transfer_transversal_apply, transfer_function_apply, ← quotient_equiv_sigma_zmod_symm_apply, apply_symm_apply]
#align subgroup.transfer_transversal_apply' Subgroup.transfer_transversal_apply'

theorem transfer_transversal_apply'' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : Zmod (minimalPeriod ((· • ·) g) q.out')) :
    ↑(toEquiv (g • transferTransversal H g).2 (g ^ (k : ℤ) • q.out')) =
      if k = 0 then g ^ minimalPeriod ((· • ·) g) q.out' * q.out'.out' else g ^ (k : ℤ) * q.out'.out' :=
  by
  rw [smul_apply_eq_smul_apply_inv_smul, transfer_transversal_apply, transfer_function_apply, ← mul_smul, ←
    zpow_neg_one, ← zpow_add, quotient_equiv_sigma_zmod_apply, smul_eq_mul, ← mul_assoc, ← zpow_one_add, Int.cast_add,
    Int.cast_neg, Int.cast_one, int_cast_cast, cast_id', id.def, ← sub_eq_neg_add, cast_sub_one, add_sub_cancel'_right]
  by_cases hk:k = 0
  · rw [if_pos hk, if_pos hk, zpow_coe_nat]
    
  · rw [if_neg hk, if_neg hk]
    
#align subgroup.transfer_transversal_apply'' Subgroup.transfer_transversal_apply''

end Subgroup

