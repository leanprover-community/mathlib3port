/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.GroupTheory.OrderOfElement

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

## Main results

- `is_complement_of_coprime` : Subgroups of coprime order are complements.
-/


open_locale BigOperators

namespace Subgroup

variable {G : Type _} [Groupₓ G] (H K : Subgroup G) (S T : Set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
  This notion generalizes left transversals, right transversals, and complementary subgroups. -/
@[to_additive "`S` and `T` are complements if `(*) : S × T → G` is a bijection"]
def IsComplement : Prop :=
  Function.Bijective fun x : S × T => x.1.1 * x.2.1

/-- `H` and `K` are complements if `(*) : H × K → G` is a bijection -/
@[to_additive "`H` and `K` are complements if `(*) : H × K → G` is a bijection"]
abbrev IsComplement' :=
  IsComplement (H : Set G) (K : Set G)

/-- The set of left-complements of `T : set G` -/
@[to_additive "The set of left-complements of `T : set G`"]
def LeftTransversals : Set (Set G) :=
  { S : Set G | IsComplement S T }

/-- The set of right-complements of `S : set G` -/
@[to_additive "The set of right-complements of `S : set G`"]
def RightTransversals : Set (Set G) :=
  { T : Set G | IsComplement S T }

variable {H K S T}

@[to_additive]
theorem is_complement'_def : IsComplement' H K ↔ IsComplement (H : Set G) (K : Set G) :=
  Iff.rfl

@[to_additive]
theorem is_complement_iff_exists_unique : IsComplement S T ↔ ∀ g : G, ∃! x : S × T, x.1.1 * x.2.1 = g :=
  Function.bijective_iff_exists_unique _

@[to_additive]
theorem IsComplement.exists_unique (h : IsComplement S T) (g : G) : ∃! x : S × T, x.1.1 * x.2.1 = g :=
  is_complement_iff_exists_unique.mp h g

@[to_additive]
theorem IsComplement'.symm (h : IsComplement' H K) : IsComplement' K H := by
  let ϕ : H × K ≃ K × H :=
    Equivₓ.mk (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => Prod.extₓ (inv_invₓ _) (inv_invₓ _))
      fun x => Prod.extₓ (inv_invₓ _) (inv_invₓ _)
  let ψ : G ≃ G := Equivₓ.mk (fun g : G => g⁻¹) (fun g : G => g⁻¹) inv_invₓ inv_invₓ
  suffices (ψ ∘ fun x : H × K => x.1.1 * x.2.1) = (fun x : K × H => x.1.1 * x.2.1) ∘ ϕ by
    rwa [is_complement'_def, is_complement, ← Equivₓ.bijective_comp, ← this, Equivₓ.comp_bijective]
  exact funext fun x => mul_inv_rev _ _

@[to_additive]
theorem is_complement'_comm : IsComplement' H K ↔ IsComplement' K H :=
  ⟨IsComplement'.symm, IsComplement'.symm⟩

@[to_additive]
theorem is_complement_top_singleton {g : G} : IsComplement (⊤ : Set G) {g} :=
  ⟨fun h => Prod.extₓ (Subtype.ext (mul_right_cancelₓ h)) rfl, fun x =>
    ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩

@[to_additive]
theorem is_complement_singleton_top {g : G} : IsComplement ({g} : Set G) ⊤ :=
  ⟨fun h => Prod.extₓ rfl (Subtype.ext (mul_left_cancelₓ h)), fun x =>
    ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩

@[to_additive]
theorem is_complement_singleton_left {g : G} : IsComplement {g} S ↔ S = ⊤ := by
  refine' ⟨fun h => top_le_iff.mp fun x hx => _, fun h => (congr_argₓ _ h).mpr is_complement_singleton_top⟩
  obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x)
  rwa [← mul_left_cancelₓ hy]

@[to_additive]
theorem is_complement_singleton_right {g : G} : IsComplement S {g} ↔ S = ⊤ := by
  refine' ⟨fun h => top_le_iff.mp fun x hx => _, fun h => (congr_argₓ _ h).mpr is_complement_top_singleton⟩
  obtain ⟨y, hy⟩ := h.2 (x * g)
  conv_rhs at hy => rw [← show y.2.1 = g from y.2.2]
  rw [← mul_right_cancelₓ hy]
  exact y.1.2

@[to_additive]
theorem is_complement_top_left : IsComplement ⊤ S ↔ ∃ g : G, S = {g} := by
  refine' ⟨fun h => set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, fun a ha b hb => _⟩, _⟩
  · obtain ⟨a, ha⟩ := h.2 1
    exact ⟨a.2.1, a.2.2⟩
    
  · have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : Set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
      h.1 ((inv_mul_selfₓ a).trans (inv_mul_selfₓ b).symm)
    exact subtype.ext_iff.mp (prod.ext_iff.mp this).2
    
  · rintro ⟨g, rfl⟩
    exact is_complement_top_singleton
    

@[to_additive]
theorem is_complement_top_right : IsComplement S ⊤ ↔ ∃ g : G, S = {g} := by
  refine' ⟨fun h => set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, fun a ha b hb => _⟩, _⟩
  · obtain ⟨a, ha⟩ := h.2 1
    exact ⟨a.1.1, a.1.2⟩
    
  · have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : Set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
      h.1 ((mul_inv_selfₓ a).trans (mul_inv_selfₓ b).symm)
    exact subtype.ext_iff.mp (prod.ext_iff.mp this).1
    
  · rintro ⟨g, rfl⟩
    exact is_complement_singleton_top
    

@[to_additive]
theorem is_complement'_top_bot : IsComplement' (⊤ : Subgroup G) ⊥ :=
  is_complement_top_singleton

@[to_additive]
theorem is_complement'_bot_top : IsComplement' (⊥ : Subgroup G) ⊤ :=
  is_complement_singleton_top

@[simp, to_additive]
theorem is_complement'_bot_left : IsComplement' ⊥ H ↔ H = ⊤ :=
  is_complement_singleton_left.trans coe_eq_univ

@[simp, to_additive]
theorem is_complement'_bot_right : IsComplement' H ⊥ ↔ H = ⊤ :=
  is_complement_singleton_right.trans coe_eq_univ

@[simp, to_additive]
theorem is_complement'_top_left : IsComplement' ⊤ H ↔ H = ⊥ :=
  is_complement_top_left.trans coe_eq_singleton

@[simp, to_additive]
theorem is_complement'_top_right : IsComplement' H ⊤ ↔ H = ⊥ :=
  is_complement_top_right.trans coe_eq_singleton

@[to_additive]
theorem mem_left_transversals_iff_exists_unique_inv_mul_mem :
    S ∈ LeftTransversals T ↔ ∀ g : G, ∃! s : S, (s : G)⁻¹ * g ∈ T := by
  rw [left_transversals, Set.mem_set_of_eq, is_complement_iff_exists_unique]
  refine' ⟨fun h g => _, fun h g => _⟩
  · obtain ⟨x, h1, h2⟩ := h g
    exact
      ⟨x.1, (congr_argₓ (· ∈ T) (eq_inv_mul_of_mul_eq h1)).mp x.2.2, fun y hy =>
        (prod.ext_iff.mp (h2 ⟨y, y⁻¹ * g, hy⟩ (mul_inv_cancel_left y g))).1⟩
    
  · obtain ⟨x, h1, h2⟩ := h g
    refine' ⟨⟨x, x⁻¹ * g, h1⟩, mul_inv_cancel_left x g, fun y hy => _⟩
    have := h2 y.1 ((congr_argₓ (· ∈ T) (eq_inv_mul_of_mul_eq hy)).mp y.2.2)
    exact Prod.extₓ this (Subtype.ext (eq_inv_mul_of_mul_eq ((congr_argₓ _ this).mp hy)))
    

@[to_additive]
theorem mem_right_transversals_iff_exists_unique_mul_inv_mem :
    S ∈ RightTransversals T ↔ ∀ g : G, ∃! s : S, g * (s : G)⁻¹ ∈ T := by
  rw [right_transversals, Set.mem_set_of_eq, is_complement_iff_exists_unique]
  refine' ⟨fun h g => _, fun h g => _⟩
  · obtain ⟨x, h1, h2⟩ := h g
    exact
      ⟨x.2, (congr_argₓ (· ∈ T) (eq_mul_inv_of_mul_eq h1)).mp x.1.2, fun y hy =>
        (prod.ext_iff.mp (h2 ⟨⟨g * y⁻¹, hy⟩, y⟩ (inv_mul_cancel_right g y))).2⟩
    
  · obtain ⟨x, h1, h2⟩ := h g
    refine' ⟨⟨⟨g * x⁻¹, h1⟩, x⟩, inv_mul_cancel_right g x, fun y hy => _⟩
    have := h2 y.2 ((congr_argₓ (· ∈ T) (eq_mul_inv_of_mul_eq hy)).mp y.1.2)
    exact Prod.extₓ (Subtype.ext (eq_mul_inv_of_mul_eq ((congr_argₓ _ this).mp hy))) this
    

@[to_additive]
theorem mem_left_transversals_iff_exists_unique_quotient_mk'_eq :
    S ∈ LeftTransversals (H : Set G) ↔ ∀ q : Quotientₓ (QuotientGroup.leftRel H), ∃! s : S, Quotientₓ.mk' s.1 = q := by
  have key : ∀ g h, Quotientₓ.mk' g = Quotientₓ.mk' h ↔ g⁻¹ * h ∈ H := @Quotientₓ.eq' G (QuotientGroup.leftRel H)
  simp_rw [mem_left_transversals_iff_exists_unique_inv_mul_mem, SetLike.mem_coe, ← key]
  exact ⟨fun h q => Quotientₓ.induction_on' q h, fun h g => h (Quotientₓ.mk' g)⟩

@[to_additive]
theorem mem_right_transversals_iff_exists_unique_quotient_mk'_eq :
    S ∈ RightTransversals (H : Set G) ↔ ∀ q : Quotientₓ (QuotientGroup.rightRel H), ∃! s : S, Quotientₓ.mk' s.1 = q :=
  by
  have key : ∀ g h, Quotientₓ.mk' g = Quotientₓ.mk' h ↔ h * g⁻¹ ∈ H := @Quotientₓ.eq' G (QuotientGroup.rightRel H)
  simp_rw [mem_right_transversals_iff_exists_unique_mul_inv_mem, SetLike.mem_coe, ← key]
  exact ⟨fun h q => Quotientₓ.induction_on' q h, fun h g => h (Quotientₓ.mk' g)⟩

@[to_additive]
theorem mem_left_transversals_iff_bijective :
    S ∈ LeftTransversals (H : Set G) ↔
      Function.Bijective (S.restrict (Quotientₓ.mk' : G → Quotientₓ (QuotientGroup.leftRel H))) :=
  mem_left_transversals_iff_exists_unique_quotient_mk'_eq.trans
    (Function.bijective_iff_exists_unique (S.restrict Quotientₓ.mk')).symm

@[to_additive]
theorem mem_right_transversals_iff_bijective :
    S ∈ RightTransversals (H : Set G) ↔
      Function.Bijective (Set.restrict (Quotientₓ.mk' : G → Quotientₓ (QuotientGroup.rightRel H)) S) :=
  mem_right_transversals_iff_exists_unique_quotient_mk'_eq.trans
    (Function.bijective_iff_exists_unique (S.restrict Quotientₓ.mk')).symm

@[to_additive]
instance : Inhabited (LeftTransversals (H : Set G)) :=
  ⟨⟨Set.Range Quotientₓ.out',
      mem_left_transversals_iff_bijective.mpr
        ⟨by
          rintro ⟨_, q₁, rfl⟩ ⟨_, q₂, rfl⟩ hg
          rw [(q₁.out_eq'.symm.trans hg).trans q₂.out_eq'], fun q => ⟨⟨q.out', q, rfl⟩, Quotientₓ.out_eq' q⟩⟩⟩⟩

@[to_additive]
instance : Inhabited (RightTransversals (H : Set G)) :=
  ⟨⟨Set.Range Quotientₓ.out',
      mem_right_transversals_iff_bijective.mpr
        ⟨by
          rintro ⟨_, q₁, rfl⟩ ⟨_, q₂, rfl⟩ hg
          rw [(q₁.out_eq'.symm.trans hg).trans q₂.out_eq'], fun q => ⟨⟨q.out', q, rfl⟩, Quotientₓ.out_eq' q⟩⟩⟩⟩

theorem IsComplement'.is_compl (h : IsComplement' H K) : IsCompl H K := by
  refine'
    ⟨fun g ⟨p, q⟩ =>
      let x : H × K := ⟨⟨g, p⟩, 1⟩
      let y : H × K := ⟨1, g, q⟩
      subtype.ext_iff.mp (prod.ext_iff.mp (show x = y from h.1 ((mul_oneₓ g).trans (one_mulₓ g).symm))).1,
      fun g _ => _⟩
  obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g
  exact Subgroup.mul_mem_sup h.2 k.2

theorem IsComplement'.sup_eq_top (h : Subgroup.IsComplement' H K) : H⊔K = ⊤ :=
  h.IsCompl.sup_eq_top

theorem IsComplement'.disjoint (h : IsComplement' H K) : Disjoint H K :=
  h.IsCompl.Disjoint

theorem IsComplement.card_mul [Fintype G] [Fintype S] [Fintype T] (h : IsComplement S T) :
    Fintype.card S * Fintype.card T = Fintype.card G :=
  (Fintype.card_prod _ _).symm.trans (Fintype.card_of_bijective h)

theorem IsComplement'.card_mul [Fintype G] [Fintype H] [Fintype K] (h : IsComplement' H K) :
    Fintype.card H * Fintype.card K = Fintype.card G :=
  h.card_mul

theorem is_complement'_of_card_mul_and_disjoint [Fintype G] [Fintype H] [Fintype K]
    (h1 : Fintype.card H * Fintype.card K = Fintype.card G) (h2 : Disjoint H K) : IsComplement' H K := by
  refine' (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun x y h => _, (Fintype.card_prod H K).trans h1⟩
  rw [← eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_inv_eq_iff_eq_mul] at h
  change ↑(x.2 * y.2⁻¹) = ↑(x.1⁻¹ * y.1) at h
  rw [Prod.ext_iff, ← @inv_mul_eq_one H _ x.1 y.1, ← @mul_inv_eq_one K _ x.2 y.2, Subtype.ext_iff, Subtype.ext_iff,
    coe_one, coe_one, h, and_selfₓ, ← mem_bot, ← h2.eq_bot, mem_inf]
  exact ⟨Subtype.mem (x.1⁻¹ * y.1), (congr_argₓ (· ∈ K) h).mp (Subtype.mem (x.2 * y.2⁻¹))⟩

theorem is_complement'_iff_card_mul_and_disjoint [Fintype G] [Fintype H] [Fintype K] :
    IsComplement' H K ↔ Fintype.card H * Fintype.card K = Fintype.card G ∧ Disjoint H K :=
  ⟨fun h => ⟨h.card_mul, h.Disjoint⟩, fun h => is_complement'_of_card_mul_and_disjoint h.1 h.2⟩

theorem is_complement'_of_coprime [Fintype G] [Fintype H] [Fintype K]
    (h1 : Fintype.card H * Fintype.card K = Fintype.card G) (h2 : Nat.Coprime (Fintype.card H) (Fintype.card K)) :
    IsComplement' H K :=
  is_complement'_of_card_mul_and_disjoint h1 (disjoint_iff.mpr (inf_eq_bot_of_coprime h2))

end Subgroup

