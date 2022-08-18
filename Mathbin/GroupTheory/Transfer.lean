/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.GroupTheory.Complement
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.Index

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
- `transfer_center_pow`: The transfer homomorphism `G →*  center G`.
-/


open BigOperators

variable {G : Type _} [Groupₓ G] {H : Subgroup G} {A : Type _} [CommGroupₓ A] (ϕ : H →* A)

namespace Subgroup

namespace LeftTransversals

open Finset MulAction

open Pointwise

variable (R S T : LeftTransversals (H : Set G)) [Fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
  let α := MemLeftTransversals.toEquiv S.2
  let β := MemLeftTransversals.toEquiv T.2
  ∏ q,
    ϕ
      ⟨(α q)⁻¹ * β q,
        QuotientGroup.left_rel_apply.mp <| Quotientₓ.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive]
theorem diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
  prod_mul_distrib.symm.trans
    (prod_congr rfl fun q hq =>
      (ϕ.map_mul _ _).symm.trans
        (congr_arg ϕ
          (by
            simp_rw [Subtype.ext_iff, coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left])))

@[to_additive]
theorem diff_self : diff ϕ T T = 1 :=
  mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive]
theorem diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
  inv_eq_of_mul_eq_one_right <| (diff_mul_diff ϕ S T S).trans <| diff_self ϕ S

@[to_additive]
theorem smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
  prod_bij' (fun q _ => g⁻¹ • q) (fun _ _ => mem_univ _)
    (fun _ _ =>
      congr_arg ϕ
        (by
          simp_rw [coe_mk, smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc,
            inv_mul_cancel_leftₓ]))
    (fun q _ => g • q) (fun _ _ => mem_univ _) (fun q _ => smul_inv_smul g q) fun q _ => inv_smul_smul g q

end LeftTransversals

end Subgroup

namespace MonoidHom

open MulAction Subgroup Subgroup.LeftTransversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive
      "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,\nthe transfer homomorphism is `transfer ϕ : G →+ A`."]
noncomputable def transfer [Fintype (G ⧸ H)] : G →* A :=
  let T : LeftTransversals (H : Set G) := Inhabited.default
  { toFun := fun g => diff ϕ T (g • T),
    map_one' := by
      rw [one_smul, diff_self],
    map_mul' := fun g h => by
      rw [mul_smul, ← diff_mul_diff, smul_diff_smul] }

variable (T : LeftTransversals (H : Set G))

@[to_additive]
theorem transfer_def [Fintype (G ⧸ H)] (g : G) : transfer ϕ g = diff ϕ T (g • T) := by
  rw [transfer, ← diff_mul_diff, ← smul_diff_smul, mul_comm, diff_mul_diff] <;> rfl

/-- Explicit computation of the transfer homomorphism. -/
theorem transfer_eq_prod_quotient_orbit_rel_zpowers_quot [Fintype (G ⧸ H)] (g : G)
    [Fintype (Quotientₓ (orbitRel (zpowers g) (G ⧸ H)))] :
    transfer ϕ g =
      ∏ q : Quotientₓ (orbitRel (zpowers g) (G ⧸ H)),
        ϕ
          ⟨q.out'.out'⁻¹ * g ^ Function.minimalPeriod ((· • ·) g) q.out' * q.out'.out',
            QuotientGroup.out'_conj_pow_minimal_period_mem H g q.out'⟩ :=
  by
  classical
  calc
    transfer ϕ g = ∏ q : G ⧸ H, _ := transfer_def ϕ (transfer_transversal H g) g
    _ = _ := ((quotient_equiv_sigma_zmod H g).symm.prod_comp _).symm
    _ = _ := Finset.prod_sigma _ _ _
    _ = _ := Fintype.prod_congr _ _ fun q => _
    
  simp only [← quotient_equiv_sigma_zmod_symm_apply, ← transfer_transversal_apply', ← transfer_transversal_apply'']
  rw [Fintype.prod_eq_single (0 : Zmod (Function.minimalPeriod ((· • ·) g) q.out')) fun k hk => _]
  · simp only [← if_pos, ← Zmod.cast_zero, ← zpow_zero, ← one_mulₓ, ← mul_assoc]
    
  · simp only [← if_neg hk, ← inv_mul_selfₓ]
    exact map_one ϕ
    

/-- Auxillary lemma in order to state `transfer_eq_pow`. -/
theorem transfer_eq_pow_aux (g : G) (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    g ^ H.index ∈ H := by
  by_cases' hH : H.index = 0
  · rw [hH, pow_zeroₓ]
    exact H.one_mem
    
  haveI := fintype_of_index_ne_zero hH
  classical
  replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H := fun k g₀ hk =>
    (_root_.congr_arg (· ∈ H) (key k g₀ hk)).mp hk
  replace key : ∀ q : G ⧸ H, g ^ Function.minimalPeriod ((· • ·) g) q ∈ H := fun q =>
    key (Function.minimalPeriod ((· • ·) g) q) q.out' (QuotientGroup.out'_conj_pow_minimal_period_mem H g q)
  let f : Quotientₓ (orbit_rel (zpowers g) (G ⧸ H)) → zpowers g := fun q =>
    (⟨g, mem_zpowers g⟩ : zpowers g) ^ Function.minimalPeriod ((· • ·) g) q.out'
  have hf : ∀ q, f q ∈ H.subgroup_of (zpowers g) := fun q => key q.out'
  replace key := Subgroup.prod_mem (H.subgroup_of (zpowers g)) fun q (hq : q ∈ Finset.univ) => hf q
  simpa only [← minimal_period_eq_card, ← Finset.prod_pow_eq_pow_sum, ← Fintype.card_sigma, ←
    Fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)), ← index_eq_card] using key

theorem transfer_eq_pow [Fintype (G ⧸ H)] (g : G)
    (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g key⟩ := by
  classical
  change ∀ (k g₀) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key
  rw [transfer_eq_prod_quotient_orbit_rel_zpowers_quot, ← Finset.prod_to_list, List.prod_map_hom]
  refine' congr_arg ϕ (Subtype.coe_injective _)
  rw [H.coe_mk, ← (zpowers g).coe_mk g (mem_zpowers g), ← (zpowers g).coe_pow, (zpowers g).coe_mk, index_eq_card,
    Fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)), Fintype.card_sigma, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_to_list]
  simp only [← coe_list_prod, ← List.map_mapₓ, minimal_period_eq_card]
  congr 2
  funext
  apply key

theorem transfer_center_eq_pow [Fintype (G ⧸ center G)] (g : G) :
    transfer (MonoidHom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
  transfer_eq_pow (id (center G)) g fun k _ hk => by
    rw [← mul_right_injₓ, hk, mul_inv_cancel_rightₓ]

/-- The transfer homomorphism `G →* center G`. -/
noncomputable def transferCenterPow [Fintype (G ⧸ center G)] : G →* center G where
  toFun := fun g => ⟨g ^ (center G).index, (center G).pow_index_mem g⟩
  map_one' := Subtype.ext (one_pow (center G).index)
  map_mul' := fun a b => by
    simp_rw [← show ∀ g, (_ : center G) = _ from transfer_center_eq_pow, map_mul]

@[simp]
theorem transfer_center_pow_apply [Fintype (G ⧸ center G)] (g : G) : ↑(transferCenterPow g) = g ^ (center G).index :=
  rfl

/-- The transfer homomorphism `G →* center G`. -/
noncomputable def transferCenterPow' (h : (center G).index ≠ 0) : G →* center G :=
  @transferCenterPow G _ (fintypeOfIndexNeZero h)

@[simp]
theorem transfer_center_pow'_apply (h : (center G).index ≠ 0) (g : G) :
    ↑(transferCenterPow' h g) = g ^ (center G).index :=
  rfl

end MonoidHom

