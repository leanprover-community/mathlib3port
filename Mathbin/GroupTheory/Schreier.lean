/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.Data.Finset.Pointwise
import Mathbin.GroupTheory.Complement
import Mathbin.GroupTheory.Finiteness
import Mathbin.GroupTheory.Index
import Mathbin.Tactic.Group

/-!
# Schreier's Lemma

In this file we prove Schreier's lemma.

## Main results

- `closure_mul_image_eq` : **Schreier's Lemma**: If `R : set G` is a right_transversal
  of `H : subgroup G` with `1 ∈ R`, and if `G` is generated by `S : set G`,
  then `H` is generated by the `set` `(R * S).image (λ g, g * (to_fun hR g)⁻¹)`.
- `fg_of_index_ne_zero` : **Schreier's Lemma**: A finite index subgroup of a finitely generated
  group is finitely generated.
-/


open Pointwise

namespace Subgroup

open MemRightTransversals

variable {G : Type _} [Groupₓ G] {H : Subgroup G} {R S : Set G}

theorem closure_mul_image_mul_eq_top (hR : R ∈ RightTransversals (H : Set G)) (hR1 : (1 : G) ∈ R) (hS : closure S = ⊤) :
    (closure ((R * S).Image fun g => g * (toFun hR g)⁻¹) : Set G) * R = ⊤ := by
  let f : G → R := fun g => to_fun hR g
  let U : Set G := (R * S).Image fun g => g * (f g)⁻¹
  change (closure U : Set G) * R = ⊤
  refine' top_le_iff.mp fun g hg => _
  apply closure_induction_right (eq_top_iff.mp hS (mem_top g))
  · exact ⟨1, 1, (closure U).one_mem, hR1, one_mulₓ 1⟩
    
  · rintro - s hs ⟨u, r, hu, hr, rfl⟩
    rw
      [show u * r * s = u * (r * s * (f (r * s))⁻¹) * f (r * s) by
        group]
    refine' Set.mul_mem_mul ((closure U).mul_mem hu _) (f (r * s)).coe_prop
    exact subset_closure ⟨r * s, Set.mul_mem_mul hr hs, rfl⟩
    
  · rintro - s hs ⟨u, r, hu, hr, rfl⟩
    rw
      [show u * r * s⁻¹ = u * (f (r * s⁻¹) * s * r⁻¹)⁻¹ * f (r * s⁻¹) by
        group]
    refine' Set.mul_mem_mul ((closure U).mul_mem hu ((closure U).inv_mem _)) (f (r * s⁻¹)).2
    refine' subset_closure ⟨f (r * s⁻¹) * s, Set.mul_mem_mul (f (r * s⁻¹)).2 hs, _⟩
    rw [mul_right_injₓ, inv_inj, ← Subtype.coe_mk r hr, ← Subtype.ext_iff, Subtype.coe_mk]
    apply
      (mem_right_transversals_iff_exists_unique_mul_inv_mem.mp hR (f (r * s⁻¹) * s)).unique
        (mul_inv_to_fun_mem hR (f (r * s⁻¹) * s))
    rw [mul_assoc, ← inv_invₓ s, ← mul_inv_rev, inv_invₓ]
    exact to_fun_mul_inv_mem hR (r * s⁻¹)
    

/-- **Schreier's Lemma**: If `R : set G` is a right_transversal of `H : subgroup G`
  with `1 ∈ R`, and if `G` is generated by `S : set G`, then `H` is generated by the `set`
  `(R * S).image (λ g, g * (to_fun hR g)⁻¹)`. -/
theorem closure_mul_image_eq (hR : R ∈ RightTransversals (H : Set G)) (hR1 : (1 : G) ∈ R) (hS : closure S = ⊤) :
    closure ((R * S).Image fun g => g * (toFun hR g)⁻¹) = H := by
  have hU : closure ((R * S).Image fun g => g * (to_fun hR g)⁻¹) ≤ H := by
    rw [closure_le]
    rintro - ⟨g, -, rfl⟩
    exact mul_inv_to_fun_mem hR g
  refine' le_antisymmₓ hU fun h hh => _
  obtain ⟨g, r, hg, hr, rfl⟩ := show h ∈ _ from eq_top_iff.mp (closure_mul_image_mul_eq_top hR hR1 hS) (mem_top h)
  suffices (⟨r, hr⟩ : R) = (⟨1, hR1⟩ : R) by
    rwa [show r = 1 from subtype.ext_iff.mp this, mul_oneₓ]
  apply (mem_right_transversals_iff_exists_unique_mul_inv_mem.mp hR r).unique
  · rw [Subtype.coe_mk, mul_inv_selfₓ]
    exact H.one_mem
    
  · rw [Subtype.coe_mk, one_inv, mul_oneₓ]
    exact (H.mul_mem_cancel_left (hU hg)).mp hh
    

/-- **Schreier's Lemma**: If `R : set G` is a right_transversal of `H : subgroup G`
  with `1 ∈ R`, and if `G` is generated by `S : set G`, then `H` is generated by the `set`
  `(R * S).image (λ g, g * (to_fun hR g)⁻¹)`. -/
theorem closure_mul_image_eq_top (hR : R ∈ RightTransversals (H : Set G)) (hR1 : (1 : G) ∈ R) (hS : closure S = ⊤) :
    closure ((R * S).Image fun g => ⟨g * (toFun hR g)⁻¹, mul_inv_to_fun_mem hR g⟩ : Set H) = ⊤ := by
  rw [eq_top_iff, ← map_subtype_le_map_subtype, MonoidHom.map_closure, Set.image_image]
  exact (map_subtype_le ⊤).trans (ge_of_eq (closure_mul_image_eq hR hR1 hS))

/-- **Schreier's Lemma**: If `R : finset G` is a right_transversal of `H : subgroup G`
  with `1 ∈ R`, and if `G` is generated by `S : finset G`, then `H` is generated by the `finset`
  `(R * S).image (λ g, g * (to_fun hR g)⁻¹)`. -/
theorem closure_mul_image_eq_top' [DecidableEq G] {R S : Finset G} (hR : (R : Set G) ∈ RightTransversals (H : Set G))
    (hR1 : (1 : G) ∈ R) (hS : closure (S : Set G) = ⊤) :
    closure (((R * S).Image fun g => ⟨_, mul_inv_to_fun_mem hR g⟩ : Finset H) : Set H) = ⊤ := by
  rw [Finset.coe_image, Finset.coe_mul]
  exact closure_mul_image_eq_top hR hR1 hS

theorem exists_finset_card_le_mul (hH : H.index ≠ 0) {S : Finset G} (hS : closure (S : Set G) = ⊤) :
    ∃ T : Finset H, T.card ≤ H.index * S.card ∧ closure (T : Set H) = ⊤ := by
  have : DecidableEq G := Classical.decEq G
  obtain ⟨R₀, hR : R₀ ∈ right_transversals (H : Set G), hR1⟩ := exists_right_transversal (1 : G)
  have : Fintype (G ⧸ H) := fintype_of_index_ne_zero hH
  have : Fintype R₀ := Fintype.ofEquiv _ (mem_right_transversals.to_equiv hR)
  let R : Finset G := Set.toFinset R₀
  replace hR : (R : Set G) ∈ right_transversals (H : Set G) := by
    rwa [Set.coe_to_finset]
  replace hR1 : (1 : G) ∈ R := by
    rwa [Set.mem_to_finset]
  refine' ⟨_, _, closure_mul_image_eq_top' hR hR1 hS⟩
  calc _ ≤ (R * S).card := Finset.card_image_le _ ≤ (R.product S).card := Finset.card_image_le _ = R.card * S.card :=
      R.card_product S _ = H.index * S.card := congr_argₓ (· * S.card) _
  calc R.card = Fintype.card R := (Fintype.card_coe R).symm _ = _ :=
      (Fintype.card_congr (mem_right_transversals.to_equiv hR)).symm _ = Fintype.card (G ⧸ H) :=
      QuotientGroup.card_quotient_right_rel H _ = H.index := H.index_eq_card.symm

/-- **Schreier's Lemma**: A finite index subgroup of a finitely generated
  group is finitely generated. -/
theorem fg_of_index_ne_zero [hG : Groupₓ.Fg G] (hH : H.index ≠ 0) : Groupₓ.Fg H := by
  obtain ⟨S, hS⟩ := hG.1
  obtain ⟨T, -, hT⟩ := exists_finset_card_le_mul hH hS
  exact ⟨⟨T, hT⟩⟩

theorem rank_le_index_mul_rank [hG : Groupₓ.Fg G] {H : Subgroup G} (hH : H.index ≠ 0)
    [DecidablePred fun n => ∃ S : Finset G, S.card = n ∧ Subgroup.closure (S : Set G) = ⊤]
    [DecidablePred fun n => ∃ S : Finset H, S.card = n ∧ Subgroup.closure (S : Set H) = ⊤] :
    @Groupₓ.rank H _ (fg_of_index_ne_zero hH) _ ≤ H.index * Groupₓ.rank G := by
  have := fg_of_index_ne_zero hH
  obtain ⟨S, hS₀, hS⟩ := Groupₓ.rank_spec G
  obtain ⟨T, hT₀, hT⟩ := exists_finset_card_le_mul hH hS
  calc Groupₓ.rank H ≤ T.card := Groupₓ.rank_le H hT _ ≤ H.index * S.card := hT₀ _ = H.index * Groupₓ.rank G :=
      congr_argₓ ((· * ·) H.index) hS₀

end Subgroup

