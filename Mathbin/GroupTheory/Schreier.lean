/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module group_theory.schreier
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Abelianization
import Mathbin.GroupTheory.Exponent
import Mathbin.GroupTheory.Transfer

/-!
# Schreier's Lemma

In this file we prove Schreier's lemma.

## Main results

- `closure_mul_image_eq` : **Schreier's Lemma**: If `R : set G` is a right_transversal
  of `H : subgroup G` with `1 ∈ R`, and if `G` is generated by `S : set G`,
  then `H` is generated by the `set` `(R * S).image (λ g, g * (to_fun hR g)⁻¹)`.
- `fg_of_index_ne_zero` : **Schreier's Lemma**: A finite index subgroup of a finitely generated
  group is finitely generated.
- `card_commutator_le_of_finite_commutator_set`: A theorem of Schur: The size of the commutator
  subgroup is bounded in terms of the number of commutators.
-/


open Pointwise

namespace Subgroup

open MemRightTransversals

variable {G : Type _} [Group G] {H : Subgroup G} {R S : Set G}

theorem closure_mul_image_mul_eq_top (hR : R ∈ rightTransversals (H : Set G)) (hR1 : (1 : G) ∈ R)
    (hS : closure S = ⊤) : (closure ((R * S).image fun g => g * (toFun hR g)⁻¹) : Set G) * R = ⊤ :=
  by
  let f : G → R := fun g => to_fun hR g
  let U : Set G := (R * S).image fun g => g * (f g)⁻¹
  change (closure U : Set G) * R = ⊤
  refine' top_le_iff.mp fun g hg => _
  apply closure_induction_right (eq_top_iff.mp hS (mem_top g))
  · exact ⟨1, 1, (closure U).one_mem, hR1, one_mul 1⟩
  · rintro - s hs ⟨u, r, hu, hr, rfl⟩
    rw [show u * r * s = u * (r * s * (f (r * s))⁻¹) * f (r * s) by group]
    refine' Set.mul_mem_mul ((closure U).mul_mem hu _) (f (r * s)).coe_prop
    exact subset_closure ⟨r * s, Set.mul_mem_mul hr hs, rfl⟩
  · rintro - s hs ⟨u, r, hu, hr, rfl⟩
    rw [show u * r * s⁻¹ = u * (f (r * s⁻¹) * s * r⁻¹)⁻¹ * f (r * s⁻¹) by group]
    refine' Set.mul_mem_mul ((closure U).mul_mem hu ((closure U).inv_mem _)) (f (r * s⁻¹)).2
    refine' subset_closure ⟨f (r * s⁻¹) * s, Set.mul_mem_mul (f (r * s⁻¹)).2 hs, _⟩
    rw [mul_right_inj, inv_inj, ← Subtype.coe_mk r hr, ← Subtype.ext_iff, Subtype.coe_mk]
    apply
      (mem_right_transversals_iff_exists_unique_mul_inv_mem.mp hR (f (r * s⁻¹) * s)).unique
        (mul_inv_to_fun_mem hR (f (r * s⁻¹) * s))
    rw [mul_assoc, ← inv_inv s, ← mul_inv_rev, inv_inv]
    exact to_fun_mul_inv_mem hR (r * s⁻¹)
#align subgroup.closure_mul_image_mul_eq_top Subgroup.closure_mul_image_mul_eq_top

/-- **Schreier's Lemma**: If `R : set G` is a right_transversal of `H : subgroup G`
  with `1 ∈ R`, and if `G` is generated by `S : set G`, then `H` is generated by the `set`
  `(R * S).image (λ g, g * (to_fun hR g)⁻¹)`. -/
theorem closure_mul_image_eq (hR : R ∈ rightTransversals (H : Set G)) (hR1 : (1 : G) ∈ R)
    (hS : closure S = ⊤) : closure ((R * S).image fun g => g * (toFun hR g)⁻¹) = H :=
  by
  have hU : closure ((R * S).image fun g => g * (to_fun hR g)⁻¹) ≤ H :=
    by
    rw [closure_le]
    rintro - ⟨g, -, rfl⟩
    exact mul_inv_to_fun_mem hR g
  refine' le_antisymm hU fun h hh => _
  obtain ⟨g, r, hg, hr, rfl⟩ :=
    show h ∈ _ from eq_top_iff.mp (closure_mul_image_mul_eq_top hR hR1 hS) (mem_top h)
  suffices (⟨r, hr⟩ : R) = (⟨1, hR1⟩ : R) by rwa [show r = 1 from subtype.ext_iff.mp this, mul_one]
  apply (mem_right_transversals_iff_exists_unique_mul_inv_mem.mp hR r).unique
  · rw [Subtype.coe_mk, mul_inv_self]
    exact H.one_mem
  · rw [Subtype.coe_mk, inv_one, mul_one]
    exact (H.mul_mem_cancel_left (hU hg)).mp hh
#align subgroup.closure_mul_image_eq Subgroup.closure_mul_image_eq

/-- **Schreier's Lemma**: If `R : set G` is a right_transversal of `H : subgroup G`
  with `1 ∈ R`, and if `G` is generated by `S : set G`, then `H` is generated by the `set`
  `(R * S).image (λ g, g * (to_fun hR g)⁻¹)`. -/
theorem closure_mul_image_eq_top (hR : R ∈ rightTransversals (H : Set G)) (hR1 : (1 : G) ∈ R)
    (hS : closure S = ⊤) :
    closure ((R * S).image fun g => ⟨g * (toFun hR g)⁻¹, mul_inv_toFun_mem hR g⟩ : Set H) = ⊤ :=
  by
  rw [eq_top_iff, ← map_subtype_le_map_subtype, MonoidHom.map_closure, Set.image_image]
  exact (map_subtype_le ⊤).trans (ge_of_eq (closure_mul_image_eq hR hR1 hS))
#align subgroup.closure_mul_image_eq_top Subgroup.closure_mul_image_eq_top

/-- **Schreier's Lemma**: If `R : finset G` is a right_transversal of `H : subgroup G`
  with `1 ∈ R`, and if `G` is generated by `S : finset G`, then `H` is generated by the `finset`
  `(R * S).image (λ g, g * (to_fun hR g)⁻¹)`. -/
theorem closure_mul_image_eq_top' [DecidableEq G] {R S : Finset G}
    (hR : (R : Set G) ∈ rightTransversals (H : Set G)) (hR1 : (1 : G) ∈ R)
    (hS : closure (S : Set G) = ⊤) :
    closure (((R * S).image fun g => ⟨_, mul_inv_toFun_mem hR g⟩ : Finset H) : Set H) = ⊤ :=
  by
  rw [Finset.coe_image, Finset.coe_mul]
  exact closure_mul_image_eq_top hR hR1 hS
#align subgroup.closure_mul_image_eq_top' Subgroup.closure_mul_image_eq_top'

variable (H)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem exists_finset_card_le_mul [FiniteIndex H] {S : Finset G} (hS : closure (S : Set G) = ⊤) :
    ∃ T : Finset H, T.card ≤ H.index * S.card ∧ closure (T : Set H) = ⊤ :=
  by
  letI := H.fintype_quotient_of_finite_index
  haveI : DecidableEq G := Classical.decEq G
  obtain ⟨R₀, hR : R₀ ∈ right_transversals (H : Set G), hR1⟩ := exists_right_transversal (1 : G)
  haveI : Fintype R₀ := Fintype.ofEquiv _ (mem_right_transversals.to_equiv hR)
  let R : Finset G := Set.toFinset R₀
  replace hR : (R : Set G) ∈ right_transversals (H : Set G) := by rwa [Set.coe_toFinset]
  replace hR1 : (1 : G) ∈ R := by rwa [Set.mem_toFinset]
  refine' ⟨_, _, closure_mul_image_eq_top' hR hR1 hS⟩
  calc
    _ ≤ (R * S).card := Finset.card_image_le
    _ ≤ (R ×ˢ S).card := Finset.card_image_le
    _ = R.card * S.card := R.card_product S
    _ = H.index * S.card := congr_arg (· * S.card) _
    
  calc
    R.card = Fintype.card R := (Fintype.card_coe R).symm
    _ = _ := (Fintype.card_congr (mem_right_transversals.to_equiv hR)).symm
    _ = Fintype.card (G ⧸ H) := QuotientGroup.card_quotient_rightRel H
    _ = H.index := H.index_eq_card.symm
    
#align subgroup.exists_finset_card_le_mul Subgroup.exists_finset_card_le_mul

/-- **Schreier's Lemma**: A finite index subgroup of a finitely generated
  group is finitely generated. -/
instance fg_of_index_ne_zero [hG : Group.Fg G] [FiniteIndex H] : Group.Fg H :=
  by
  obtain ⟨S, hS⟩ := hG.1
  obtain ⟨T, -, hT⟩ := exists_finset_card_le_mul H hS
  exact ⟨⟨T, hT⟩⟩
#align subgroup.fg_of_index_ne_zero Subgroup.fg_of_index_ne_zero

theorem rank_le_index_mul_rank [hG : Group.Fg G] [FiniteIndex H] :
    Group.rank H ≤ H.index * Group.rank G :=
  by
  haveI := H.fg_of_index_ne_zero
  obtain ⟨S, hS₀, hS⟩ := Group.rank_spec G
  obtain ⟨T, hT₀, hT⟩ := exists_finset_card_le_mul H hS
  calc
    Group.rank H ≤ T.card := Group.rank_le H hT
    _ ≤ H.index * S.card := hT₀
    _ = H.index * Group.rank G := congr_arg ((· * ·) H.index) hS₀
    
#align subgroup.rank_le_index_mul_rank Subgroup.rank_le_index_mul_rank

variable (G)

/-- If `G` has `n` commutators `[g₁, g₂]`, then `|G'| ∣ [G : Z(G)] ^ ([G : Z(G)] * n + 1)`,
where `G'` denotes the commutator of `G`. -/
theorem card_commutator_dvd_index_center_pow [Finite (commutatorSet G)] :
    Nat.card (commutator G) ∣
      (center G).index ^ ((center G).index * Nat.card (commutatorSet G) + 1) :=
  by
  -- First handle the case when `Z(G)` has infinite index and `[G : Z(G)]` is defined to be `0`
  by_cases hG : (center G).index = 0
  · simp_rw [hG, zero_mul, zero_add, pow_one, dvd_zero]
  haveI : finite_index (center G) := ⟨hG⟩
  -- Rewrite as `|Z(G) ∩ G'| * [G' : Z(G) ∩ G'] ∣ [G : Z(G)] ^ ([G : Z(G)] * n) * [G : Z(G)]`
  rw [← ((center G).subgroupOf (commutator G)).card_mul_index, pow_succ']
  -- We have `h1 : [G' : Z(G) ∩ G'] ∣ [G : Z(G)]`
  have h1 := relindex_dvd_index_of_normal (center G) (commutator G)
  -- So we can reduce to proving `|Z(G) ∩ G'| ∣ [G : Z(G)] ^ ([G : Z(G)] * n)`
  refine' mul_dvd_mul _ h1
  -- We know that `[G' : Z(G) ∩ G'] < ∞` by `h1` and `hG`
  haveI : finite_index ((center G).subgroupOf (commutator G)) := ⟨ne_zero_of_dvd_ne_zero hG h1⟩
  -- We have `h2 : rank (Z(G) ∩ G') ≤ [G' : Z(G) ∩ G'] * rank G'` by Schreier's lemma
  have h2 := rank_le_index_mul_rank ((center G).subgroupOf (commutator G))
  -- We have `h3 : [G' : Z(G) ∩ G'] * rank G' ≤ [G : Z(G)] * n` by `h1` and `rank G' ≤ n`
  have h3 := Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero hG) h1) (rank_commutator_le_card G)
  -- So we can reduce to proving `|Z(G) ∩ G'| ∣ [G : Z(G)] ^ rank (Z(G) ∩ G')`
  refine' dvd_trans _ (pow_dvd_pow (center G).index (h2.trans h3))
  -- `Z(G) ∩ G'` is abelian, so it enough to prove that `g ^ [G : Z(G)] = 1` for `g ∈ Z(G) ∩ G'`
  apply card_dvd_exponent_pow_rank' _ fun g => _
  -- `Z(G)` is abelian, so `g ∈ Z(G) ∩ G' ≤ G' ≤ ker (transfer : G → Z(G))`
  have := Abelianization.commutator_subset_ker (MonoidHom.transferCenterPow G) g.1.2
  -- `transfer g` is defeq to `g ^ [G : Z(G)]`, so we are done
  simpa only [MonoidHom.mem_ker, Subtype.ext_iff] using this
#align subgroup.card_commutator_dvd_index_center_pow Subgroup.card_commutator_dvd_index_center_pow

/-- A bound for the size of the commutator subgroup in terms of the number of commutators. -/
def cardCommutatorBound (n : ℕ) :=
  (n ^ (2 * n)) ^ (n ^ (2 * n + 1) + 1)
#align subgroup.card_commutator_bound Subgroup.cardCommutatorBound

/-- A theorem of Schur: The size of the commutator subgroup is bounded in terms of the number of
  commutators. -/
theorem card_commutator_le_of_finite_commutatorSet [Finite (commutatorSet G)] :
    Nat.card (commutator G) ≤ cardCommutatorBound (Nat.card (commutatorSet G)) :=
  by
  have h1 := index_center_le_pow (closureCommutatorRepresentatives G)
  have h2 := card_commutator_dvd_index_center_pow (closureCommutatorRepresentatives G)
  rw [card_commutatorSet_closureCommutatorRepresentatives] at h1 h2
  rw [card_commutator_closureCommutatorRepresentatives] at h2
  replace h1 :=
    h1.trans
      (Nat.pow_le_pow_of_le_right Finite.card_pos (rank_closureCommutatorRepresentatives_le G))
  replace h2 := h2.trans (pow_dvd_pow _ (add_le_add_right (mul_le_mul_right' h1 _) 1))
  rw [← pow_succ'] at h2
  refine' (Nat.le_of_dvd _ h2).trans (Nat.pow_le_pow_of_le_left h1 _)
  exact pow_pos (Nat.pos_of_ne_zero finite_index.finite_index) _
#align subgroup.card_commutator_le_of_finite_commutator_set Subgroup.card_commutator_le_of_finite_commutatorSet

/-- A theorem of Schur: A group with finitely many commutators has finite commutator subgroup. -/
instance [Finite (commutatorSet G)] : Finite (commutator G) :=
  by
  have h2 := card_commutator_dvd_index_center_pow (closureCommutatorRepresentatives G)
  refine' Nat.finite_of_card_ne_zero fun h => _
  rw [card_commutator_closureCommutatorRepresentatives, h, zero_dvd_iff] at h2
  exact finite_index.finite_index (pow_eq_zero h2)

end Subgroup

