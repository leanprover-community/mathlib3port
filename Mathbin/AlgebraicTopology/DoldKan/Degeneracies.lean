/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.degeneracies
! leanprover-community/mathlib commit 4f81bc21e32048db7344b7867946e992cf5f68cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.Decomposition
import Mathbin.Tactic.FinCases

/-!

# Behaviour of P_infty with respect to degeneracies

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For any `X : simplicial_object C` where `C` is an abelian category,
the projector `P_infty : K[X] ⟶ K[X]` is supposed to be the projection
on the normalized subcomplex, parallel to the degenerate subcomplex, i.e.
the subcomplex generated by the images of all `X.σ i`.

In this file, we obtain `degeneracy_comp_P_infty` which states that
if `X : simplicial_object C` with `C` a preadditive category,
`θ : [n] ⟶ Δ'` is a non injective map in `simplex_category`, then
`X.map θ.op ≫ P_infty.f n = 0`. It follows from the more precise
statement vanishing statement `σ_comp_P_eq_zero` for the `P q`.

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
  Opposite

open scoped Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C]

#print AlgebraicTopology.DoldKan.HigherFacesVanish.comp_σ /-
theorem HigherFacesVanish.comp_σ {Y : C} {X : SimplicialObject C} {n b q : ℕ} {φ : Y ⟶ X _[n + 1]}
    (v : HigherFacesVanish q φ) (hnbq : n + 1 = b + q) :
    HigherFacesVanish q
      (φ ≫
        X.σ ⟨b, by simpa only [hnbq, Nat.lt_succ_iff, le_add_iff_nonneg_right] using zero_le q⟩) :=
  fun j hj =>
  by
  rw [assoc, simplicial_object.δ_comp_σ_of_gt', Fin.pred_succ, v.comp_δ_eq_zero_assoc _ _ hj,
    zero_comp]
  · intro hj'
    simpa only [hj', hnbq, Fin.val_zero, zero_add, add_comm b, add_assoc, false_and_iff,
      add_le_iff_nonpos_right, le_zero_iff, add_eq_zero_iff, Nat.one_ne_zero] using hj
  · simp only [Fin.lt_iff_val_lt_val, Nat.lt_iff_add_one_le, Fin.succ_mk, Fin.val_mk, Fin.val_succ,
      add_le_add_iff_right]
    linarith
#align algebraic_topology.dold_kan.higher_faces_vanish.comp_σ AlgebraicTopology.DoldKan.HigherFacesVanish.comp_σ
-/

#print AlgebraicTopology.DoldKan.σ_comp_P_eq_zero /-
theorem σ_comp_P_eq_zero (X : SimplicialObject C) {n q : ℕ} (i : Fin (n + 1)) (hi : n + 1 ≤ i + q) :
    X.σ i ≫ (P q).f (n + 1) = 0 :=
  by
  induction' q with q hq generalizing i hi
  · exfalso
    have h := Fin.is_lt i
    linarith
  · by_cases n + 1 ≤ (i : ℕ) + q
    · unfold P
      simp only [HomologicalComplex.comp_f, ← assoc]
      rw [hq i h, zero_comp]
    · have hi' : n = (i : ℕ) + q :=
        by
        cases' le_iff_exists_add.mp hi with j hj
        rw [← Nat.lt_succ_iff, Nat.succ_eq_add_one, add_assoc, hj, not_lt, add_le_iff_nonpos_right,
          nonpos_iff_eq_zero] at h 
        rw [← add_left_inj 1, add_assoc, hj, self_eq_add_right, h]
      cases n
      · fin_cases i
        rw [show q = 0 by linarith]
        unfold P
        simp only [id_comp, HomologicalComplex.add_f_apply, comp_add, HomologicalComplex.id_f, Hσ,
          Homotopy.nullHomotopicMap'_f (c_mk 2 1 rfl) (c_mk 1 0 rfl),
          alternating_face_map_complex.obj_d_eq]
        erw [hσ'_eq' (zero_add 0).symm, hσ'_eq' (add_zero 1).symm, comp_id, Fin.sum_univ_two,
          Fin.sum_univ_succ, Fin.sum_univ_two]
        simp only [pow_zero, pow_one, pow_two, Fin.val_zero, Fin.val_one, Fin.val_two, one_zsmul,
          neg_zsmul, Fin.mk_zero, Fin.mk_one, Fin.val_succ, pow_add, one_mul, neg_mul, neg_neg,
          Fin.succ_zero_eq_one, Fin.succ_one_eq_two, comp_neg, neg_comp, add_comp, comp_add]
        erw [simplicial_object.δ_comp_σ_self, simplicial_object.δ_comp_σ_self_assoc,
          simplicial_object.δ_comp_σ_succ, comp_id,
          simplicial_object.δ_comp_σ_of_le X
            (show (0 : Fin 2) ≤ Fin.castSucc 0 by rw [Fin.castSucc_zero]),
          simplicial_object.δ_comp_σ_self_assoc, simplicial_object.δ_comp_σ_succ_assoc]
        abel
      · rw [← id_comp (X.σ i), ← (P_add_Q_f q n.succ : _ = 𝟙 (X.obj _)), add_comp, add_comp]
        have v : higher_faces_vanish q ((P q).f n.succ ≫ X.σ i) :=
          (higher_faces_vanish.of_P q n).comp_σ hi'
        unfold P
        erw [← assoc, v.comp_P_eq_self, HomologicalComplex.add_f_apply, preadditive.comp_add,
          comp_id, v.comp_Hσ_eq hi', assoc, simplicial_object.δ_comp_σ_succ'_assoc, Fin.eta,
          decomposition_Q n q, sum_comp, sum_comp, Finset.sum_eq_zero, add_zero, add_neg_eq_zero]
        swap
        · ext; simp only [Fin.val_mk, Fin.val_succ]
        · intro j hj
          simp only [true_and_iff, Finset.mem_univ, Finset.mem_filter] at hj 
          simp only [Nat.succ_eq_add_one] at hi' 
          obtain ⟨k, hk⟩ := Nat.le.dest (nat.lt_succ_iff.mp (Fin.is_lt j))
          rw [add_comm] at hk 
          have hi'' : i = Fin.castSucc ⟨i, by linarith⟩ := by ext;
            simp only [Fin.castSucc_mk, Fin.eta]
          have eq :=
            hq j.rev.succ
              (by
                simp only [← hk, Fin.rev_eq j hk.symm, Nat.succ_eq_add_one, Fin.succ_mk, Fin.val_mk]
                linarith)
          rw [HomologicalComplex.comp_f, assoc, assoc, assoc, hi'',
            simplicial_object.σ_comp_σ_assoc, reassoc_of Eq, zero_comp, comp_zero, comp_zero,
            comp_zero]
          simp only [Fin.rev_eq j hk.symm, Fin.le_iff_val_le_val, Fin.val_mk]
          linarith
#align algebraic_topology.dold_kan.σ_comp_P_eq_zero AlgebraicTopology.DoldKan.σ_comp_P_eq_zero
-/

#print AlgebraicTopology.DoldKan.σ_comp_PInfty /-
@[simp, reassoc]
theorem σ_comp_PInfty (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ PInfty.f (n + 1) = 0 :=
  by
  rw [P_infty_f, σ_comp_P_eq_zero X i]
  simp only [le_add_iff_nonneg_left, zero_le]
#align algebraic_topology.dold_kan.σ_comp_P_infty AlgebraicTopology.DoldKan.σ_comp_PInfty
-/

#print AlgebraicTopology.DoldKan.degeneracy_comp_PInfty /-
@[reassoc]
theorem degeneracy_comp_PInfty (X : SimplicialObject C) (n : ℕ) {Δ' : SimplexCategory}
    (θ : [n] ⟶ Δ') (hθ : ¬Mono θ) : X.map θ.op ≫ PInfty.f n = 0 :=
  by
  rw [SimplexCategory.mono_iff_injective] at hθ 
  cases n
  · exfalso
    apply hθ
    intro x y h
    fin_cases x
    fin_cases y
  · obtain ⟨i, α, h⟩ := SimplexCategory.eq_σ_comp_of_not_injective θ hθ
    rw [h, op_comp, X.map_comp, assoc, show X.map (SimplexCategory.σ i).op = X.σ i by rfl,
      σ_comp_P_infty, comp_zero]
#align algebraic_topology.dold_kan.degeneracy_comp_P_infty AlgebraicTopology.DoldKan.degeneracy_comp_PInfty
-/

end DoldKan

end AlgebraicTopology

