/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.DoldKan.Homotopies
import Mathbin.Data.Nat.Parity
import Mathbin.Tactic.RingExp

/-!

# Study of face maps for the Dold-Kan correspondence

TODO (@joelriou) continue adding the various files referenced below

In this file, we obtain the technical lemmas that are used in the file
`projections.lean` in order to get basic properties of the endomorphisms
`P q : K[X] ⟶ K[X]` with respect to face maps (see `homotopies.lean` for the
role of these endomorphisms in the overall strategy of proof).

The main lemma in this file is `higher_faces_vanish.induction`. It is based
on two technical lemmas `higher_faces_vanish.comp_Hσ_eq` and
`higher_faces_vanish.comp_Hσ_eq_zero`.

-/


open Nat

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Category

open CategoryTheory.Preadditive

open CategoryTheory.SimplicialObject

open Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C]

variable {X : SimplicialObject C}

/-- A morphism `φ : Y ⟶ X _[n+1]` satisfies `higher_faces_vanish q φ`
when the compositions `φ ≫ X.δ j` are `0` for `j ≥ max 1 (n+2-q)`. When `q ≤ n+1`,
it basically means that the composition `φ ≫ X.δ j` are `0` for the `q` highest
possible values of a nonzero `j`. Otherwise, when `q ≥ n+2`, all the compositions
`φ ≫ X.δ j` for nonzero `j` vanish. See also the lemma `comp_P_eq_self_iff` in
`projections.lean` which states that `higher_faces_vanish q φ` is equivalent to
the identity `φ ≫ (P q).f (n+1) = φ`. -/
def HigherFacesVanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n + 1]) : Prop :=
  ∀ j : Fin (n + 1), n + 1 ≤ (j : ℕ) + q → φ ≫ X.δ j.succ = 0

namespace HigherFacesVanish

theorem of_succ {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish (q + 1) φ) : HigherFacesVanish q φ :=
  fun j hj => v j (by simpa only [← add_assoc] using le_add_right hj)

theorem of_comp {Y Z : C} {q n : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) (f : Z ⟶ Y) :
    HigherFacesVanish q (f ≫ φ) := fun j hj => by rw [assoc, v j hj, comp_zero]

theorem comp_Hσ_eq {Y : C} {n a q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) (hnaq : n = a + q) :
    φ ≫ (hσ q).f (n + 1) =
      -(φ ≫
          X.δ ⟨a + 1, Nat.succ_lt_succ (Nat.lt_succ_iff.mpr (Nat.le.intro hnaq.symm))⟩ ≫
            X.σ ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro hnaq.symm)⟩) :=
  by
  have hnaq_shift : ∀ d : ℕ, n + d = a + d + q := by
    intro d
    rw [add_assoc, add_comm d, ← add_assoc, hnaq]
  rw [Hσ, Homotopy.null_homotopic_map'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl),
    hσ'_eq hnaq (c_mk (n + 1) n rfl), hσ'_eq (hnaq_shift 1) (c_mk (n + 2) (n + 1) rfl)]
  simp only [alternating_face_map_complex.obj_d_eq, eq_to_hom_refl, comp_id, comp_sum, sum_comp, comp_add]
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul]
  -- cleaning up the first sum
  rw [← Fin.sum_congr' _ (hnaq_shift 2).symm, Fin.sum_trunc]
  swap
  · rintro ⟨k, hk⟩
    suffices φ ≫ X.δ (⟨a + 2 + k, by linarith⟩ : Fin (n + 2)) = 0 by
      simp only [this, Fin.nat_add_mk, Fin.cast_mk, zero_comp, smul_zero]
    convert
      v ⟨a + k + 1, by linarith⟩
        (by
          rw [Fin.coe_mk]
          linarith)
    rw [Nat.succ_eq_add_one]
    linarith
    
  -- cleaning up the second sum
  rw [← Fin.sum_congr' _ (hnaq_shift 3).symm, @Fin.sum_trunc _ _ (a + 3)]
  swap
  · rintro ⟨k, hk⟩
    suffices φ ≫ X.σ ⟨a + 1, by linarith⟩ ≫ X.δ ⟨a + 3 + k, by linarith⟩ = 0 by
      dsimp
      rw [assoc, this, smul_zero]
    let i : Fin (n + 1) := ⟨a + 1 + k, by linarith⟩
    have h : Fin.castSucc (⟨a + 1, by linarith⟩ : Fin (n + 1)) < i.succ := by
      simp only [Fin.lt_iff_coe_lt_coe, Fin.cast_succ_mk, Fin.coe_mk, Fin.succ_mk]
      linarith
    have δσ_rel := δ_comp_σ_of_gt X h
    conv_lhs at δσ_rel => simp only [Fin.cast_succ_mk, Fin.succ_mk, show a + 1 + k + 1 + 1 = a + 3 + k by linarith]
    rw [δσ_rel, ← assoc, v i, zero_comp]
    simp only [i, Fin.coe_mk]
    linarith
    
  -- leaving out three specific terms
conv_lhs =>
  congr
  skip
  rw [Fin.sum_univ_cast_succ, Fin.sum_univ_cast_succ]
  rw [Fin.sum_univ_cast_succ]
  simp only [Fin.last, Fin.cast_le_mk, Fin.coe_cast, Fin.cast_mk, Fin.coe_cast_le, Fin.coe_mk, Fin.cast_succ_mk,
    Fin.coe_cast_succ]
  /- the purpose of the following `simplif` is to create three subgoals in order
      to finish the proof -/
  have simplif : ∀ a b c d e f : Y ⟶ X _[n + 1], b = f → d + e = 0 → c + a = 0 → a + b + (c + d + e) = f := by
    intro a b c d e f h1 h2 h3
    rw [add_assoc c d e, h2, add_zero, add_comm a b, add_assoc, add_comm a c, h3, add_zero, h1]
  apply simplif
  · -- b=f
    rw [← pow_add, Odd.neg_one_pow, neg_smul, one_zsmul]
    use a
    linarith
    
  · -- d+e = 0
    let b : Fin (n + 2) := ⟨a + 1, by linarith⟩
    have eq₁ : X.σ b ≫ X.δ (Fin.castSucc b) = 𝟙 _ := δ_comp_σ_self _
    have eq₂ : X.σ b ≫ X.δ b.succ = 𝟙 _ := δ_comp_σ_succ _
    simp only [b, Fin.cast_succ_mk, Fin.succ_mk] at eq₁ eq₂
    simp only [eq₁, eq₂, Fin.last, assoc, Fin.cast_succ_mk, Fin.cast_le_mk, Fin.coe_mk, comp_id, add_eq_zero_iff_eq_neg,
      ← neg_zsmul]
    congr
    ring_exp
    rw [mul_one]
    
  · -- c+a = 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    rintro ⟨i, hi⟩ h₀
    have hia : (⟨i, by linarith⟩ : Fin (n + 2)) ≤ Fin.castSucc (⟨a, by linarith⟩ : Fin (n + 1)) := by
      simpa only [Fin.le_iff_coe_le_coe, Fin.coe_mk, Fin.cast_succ_mk, ← lt_succ_iff] using hi
    simp only [Fin.coe_mk, Fin.cast_le_mk, Fin.cast_succ_mk, Fin.succ_mk, assoc, Fin.cast_mk, ← δ_comp_σ_of_le X hia,
      add_eq_zero_iff_eq_neg, ← neg_zsmul]
    congr
    ring_exp
    

theorem comp_Hσ_eq_zero {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) (hqn : n < q) :
    φ ≫ (hσ q).f (n + 1) = 0 := by
  simp only [Hσ, Homotopy.null_homotopic_map'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]
  rw [hσ'_eq_zero hqn (c_mk (n + 1) n rfl), comp_zero, zero_add]
  by_cases hqn':n + 1 < q
  · rw [hσ'_eq_zero hqn' (c_mk (n + 2) (n + 1) rfl), zero_comp, comp_zero]
    
  · simp only [hσ'_eq (show n + 1 = 0 + q by linarith) (c_mk (n + 2) (n + 1) rfl), pow_zero, Fin.mk_zero, one_zsmul,
      eq_to_hom_refl, comp_id, comp_sum, alternating_face_map_complex.obj_d_eq]
    rw [← Fin.sum_congr' _ (show 2 + (n + 1) = n + 1 + 2 by linarith), Fin.sum_trunc]
    · simp only [Fin.sum_univ_cast_succ, Fin.sum_univ_zero, zero_add, Fin.last, Fin.cast_le_mk, Fin.cast_mk,
        Fin.cast_succ_mk]
      simp only [Fin.mk_zero, Fin.coe_zero, pow_zero, one_zsmul, Fin.mk_one, Fin.coe_one, pow_one, neg_smul, comp_neg]
      erw [δ_comp_σ_self, δ_comp_σ_succ, add_right_neg]
      
    · intro j
      simp only [comp_zsmul]
      convert zsmul_zero _
      have h : Fin.cast (by rw [add_comm 2]) (Fin.natAdd 2 j) = j.succ.succ := by
        ext
        simp only [add_comm 2, Fin.coe_cast, Fin.coe_nat_add, Fin.coe_succ]
      rw [h, ← Fin.cast_succ_zero, δ_comp_σ_of_gt X]
      swap
      · exact Fin.succ_pos j
        
      simp only [← assoc, v j (by linarith), zero_comp]
      
    

theorem induction {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) :
    HigherFacesVanish (q + 1) (φ ≫ (𝟙 _ + hσ q).f (n + 1)) := by
  intro j hj₁
  dsimp
  simp only [comp_add, add_comp, comp_id]
  -- when n < q, the result follows immediately from the assumption
  by_cases hqn:n < q
  · rw [v.comp_Hσ_eq_zero hqn, zero_comp, add_zero, v j (by linarith)]
    
  -- we now assume that n≥q, and write n=a+q
  cases' Nat.le.dest (not_lt.mp hqn) with a ha
  rw [v.comp_Hσ_eq (show n = a + q by linarith), neg_comp, add_neg_eq_zero, assoc, assoc]
  cases' n with m hm
  -- the boundary case n=0
  · simpa only [Nat.eq_zero_of_add_eq_zero_left ha, Fin.eq_zero j, Fin.mk_zero, Fin.mk_one, δ_comp_σ_succ, comp_id]
    
  -- in the other case, we need to write n as m+1
  -- then, we first consider the particular case j = a
  by_cases hj₂:a = (j : ℕ)
  · simp only [hj₂, Fin.eta, δ_comp_σ_succ, comp_id]
    congr
    ext
    simp only [Fin.coe_succ, Fin.coe_mk]
    
  -- now, we assume j ≠ a (i.e. a < j)
  have haj : a < j := (Ne.le_iff_lt hj₂).mp (by linarith)
  have hj₃ := j.is_lt
  have ham : a ≤ m := by
    by_contra
    rw [not_le, ← Nat.succ_le_iff] at h
    linarith
  have ineq₁ : Fin.castSucc (⟨a, nat.lt_succ_iff.mpr ham⟩ : Fin (m + 1)) < j := by
    rw [Fin.lt_iff_coe_lt_coe]
    exact haj
  have eq₁ := δ_comp_σ_of_gt X ineq₁
  rw [Fin.cast_succ_mk] at eq₁
  rw [eq₁]
  obtain ham' | ham'' := ham.lt_or_eq
  · -- case where `a<m`
    have ineq₂ : Fin.castSucc (⟨a + 1, Nat.succ_lt_succ ham'⟩ : Fin (m + 1)) ≤ j := by
      simpa only [Fin.le_iff_coe_le_coe] using nat.succ_le_iff.mpr haj
    have eq₂ := δ_comp_δ X ineq₂
    simp only [Fin.cast_succ_mk] at eq₂
    slice_rhs 2 3 => rw [← eq₂]
    simp only [← assoc, v j (by linarith), zero_comp]
    
  · -- in the last case, a=m, q=1 and j=a+1
    have hq : q = 1 := by rw [← add_left_inj a, ha, ham'', add_comm]
    have hj₄ : (⟨a + 1, by linarith⟩ : Fin (m + 3)) = Fin.castSucc j := by
      ext
      simp only [Fin.coe_mk, Fin.coe_cast_succ]
      linarith
    slice_rhs 2 3 => rw [hj₄, δ_comp_δ_self]
    simp only [← assoc, v j (by linarith), zero_comp]
    

end HigherFacesVanish

end DoldKan

end AlgebraicTopology

