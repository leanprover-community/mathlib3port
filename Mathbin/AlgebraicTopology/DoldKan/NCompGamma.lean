/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.DoldKan.GammaCompN
import Mathbin.AlgebraicTopology.DoldKan.NReflectsIso

/-! The unit isomorphism of the Dold-Kan equivalence

In order to construct the unit isomorphism of the Dold-Kan equivalence,
we first construct natural transformations
`Γ₂N₁.nat_trans : N₁ ⋙ Γ₂ ⟶ to_karoubi (simplicial_object C)` and
`Γ₂N₂.nat_trans : N₂ ⋙ Γ₂ ⟶ 𝟭 (simplicial_object C)` (TODO).
It is then shown that `Γ₂N₂.nat_trans` is an isomorphism by using
that it becomes an isomorphism after the application of the functor
`N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`
which reflects isomorphisms.

-/


noncomputable section

open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents SimplexCategory Opposite SimplicialObject

open Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C]

theorem P_infty_comp_map_mono_eq_zero (X : SimplicialObject C) {n : ℕ} {Δ' : SimplexCategory}
    (i : Δ' ⟶ [n]) [hi : Mono i] (h₁ : Δ'.len ≠ n) (h₂ : ¬Isδ₀ i) : pInfty.f n ≫ X.map i.op = 0 :=
  by 
  induction' Δ' using SimplexCategory.rec with m
  obtain ⟨k, hk⟩ :=
    Nat.exists_eq_add_of_lt
      (len_lt_of_mono i fun h => by 
        rw [← h] at h₁
        exact h₁ rfl)
  simp only [len_mk] at hk
  cases k
  · change n = m + 1 at hk
    subst hk
    obtain ⟨j, rfl⟩ := eq_δ_of_mono i
    rw [is_δ₀.iff] at h₂
    have h₃ : 1 ≤ (j : ℕ) := by 
      by_contra
      exact h₂ (by simpa only [Fin.ext_iff, not_le, Nat.lt_one_iff] using h)
    exact (higher_faces_vanish.of_P (m + 1) m).comp_δ_eq_zero j h₂ (by linarith)
  · simp only [Nat.succ_eq_add_one, ← add_assoc] at hk
    clear h₂ hi
    subst hk
    obtain ⟨j₁, i, rfl⟩ :=
      eq_comp_δ_of_not_surjective i fun h => by
        have h' := len_le_of_epi (SimplexCategory.epi_iff_surjective.2 h)
        dsimp at h'
        linarith
    obtain ⟨j₂, i, rfl⟩ :=
      eq_comp_δ_of_not_surjective i fun h => by
        have h' := len_le_of_epi (SimplexCategory.epi_iff_surjective.2 h)
        dsimp at h'
        linarith
    by_cases hj₁ : j₁ = 0
    · subst hj₁
      rw [assoc, ← SimplexCategory.δ_comp_δ'' (Fin.zero_le _)]
      simp only [op_comp, X.map_comp, assoc, P_infty_f]
      erw [(higher_faces_vanish.of_P _ _).comp_δ_eq_zero_assoc _ j₂.succ_ne_zero, zero_comp]
      rw [Fin.coe_succ]
      linarith
    · simp only [op_comp, X.map_comp, assoc, P_infty_f]
      erw [(higher_faces_vanish.of_P _ _).comp_δ_eq_zero_assoc _ hj₁, zero_comp]
      by_contra
      exact
        hj₁
          (by 
            simp only [Fin.ext_iff, Fin.coe_zero]
            linarith)
#align
  algebraic_topology.dold_kan.P_infty_comp_map_mono_eq_zero AlgebraicTopology.DoldKan.P_infty_comp_map_mono_eq_zero

@[reassoc]
theorem Γ₀_obj_termwise_map_mono_comp_P_infty (X : SimplicialObject C) {Δ Δ' : SimplexCategory}
    (i : Δ ⟶ Δ') [Mono i] :
    Γ₀.Obj.Termwise.mapMono (AlternatingFaceMapComplex.obj X) i ≫ pInfty.f Δ.len =
      pInfty.f Δ'.len ≫ X.map i.op :=
  by 
  induction' Δ using SimplexCategory.rec with n
  induction' Δ' using SimplexCategory.rec with n'
  dsimp
  -- We start with the case `i` is an identity
  by_cases n = n'
  · subst h
    simp only [SimplexCategory.eq_id_of_mono i, Γ₀.obj.termwise.map_mono_id, op_id, X.map_id]
    dsimp
    simp only [id_comp, comp_id]
  by_cases hi : is_δ₀ i
  -- The case `i = δ 0`
  · have h' : n' = n + 1 := hi.left
    subst h'
    simp only [Γ₀.obj.termwise.map_mono_δ₀' _ i hi]
    dsimp
    rw [← P_infty.comm' _ n rfl, alternating_face_map_complex.obj_d_eq]
    simp only [eq_self_iff_true, id_comp, if_true, preadditive.comp_sum]
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    rotate_left
    · intro b hb hb'
      rw [preadditive.comp_zsmul]
      erw [P_infty_comp_map_mono_eq_zero X (SimplexCategory.δ b) h
          (by 
            rw [is_δ₀.iff]
            exact hb'),
        zsmul_zero]
    · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff]
    · simpa only [hi.eq_δ₀, Fin.coe_zero, pow_zero, one_zsmul]
  -- The case `i ≠ δ 0`
  · rw [Γ₀.obj.termwise.map_mono_eq_zero _ i _ hi, zero_comp]
    swap
    · by_contra h'
      exact h (congr_arg SimplexCategory.len h'.symm)
    rw [P_infty_comp_map_mono_eq_zero]
    · exact h
    · by_contra h'
      exact hi h'
#align
  algebraic_topology.dold_kan.Γ₀_obj_termwise_map_mono_comp_P_infty AlgebraicTopology.DoldKan.Γ₀_obj_termwise_map_mono_comp_P_infty

variable [HasFiniteCoproducts C]

namespace Γ₂N₁

/-- The natural transformation `N₁ ⋙ Γ₂ ⟶ to_karoubi (simplicial_object C)`. -/
@[simps]
def natTrans :
    (n₁ : SimplicialObject C ⥤ _) ⋙ Γ₂ ⟶
      toKaroubi
        _ where 
  app X :=
    { f :=
        { app := fun Δ => (Γ₀.splitting K[X]).desc Δ fun A => pInfty.f A.1.unop.len ≫ X.map A.e.op,
          naturality' := fun Δ Δ' θ => by
            apply (Γ₀.splitting K[X]).hom_ext'
            intro A
            change _ ≫ (Γ₀.obj K[X]).map θ ≫ _ = _
            simp only [splitting.ι_desc_assoc, assoc, Γ₀.obj.map_on_summand'_assoc,
              splitting.ι_desc]
            erw [Γ₀_obj_termwise_map_mono_comp_P_infty_assoc X (image.ι (θ.unop ≫ A.e))]
            dsimp only [to_karoubi]
            simp only [← X.map_comp]
            congr 2
            simp only [eq_to_hom_refl, id_comp, comp_id, ← op_comp]
            exact Quiver.Hom.unop_inj (A.fac_pull θ) },
      comm := by 
        apply (Γ₀.splitting K[X]).hom_ext
        intro n
        dsimp [N₁]
        simp only [← splitting.ι_summand_id, splitting.ι_desc, comp_id, splitting.ι_desc_assoc,
          assoc, P_infty_f_idem_assoc] }
  naturality' X Y f := by 
    ext1
    apply (Γ₀.splitting K[X]).hom_ext
    intro n
    dsimp [N₁, to_karoubi]
    simpa only [← splitting.ι_summand_id, splitting.ι_desc, splitting.ι_desc_assoc, assoc,
      P_infty_f_idem_assoc, karoubi.comp_f, nat_trans.comp_app, Γ₂_map_f_app,
      HomologicalComplex.comp_f, alternating_face_map_complex.map_f, P_infty_f_naturality_assoc,
      nat_trans.naturality]
#align algebraic_topology.dold_kan.Γ₂N₁.nat_trans AlgebraicTopology.DoldKan.Γ₂N₁.natTrans

end Γ₂N₁

end DoldKan

end AlgebraicTopology

