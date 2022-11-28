/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.SplitSimplicialObject
import Mathbin.CategoryTheory.Preadditive.Basic
import Mathbin.AlgebraicTopology.DoldKan.Degeneracies

/-!

# Split simplicial objects in preadditive categories

TODO @joelriou: Define a functor `N' : simplicial_object.split C ⥤ chain_complex C ℕ`
when `C` is a preadditive category, and get an isomorphism
`N' ⋙ to_karoubi (chain_complex C ℕ) ≅ forget C ⋙ dold_kan.N₁`

-/


noncomputable section

open
  CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive Opposite AlgebraicTopology.DoldKan

open BigOperators Simplicial

namespace SimplicialObject

namespace Splitting

variable {C : Type _} [Category C] [HasFiniteCoproducts C] {X : SimplicialObject C} (s : Splitting X)

/-- The projection on a summand of the coproduct decomposition given
by a splitting of a simplicial object. -/
def πSummand [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) : X.obj Δ ⟶ s.n A.1.unop.len := by
  refine' (s.iso Δ).inv ≫ sigma.desc fun B => _
  by_cases B = A
  · exact
      eq_to_hom
        (by
          subst h
          rfl)
    
  · exact 0
    
#align simplicial_object.splitting.π_summand SimplicialObject.Splitting.πSummand

@[simp, reassoc]
theorem ι_π_summand_eq_id [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    s.ιSummand A ≫ s.πSummand A = 𝟙 _ := by
  dsimp [ι_summand, π_summand]
  simp only [summand, assoc, is_iso.hom_inv_id_assoc]
  erw [colimit.ι_desc, cofan.mk_ι_app]
  dsimp
  simp only [eq_self_iff_true, if_true]
#align simplicial_object.splitting.ι_π_summand_eq_id SimplicialObject.Splitting.ι_π_summand_eq_id

@[simp, reassoc]
theorem ι_π_summand_eq_zero [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A B : IndexSet Δ) (h : B ≠ A) :
    s.ιSummand A ≫ s.πSummand B = 0 := by
  dsimp [ι_summand, π_summand]
  simp only [summand, assoc, is_iso.hom_inv_id_assoc]
  erw [colimit.ι_desc, cofan.mk_ι_app]
  apply dif_neg
  exact h.symm
#align simplicial_object.splitting.ι_π_summand_eq_zero SimplicialObject.Splitting.ι_π_summand_eq_zero

variable [Preadditive C]

theorem decomposition_id (Δ : SimplexCategoryᵒᵖ) : 𝟙 (X.obj Δ) = ∑ A : IndexSet Δ, s.πSummand A ≫ s.ιSummand A := by
  apply s.hom_ext'
  intro A
  rw [comp_id, comp_sum, Finset.sum_eq_single A, ι_π_summand_eq_id_assoc]
  · intro B h₁ h₂
    rw [s.ι_π_summand_eq_zero_assoc _ _ h₂, zero_comp]
    
  · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff]
    
#align simplicial_object.splitting.decomposition_id SimplicialObject.Splitting.decomposition_id

@[simp, reassoc]
theorem σ_comp_π_summand_id_eq_zero {n : ℕ} (i : Fin (n + 1)) : X.σ i ≫ s.πSummand (IndexSet.id (op [n + 1])) = 0 := by
  apply s.hom_ext'
  intro A
  dsimp only [simplicial_object.σ]
  rw [comp_zero, s.ι_summand_epi_naturality_assoc A (SimplexCategory.σ i).op, ι_π_summand_eq_zero]
  symm
  change ¬(A.epi_comp (SimplexCategory.σ i).op).EqId
  rw [index_set.eq_id_iff_len_eq]
  have h := SimplexCategory.len_le_of_epi (inferInstance : epi A.e)
  dsimp at h⊢
  linarith
#align simplicial_object.splitting.σ_comp_π_summand_id_eq_zero SimplicialObject.Splitting.σ_comp_π_summand_id_eq_zero

/-- If a simplicial object `X` in an additive category is split,
then `P_infty` vanishes on all the summands of `X _[n]` which do
not correspond to the identity of `[n]`. -/
theorem ι_summand_comp_P_infty_eq_zero {X : SimplicialObject C} (s : SimplicialObject.Splitting X) {n : ℕ}
    (A : SimplicialObject.Splitting.IndexSet (op [n])) (hA : ¬A.EqId) : s.ιSummand A ≫ pInfty.f n = 0 := by
  rw [SimplicialObject.Splitting.IndexSet.eq_id_iff_mono] at hA
  rw [SimplicialObject.Splitting.ι_summand_eq, assoc, degeneracy_comp_P_infty X n A.e hA, comp_zero]
#align
  simplicial_object.splitting.ι_summand_comp_P_infty_eq_zero SimplicialObject.Splitting.ι_summand_comp_P_infty_eq_zero

end Splitting

end SimplicialObject

