/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.DoldKan.Projections
import Mathbin.CategoryTheory.Idempotents.FunctorCategories
import Mathbin.CategoryTheory.Idempotents.FunctorExtension

/-!

# Construction of the projection `P_infty` for the Dold-Kan correspondence

TODO (@joelriou) continue adding the various files referenced below

In this file, we construct the projection `P_infty : K[X] ⟶ K[X]` by passing
to the limit the projections `P q` defined in `projections.lean`. This
projection is a critical tool in this formalisation of the Dold-Kan correspondence,
because in the case of abelian categories, `P_infty` corresponds to the
projection on the normalized Moore subcomplex, with kernel the degenerate subcomplex.
(See `equivalence.lean` for the general strategy of proof.)

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Preadditive

open CategoryTheory.SimplicialObject

open CategoryTheory.Idempotents

open Opposite

open Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] {X : SimplicialObject C}

theorem P_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) : ((p (q + 1)).f n : X _[n] ⟶ _) = (p q).f n := by
  cases n
  · simp only [P_f_0_eq]
    
  · unfold P
    simp only [add_right_eq_selfₓ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply, comp_id]
    exact (higher_faces_vanish.of_P q n).comp_Hσ_eq_zero (nat.succ_le_iff.mp hqn)
    

theorem Q_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) : ((q (q + 1)).f n : X _[n] ⟶ _) = (q q).f n := by
  simp only [Q, HomologicalComplex.sub_f_apply, P_is_eventually_constant hqn]

/-- The endomorphism `P_infty : K[X] ⟶ K[X]` obtained from the `P q` by passing to the limit. -/
def pInfty : K[X] ⟶ K[X] :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => ((p n).f n : X _[n] ⟶ _)) fun n => by
    simpa only [←
      P_is_eventually_constant
        (show n ≤ n by
          rfl),
      alternating_face_map_complex.obj_d_eq] using (P (n + 1)).comm (n + 1) n

@[simp]
theorem P_infty_f_0 : (pInfty.f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
  rfl

theorem P_infty_f (n : ℕ) : (pInfty.f n : X _[n] ⟶ X _[n]) = (p n).f n :=
  rfl

@[simp, reassoc]
theorem P_infty_f_naturality (n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op [n]) ≫ pInfty.f n = pInfty.f n ≫ f.app (op [n]) :=
  P_f_naturality n n f

@[simp, reassoc]
theorem P_infty_f_idem (n : ℕ) : (pInfty.f n : X _[n] ⟶ _) ≫ pInfty.f n = pInfty.f n := by
  simp only [P_infty_f, P_f_idem]

@[simp, reassoc]
theorem P_infty_idem : (pInfty : K[X] ⟶ _) ≫ P_infty = P_infty := by
  ext n
  exact P_infty_f_idem n

variable (C)

/-- `P_infty` induces a natural transformation, i.e. an endomorphism of
the functor `alternating_face_map_complex C`. -/
@[simps]
def natTransPInfty : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app := fun _ => pInfty
  naturality' := fun X Y f => by
    ext n
    exact P_infty_f_naturality n f

/-- The natural transformation in each degree that is induced by `nat_trans_P_infty`. -/
@[simps]
def natTransPInftyF (n : ℕ) :=
  natTransPInfty C ◫ 𝟙 (HomologicalComplex.eval _ _ n)

variable {C}

@[simp]
theorem map_P_infty_f {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive] (X : SimplicialObject C)
    (n : ℕ) :
    (pInfty : K[((whiskering C D).obj G).obj X] ⟶ _).f n = G.map ((pInfty : AlternatingFaceMapComplex.obj X ⟶ _).f n) :=
  by
  simp only [P_infty_f, map_P]

/-- Given an object `Y : karoubi (simplicial_object C)`, this lemma
computes `P_infty` for the associated object in `simplicial_object (karoubi C)`
in terms of `P_infty` for `Y.X : simplicial_object C` and `Y.p`. -/
theorem karoubi_P_infty_f {Y : Karoubi (SimplicialObject C)} (n : ℕ) :
    ((pInfty : K[(karoubiFunctorCategoryEmbedding _ _).obj Y] ⟶ _).f n).f =
      Y.p.app (op [n]) ≫ (pInfty : K[Y.x] ⟶ _).f n :=
  by
  -- We introduce P_infty endomorphisms P₁, P₂, P₃, P₄ on various objects Y₁, Y₂, Y₃, Y₄.
  let Y₁ := (karoubi_functor_category_embedding _ _).obj Y
  let Y₂ := Y.X
  let Y₃ := ((whiskering _ _).obj (to_karoubi C)).obj Y.X
  let Y₄ := (karoubi_functor_category_embedding _ _).obj ((to_karoubi _).obj Y.X)
  let P₁ : K[Y₁] ⟶ _ := P_infty
  let P₂ : K[Y₂] ⟶ _ := P_infty
  let P₃ : K[Y₃] ⟶ _ := P_infty
  let P₄ : K[Y₄] ⟶ _ := P_infty
  -- The statement of lemma relates P₁ and P₂.
  change (P₁.f n).f = Y.p.app (op [n]) ≫ P₂.f n
  -- The proof proceeds by obtaining relations h₃₂, h₄₃, h₁₄.
  have h₃₂ : (P₃.f n).f = P₂.f n := karoubi.hom_ext.mp (map_P_infty_f (to_karoubi C) Y₂ n)
  have h₄₃ : P₄.f n = P₃.f n := by
    have h := functor.congr_obj (to_karoubi_comp_karoubi_functor_category_embedding _ _) Y₂
    simp only [← nat_trans_P_infty_f_app]
    congr
  let τ₁ := 𝟙 (karoubi_functor_category_embedding SimplexCategoryᵒᵖ C)
  let τ₂ := nat_trans_P_infty_f (karoubi C) n
  let τ := τ₁ ◫ τ₂
  have h₁₄ := idempotents.nat_trans_eq τ Y
  dsimp' [τ, τ₁, τ₂, nat_trans_P_infty_f]  at h₁₄
  rw [id_comp, id_comp, comp_id, comp_id] at h₁₄
  -- We use the three equalities h₃₂, h₄₃, h₁₄.
  rw [← h₃₂, ← h₄₃, h₁₄]
  simp only [karoubi_functor_category_embedding.map_app_f, karoubi.decomp_id_p_f, karoubi.decomp_id_i_f, karoubi.comp]
  let π : Y₄ ⟶ Y₄ := (to_karoubi _ ⋙ karoubi_functor_category_embedding _ _).map Y.p
  have eq := karoubi.hom_ext.mp (P_infty_f_naturality n π)
  simp only [karoubi.comp] at eq
  dsimp' [π]  at eq
  rw [← Eq, reassoc_of (app_idem Y (op [n]))]

end DoldKan

end AlgebraicTopology

