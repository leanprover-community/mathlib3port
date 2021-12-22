import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.IsConnected
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Connected limits

A connected limit is a limit whose shape is a connected category.

We give examples of connected categories, and prove that the functor given
by `(X × -)` preserves any connected limit. That is, any limit of shape `J`
where `J` is a connected category is preserved by the functor `(X × -)`.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

section Examples

-- failed to format: format: uncaught backtrack exception
instance
  wide_pullback_shape_connected
  ( J : Type v₁ ) : is_connected ( wide_pullback_shape J )
  := by apply is_connected.of_induct introv hp t cases j · exact hp · rwa [ t ( wide_pullback_shape.hom.term j ) ]

-- failed to format: format: uncaught backtrack exception
instance
  wide_pushout_shape_connected
  ( J : Type v₁ ) : is_connected ( wide_pushout_shape J )
  := by apply is_connected.of_induct introv hp t cases j · exact hp · rwa [ ← t ( wide_pushout_shape.hom.init j ) ]

instance parallel_pair_inhabited : Inhabited walking_parallel_pair :=
  ⟨walking_parallel_pair.one⟩

-- failed to format: format: uncaught backtrack exception
instance
  parallel_pair_connected
  : is_connected walking_parallel_pair
  := by apply is_connected.of_induct introv _ t cases j · rwa [ t walking_parallel_pair_hom.left ] · assumption

end Examples

attribute [local tidy] tactic.case_bash

variable {C : Type u₂} [category.{v₂} C]

variable [has_binary_products C]

variable {J : Type v₂} [small_category J]

namespace ProdPreservesConnectedLimits

/--  (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ K :=
  { app := fun Y => limits.prod.snd }

/--  (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ (Functor.Const J).obj X :=
  { app := fun Y => limits.prod.fst }

/--  (Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
def forget_cone {X : C} {K : J ⥤ C} (s : cone (K ⋙ prod.functor.obj X)) : cone K :=
  { x := s.X, π := s.π ≫ γ₂ X }

end ProdPreservesConnectedLimits

open ProdPreservesConnectedLimits

/-- 
The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, eg `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic to
`X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
noncomputable def prod_preserves_connected_limits [is_connected J] (X : C) :
    preserves_limits_of_shape J (prod.functor.obj X) :=
  { PreservesLimit := fun K =>
      { preserves := fun c l =>
          { lift := fun s => prod.lift (s.π.app (Classical.arbitrary _) ≫ limits.prod.fst) (l.lift (forget_cone s)),
            fac' := fun s j => by
              apply prod.hom_ext
              ·
                erw [assoc, lim_map_π, comp_id, limit.lift_π]
                exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
              ·
                simp [← l.fac (forget_cone s) j],
            uniq' := fun s m L => by
              apply prod.hom_ext
              ·
                erw [limit.lift_π, ← L (Classical.arbitrary J), assoc, lim_map_π, comp_id]
                rfl
              ·
                rw [limit.lift_π]
                apply l.uniq (forget_cone s)
                intro j
                simp [← L j] } } }

end CategoryTheory

