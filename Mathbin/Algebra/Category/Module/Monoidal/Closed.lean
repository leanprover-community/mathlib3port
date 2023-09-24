/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import CategoryTheory.Closed.Monoidal
import Algebra.Category.Module.Monoidal.Symmetric

#align_import algebra.category.Module.monoidal.closed from "leanprover-community/mathlib"@"c20927220ef87bb4962ba08bf6da2ce3cf50a6dd"

/-!
# The monoidal closed structure on `Module R`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe v w x u

open CategoryTheory

open Opposite

namespace ModuleCat

variable {R : Type u} [CommRing R]

attribute [local ext] TensorProduct.ext

#print ModuleCat.monoidalClosedHomEquiv /-
/-- Auxiliary definition for the `monoidal_closed` instance on `Module R`.
(This is only a separate definition in order to speed up typechecking. )
-/
@[simps]
def monoidalClosedHomEquiv (M N P : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft M).obj N ⟶ P) ≃
      (N ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op M)).obj P)
    where
  toFun f := LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).Hom ≫ f)
  invFun f := (β_ M N).Hom ≫ TensorProduct.lift f
  left_inv f := by
    ext m n
    simp only [TensorProduct.mk_apply, TensorProduct.lift.tmul, LinearMap.compr₂_apply,
      Function.comp_apply, coe_comp, monoidal_category.braiding_hom_apply]
  right_inv f := by
    ext m n
    simp only [TensorProduct.mk_apply, TensorProduct.lift.tmul, LinearMap.compr₂_apply,
      symmetric_category.symmetry_assoc]
#align Module.monoidal_closed_hom_equiv ModuleCat.monoidalClosedHomEquiv
-/

instance : MonoidalClosed (ModuleCat.{u} R)
    where closed' M :=
    {
      isAdj :=
        { right := (linearCoyoneda R (ModuleCat.{u} R)).obj (op M)
          adj := Adjunction.mkOfHomEquiv { homEquiv := fun N P => monoidalClosedHomEquiv M N P } } }

#print ModuleCat.ihom_map_apply /-
theorem ihom_map_apply {M N P : ModuleCat.{u} R} (f : N ⟶ P) (g : ModuleCat.of R (M ⟶ N)) :
    (ihom M).map f g = g ≫ f :=
  rfl
#align Module.ihom_map_apply ModuleCat.ihom_map_apply
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print ModuleCat.monoidalClosed_curry /-
-- I can't seem to express the function coercion here without writing `@coe_fn`.
@[simp]
theorem monoidalClosed_curry {M N P : ModuleCat.{u} R} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
    @coeFn _ _ LinearMap.hasCoeToFun ((MonoidalClosed.curry f : N →ₗ[R] M →ₗ[R] P) y) x =
      f (x ⊗ₜ[R] y) :=
  rfl
#align Module.monoidal_closed_curry ModuleCat.monoidalClosed_curry
-/

#print ModuleCat.monoidalClosed_uncurry /-
@[simp]
theorem monoidalClosed_uncurry {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M)
    (y : N) : MonoidalClosed.uncurry f (x ⊗ₜ[R] y) = (@coeFn _ _ LinearMap.hasCoeToFun (f y)) x :=
  rfl
#align Module.monoidal_closed_uncurry ModuleCat.monoidalClosed_uncurry
-/

#print ModuleCat.ihom_ev_app /-
/-- Describes the counit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this
should give a map `M ⊗ Hom(M, N) ⟶ N`, so we flip the order of the arguments in the identity map
`Hom(M, N) ⟶ (M ⟶ N)` and uncurry the resulting map `M ⟶ Hom(M, N) ⟶ N.` -/
theorem ihom_ev_app (M N : ModuleCat.{u} R) :
    (ihom.ev M).app N = TensorProduct.uncurry _ _ _ _ LinearMap.id.flip :=
  by
  ext
  exact ModuleCat.monoidalClosed_uncurry _ _ _
#align Module.ihom_ev_app ModuleCat.ihom_ev_app
-/

#print ModuleCat.ihom_coev_app /-
/-- Describes the unit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this should
define a map `N ⟶ Hom(M, M ⊗ N)`, which is given by flipping the arguments in the natural
`R`-bilinear map `M ⟶ N ⟶ M ⊗ N`. -/
theorem ihom_coev_app (M N : ModuleCat.{u} R) :
    (ihom.coev M).app N = (TensorProduct.mk _ _ _).flip :=
  rfl
#align Module.ihom_coev_app ModuleCat.ihom_coev_app
-/

#print ModuleCat.monoidalClosed_pre_app /-
theorem monoidalClosed_pre_app {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R) (f : N ⟶ M) :
    (MonoidalClosed.pre f).app P = LinearMap.lcomp R _ f :=
  rfl
#align Module.monoidal_closed_pre_app ModuleCat.monoidalClosed_pre_app
-/

end ModuleCat

