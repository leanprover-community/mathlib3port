/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathbin.CategoryTheory.Abelian.Exact
import Mathbin.CategoryTheory.Preadditive.Injective
import Mathbin.CategoryTheory.Preadditive.Yoneda

/-!
# Injective objects in abelian categories

* Objects in an abelian categories are injective if and only if the preadditive Yoneda functor
  on them preserves finite colimits.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Injective

open Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The preadditive Yoneda functor on `J` preserves colimits if `J` is injective. -/
def preservesFiniteColimitsPreadditiveYonedaObjOfInjective (J : C) [hP : Injective J] :
    PreservesFiniteColimits (preadditiveYonedaObj J) := by
  letI := (injective_iff_preserves_epimorphisms_preadditive_yoneda_obj' J).mp hP
  apply functor.preserves_finite_colimits_of_preserves_epis_and_kernels

/-- An object is injective if its preadditive Yoneda functor preserves finite colimits. -/
theorem injective_of_preserves_finite_colimits_preadditive_yoneda_obj (J : C)
    [hP : PreservesFiniteColimits (preadditiveYonedaObj J)] : Injective J := by
  rw [injective_iff_preserves_epimorphisms_preadditive_yoneda_obj']
  infer_instance

end CategoryTheory

