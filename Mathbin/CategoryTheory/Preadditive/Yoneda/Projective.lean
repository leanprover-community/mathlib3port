/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.Yoneda.Basic
import Mathbin.CategoryTheory.Preadditive.Projective
import Mathbin.Algebra.Category.Group.EpiMono
import Mathbin.Algebra.Category.Module.EpiMono

#align_import category_theory.preadditive.yoneda.projective from "leanprover-community/mathlib"@"bd15ff41b70f5e2cc210f26f25a8d5c53b20d3de"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An object is projective iff the preadditive coyoneda functor on it preserves epimorphisms.
-/


universe v u

open Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

namespace Projective

#print CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj /-
theorem projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj (P : C) :
    Projective P ↔ (preadditiveCoyoneda.obj (op P)).PreservesEpimorphisms :=
  by
  rw [projective_iff_preserves_epimorphisms_coyoneda_obj]
  refine' ⟨fun h : (preadditive_coyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms => _, _⟩
  ·
    exact
      functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda.obj (op P))
        (forget _)
  · intro
    exact (inferInstance : (preadditive_coyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms)
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj
-/

#print CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj' /-
theorem projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj' (P : C) :
    Projective P ↔ (preadditiveCoyonedaObj (op P)).PreservesEpimorphisms :=
  by
  rw [projective_iff_preserves_epimorphisms_coyoneda_obj]
  refine' ⟨fun h : (preadditive_coyoneda_obj (op P) ⋙ forget _).PreservesEpimorphisms => _, _⟩
  ·
    exact
      functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda_obj (op P))
        (forget _)
  · intro
    exact (inferInstance : (preadditive_coyoneda_obj (op P) ⋙ forget _).PreservesEpimorphisms)
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj'
-/

end Projective

end Preadditive

end CategoryTheory

