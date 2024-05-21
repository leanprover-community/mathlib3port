/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import CategoryTheory.Limits.Shapes.BinaryProducts
import CategoryTheory.Monad.Products
import CategoryTheory.Comma.Over

#align_import category_theory.adjunction.over from "leanprover-community/mathlib"@"4f81bc21e32048db7344b7867946e992cf5f68cc"

/-!
# Adjunctions related to the over category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Construct the left adjoint `star X` to `over.forget X : over X ⥤ C`.

## TODO
Show `star X` itself has a left adjoint provided `C` is locally cartesian closed.
-/


noncomputable section

universe v u

-- declare the `v`'s first; see `category_theory.category` for an explanation
namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [Category.{v} C] (X : C)

#print CategoryTheory.Over.star /-
/--
The functor from `C` to `over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps obj_left obj_hom mapLeft]
def CategoryTheory.Over.star [HasBinaryProducts C] : C ⥤ Over X :=
  cofree _ ⋙ coalgebraToOver X
#align category_theory.star CategoryTheory.Over.star
-/

#print CategoryTheory.Over.forgetAdjStar /-
/-- The functor `over.forget X : over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def CategoryTheory.Over.forgetAdjStar [HasBinaryProducts C] :
    Over.forget X ⊣ CategoryTheory.Over.star X :=
  (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)
#align category_theory.forget_adj_star CategoryTheory.Over.forgetAdjStar
-/

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [HasBinaryProducts C] : CategoryTheory.Functor.IsLeftAdjoint (Over.forget X) :=
  ⟨_, CategoryTheory.Over.forgetAdjStar X⟩

end CategoryTheory

