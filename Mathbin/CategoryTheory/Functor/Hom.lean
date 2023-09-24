/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import CategoryTheory.Products.Basic
import CategoryTheory.Types

#align_import category_theory.functor.hom from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The hom functor, sending `(X, Y)` to the type `X ⟶ Y`.
-/


universe v u

open Opposite

open CategoryTheory

namespace CategoryTheory.Functor

variable (C : Type u) [Category.{v} C]

#print CategoryTheory.Functor.hom /-
/-- `functor.hom` is the hom-pairing, sending `(X, Y)` to `X ⟶ Y`, contravariant in `X` and
covariant in `Y`. -/
@[simps]
def hom : Cᵒᵖ × C ⥤ Type v where
  obj p := unop p.1 ⟶ p.2
  map X Y f h := f.1.unop ≫ h ≫ f.2
#align category_theory.functor.hom CategoryTheory.Functor.hom
-/

end CategoryTheory.Functor

