/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import AlgebraicTopology.SimplicialObject
import CategoryTheory.Idempotents.FunctorCategories

#align_import category_theory.idempotents.simplicial_object from "leanprover-community/mathlib"@"9a48a083b390d9b84a71efbdc4e8dfa26a687104"

/-!

# Idempotent completeness of categories of simplicial objects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we provide an instance expressing that `simplicial_object C`
and `cosimplicial_object C` are idempotent complete categories when the
category `C` is.

-/


namespace CategoryTheory

namespace Idempotents

variable {C : Type _} [Category C] [IsIdempotentComplete C]

instance : IsIdempotentComplete (SimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _

instance : IsIdempotentComplete (CosimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _

end Idempotents

end CategoryTheory

