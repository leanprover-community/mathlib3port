/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Algebra.Group.Defs
import Logic.Embedding.Basic

#align_import algebra.hom.embedding from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# The embedding of a cancellative semigroup into itself by multiplication by a fixed element.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {R : Type _}

section LeftOrRightCancelSemigroup

#print mulLeftEmbedding /-
/-- The embedding of a left cancellative semigroup into itself
by left multiplication by a fixed element.
 -/
@[to_additive
      "The embedding of a left cancellative additive semigroup into itself\n   by left translation by a fixed element.",
  simps]
def mulLeftEmbedding {G : Type _} [LeftCancelSemigroup G] (g : G) : G ↪ G
    where
  toFun h := g * h
  inj' := mul_right_injective g
#align mul_left_embedding mulLeftEmbedding
#align add_left_embedding addLeftEmbedding
-/

#print mulRightEmbedding /-
/-- The embedding of a right cancellative semigroup into itself
by right multiplication by a fixed element.
 -/
@[to_additive
      "The embedding of a right cancellative additive semigroup into itself\n   by right translation by a fixed element.",
  simps]
def mulRightEmbedding {G : Type _} [RightCancelSemigroup G] (g : G) : G ↪ G
    where
  toFun h := h * g
  inj' := mul_left_injective g
#align mul_right_embedding mulRightEmbedding
#align add_right_embedding addRightEmbedding
-/

#print mulLeftEmbedding_eq_mulRightEmbedding /-
@[to_additive]
theorem mulLeftEmbedding_eq_mulRightEmbedding {G : Type _} [CancelCommMonoid G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by ext; exact mul_comm _ _
#align mul_left_embedding_eq_mul_right_embedding mulLeftEmbedding_eq_mulRightEmbedding
#align add_left_embedding_eq_add_right_embedding addLeftEmbedding_eq_addRightEmbedding
-/

end LeftOrRightCancelSemigroup

