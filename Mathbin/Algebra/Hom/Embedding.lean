/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.hom.embedding
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Embedding.Basic

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
-/

#print mul_left_embedding_eq_mul_right_embedding /-
@[to_additive]
theorem mul_left_embedding_eq_mul_right_embedding {G : Type _} [CancelCommMonoid G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by
  ext
  exact mul_comm _ _
#align mul_left_embedding_eq_mul_right_embedding mul_left_embedding_eq_mul_right_embedding
-/

end LeftOrRightCancelSemigroup

