/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.Ring.Pi

#align_import algebra.star.pi from "leanprover-community/mathlib"@"9abfa6f0727d5adc99067e325e15d1a9de17fd8e"

/-!
# `star` on pi types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We put a `has_star` structure on pi types that operates elementwise, such that it describes the
complex conjugation of vectors.
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
namespace Pi

instance [∀ i, Star (f i)] : Star (∀ i, f i) where unit x i := star (x i)

#print Pi.star_apply /-
@[simp]
theorem star_apply [∀ i, Star (f i)] (x : ∀ i, f i) (i : I) : star x i = star (x i) :=
  rfl
#align pi.star_apply Pi.star_apply
-/

#print Pi.star_def /-
theorem star_def [∀ i, Star (f i)] (x : ∀ i, f i) : star x = fun i => star (x i) :=
  rfl
#align pi.star_def Pi.star_def
-/

instance [∀ i, Star (f i)] [∀ i, TrivialStar (f i)] : TrivialStar (∀ i, f i)
    where star_trivial _ := funext fun _ => star_trivial _

instance [∀ i, InvolutiveStar (f i)] : InvolutiveStar (∀ i, f i)
    where star_involutive _ := funext fun _ => star_star _

instance [∀ i, Semigroup (f i)] [∀ i, StarSemigroup (f i)] : StarSemigroup (∀ i, f i)
    where star_hMul _ _ := funext fun _ => star_hMul _ _

instance [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] : StarAddMonoid (∀ i, f i)
    where star_add _ _ := funext fun _ => star_add _ _

instance [∀ i, NonUnitalSemiring (f i)] [∀ i, StarRing (f i)] : StarRing (∀ i, f i) :=
  { Pi.starAddMonoid, (Pi.starSemigroup : StarSemigroup (∀ i, f i)) with }

instance {R : Type w} [∀ i, SMul R (f i)] [Star R] [∀ i, Star (f i)] [∀ i, StarModule R (f i)] :
    StarModule R (∀ i, f i) where star_smul r x := funext fun i => star_smul r (x i)

#print Pi.single_star /-
theorem single_star [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] [DecidableEq I] (i : I)
    (a : f i) : Pi.single i (star a) = star (Pi.single i a) :=
  single_op (fun i => @star (f i) _) (fun i => star_zero _) i a
#align pi.single_star Pi.single_star
-/

end Pi

namespace Function

#print Function.update_star /-
theorem update_star [∀ i, Star (f i)] [DecidableEq I] (h : ∀ i : I, f i) (i : I) (a : f i) :
    Function.update (star h) i (star a) = star (Function.update h i a) :=
  funext fun j => (apply_update (fun i => star) h i a j).symm
#align function.update_star Function.update_star
-/

#print Function.star_sum_elim /-
theorem star_sum_elim {I J α : Type _} (x : I → α) (y : J → α) [Star α] :
    star (Sum.elim x y) = Sum.elim (star x) (star y) := by ext x; cases x <;> simp
#align function.star_sum_elim Function.star_sum_elim
-/

end Function

