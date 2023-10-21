/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Algebra.GradedMonoid

#align_import algebra.graded_mul_action from "leanprover-community/mathlib"@"0ebfdb71919ac6ca5d7fbc61a082fa2519556818"

/-!
# Additively-graded multiplicative action structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `graded_monoid A` such that `(•) : A i → M j → M (i + j)`; that is to say, `A`
has an additively-graded multiplicative action on `M`. The typeclasses are:

* `graded_monoid.ghas_smul A M`
* `graded_monoid.gmul_action A M`

With the `sigma_graded` locale open, these respectively imbue:

* `has_smul (graded_monoid A) (graded_monoid M)`
* `mul_action (graded_monoid A) (graded_monoid M)`

For now, these typeclasses are primarily used in the construction of `direct_sum.gmodule.module` and
the rest of that file.

## Internally graded multiplicative actions

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`set_like` subobjects (such as `add_submonoid`s, `add_subgroup`s, or `submodule`s), this file
provides the `Prop` typeclasses:

* `set_like.has_graded_smul A M` (which provides the obvious `graded_monoid.ghas_smul A` instance)

which provides the API lemma

* `set_like.graded_smul_mem_graded`

Note that there is no need for `set_like.graded_mul_action` or similar, as all the information it
would contain is already supplied by `has_graded_smul` when the objects within `A` and `M` have
a `mul_action` instance.

## tags

graded action
-/


variable {ι : Type _}

namespace GradedMonoid

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _) (M : ι → Type _)

/-- A graded version of `has_smul`. Scalar multiplication combines grades additively, i.e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`-/
class GSmul [Add ι] where
  smul {i j} : A i → M j → M (i + j)
#align graded_monoid.ghas_smul GradedMonoid.GSmulₓ

#print GradedMonoid.GMul.toGSmul /-
/-- A graded version of `has_mul.to_has_smul` -/
instance GMul.toGSmul [Add ι] [GMul A] : GSmul A A where smul _ _ := GMul.mul
#align graded_monoid.ghas_mul.to_ghas_smul GradedMonoid.GMul.toGSmul
-/

#print GradedMonoid.GSmul.toSMul /-
instance GSmul.toSMul [Add ι] [GSmul A M] : SMul (GradedMonoid A) (GradedMonoid M) :=
  ⟨fun (x : GradedMonoid A) (y : GradedMonoid M) => ⟨_, GSmul.smul x.snd y.snd⟩⟩
#align graded_monoid.ghas_smul.to_has_smul GradedMonoid.GSmul.toSMul
-/

#print GradedMonoid.mk_smul_mk /-
theorem mk_smul_mk [Add ι] [GSmul A M] {i j} (a : A i) (b : M j) :
    mk i a • mk j b = mk (i + j) (GSmul.smul a b) :=
  rfl
#align graded_monoid.mk_smul_mk GradedMonoid.mk_smul_mk
-/

/-- A graded version of `mul_action`. -/
class GMulAction [AddMonoid ι] [GMonoid A] extends GSmul A M where
  one_smul (b : GradedMonoid M) : (1 : GradedMonoid A) • b = b
  hMul_smul (a a' : GradedMonoid A) (b : GradedMonoid M) : (a * a') • b = a • a' • b
#align graded_monoid.gmul_action GradedMonoid.GMulActionₓ

#print GradedMonoid.GMonoid.toGMulAction /-
/-- The graded version of `monoid.to_mul_action`. -/
instance GMonoid.toGMulAction [AddMonoid ι] [GMonoid A] : GMulAction A A :=
  { GMul.toGSmul _ with
    one_smul := GMonoid.one_hMul
    hMul_smul := GMonoid.hMul_assoc }
#align graded_monoid.gmonoid.to_gmul_action GradedMonoid.GMonoid.toGMulAction
-/

#print GradedMonoid.GMulAction.toMulAction /-
instance GMulAction.toMulAction [AddMonoid ι] [GMonoid A] [GMulAction A M] :
    MulAction (GradedMonoid A) (GradedMonoid M)
    where
  one_smul := GMulAction.one_smul
  hMul_smul := GMulAction.hMul_smul
#align graded_monoid.gmul_action.to_mul_action GradedMonoid.GMulAction.toMulAction
-/

end Defs

end GradedMonoid

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type _}

/-- A version of `graded_monoid.ghas_smul` for internally graded objects. -/
class SetLike.GradedSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) : Prop where
  smul_mem : ∀ ⦃i j : ι⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i + j)
#align set_like.has_graded_smul SetLike.GradedSmulₓ

#print SetLike.toGSmul /-
instance SetLike.toGSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) [SetLike.GradedSmul A B] :
    GradedMonoid.GSmul (fun i => A i) fun i => B i
    where smul i j a b := ⟨(a : R) • b, SetLike.GradedSmul.smul_mem a.2 b.2⟩
#align set_like.ghas_smul SetLike.toGSmul
-/

#print SetLike.coe_GSmul /-
@[simp]
theorem SetLike.coe_GSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) [SetLike.GradedSmul A B] {i j : ι} (x : A i) (y : B j) :
    (@GradedMonoid.GSmul.smul ι (fun i => A i) (fun i => B i) _ _ i j x y : M) = (x : R) • y :=
  rfl
#align set_like.coe_ghas_smul SetLike.coe_GSmul
-/

#print SetLike.GradedMul.toGradedSmul /-
/-- Internally graded version of `has_mul.to_has_smul`. -/
instance SetLike.GradedMul.toGradedSmul [AddMonoid ι] [Monoid R] {S : Type _} [SetLike S R]
    (A : ι → S) [SetLike.GradedMonoid A] : SetLike.GradedSmul A A
    where smul_mem i j ai bj hi hj := SetLike.GradedMonoid.hMul_mem hi hj
#align set_like.has_graded_mul.to_has_graded_smul SetLike.GradedMul.toGradedSmul
-/

end Subobjects

section HomogeneousElements

variable {S R N M : Type _} [SetLike S R] [SetLike N M]

#print SetLike.Homogeneous.graded_smul /-
theorem SetLike.Homogeneous.graded_smul [Add ι] [SMul R M] {A : ι → S} {B : ι → N}
    [SetLike.GradedSmul A B] {a : R} {b : M} :
    SetLike.Homogeneous A a → SetLike.Homogeneous B b → SetLike.Homogeneous B (a • b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.GradedSmul.smul_mem hi hj⟩
#align set_like.is_homogeneous.graded_smul SetLike.Homogeneous.graded_smul
-/

end HomogeneousElements

