/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser

! This file was ported from Lean 3 source module algebra.graded_mul_action
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GradedMonoid

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

#print GradedMonoid.GSmul /-
/-- A graded version of `has_smul`. Scalar multiplication combines grades additively, i.e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`-/
class GSmul [Add ι] where
  smul {i j} : A i → M j → M (i + j)
#align graded_monoid.ghas_smul GradedMonoid.GSmul
-/

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

/- warning: graded_monoid.mk_smul_mk -> GradedMonoid.mk_smul_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) (M : ι -> Type.{u3}) [_inst_1 : Add.{u1} ι] [_inst_2 : GradedMonoid.GSmul.{u1, u2, u3} ι A M _inst_1] {i : ι} {j : ι} (a : A i) (b : M j), Eq.{succ (max u1 u3)} (GradedMonoid.{u1, u3} ι (fun {j : ι} => M j)) (SMul.smul.{max u1 u2, max u1 u3} (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) (GradedMonoid.{u1, u3} ι (fun {j : ι} => M j)) (GradedMonoid.GSmul.toSMul.{u1, u2, u3} ι (fun {i : ι} => A i) (fun {j : ι} => M j) _inst_1 _inst_2) (GradedMonoid.mk.{u1, u2} ι (fun {i : ι} => A i) i a) (GradedMonoid.mk.{u1, u3} ι (fun {j : ι} => M j) j b)) (GradedMonoid.mk.{u1, u3} ι (fun {j : ι} => M j) (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι _inst_1) i j) (GradedMonoid.GSmul.smul.{u1, u2, u3} ι (fun {i : ι} => A i) M _inst_1 _inst_2 i j a b))
but is expected to have type
  forall {ι : Type.{u3}} (A : ι -> Type.{u2}) (M : ι -> Type.{u1}) [_inst_1 : Add.{u3} ι] [_inst_2 : GradedMonoid.GSmul.{u3, u2, u1} ι A M _inst_1] {i : ι} {j : ι} (a : A i) (b : M j), Eq.{max (succ u3) (succ u1)} (GradedMonoid.{u3, u1} ι M) (HSMul.hSMul.{max u2 u3, max u1 u3, max u3 u1} (GradedMonoid.{u3, u2} ι A) (GradedMonoid.{u3, u1} ι M) (GradedMonoid.{u3, u1} ι M) (instHSMul.{max u3 u2, max u3 u1} (GradedMonoid.{u3, u2} ι A) (GradedMonoid.{u3, u1} ι M) (GradedMonoid.GSmul.toSMul.{u3, u2, u1} ι A M _inst_1 _inst_2)) (GradedMonoid.mk.{u3, u2} ι A i a) (GradedMonoid.mk.{u3, u1} ι M j b)) (GradedMonoid.mk.{u3, u1} ι M (HAdd.hAdd.{u3, u3, u3} ι ι ι (instHAdd.{u3} ι _inst_1) i j) (GradedMonoid.GSmul.smul.{u3, u2, u1} ι A M _inst_1 _inst_2 i j a b))
Case conversion may be inaccurate. Consider using '#align graded_monoid.mk_smul_mk GradedMonoid.mk_smul_mkₓ'. -/
theorem mk_smul_mk [Add ι] [GSmul A M] {i j} (a : A i) (b : M j) :
    mk i a • mk j b = mk (i + j) (GSmul.smul a b) :=
  rfl
#align graded_monoid.mk_smul_mk GradedMonoid.mk_smul_mk

#print GradedMonoid.GMulAction /-
/-- A graded version of `mul_action`. -/
class GMulAction [AddMonoid ι] [GMonoid A] extends GSmul A M where
  one_smul (b : GradedMonoid M) : (1 : GradedMonoid A) • b = b
  mul_smul (a a' : GradedMonoid A) (b : GradedMonoid M) : (a * a') • b = a • a' • b
#align graded_monoid.gmul_action GradedMonoid.GMulAction
-/

#print GradedMonoid.GMonoid.toGMulAction /-
/-- The graded version of `monoid.to_mul_action`. -/
instance GMonoid.toGMulAction [AddMonoid ι] [GMonoid A] : GMulAction A A :=
  { GMul.toGSmul _ with
    one_smul := GMonoid.one_mul
    mul_smul := GMonoid.mul_assoc }
#align graded_monoid.gmonoid.to_gmul_action GradedMonoid.GMonoid.toGMulAction
-/

#print GradedMonoid.GMulAction.toMulAction /-
instance GMulAction.toMulAction [AddMonoid ι] [GMonoid A] [GMulAction A M] :
    MulAction (GradedMonoid A) (GradedMonoid M)
    where
  one_smul := GMulAction.one_smul
  mul_smul := GMulAction.mul_smul
#align graded_monoid.gmul_action.to_mul_action GradedMonoid.GMulAction.toMulAction
-/

end Defs

end GradedMonoid

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type _}

#print SetLike.GradedSmul /-
/-- A version of `graded_monoid.ghas_smul` for internally graded objects. -/
class SetLike.GradedSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
  (A : ι → S) (B : ι → N) : Prop where
  smul_mem : ∀ ⦃i j : ι⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i + j)
#align set_like.has_graded_smul SetLike.GradedSmul
-/

#print SetLike.toGSmul /-
instance SetLike.toGSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) [SetLike.GradedSmul A B] :
    GradedMonoid.GSmul (fun i => A i) fun i => B i
    where smul i j a b := ⟨(a : R) • b, SetLike.GradedSmul.smul_mem a.2 b.2⟩
#align set_like.ghas_smul SetLike.toGSmul
-/

/- warning: set_like.coe_ghas_smul -> SetLike.coe_GSmul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {S : Type.{u2}} {R : Type.{u3}} {N : Type.{u4}} {M : Type.{u5}} [_inst_1 : SetLike.{u2, u3} S R] [_inst_2 : SetLike.{u4, u5} N M] [_inst_3 : SMul.{u3, u5} R M] [_inst_4 : Add.{u1} ι] (A : ι -> S) (B : ι -> N) [_inst_5 : SetLike.GradedSmul.{u1, u2, u3, u4, u5} ι S R N M _inst_1 _inst_2 _inst_3 _inst_4 A B] {i : ι} {j : ι} (x : coeSort.{succ u2, succ (succ u3)} S Type.{u3} (SetLike.hasCoeToSort.{u2, u3} S R _inst_1) (A i)) (y : coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B j)), Eq.{succ u5} M ((fun (a : Type.{u5}) (b : Type.{u5}) [self : HasLiftT.{succ u5, succ u5} a b] => self.0) ((fun (i : ι) => coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B i)) (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι _inst_4) i j)) M (HasLiftT.mk.{succ u5, succ u5} ((fun (i : ι) => coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B i)) (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι _inst_4) i j)) M (CoeTCₓ.coe.{succ u5, succ u5} ((fun (i : ι) => coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B i)) (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι _inst_4) i j)) M (coeBase.{succ u5, succ u5} ((fun (i : ι) => coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B i)) (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι _inst_4) i j)) M (coeSubtype.{succ u5} M (fun (x : M) => Membership.Mem.{u5, u4} M N (SetLike.hasMem.{u4, u5} N M _inst_2) x (B (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι _inst_4) i j))))))) (GradedMonoid.GSmul.smul.{u1, u3, u5} ι (fun (i : ι) => coeSort.{succ u2, succ (succ u3)} S Type.{u3} (SetLike.hasCoeToSort.{u2, u3} S R _inst_1) (A i)) (fun (i : ι) => coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B i)) _inst_4 (SetLike.toGSmul.{u1, u2, u3, u4, u5} ι S R N M _inst_1 _inst_2 _inst_3 _inst_4 (fun (i : ι) => A i) (fun (i : ι) => B i) _inst_5) i j x y)) (SMul.smul.{u3, u5} R M _inst_3 ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u2, succ (succ u3)} S Type.{u3} (SetLike.hasCoeToSort.{u2, u3} S R _inst_1) (A i)) R (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u2, succ (succ u3)} S Type.{u3} (SetLike.hasCoeToSort.{u2, u3} S R _inst_1) (A i)) R (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u2, succ (succ u3)} S Type.{u3} (SetLike.hasCoeToSort.{u2, u3} S R _inst_1) (A i)) R (coeBase.{succ u3, succ u3} (coeSort.{succ u2, succ (succ u3)} S Type.{u3} (SetLike.hasCoeToSort.{u2, u3} S R _inst_1) (A i)) R (coeSubtype.{succ u3} R (fun (x : R) => Membership.Mem.{u3, u2} R S (SetLike.hasMem.{u2, u3} S R _inst_1) x (A i)))))) x) ((fun (a : Type.{u5}) (b : Type.{u5}) [self : HasLiftT.{succ u5, succ u5} a b] => self.0) (coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B j)) M (HasLiftT.mk.{succ u5, succ u5} (coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B j)) M (CoeTCₓ.coe.{succ u5, succ u5} (coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B j)) M (coeBase.{succ u5, succ u5} (coeSort.{succ u4, succ (succ u5)} N Type.{u5} (SetLike.hasCoeToSort.{u4, u5} N M _inst_2) (B j)) M (coeSubtype.{succ u5} M (fun (x : M) => Membership.Mem.{u5, u4} M N (SetLike.hasMem.{u4, u5} N M _inst_2) x (B j)))))) y))
but is expected to have type
  forall {ι : Type.{u1}} {S : Type.{u5}} {R : Type.{u4}} {N : Type.{u3}} {M : Type.{u2}} [_inst_1 : SetLike.{u5, u4} S R] [_inst_2 : SetLike.{u3, u2} N M] [_inst_3 : SMul.{u4, u2} R M] [_inst_4 : Add.{u1} ι] (A : ι -> S) (B : ι -> N) [_inst_5 : SetLike.GradedSmul.{u1, u5, u4, u3, u2} ι S R N M _inst_1 _inst_2 _inst_3 _inst_4 A B] {i : ι} {j : ι} (x : Subtype.{succ u4} R (fun (x : R) => Membership.mem.{u4, u5} R S (SetLike.instMembership.{u5, u4} S R _inst_1) x (A i))) (y : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u3} M N (SetLike.instMembership.{u3, u2} N M _inst_2) x (B j))), Eq.{succ u2} M (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u3, u2} N M _inst_2 (B (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι _inst_4) i j)))) (GradedMonoid.GSmul.smul.{u1, u4, u2} ι (fun (i : ι) => Subtype.{succ u4} R (fun (x : R) => Membership.mem.{u4, u5} R S (SetLike.instMembership.{u5, u4} S R _inst_1) x (A i))) (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u3} M N (SetLike.instMembership.{u3, u2} N M _inst_2) x (B i))) _inst_4 (SetLike.toGSmul.{u1, u5, u4, u3, u2} ι S R N M _inst_1 _inst_2 _inst_3 _inst_4 (fun (i : ι) => A i) (fun (i : ι) => B i) _inst_5) i j x y)) (HSMul.hSMul.{u4, u2, u2} R M M (instHSMul.{u4, u2} R M _inst_3) (Subtype.val.{succ u4} R (fun (x : R) => Membership.mem.{u4, u5} R S (SetLike.instMembership.{u5, u4} S R _inst_1) x (A i)) x) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u3} M N (SetLike.instMembership.{u3, u2} N M _inst_2) x (B j)) y))
Case conversion may be inaccurate. Consider using '#align set_like.coe_ghas_smul SetLike.coe_GSmulₓ'. -/
@[simp]
theorem SetLike.coe_GSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) [SetLike.GradedSmul A B] {i j : ι} (x : A i) (y : B j) :
    (@GradedMonoid.GSmul.smul ι (fun i => A i) (fun i => B i) _ _ i j x y : M) = (x : R) • y :=
  rfl
#align set_like.coe_ghas_smul SetLike.coe_GSmul

/- warning: set_like.has_graded_mul.to_has_graded_smul -> SetLike.GradedMul.toGradedSmul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : Monoid.{u2} R] {S : Type.{u3}} [_inst_3 : SetLike.{u3, u2} S R] (A : ι -> S) [_inst_4 : SetLike.GradedMonoid.{u1, u2, u3} ι R S _inst_3 _inst_2 _inst_1 A], SetLike.GradedSmul.{u1, u3, u2, u3, u2} ι S R S R _inst_3 _inst_3 (Mul.toSMul.{u2} R (MulOneClass.toHasMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2))) (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) A A
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : Monoid.{u2} R] {S : Type.{u3}} [_inst_3 : SetLike.{u3, u2} S R] (A : ι -> S) [_inst_4 : SetLike.GradedMonoid.{u1, u2, u3} ι R S _inst_3 _inst_2 _inst_1 A], SetLike.GradedSmul.{u1, u3, u2, u3, u2} ι S R S R _inst_3 _inst_3 (MulAction.toSMul.{u2, u2} R R _inst_2 (Monoid.toMulAction.{u2} R _inst_2)) (AddZeroClass.toAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) A A
Case conversion may be inaccurate. Consider using '#align set_like.has_graded_mul.to_has_graded_smul SetLike.GradedMul.toGradedSmulₓ'. -/
/-- Internally graded version of `has_mul.to_has_smul`. -/
instance SetLike.GradedMul.toGradedSmul [AddMonoid ι] [Monoid R] {S : Type _} [SetLike S R]
    (A : ι → S) [SetLike.GradedMonoid A] : SetLike.GradedSmul A A
    where smul_mem i j ai bj hi hj := SetLike.GradedMonoid.mul_mem hi hj
#align set_like.has_graded_mul.to_has_graded_smul SetLike.GradedMul.toGradedSmul

end Subobjects

section HomogeneousElements

variable {S R N M : Type _} [SetLike S R] [SetLike N M]

/- warning: set_like.is_homogeneous.graded_smul -> SetLike.Homogeneous.graded_smul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {S : Type.{u2}} {R : Type.{u3}} {N : Type.{u4}} {M : Type.{u5}} [_inst_1 : SetLike.{u2, u3} S R] [_inst_2 : SetLike.{u4, u5} N M] [_inst_3 : Add.{u1} ι] [_inst_4 : SMul.{u3, u5} R M] {A : ι -> S} {B : ι -> N} [_inst_5 : SetLike.GradedSmul.{u1, u2, u3, u4, u5} ι S R N M _inst_1 _inst_2 _inst_4 _inst_3 A B] {a : R} {b : M}, (SetLike.Homogeneous.{u1, u3, u2} ι R S _inst_1 A a) -> (SetLike.Homogeneous.{u1, u5, u4} ι M N _inst_2 B b) -> (SetLike.Homogeneous.{u1, u5, u4} ι M N _inst_2 B (SMul.smul.{u3, u5} R M _inst_4 a b))
but is expected to have type
  forall {ι : Type.{u5}} {S : Type.{u2}} {R : Type.{u4}} {N : Type.{u1}} {M : Type.{u3}} [_inst_1 : SetLike.{u2, u4} S R] [_inst_2 : SetLike.{u1, u3} N M] [_inst_3 : Add.{u5} ι] [_inst_4 : SMul.{u4, u3} R M] {A : ι -> S} {B : ι -> N} [_inst_5 : SetLike.GradedSmul.{u5, u2, u4, u1, u3} ι S R N M _inst_1 _inst_2 _inst_4 _inst_3 A B] {a : R} {b : M}, (SetLike.Homogeneous.{u5, u4, u2} ι R S _inst_1 A a) -> (SetLike.Homogeneous.{u5, u3, u1} ι M N _inst_2 B b) -> (SetLike.Homogeneous.{u5, u3, u1} ι M N _inst_2 B (HSMul.hSMul.{u4, u3, u3} R M M (instHSMul.{u4, u3} R M _inst_4) a b))
Case conversion may be inaccurate. Consider using '#align set_like.is_homogeneous.graded_smul SetLike.Homogeneous.graded_smulₓ'. -/
theorem SetLike.Homogeneous.graded_smul [Add ι] [SMul R M] {A : ι → S} {B : ι → N}
    [SetLike.GradedSmul A B] {a : R} {b : M} :
    SetLike.Homogeneous A a → SetLike.Homogeneous B b → SetLike.Homogeneous B (a • b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.GradedSmul.smul_mem hi hj⟩
#align set_like.is_homogeneous.graded_smul SetLike.Homogeneous.graded_smul

end HomogeneousElements

