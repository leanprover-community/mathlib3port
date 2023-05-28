/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module algebra.algebra.unitization
! leanprover-community/mathlib commit 932872382355f00112641d305ba0619305dc8642
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.LinearAlgebra.Prod
import Mathbin.Algebra.Hom.NonUnitalAlg

/-!
# Unitization of a non-unital algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a non-unital `R`-algebra `A` (given via the type classes
`[non_unital_ring A] [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]`) we construct
the minimal unital `R`-algebra containing `A` as an ideal. This object `algebra.unitization R A` is
a type synonym for `R × A` on which we place a different multiplicative structure, namely,
`(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity
is `(1, 0)`.

Note, when `A` is a *unital* `R`-algebra, then `unitization R A` constructs a new multiplicative
identity different from the old one, and so in general `unitization R A` and `A` will not be
isomorphic even in the unital case. This approach actually has nice functorial properties.

There is a natural coercion from `A` to `unitization R A` given by `λ a, (0, a)`, the image
of which is a proper ideal (TODO), and when `R` is a field this ideal is maximal. Moreover,
this ideal is always an essential ideal (it has nontrivial intersection with every other nontrivial
ideal).

Every non-unital algebra homomorphism from `A` into a *unital* `R`-algebra `B` has a unique
extension to a (unital) algebra homomorphism from `unitization R A` to `B`.

## Main definitions

* `unitization R A`: the unitization of a non-unital `R`-algebra `A`.
* `unitization.algebra`: the unitization of `A` as a (unital) `R`-algebra.
* `unitization.coe_non_unital_alg_hom`: coercion as a non-unital algebra homomorphism.
* `non_unital_alg_hom.to_alg_hom φ`: the extension of a non-unital algebra homomorphism `φ : A → B`
  into a unital `R`-algebra `B` to an algebra homomorphism `unitization R A →ₐ[R] B`.

## Main results

* `non_unital_alg_hom.to_alg_hom_unique`: the extension is unique

## TODO

* prove the unitization operation is a functor between the appropriate categories
* prove the image of the coercion is an essential ideal, maximal if scalars are a field.
-/


#print Unitization /-
/-- The minimal unitization of a non-unital `R`-algebra `A`. This is just a type synonym for
`R × A`.-/
def Unitization (R A : Type _) :=
  R × A
#align unitization Unitization
-/

namespace Unitization

section Basic

variable {R A : Type _}

#print Unitization.inl /-
/-- The canonical inclusion `R → unitization R A`. -/
def inl [Zero A] (r : R) : Unitization R A :=
  (r, 0)
#align unitization.inl Unitization.inl
-/

/-- The canonical inclusion `A → unitization R A`. -/
instance [Zero R] : CoeTC A (Unitization R A) where coe a := (0, a)

#print Unitization.fst /-
/-- The canonical projection `unitization R A → R`. -/
def fst (x : Unitization R A) : R :=
  x.1
#align unitization.fst Unitization.fst
-/

#print Unitization.snd /-
/-- The canonical projection `unitization R A → A`. -/
def snd (x : Unitization R A) : A :=
  x.2
#align unitization.snd Unitization.snd
-/

/- warning: unitization.ext -> Unitization.ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {x : Unitization.{u1, u2} R A} {y : Unitization.{u1, u2} R A}, (Eq.{succ u1} R (Unitization.fst.{u1, u2} R A x) (Unitization.fst.{u1, u2} R A y)) -> (Eq.{succ u2} A (Unitization.snd.{u1, u2} R A x) (Unitization.snd.{u1, u2} R A y)) -> (Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) x y)
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} {x : Unitization.{u2, u1} R A} {y : Unitization.{u2, u1} R A}, (Eq.{succ u2} R (Unitization.fst.{u2, u1} R A x) (Unitization.fst.{u2, u1} R A y)) -> (Eq.{succ u1} A (Unitization.snd.{u2, u1} R A x) (Unitization.snd.{u2, u1} R A y)) -> (Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) x y)
Case conversion may be inaccurate. Consider using '#align unitization.ext Unitization.extₓ'. -/
@[ext]
theorem ext {x y : Unitization R A} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2
#align unitization.ext Unitization.ext

section

variable (A)

#print Unitization.fst_inl /-
@[simp]
theorem fst_inl [Zero A] (r : R) : (inl r : Unitization R A).fst = r :=
  rfl
#align unitization.fst_inl Unitization.fst_inl
-/

#print Unitization.snd_inl /-
@[simp]
theorem snd_inl [Zero A] (r : R) : (inl r : Unitization R A).snd = 0 :=
  rfl
#align unitization.snd_inl Unitization.snd_inl
-/

end

section

variable (R)

/- warning: unitization.fst_coe -> Unitization.fst_inr is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : Zero.{u1} R] (a : A), Eq.{succ u1} R (Unitization.fst.{u1, u2} R A ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A _inst_1))) a)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R _inst_1)))
but is expected to have type
  forall (R : Type.{u2}) {A : Type.{u1}} [_inst_1 : Zero.{u2} R] (a : A), Eq.{succ u2} R (Unitization.fst.{u2, u1} R A (Unitization.inr.{u2, u1} R A _inst_1 a)) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R _inst_1))
Case conversion may be inaccurate. Consider using '#align unitization.fst_coe Unitization.fst_inrₓ'. -/
@[simp]
theorem fst_inr [Zero R] (a : A) : (a : Unitization R A).fst = 0 :=
  rfl
#align unitization.fst_coe Unitization.fst_inr

/- warning: unitization.snd_coe -> Unitization.snd_inr is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : Zero.{u1} R] (a : A), Eq.{succ u2} A (Unitization.snd.{u1, u2} R A ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A _inst_1))) a)) a
but is expected to have type
  forall (R : Type.{u2}) {A : Type.{u1}} [_inst_1 : Zero.{u2} R] (a : A), Eq.{succ u1} A (Unitization.snd.{u2, u1} R A (Unitization.inr.{u2, u1} R A _inst_1 a)) a
Case conversion may be inaccurate. Consider using '#align unitization.snd_coe Unitization.snd_inrₓ'. -/
@[simp]
theorem snd_inr [Zero R] (a : A) : (a : Unitization R A).snd = a :=
  rfl
#align unitization.snd_coe Unitization.snd_inr

end

#print Unitization.inl_injective /-
theorem inl_injective [Zero A] : Function.Injective (inl : R → Unitization R A) :=
  Function.LeftInverse.injective <| fst_inl _
#align unitization.inl_injective Unitization.inl_injective
-/

/- warning: unitization.coe_injective -> Unitization.inr_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Zero.{u1} R], Function.Injective.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A _inst_1))))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Zero.{u2} R], Function.Injective.{succ u1, max (succ u2) (succ u1)} A (Unitization.{u2, u1} R A) (Unitization.inr.{u2, u1} R A _inst_1)
Case conversion may be inaccurate. Consider using '#align unitization.coe_injective Unitization.inr_injectiveₓ'. -/
theorem inr_injective [Zero R] : Function.Injective (coe : A → Unitization R A) :=
  Function.LeftInverse.injective <| snd_inr _
#align unitization.coe_injective Unitization.inr_injective

end Basic

/-! ### Structures inherited from `prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type _} {S : Type _} {R : Type _} {A : Type _}

instance [Inhabited R] [Inhabited A] : Inhabited (Unitization R A) :=
  Prod.inhabited

instance [Zero R] [Zero A] : Zero (Unitization R A) :=
  Prod.hasZero

instance [Add R] [Add A] : Add (Unitization R A) :=
  Prod.hasAdd

instance [Neg R] [Neg A] : Neg (Unitization R A) :=
  Prod.hasNeg

instance [AddSemigroup R] [AddSemigroup A] : AddSemigroup (Unitization R A) :=
  Prod.addSemigroup

instance [AddZeroClass R] [AddZeroClass A] : AddZeroClass (Unitization R A) :=
  Prod.addZeroClass

instance [AddMonoid R] [AddMonoid A] : AddMonoid (Unitization R A) :=
  Prod.addMonoid

instance [AddGroup R] [AddGroup A] : AddGroup (Unitization R A) :=
  Prod.addGroup

instance [AddCommSemigroup R] [AddCommSemigroup A] : AddCommSemigroup (Unitization R A) :=
  Prod.addCommSemigroup

instance [AddCommMonoid R] [AddCommMonoid A] : AddCommMonoid (Unitization R A) :=
  Prod.addCommMonoid

instance [AddCommGroup R] [AddCommGroup A] : AddCommGroup (Unitization R A) :=
  Prod.addCommGroup

instance [SMul S R] [SMul S A] : SMul S (Unitization R A) :=
  Prod.smul

instance [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMul T S] [IsScalarTower T S R]
    [IsScalarTower T S A] : IsScalarTower T S (Unitization R A) :=
  Prod.isScalarTower

instance [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMulCommClass T S R] [SMulCommClass T S A] :
    SMulCommClass T S (Unitization R A) :=
  Prod.sMulCommClass

instance [SMul S R] [SMul S A] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ A] [IsCentralScalar S R]
    [IsCentralScalar S A] : IsCentralScalar S (Unitization R A) :=
  Prod.isCentralScalar

instance [Monoid S] [MulAction S R] [MulAction S A] : MulAction S (Unitization R A) :=
  Prod.mulAction

instance [Monoid S] [AddMonoid R] [AddMonoid A] [DistribMulAction S R] [DistribMulAction S A] :
    DistribMulAction S (Unitization R A) :=
  Prod.distribMulAction

instance [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A] :
    Module S (Unitization R A) :=
  Prod.module

/- warning: unitization.fst_zero -> Unitization.fst_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} A], Eq.{succ u1} R (Unitization.fst.{u1, u2} R A (OfNat.ofNat.{max u1 u2} (Unitization.{u1, u2} R A) 0 (OfNat.mk.{max u1 u2} (Unitization.{u1, u2} R A) 0 (Zero.zero.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasZero.{u1, u2} R A _inst_1 _inst_2))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Zero.{u2} R] [_inst_2 : Zero.{u1} A], Eq.{succ u2} R (Unitization.fst.{u2, u1} R A (OfNat.ofNat.{max u2 u1} (Unitization.{u2, u1} R A) 0 (Zero.toOfNat0.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.zero.{u2, u1} R A _inst_1 _inst_2)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R _inst_1))
Case conversion may be inaccurate. Consider using '#align unitization.fst_zero Unitization.fst_zeroₓ'. -/
@[simp]
theorem fst_zero [Zero R] [Zero A] : (0 : Unitization R A).fst = 0 :=
  rfl
#align unitization.fst_zero Unitization.fst_zero

/- warning: unitization.snd_zero -> Unitization.snd_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} A], Eq.{succ u2} A (Unitization.snd.{u1, u2} R A (OfNat.ofNat.{max u1 u2} (Unitization.{u1, u2} R A) 0 (OfNat.mk.{max u1 u2} (Unitization.{u1, u2} R A) 0 (Zero.zero.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasZero.{u1, u2} R A _inst_1 _inst_2))))) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A _inst_2)))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Zero.{u2} R] [_inst_2 : Zero.{u1} A], Eq.{succ u1} A (Unitization.snd.{u2, u1} R A (OfNat.ofNat.{max u2 u1} (Unitization.{u2, u1} R A) 0 (Zero.toOfNat0.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.zero.{u2, u1} R A _inst_1 _inst_2)))) (OfNat.ofNat.{u1} A 0 (Zero.toOfNat0.{u1} A _inst_2))
Case conversion may be inaccurate. Consider using '#align unitization.snd_zero Unitization.snd_zeroₓ'. -/
@[simp]
theorem snd_zero [Zero R] [Zero A] : (0 : Unitization R A).snd = 0 :=
  rfl
#align unitization.snd_zero Unitization.snd_zero

/- warning: unitization.fst_add -> Unitization.fst_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Add.{u1} R] [_inst_2 : Add.{u2} A] (x₁ : Unitization.{u1, u2} R A) (x₂ : Unitization.{u1, u2} R A), Eq.{succ u1} R (Unitization.fst.{u1, u2} R A (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHAdd.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasAdd.{u1, u2} R A _inst_1 _inst_2)) x₁ x₂)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R _inst_1) (Unitization.fst.{u1, u2} R A x₁) (Unitization.fst.{u1, u2} R A x₂))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Add.{u2} R] [_inst_2 : Add.{u1} A] (x₁ : Unitization.{u2, u1} R A) (x₂ : Unitization.{u2, u1} R A), Eq.{succ u2} R (Unitization.fst.{u2, u1} R A (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHAdd.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.add.{u2, u1} R A _inst_1 _inst_2)) x₁ x₂)) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R _inst_1) (Unitization.fst.{u2, u1} R A x₁) (Unitization.fst.{u2, u1} R A x₂))
Case conversion may be inaccurate. Consider using '#align unitization.fst_add Unitization.fst_addₓ'. -/
@[simp]
theorem fst_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl
#align unitization.fst_add Unitization.fst_add

/- warning: unitization.snd_add -> Unitization.snd_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Add.{u1} R] [_inst_2 : Add.{u2} A] (x₁ : Unitization.{u1, u2} R A) (x₂ : Unitization.{u1, u2} R A), Eq.{succ u2} A (Unitization.snd.{u1, u2} R A (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHAdd.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasAdd.{u1, u2} R A _inst_1 _inst_2)) x₁ x₂)) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) (Unitization.snd.{u1, u2} R A x₁) (Unitization.snd.{u1, u2} R A x₂))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Add.{u2} R] [_inst_2 : Add.{u1} A] (x₁ : Unitization.{u2, u1} R A) (x₂ : Unitization.{u2, u1} R A), Eq.{succ u1} A (Unitization.snd.{u2, u1} R A (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHAdd.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.add.{u2, u1} R A _inst_1 _inst_2)) x₁ x₂)) (HAdd.hAdd.{u1, u1, u1} A A A (instHAdd.{u1} A _inst_2) (Unitization.snd.{u2, u1} R A x₁) (Unitization.snd.{u2, u1} R A x₂))
Case conversion may be inaccurate. Consider using '#align unitization.snd_add Unitization.snd_addₓ'. -/
@[simp]
theorem snd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl
#align unitization.snd_add Unitization.snd_add

/- warning: unitization.fst_neg -> Unitization.fst_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Neg.{u1} R] [_inst_2 : Neg.{u2} A] (x : Unitization.{u1, u2} R A), Eq.{succ u1} R (Unitization.fst.{u1, u2} R A (Neg.neg.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasNeg.{u1, u2} R A _inst_1 _inst_2) x)) (Neg.neg.{u1} R _inst_1 (Unitization.fst.{u1, u2} R A x))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Neg.{u2} R] [_inst_2 : Neg.{u1} A] (x : Unitization.{u2, u1} R A), Eq.{succ u2} R (Unitization.fst.{u2, u1} R A (Neg.neg.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.neg.{u2, u1} R A _inst_1 _inst_2) x)) (Neg.neg.{u2} R _inst_1 (Unitization.fst.{u2, u1} R A x))
Case conversion may be inaccurate. Consider using '#align unitization.fst_neg Unitization.fst_negₓ'. -/
@[simp]
theorem fst_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).fst = -x.fst :=
  rfl
#align unitization.fst_neg Unitization.fst_neg

/- warning: unitization.snd_neg -> Unitization.snd_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Neg.{u1} R] [_inst_2 : Neg.{u2} A] (x : Unitization.{u1, u2} R A), Eq.{succ u2} A (Unitization.snd.{u1, u2} R A (Neg.neg.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasNeg.{u1, u2} R A _inst_1 _inst_2) x)) (Neg.neg.{u2} A _inst_2 (Unitization.snd.{u1, u2} R A x))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Neg.{u2} R] [_inst_2 : Neg.{u1} A] (x : Unitization.{u2, u1} R A), Eq.{succ u1} A (Unitization.snd.{u2, u1} R A (Neg.neg.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.neg.{u2, u1} R A _inst_1 _inst_2) x)) (Neg.neg.{u1} A _inst_2 (Unitization.snd.{u2, u1} R A x))
Case conversion may be inaccurate. Consider using '#align unitization.snd_neg Unitization.snd_negₓ'. -/
@[simp]
theorem snd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).snd = -x.snd :=
  rfl
#align unitization.snd_neg Unitization.snd_neg

/- warning: unitization.fst_smul -> Unitization.fst_smul is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : SMul.{u1, u2} S R] [_inst_2 : SMul.{u1, u3} S A] (s : S) (x : Unitization.{u2, u3} R A), Eq.{succ u2} R (Unitization.fst.{u2, u3} R A (SMul.smul.{u1, max u2 u3} S (Unitization.{u2, u3} R A) (Unitization.hasSmul.{u1, u2, u3} S R A _inst_1 _inst_2) s x)) (SMul.smul.{u1, u2} S R _inst_1 s (Unitization.fst.{u2, u3} R A x))
but is expected to have type
  forall {S : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : SMul.{u3, u2} S R] [_inst_2 : SMul.{u3, u1} S A] (s : S) (x : Unitization.{u2, u1} R A), Eq.{succ u2} R (Unitization.fst.{u2, u1} R A (HSMul.hSMul.{u3, max u2 u1, max u2 u1} S (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHSMul.{u3, max u2 u1} S (Unitization.{u2, u1} R A) (Unitization.smul.{u3, u2, u1} S R A _inst_1 _inst_2)) s x)) (HSMul.hSMul.{u3, u2, u2} S R R (instHSMul.{u3, u2} S R _inst_1) s (Unitization.fst.{u2, u1} R A x))
Case conversion may be inaccurate. Consider using '#align unitization.fst_smul Unitization.fst_smulₓ'. -/
@[simp]
theorem fst_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).fst = s • x.fst :=
  rfl
#align unitization.fst_smul Unitization.fst_smul

/- warning: unitization.snd_smul -> Unitization.snd_smul is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : SMul.{u1, u2} S R] [_inst_2 : SMul.{u1, u3} S A] (s : S) (x : Unitization.{u2, u3} R A), Eq.{succ u3} A (Unitization.snd.{u2, u3} R A (SMul.smul.{u1, max u2 u3} S (Unitization.{u2, u3} R A) (Unitization.hasSmul.{u1, u2, u3} S R A _inst_1 _inst_2) s x)) (SMul.smul.{u1, u3} S A _inst_2 s (Unitization.snd.{u2, u3} R A x))
but is expected to have type
  forall {S : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : SMul.{u3, u2} S R] [_inst_2 : SMul.{u3, u1} S A] (s : S) (x : Unitization.{u2, u1} R A), Eq.{succ u1} A (Unitization.snd.{u2, u1} R A (HSMul.hSMul.{u3, max u2 u1, max u2 u1} S (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHSMul.{u3, max u2 u1} S (Unitization.{u2, u1} R A) (Unitization.smul.{u3, u2, u1} S R A _inst_1 _inst_2)) s x)) (HSMul.hSMul.{u3, u1, u1} S A A (instHSMul.{u3, u1} S A _inst_2) s (Unitization.snd.{u2, u1} R A x))
Case conversion may be inaccurate. Consider using '#align unitization.snd_smul Unitization.snd_smulₓ'. -/
@[simp]
theorem snd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).snd = s • x.snd :=
  rfl
#align unitization.snd_smul Unitization.snd_smul

section

variable (A)

/- warning: unitization.inl_zero -> Unitization.inl_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (A : Type.{u2}) [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} A], Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (Unitization.inl.{u1, u2} R A _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R _inst_1)))) (OfNat.ofNat.{max u1 u2} (Unitization.{u1, u2} R A) 0 (OfNat.mk.{max u1 u2} (Unitization.{u1, u2} R A) 0 (Zero.zero.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasZero.{u1, u2} R A _inst_1 _inst_2))))
but is expected to have type
  forall {R : Type.{u2}} (A : Type.{u1}) [_inst_1 : Zero.{u2} R] [_inst_2 : Zero.{u1} A], Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inl.{u2, u1} R A _inst_2 (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R _inst_1))) (OfNat.ofNat.{max u2 u1} (Unitization.{u2, u1} R A) 0 (Zero.toOfNat0.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.zero.{u2, u1} R A _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align unitization.inl_zero Unitization.inl_zeroₓ'. -/
@[simp]
theorem inl_zero [Zero R] [Zero A] : (inl 0 : Unitization R A) = 0 :=
  rfl
#align unitization.inl_zero Unitization.inl_zero

/- warning: unitization.inl_add -> Unitization.inl_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (A : Type.{u2}) [_inst_1 : Add.{u1} R] [_inst_2 : AddZeroClass.{u2} A] (r₁ : R) (r₂ : R), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (Unitization.inl.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A _inst_2) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R _inst_1) r₁ r₂)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHAdd.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasAdd.{u1, u2} R A _inst_1 (AddZeroClass.toHasAdd.{u2} A _inst_2))) (Unitization.inl.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A _inst_2) r₁) (Unitization.inl.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A _inst_2) r₂))
but is expected to have type
  forall {R : Type.{u2}} (A : Type.{u1}) [_inst_1 : Add.{u2} R] [_inst_2 : AddZeroClass.{u1} A] (r₁ : R) (r₂ : R), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inl.{u2, u1} R A (AddZeroClass.toZero.{u1} A _inst_2) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R _inst_1) r₁ r₂)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHAdd.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.add.{u2, u1} R A _inst_1 (AddZeroClass.toAdd.{u1} A _inst_2))) (Unitization.inl.{u2, u1} R A (AddZeroClass.toZero.{u1} A _inst_2) r₁) (Unitization.inl.{u2, u1} R A (AddZeroClass.toZero.{u1} A _inst_2) r₂))
Case conversion may be inaccurate. Consider using '#align unitization.inl_add Unitization.inl_addₓ'. -/
@[simp]
theorem inl_add [Add R] [AddZeroClass A] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : Unitization R A) = inl r₁ + inl r₂ :=
  ext rfl (add_zero 0).symm
#align unitization.inl_add Unitization.inl_add

/- warning: unitization.inl_neg -> Unitization.inl_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (A : Type.{u2}) [_inst_1 : Neg.{u1} R] [_inst_2 : AddGroup.{u2} A] (r : R), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (Unitization.inl.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)))) (Neg.neg.{u1} R _inst_1 r)) (Neg.neg.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasNeg.{u1, u2} R A _inst_1 (SubNegMonoid.toHasNeg.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2))) (Unitization.inl.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_2)))) r))
but is expected to have type
  forall {R : Type.{u2}} (A : Type.{u1}) [_inst_1 : Neg.{u2} R] [_inst_2 : AddGroup.{u1} A] (r : R), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inl.{u2, u1} R A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (AddGroup.toSubtractionMonoid.{u1} A _inst_2)))) (Neg.neg.{u2} R _inst_1 r)) (Neg.neg.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.neg.{u2, u1} R A _inst_1 (NegZeroClass.toNeg.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (AddGroup.toSubtractionMonoid.{u1} A _inst_2))))) (Unitization.inl.{u2, u1} R A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (AddGroup.toSubtractionMonoid.{u1} A _inst_2)))) r))
Case conversion may be inaccurate. Consider using '#align unitization.inl_neg Unitization.inl_negₓ'. -/
@[simp]
theorem inl_neg [Neg R] [AddGroup A] (r : R) : (inl (-r) : Unitization R A) = -inl r :=
  ext rfl neg_zero.symm
#align unitization.inl_neg Unitization.inl_neg

/- warning: unitization.inl_smul -> Unitization.inl_smul is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} {R : Type.{u2}} (A : Type.{u3}) [_inst_1 : Monoid.{u1} S] [_inst_2 : AddMonoid.{u3} A] [_inst_3 : SMul.{u1, u2} S R] [_inst_4 : DistribMulAction.{u1, u3} S A _inst_1 _inst_2] (s : S) (r : R), Eq.{max (succ u2) (succ u3)} (Unitization.{u2, u3} R A) (Unitization.inl.{u2, u3} R A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_2)) (SMul.smul.{u1, u2} S R _inst_3 s r)) (SMul.smul.{u1, max u2 u3} S (Unitization.{u2, u3} R A) (Unitization.hasSmul.{u1, u2, u3} S R A _inst_3 (SMulZeroClass.toHasSmul.{u1, u3} S A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u3} S A (AddMonoid.toAddZeroClass.{u3} A _inst_2) (DistribMulAction.toDistribSMul.{u1, u3} S A _inst_1 _inst_2 _inst_4)))) s (Unitization.inl.{u2, u3} R A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_2)) r))
but is expected to have type
  forall {S : Type.{u3}} {R : Type.{u1}} (A : Type.{u2}) [_inst_1 : Monoid.{u3} S] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : SMul.{u3, u1} S R] [_inst_4 : DistribMulAction.{u3, u2} S A _inst_1 _inst_2] (s : S) (r : R), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (Unitization.inl.{u1, u2} R A (AddMonoid.toZero.{u2} A _inst_2) (HSMul.hSMul.{u3, u1, u1} S R R (instHSMul.{u3, u1} S R _inst_3) s r)) (HSMul.hSMul.{u3, max u2 u1, max u1 u2} S (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHSMul.{u3, max u1 u2} S (Unitization.{u1, u2} R A) (Unitization.smul.{u3, u1, u2} S R A _inst_3 (SMulZeroClass.toSMul.{u3, u2} S A (AddMonoid.toZero.{u2} A _inst_2) (DistribSMul.toSMulZeroClass.{u3, u2} S A (AddMonoid.toAddZeroClass.{u2} A _inst_2) (DistribMulAction.toDistribSMul.{u3, u2} S A _inst_1 _inst_2 _inst_4))))) s (Unitization.inl.{u1, u2} R A (AddMonoid.toZero.{u2} A _inst_2) r))
Case conversion may be inaccurate. Consider using '#align unitization.inl_smul Unitization.inl_smulₓ'. -/
@[simp]
theorem inl_smul [Monoid S] [AddMonoid A] [SMul S R] [DistribMulAction S A] (s : S) (r : R) :
    (inl (s • r) : Unitization R A) = s • inl r :=
  ext rfl (smul_zero s).symm
#align unitization.inl_smul Unitization.inl_smul

end

section

variable (R)

/- warning: unitization.coe_zero -> Unitization.inr_zero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} A], Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A _inst_1))) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A _inst_2)))) (OfNat.ofNat.{max u1 u2} (Unitization.{u1, u2} R A) 0 (OfNat.mk.{max u1 u2} (Unitization.{u1, u2} R A) 0 (Zero.zero.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasZero.{u1, u2} R A _inst_1 _inst_2))))
but is expected to have type
  forall (R : Type.{u2}) {A : Type.{u1}} [_inst_1 : Zero.{u2} R] [_inst_2 : Zero.{u1} A], Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inr.{u2, u1} R A _inst_1 (OfNat.ofNat.{u1} A 0 (Zero.toOfNat0.{u1} A _inst_2))) (OfNat.ofNat.{max u2 u1} (Unitization.{u2, u1} R A) 0 (Zero.toOfNat0.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.zero.{u2, u1} R A _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align unitization.coe_zero Unitization.inr_zeroₓ'. -/
@[simp]
theorem inr_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Unitization R A) :=
  rfl
#align unitization.coe_zero Unitization.inr_zero

/- warning: unitization.coe_add -> Unitization.inr_add is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : AddZeroClass.{u1} R] [_inst_2 : Add.{u2} A] (m₁ : A) (m₂ : A), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (AddZeroClass.toHasZero.{u1} R _inst_1)))) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) m₁ m₂)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHAdd.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasAdd.{u1, u2} R A (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2)) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (AddZeroClass.toHasZero.{u1} R _inst_1)))) m₁) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (AddZeroClass.toHasZero.{u1} R _inst_1)))) m₂))
but is expected to have type
  forall (R : Type.{u2}) {A : Type.{u1}} [_inst_1 : AddZeroClass.{u2} R] [_inst_2 : Add.{u1} A] (m₁ : A) (m₂ : A), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inr.{u2, u1} R A (AddZeroClass.toZero.{u2} R _inst_1) (HAdd.hAdd.{u1, u1, u1} A A A (instHAdd.{u1} A _inst_2) m₁ m₂)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHAdd.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.add.{u2, u1} R A (AddZeroClass.toAdd.{u2} R _inst_1) _inst_2)) (Unitization.inr.{u2, u1} R A (AddZeroClass.toZero.{u2} R _inst_1) m₁) (Unitization.inr.{u2, u1} R A (AddZeroClass.toZero.{u2} R _inst_1) m₂))
Case conversion may be inaccurate. Consider using '#align unitization.coe_add Unitization.inr_addₓ'. -/
@[simp]
theorem inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂ :=
  ext (add_zero 0).symm rfl
#align unitization.coe_add Unitization.inr_add

/- warning: unitization.coe_neg -> Unitization.inr_neg is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : Neg.{u2} A] (m : A), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))))))) (Neg.neg.{u2} A _inst_2 m)) (Neg.neg.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasNeg.{u1, u2} R A (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))))))) m))
but is expected to have type
  forall (R : Type.{u2}) {A : Type.{u1}} [_inst_1 : AddGroup.{u2} R] [_inst_2 : Neg.{u1} A] (m : A), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inr.{u2, u1} R A (NegZeroClass.toZero.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (AddGroup.toSubtractionMonoid.{u2} R _inst_1)))) (Neg.neg.{u1} A _inst_2 m)) (Neg.neg.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.neg.{u2, u1} R A (NegZeroClass.toNeg.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (AddGroup.toSubtractionMonoid.{u2} R _inst_1)))) _inst_2) (Unitization.inr.{u2, u1} R A (NegZeroClass.toZero.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (AddGroup.toSubtractionMonoid.{u2} R _inst_1)))) m))
Case conversion may be inaccurate. Consider using '#align unitization.coe_neg Unitization.inr_negₓ'. -/
@[simp]
theorem inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Unitization R A) = -m :=
  ext neg_zero.symm rfl
#align unitization.coe_neg Unitization.inr_neg

/- warning: unitization.coe_smul -> Unitization.inr_smul is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} (R : Type.{u2}) {A : Type.{u3}} [_inst_1 : Zero.{u2} R] [_inst_2 : Zero.{u1} S] [_inst_3 : SMulWithZero.{u1, u2} S R _inst_2 _inst_1] [_inst_4 : SMul.{u1, u3} S A] (r : S) (m : A), Eq.{max (succ u2) (succ u3)} (Unitization.{u2, u3} R A) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u3)} a b] => self.0) A (Unitization.{u2, u3} R A) (HasLiftT.mk.{succ u3, max (succ u2) (succ u3)} A (Unitization.{u2, u3} R A) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u3)} A (Unitization.{u2, u3} R A) (Unitization.hasCoeT.{u2, u3} R A _inst_1))) (SMul.smul.{u1, u3} S A _inst_4 r m)) (SMul.smul.{u1, max u2 u3} S (Unitization.{u2, u3} R A) (Unitization.hasSmul.{u1, u2, u3} S R A (SMulZeroClass.toHasSmul.{u1, u2} S R _inst_1 (SMulWithZero.toSmulZeroClass.{u1, u2} S R _inst_2 _inst_1 _inst_3)) _inst_4) r ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u3)} a b] => self.0) A (Unitization.{u2, u3} R A) (HasLiftT.mk.{succ u3, max (succ u2) (succ u3)} A (Unitization.{u2, u3} R A) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u3)} A (Unitization.{u2, u3} R A) (Unitization.hasCoeT.{u2, u3} R A _inst_1))) m))
but is expected to have type
  forall {S : Type.{u2}} (R : Type.{u3}) {A : Type.{u1}} [_inst_1 : Zero.{u3} R] [_inst_2 : Zero.{u2} S] [_inst_3 : SMulWithZero.{u2, u3} S R _inst_2 _inst_1] [_inst_4 : SMul.{u2, u1} S A] (r : S) (m : A), Eq.{max (succ u3) (succ u1)} (Unitization.{u3, u1} R A) (Unitization.inr.{u3, u1} R A _inst_1 (HSMul.hSMul.{u2, u1, u1} S A A (instHSMul.{u2, u1} S A _inst_4) r m)) (HSMul.hSMul.{u2, max u3 u1, max u3 u1} S (Unitization.{u3, u1} R A) (Unitization.{u3, u1} R A) (instHSMul.{u2, max u3 u1} S (Unitization.{u3, u1} R A) (Unitization.smul.{u2, u3, u1} S R A (SMulZeroClass.toSMul.{u2, u3} S R _inst_1 (SMulWithZero.toSMulZeroClass.{u2, u3} S R _inst_2 _inst_1 _inst_3)) _inst_4)) r (Unitization.inr.{u3, u1} R A _inst_1 m))
Case conversion may be inaccurate. Consider using '#align unitization.coe_smul Unitization.inr_smulₓ'. -/
@[simp]
theorem inr_smul [Zero R] [Zero S] [SMulWithZero S R] [SMul S A] (r : S) (m : A) :
    (↑(r • m) : Unitization R A) = r • m :=
  ext (smul_zero _).symm rfl
#align unitization.coe_smul Unitization.inr_smul

end

/- warning: unitization.inl_fst_add_coe_snd_eq -> Unitization.inl_fst_add_inr_snd_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddZeroClass.{u1} R] [_inst_2 : AddZeroClass.{u2} A] (x : Unitization.{u1, u2} R A), Eq.{succ (max u1 u2)} (Unitization.{u1, u2} R A) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHAdd.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasAdd.{u1, u2} R A (AddZeroClass.toHasAdd.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u2} A _inst_2))) (Unitization.inl.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A _inst_2) (Unitization.fst.{u1, u2} R A x)) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (AddZeroClass.toHasZero.{u1} R _inst_1)))) (Unitization.snd.{u1, u2} R A x))) x
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : AddZeroClass.{u2} R] [_inst_2 : AddZeroClass.{u1} A] (x : Unitization.{u2, u1} R A), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHAdd.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.add.{u2, u1} R A (AddZeroClass.toAdd.{u2} R _inst_1) (AddZeroClass.toAdd.{u1} A _inst_2))) (Unitization.inl.{u2, u1} R A (AddZeroClass.toZero.{u1} A _inst_2) (Unitization.fst.{u2, u1} R A x)) (Unitization.inr.{u2, u1} R A (AddZeroClass.toZero.{u2} R _inst_1) (Unitization.snd.{u2, u1} R A x))) x
Case conversion may be inaccurate. Consider using '#align unitization.inl_fst_add_coe_snd_eq Unitization.inl_fst_add_inr_snd_eqₓ'. -/
theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass A] (x : Unitization R A) :
    inl x.fst + ↑x.snd = x :=
  ext (add_zero x.1) (zero_add x.2)
#align unitization.inl_fst_add_coe_snd_eq Unitization.inl_fst_add_inr_snd_eq

/- warning: unitization.ind -> Unitization.ind is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddZeroClass.{u1} R] [_inst_2 : AddZeroClass.{u2} A] {P : (Unitization.{u1, u2} R A) -> Prop}, (forall (r : R) (a : A), P (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHAdd.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasAdd.{u1, u2} R A (AddZeroClass.toHasAdd.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u2} A _inst_2))) (Unitization.inl.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A _inst_2) r) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (AddZeroClass.toHasZero.{u1} R _inst_1)))) a))) -> (forall (x : Unitization.{u1, u2} R A), P x)
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : AddZeroClass.{u2} R] [_inst_2 : AddZeroClass.{u1} A] {P : (Unitization.{u2, u1} R A) -> Prop}, (forall (r : R) (a : A), P (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHAdd.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.add.{u2, u1} R A (AddZeroClass.toAdd.{u2} R _inst_1) (AddZeroClass.toAdd.{u1} A _inst_2))) (Unitization.inl.{u2, u1} R A (AddZeroClass.toZero.{u1} A _inst_2) r) (Unitization.inr.{u2, u1} R A (AddZeroClass.toZero.{u2} R _inst_1) a))) -> (forall (x : Unitization.{u2, u1} R A), P x)
Case conversion may be inaccurate. Consider using '#align unitization.ind Unitization.indₓ'. -/
/-- To show a property hold on all `unitization R A` it suffices to show it holds
on terms of the form `inl r + a`.

This can be used as `induction x using unitization.ind`. -/
theorem ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A → Prop}
    (h : ∀ (r : R) (a : A), P (inl r + a)) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ h x.1 x.2
#align unitization.ind Unitization.ind

/- warning: unitization.linear_map_ext -> Unitization.linearMap_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.linear_map_ext Unitization.linearMap_extₓ'. -/
/-- This cannot be marked `@[ext]` as it ends up being used instead of `linear_map.prod_ext` when
working with `R × A`. -/
theorem linearMap_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
    [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ a : A, f a = g a) : f = g :=
  LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)
#align unitization.linear_map_ext Unitization.linearMap_ext

variable (R A)

#print Unitization.inrHom /-
/-- The canonical `R`-linear inclusion `A → unitization R A`. -/
@[simps apply]
def inrHom [Semiring R] [AddCommMonoid A] [Module R A] : A →ₗ[R] Unitization R A :=
  { LinearMap.inr R R A with toFun := coe }
#align unitization.coe_hom Unitization.inrHom
-/

#print Unitization.sndHom /-
/-- The canonical `R`-linear projection `unitization R A → A`. -/
@[simps apply]
def sndHom [Semiring R] [AddCommMonoid A] [Module R A] : Unitization R A →ₗ[R] A :=
  { LinearMap.snd _ _ _ with toFun := snd }
#align unitization.snd_hom Unitization.sndHom
-/

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R A : Type _}

instance [One R] [Zero A] : One (Unitization R A) :=
  ⟨(1, 0)⟩

instance [Mul R] [Add A] [Mul A] [SMul R A] : Mul (Unitization R A) :=
  ⟨fun x y => (x.1 * y.1, x.1 • y.2 + y.1 • x.2 + x.2 * y.2)⟩

/- warning: unitization.fst_one -> Unitization.fst_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : One.{u1} R] [_inst_2 : Zero.{u2} A], Eq.{succ u1} R (Unitization.fst.{u1, u2} R A (OfNat.ofNat.{max u1 u2} (Unitization.{u1, u2} R A) 1 (OfNat.mk.{max u1 u2} (Unitization.{u1, u2} R A) 1 (One.one.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasOne.{u1, u2} R A _inst_1 _inst_2))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : One.{u2} R] [_inst_2 : Zero.{u1} A], Eq.{succ u2} R (Unitization.fst.{u2, u1} R A (OfNat.ofNat.{max u2 u1} (Unitization.{u2, u1} R A) 1 (One.toOfNat1.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.one.{u2, u1} R A _inst_1 _inst_2)))) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R _inst_1))
Case conversion may be inaccurate. Consider using '#align unitization.fst_one Unitization.fst_oneₓ'. -/
@[simp]
theorem fst_one [One R] [Zero A] : (1 : Unitization R A).fst = 1 :=
  rfl
#align unitization.fst_one Unitization.fst_one

/- warning: unitization.snd_one -> Unitization.snd_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : One.{u1} R] [_inst_2 : Zero.{u2} A], Eq.{succ u2} A (Unitization.snd.{u1, u2} R A (OfNat.ofNat.{max u1 u2} (Unitization.{u1, u2} R A) 1 (OfNat.mk.{max u1 u2} (Unitization.{u1, u2} R A) 1 (One.one.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasOne.{u1, u2} R A _inst_1 _inst_2))))) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A _inst_2)))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : One.{u2} R] [_inst_2 : Zero.{u1} A], Eq.{succ u1} A (Unitization.snd.{u2, u1} R A (OfNat.ofNat.{max u2 u1} (Unitization.{u2, u1} R A) 1 (One.toOfNat1.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.one.{u2, u1} R A _inst_1 _inst_2)))) (OfNat.ofNat.{u1} A 0 (Zero.toOfNat0.{u1} A _inst_2))
Case conversion may be inaccurate. Consider using '#align unitization.snd_one Unitization.snd_oneₓ'. -/
@[simp]
theorem snd_one [One R] [Zero A] : (1 : Unitization R A).snd = 0 :=
  rfl
#align unitization.snd_one Unitization.snd_one

/- warning: unitization.fst_mul -> Unitization.fst_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Mul.{u1} R] [_inst_2 : Add.{u2} A] [_inst_3 : Mul.{u2} A] [_inst_4 : SMul.{u1, u2} R A] (x₁ : Unitization.{u1, u2} R A) (x₂ : Unitization.{u1, u2} R A), Eq.{succ u1} R (Unitization.fst.{u1, u2} R A (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHMul.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasMul.{u1, u2} R A _inst_1 _inst_2 _inst_3 _inst_4)) x₁ x₂)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R _inst_1) (Unitization.fst.{u1, u2} R A x₁) (Unitization.fst.{u1, u2} R A x₂))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Mul.{u2} R] [_inst_2 : Add.{u1} A] [_inst_3 : Mul.{u1} A] [_inst_4 : SMul.{u2, u1} R A] (x₁ : Unitization.{u2, u1} R A) (x₂ : Unitization.{u2, u1} R A), Eq.{succ u2} R (Unitization.fst.{u2, u1} R A (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHMul.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.mul.{u2, u1} R A _inst_1 _inst_2 _inst_3 _inst_4)) x₁ x₂)) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R _inst_1) (Unitization.fst.{u2, u1} R A x₁) (Unitization.fst.{u2, u1} R A x₂))
Case conversion may be inaccurate. Consider using '#align unitization.fst_mul Unitization.fst_mulₓ'. -/
@[simp]
theorem fst_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl
#align unitization.fst_mul Unitization.fst_mul

/- warning: unitization.snd_mul -> Unitization.snd_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Mul.{u1} R] [_inst_2 : Add.{u2} A] [_inst_3 : Mul.{u2} A] [_inst_4 : SMul.{u1, u2} R A] (x₁ : Unitization.{u1, u2} R A) (x₂ : Unitization.{u1, u2} R A), Eq.{succ u2} A (Unitization.snd.{u1, u2} R A (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHMul.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasMul.{u1, u2} R A _inst_1 _inst_2 _inst_3 _inst_4)) x₁ x₂)) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) (SMul.smul.{u1, u2} R A _inst_4 (Unitization.fst.{u1, u2} R A x₁) (Unitization.snd.{u1, u2} R A x₂)) (SMul.smul.{u1, u2} R A _inst_4 (Unitization.fst.{u1, u2} R A x₂) (Unitization.snd.{u1, u2} R A x₁))) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A _inst_3) (Unitization.snd.{u1, u2} R A x₁) (Unitization.snd.{u1, u2} R A x₂)))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Mul.{u2} R] [_inst_2 : Add.{u1} A] [_inst_3 : Mul.{u1} A] [_inst_4 : SMul.{u2, u1} R A] (x₁ : Unitization.{u2, u1} R A) (x₂ : Unitization.{u2, u1} R A), Eq.{succ u1} A (Unitization.snd.{u2, u1} R A (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHMul.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.mul.{u2, u1} R A _inst_1 _inst_2 _inst_3 _inst_4)) x₁ x₂)) (HAdd.hAdd.{u1, u1, u1} A A A (instHAdd.{u1} A _inst_2) (HAdd.hAdd.{u1, u1, u1} A A A (instHAdd.{u1} A _inst_2) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A _inst_4) (Unitization.fst.{u2, u1} R A x₁) (Unitization.snd.{u2, u1} R A x₂)) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A _inst_4) (Unitization.fst.{u2, u1} R A x₂) (Unitization.snd.{u2, u1} R A x₁))) (HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A _inst_3) (Unitization.snd.{u2, u1} R A x₁) (Unitization.snd.{u2, u1} R A x₂)))
Case conversion may be inaccurate. Consider using '#align unitization.snd_mul Unitization.snd_mulₓ'. -/
@[simp]
theorem snd_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd + x₁.snd * x₂.snd :=
  rfl
#align unitization.snd_mul Unitization.snd_mul

section

variable (A)

/- warning: unitization.inl_one -> Unitization.inl_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (A : Type.{u2}) [_inst_1 : One.{u1} R] [_inst_2 : Zero.{u2} A], Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (Unitization.inl.{u1, u2} R A _inst_2 (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R _inst_1)))) (OfNat.ofNat.{max u1 u2} (Unitization.{u1, u2} R A) 1 (OfNat.mk.{max u1 u2} (Unitization.{u1, u2} R A) 1 (One.one.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasOne.{u1, u2} R A _inst_1 _inst_2))))
but is expected to have type
  forall {R : Type.{u2}} (A : Type.{u1}) [_inst_1 : One.{u2} R] [_inst_2 : Zero.{u1} A], Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inl.{u2, u1} R A _inst_2 (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R _inst_1))) (OfNat.ofNat.{max u2 u1} (Unitization.{u2, u1} R A) 1 (One.toOfNat1.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.one.{u2, u1} R A _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align unitization.inl_one Unitization.inl_oneₓ'. -/
@[simp]
theorem inl_one [One R] [Zero A] : (inl 1 : Unitization R A) = 1 :=
  rfl
#align unitization.inl_one Unitization.inl_one

/- warning: unitization.inl_mul -> Unitization.inl_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (A : Type.{u2}) [_inst_1 : Monoid.{u1} R] [_inst_2 : NonUnitalNonAssocSemiring.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} R A _inst_1 (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))] (r₁ : R) (r₂ : R), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (Unitization.inl.{u1, u2} R A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1))) r₁ r₂)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHMul.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasMul.{u1, u2} R A (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Distrib.toHasAdd.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A _inst_2)) (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} R A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} R A _inst_1 (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)) _inst_3))))) (Unitization.inl.{u1, u2} R A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A _inst_2)) r₁) (Unitization.inl.{u1, u2} R A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A _inst_2)) r₂))
but is expected to have type
  forall {R : Type.{u2}} (A : Type.{u1}) [_inst_1 : Monoid.{u2} R] [_inst_2 : NonUnitalNonAssocSemiring.{u1} A] [_inst_3 : DistribMulAction.{u2, u1} R A _inst_1 (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))] (r₁ : R) (r₂ : R), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inl.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulOneClass.toMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_1))) r₁ r₂)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHMul.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.mul.{u2, u1} R A (MulOneClass.toMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_1)) (Distrib.toAdd.{u1} A (NonUnitalNonAssocSemiring.toDistrib.{u1} A _inst_2)) (NonUnitalNonAssocSemiring.toMul.{u1} A _inst_2) (SMulZeroClass.toSMul.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u1} R A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))) (DistribMulAction.toDistribSMul.{u2, u1} R A _inst_1 (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2)) _inst_3))))) (Unitization.inl.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) r₁) (Unitization.inl.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) r₂))
Case conversion may be inaccurate. Consider using '#align unitization.inl_mul Unitization.inl_mulₓ'. -/
@[simp]
theorem inl_mul [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r₁ r₂ : R) :
    (inl (r₁ * r₂) : Unitization R A) = inl r₁ * inl r₂ :=
  ext rfl <|
    show (0 : A) = r₁ • (0 : A) + r₂ • 0 + 0 * 0 by
      simp only [smul_zero, add_zero, MulZeroClass.mul_zero]
#align unitization.inl_mul Unitization.inl_mul

/- warning: unitization.inl_mul_inl -> Unitization.inl_mul_inl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (A : Type.{u2}) [_inst_1 : Monoid.{u1} R] [_inst_2 : NonUnitalNonAssocSemiring.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} R A _inst_1 (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))] (r₁ : R) (r₂ : R), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHMul.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasMul.{u1, u2} R A (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Distrib.toHasAdd.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A _inst_2)) (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} R A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} R A _inst_1 (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)) _inst_3))))) (Unitization.inl.{u1, u2} R A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A _inst_2)) r₁) (Unitization.inl.{u1, u2} R A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A _inst_2)) r₂)) (Unitization.inl.{u1, u2} R A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1))) r₁ r₂))
but is expected to have type
  forall {R : Type.{u2}} (A : Type.{u1}) [_inst_1 : Monoid.{u2} R] [_inst_2 : NonUnitalNonAssocSemiring.{u1} A] [_inst_3 : DistribMulAction.{u2, u1} R A _inst_1 (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))] (r₁ : R) (r₂ : R), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHMul.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.mul.{u2, u1} R A (MulOneClass.toMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_1)) (Distrib.toAdd.{u1} A (NonUnitalNonAssocSemiring.toDistrib.{u1} A _inst_2)) (NonUnitalNonAssocSemiring.toMul.{u1} A _inst_2) (SMulZeroClass.toSMul.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u1} R A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))) (DistribMulAction.toDistribSMul.{u2, u1} R A _inst_1 (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2)) _inst_3))))) (Unitization.inl.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) r₁) (Unitization.inl.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) r₂)) (Unitization.inl.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulOneClass.toMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_1))) r₁ r₂))
Case conversion may be inaccurate. Consider using '#align unitization.inl_mul_inl Unitization.inl_mul_inlₓ'. -/
theorem inl_mul_inl [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r₁ r₂ : R) :
    (inl r₁ * inl r₂ : Unitization R A) = inl (r₁ * r₂) :=
  (inl_mul A r₁ r₂).symm
#align unitization.inl_mul_inl Unitization.inl_mul_inl

end

section

variable (R)

/- warning: unitization.coe_mul -> Unitization.inr_mul is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} A] [_inst_3 : Mul.{u2} A] [_inst_4 : SMulWithZero.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A _inst_2)))] (a₁ : A) (a₂ : A), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A _inst_3) a₁ a₂)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHMul.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasMul.{u1, u2} R A (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (AddZeroClass.toHasAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A _inst_2))) _inst_3 (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A _inst_2))) _inst_4)))) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) a₁) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) a₂))
but is expected to have type
  forall (R : Type.{u2}) {A : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} A] [_inst_3 : Mul.{u1} A] [_inst_4 : SMulWithZero.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (AddMonoid.toZero.{u1} A (AddCommMonoid.toAddMonoid.{u1} A _inst_2))] (a₁ : A) (a₂ : A), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inr.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A _inst_3) a₁ a₂)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHMul.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.mul.{u2, u1} R A (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (AddZeroClass.toAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A _inst_2))) _inst_3 (SMulZeroClass.toSMul.{u2, u1} R A (AddMonoid.toZero.{u1} A (AddCommMonoid.toAddMonoid.{u1} A _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (AddMonoid.toZero.{u1} A (AddCommMonoid.toAddMonoid.{u1} A _inst_2)) _inst_4)))) (Unitization.inr.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) a₁) (Unitization.inr.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) a₂))
Case conversion may be inaccurate. Consider using '#align unitization.coe_mul Unitization.inr_mulₓ'. -/
@[simp]
theorem inr_mul [Semiring R] [AddCommMonoid A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ :=
  ext (MulZeroClass.mul_zero _).symm <|
    show a₁ * a₂ = (0 : R) • a₂ + (0 : R) • a₁ + a₁ * a₂ by simp only [zero_smul, zero_add]
#align unitization.coe_mul Unitization.inr_mul

end

/- warning: unitization.inl_mul_coe -> Unitization.inl_mul_inr is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : NonUnitalNonAssocSemiring.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} R A (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))] (r : R) (a : A), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHMul.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasMul.{u1, u2} R A (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Distrib.toHasAdd.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A _inst_2)) (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} R A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} R A (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)) _inst_3))))) (Unitization.inl.{u1, u2} R A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A _inst_2)) r) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) a)) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} R A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} R A (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)) _inst_3))) r a))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : NonUnitalNonAssocSemiring.{u1} A] [_inst_3 : DistribMulAction.{u2, u1} R A (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))] (r : R) (a : A), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHMul.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.mul.{u2, u1} R A (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Distrib.toAdd.{u1} A (NonUnitalNonAssocSemiring.toDistrib.{u1} A _inst_2)) (NonUnitalNonAssocSemiring.toMul.{u1} A _inst_2) (SMulZeroClass.toSMul.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u1} R A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))) (DistribMulAction.toDistribSMul.{u2, u1} R A (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2)) _inst_3))))) (Unitization.inl.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) r) (Unitization.inr.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) a)) (Unitization.inr.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A (SMulZeroClass.toSMul.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u1} R A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))) (DistribMulAction.toDistribSMul.{u2, u1} R A (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2)) _inst_3)))) r a))
Case conversion may be inaccurate. Consider using '#align unitization.inl_mul_coe Unitization.inl_mul_inrₓ'. -/
theorem inl_mul_inr [Semiring R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r : R)
    (a : A) : (inl r * a : Unitization R A) = ↑(r • a) :=
  ext (MulZeroClass.mul_zero r) <|
    show r • a + (0 : R) • 0 + 0 * a = r • a by
      rw [smul_zero, add_zero, MulZeroClass.zero_mul, add_zero]
#align unitization.inl_mul_coe Unitization.inl_mul_inr

/- warning: unitization.coe_mul_inl -> Unitization.inr_mul_inl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : NonUnitalNonAssocSemiring.{u2} A] [_inst_3 : DistribMulAction.{u1, u2} R A (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))] (r : R) (a : A), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (Unitization.{u1, u2} R A) (instHMul.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasMul.{u1, u2} R A (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Distrib.toHasAdd.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A _inst_2)) (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} R A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} R A (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)) _inst_3))))) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) a) (Unitization.inl.{u1, u2} R A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A _inst_2)) r)) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} R A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} R A (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A _inst_2)) _inst_3))) r a))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : NonUnitalNonAssocSemiring.{u1} A] [_inst_3 : DistribMulAction.{u2, u1} R A (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))] (r : R) (a : A), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (Unitization.{u2, u1} R A) (instHMul.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.mul.{u2, u1} R A (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Distrib.toAdd.{u1} A (NonUnitalNonAssocSemiring.toDistrib.{u1} A _inst_2)) (NonUnitalNonAssocSemiring.toMul.{u1} A _inst_2) (SMulZeroClass.toSMul.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u1} R A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))) (DistribMulAction.toDistribSMul.{u2, u1} R A (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2)) _inst_3))))) (Unitization.inr.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) a) (Unitization.inl.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) r)) (Unitization.inr.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A (SMulZeroClass.toSMul.{u2, u1} R A (MulZeroClass.toZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u1} R A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2))) (DistribMulAction.toDistribSMul.{u2, u1} R A (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (AddCommMonoid.toAddMonoid.{u1} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A _inst_2)) _inst_3)))) r a))
Case conversion may be inaccurate. Consider using '#align unitization.coe_mul_inl Unitization.inr_mul_inlₓ'. -/
theorem inr_mul_inl [Semiring R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r : R)
    (a : A) : (a * inl r : Unitization R A) = ↑(r • a) :=
  ext (MulZeroClass.zero_mul r) <|
    show (0 : R) • 0 + r • a + a * 0 = r • a by
      rw [smul_zero, zero_add, MulZeroClass.mul_zero, add_zero]
#align unitization.coe_mul_inl Unitization.inr_mul_inl

#print Unitization.mulOneClass /-
instance mulOneClass [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] :
    MulOneClass (Unitization R A) :=
  { Unitization.hasOne,
    Unitization.hasMul with
    one_mul := fun x =>
      ext (one_mul x.1) <|
        show (1 : R) • x.2 + x.1 • 0 + 0 * x.2 = x.2 by
          rw [one_smul, smul_zero, add_zero, MulZeroClass.zero_mul, add_zero]
    mul_one := fun x =>
      ext (mul_one x.1) <|
        show (x.1 • 0 : A) + (1 : R) • x.2 + x.2 * 0 = x.2 by
          rw [smul_zero, zero_add, one_smul, MulZeroClass.mul_zero, add_zero] }
#align unitization.mul_one_class Unitization.mulOneClass
-/

instance [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonAssocSemiring (Unitization R A) :=
  { Unitization.mulOneClass,
    Unitization.addCommMonoid with
    zero_mul := fun x =>
      ext (MulZeroClass.zero_mul x.1) <|
        show (0 : R) • x.2 + x.1 • 0 + 0 * x.2 = 0 by
          rw [zero_smul, zero_add, smul_zero, MulZeroClass.zero_mul, add_zero]
    mul_zero := fun x =>
      ext (MulZeroClass.mul_zero x.1) <|
        show (x.1 • 0 : A) + (0 : R) • x.2 + x.2 * 0 = 0 by
          rw [smul_zero, zero_add, zero_smul, MulZeroClass.mul_zero, add_zero]
    left_distrib := fun x₁ x₂ x₃ =>
      ext (mul_add x₁.1 x₂.1 x₃.1) <|
        show
          x₁.1 • (x₂.2 + x₃.2) + (x₂.1 + x₃.1) • x₁.2 + x₁.2 * (x₂.2 + x₃.2) =
            x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 + (x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2)
          by simp only [smul_add, add_smul, mul_add]; abel
    right_distrib := fun x₁ x₂ x₃ =>
      ext (add_mul x₁.1 x₂.1 x₃.1) <|
        show
          (x₁.1 + x₂.1) • x₃.2 + x₃.1 • (x₁.2 + x₂.2) + (x₁.2 + x₂.2) * x₃.2 =
            x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2 + (x₂.1 • x₃.2 + x₃.1 • x₂.2 + x₂.2 * x₃.2)
          by simp only [add_smul, smul_add, add_mul]; abel }

instance [CommMonoid R] [NonUnitalSemiring A] [DistribMulAction R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Monoid (Unitization R A) :=
  { Unitization.mulOneClass with
    mul_assoc := fun x y z =>
      ext (mul_assoc x.1 y.1 z.1) <|
        show
          (x.1 * y.1) • z.2 + z.1 • (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) +
              (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) * z.2 =
            x.1 • (y.1 • z.2 + z.1 • y.2 + y.2 * z.2) + (y.1 * z.1) • x.2 +
              x.2 * (y.1 • z.2 + z.1 • y.2 + y.2 * z.2)
          by
          simp only [smul_add, mul_add, add_mul, smul_smul, smul_mul_assoc, mul_smul_comm,
            mul_assoc]
          nth_rw 2 [mul_comm]
          nth_rw 3 [mul_comm]
          abel }

instance [CommMonoid R] [NonUnitalCommSemiring A] [DistribMulAction R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : CommMonoid (Unitization R A) :=
  { Unitization.monoid with
    mul_comm := fun x₁ x₂ =>
      ext (mul_comm x₁.1 x₂.1) <|
        show x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 = x₂.1 • x₁.2 + x₁.1 • x₂.2 + x₂.2 * x₁.2 by
          rw [add_comm (x₁.1 • x₂.2), mul_comm] }

instance [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Semiring (Unitization R A) :=
  { Unitization.monoid, Unitization.nonAssocSemiring with }

instance [CommSemiring R] [NonUnitalCommSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : CommSemiring (Unitization R A) :=
  { Unitization.commMonoid, Unitization.nonAssocSemiring with }

variable (R A)

#print Unitization.inlRingHom /-
/-- The canonical inclusion of rings `R →+* unitization R A`. -/
@[simps apply]
def inlRingHom [Semiring R] [NonUnitalSemiring A] [Module R A] : R →+* Unitization R A
    where
  toFun := inl
  map_one' := inl_one A
  map_mul' := inl_mul A
  map_zero' := inl_zero A
  map_add' := inl_add A
#align unitization.inl_ring_hom Unitization.inlRingHom
-/

end Mul

/-! ### Star structure -/


section Star

variable {R A : Type _}

instance [Star R] [Star A] : Star (Unitization R A) :=
  ⟨fun ra => (star ra.fst, star ra.snd)⟩

/- warning: unitization.fst_star -> Unitization.fst_star is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Star.{u1} R] [_inst_2 : Star.{u2} A] (x : Unitization.{u1, u2} R A), Eq.{succ u1} R (Unitization.fst.{u1, u2} R A (Star.star.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasStar.{u1, u2} R A _inst_1 _inst_2) x)) (Star.star.{u1} R _inst_1 (Unitization.fst.{u1, u2} R A x))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Star.{u2} R] [_inst_2 : Star.{u1} A] (x : Unitization.{u2, u1} R A), Eq.{succ u2} R (Unitization.fst.{u2, u1} R A (Star.star.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.toStar.{u2, u1} R A _inst_1 _inst_2) x)) (Star.star.{u2} R _inst_1 (Unitization.fst.{u2, u1} R A x))
Case conversion may be inaccurate. Consider using '#align unitization.fst_star Unitization.fst_starₓ'. -/
@[simp]
theorem fst_star [Star R] [Star A] (x : Unitization R A) : (star x).fst = star x.fst :=
  rfl
#align unitization.fst_star Unitization.fst_star

/- warning: unitization.snd_star -> Unitization.snd_star is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Star.{u1} R] [_inst_2 : Star.{u2} A] (x : Unitization.{u1, u2} R A), Eq.{succ u2} A (Unitization.snd.{u1, u2} R A (Star.star.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasStar.{u1, u2} R A _inst_1 _inst_2) x)) (Star.star.{u2} A _inst_2 (Unitization.snd.{u1, u2} R A x))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Star.{u2} R] [_inst_2 : Star.{u1} A] (x : Unitization.{u2, u1} R A), Eq.{succ u1} A (Unitization.snd.{u2, u1} R A (Star.star.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.toStar.{u2, u1} R A _inst_1 _inst_2) x)) (Star.star.{u1} A _inst_2 (Unitization.snd.{u2, u1} R A x))
Case conversion may be inaccurate. Consider using '#align unitization.snd_star Unitization.snd_starₓ'. -/
@[simp]
theorem snd_star [Star R] [Star A] (x : Unitization R A) : (star x).snd = star x.snd :=
  rfl
#align unitization.snd_star Unitization.snd_star

/- warning: unitization.inl_star -> Unitization.inl_star is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Star.{u1} R] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : StarAddMonoid.{u2} A _inst_2] (r : R), Eq.{max (succ u1) (succ u2)} (Unitization.{u1, u2} R A) (Unitization.inl.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (Star.star.{u1} R _inst_1 r)) (Star.star.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasStar.{u1, u2} R A _inst_1 (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A _inst_2 _inst_3))) (Unitization.inl.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) r))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Star.{u2} R] [_inst_2 : AddMonoid.{u1} A] [_inst_3 : StarAddMonoid.{u1} A _inst_2] (r : R), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inl.{u2, u1} R A (AddMonoid.toZero.{u1} A _inst_2) (Star.star.{u2} R _inst_1 r)) (Star.star.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.toStar.{u2, u1} R A _inst_1 (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A _inst_2 _inst_3))) (Unitization.inl.{u2, u1} R A (AddMonoid.toZero.{u1} A _inst_2) r))
Case conversion may be inaccurate. Consider using '#align unitization.inl_star Unitization.inl_starₓ'. -/
@[simp]
theorem inl_star [Star R] [AddMonoid A] [StarAddMonoid A] (r : R) :
    inl (star r) = star (inl r : Unitization R A) :=
  ext rfl (by simp only [snd_star, star_zero, snd_inl])
#align unitization.inl_star Unitization.inl_star

/- warning: unitization.coe_star -> Unitization.inr_star is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] [_inst_3 : Star.{u2} A] (a : A), Eq.{succ (max u1 u2)} (Unitization.{u1, u2} R A) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, succ (max u1 u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, succ (max u1 u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))))) (Star.star.{u2} A _inst_3 a)) (Star.star.{max u1 u2} (Unitization.{u1, u2} R A) (Unitization.hasStar.{u1, u2} R A (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) _inst_3) ((fun (a : Type.{u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u2, max (succ u1) (succ u2)} a b] => self.0) A (Unitization.{u1, u2} R A) (HasLiftT.mk.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (CoeTCₓ.coe.{succ u2, max (succ u1) (succ u2)} A (Unitization.{u1, u2} R A) (Unitization.hasCoeT.{u1, u2} R A (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))))) a))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : AddMonoid.{u2} R] [_inst_2 : StarAddMonoid.{u2} R _inst_1] [_inst_3 : Star.{u1} A] (a : A), Eq.{max (succ u2) (succ u1)} (Unitization.{u2, u1} R A) (Unitization.inr.{u2, u1} R A (AddMonoid.toZero.{u2} R _inst_1) (Star.star.{u1} A _inst_3 a)) (Star.star.{max u2 u1} (Unitization.{u2, u1} R A) (Unitization.toStar.{u2, u1} R A (InvolutiveStar.toStar.{u2} R (StarAddMonoid.toInvolutiveStar.{u2} R _inst_1 _inst_2)) _inst_3) (Unitization.inr.{u2, u1} R A (AddMonoid.toZero.{u2} R _inst_1) a))
Case conversion may be inaccurate. Consider using '#align unitization.coe_star Unitization.inr_starₓ'. -/
@[simp]
theorem inr_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) :
    ↑(star a) = star (a : Unitization R A) :=
  ext (by simp only [fst_star, star_zero, fst_coe]) rfl
#align unitization.coe_star Unitization.inr_star

instance [AddMonoid R] [AddMonoid A] [StarAddMonoid R] [StarAddMonoid A] :
    StarAddMonoid (Unitization R A)
    where
  star_involutive x := ext (star_star x.fst) (star_star x.snd)
  star_add x y := ext (star_add x.fst y.fst) (star_add x.snd y.snd)

instance [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A] [Module R A]
    [StarModule R A] : StarModule R (Unitization R A) where star_smul r x := ext (by simp) (by simp)

instance [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] : StarRing (Unitization R A) :=
  { Unitization.starAddMonoid with
    star_mul := fun x y =>
      ext (by simp [star_mul]) (by simp [star_mul, add_comm (star x.fst • star y.snd)]) }

end Star

/-! ### Algebra structure -/


section Algebra

variable (S R A : Type _) [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Algebra S R] [DistribMulAction S A]
  [IsScalarTower S R A]

/- warning: unitization.algebra -> Unitization.algebra is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.algebra Unitization.algebraₓ'. -/
instance algebra : Algebra S (Unitization R A) :=
  {
    (Unitization.inlRingHom R A).comp
      (algebraMap S
        R) with
    commutes' := fun r x => by
      induction x using Unitization.ind
      simp only [mul_add, add_mul, RingHom.toFun_eq_coe, RingHom.coe_comp, Function.comp_apply,
        inl_ring_hom_apply, inl_mul_inl]
      rw [inl_mul_coe, coe_mul_inl, mul_comm]
    smul_def' := fun s x => by
      induction x using Unitization.ind
      simp only [mul_add, smul_add, RingHom.toFun_eq_coe, RingHom.coe_comp, Function.comp_apply,
        inl_ring_hom_apply, Algebra.algebraMap_eq_smul_one]
      rw [inl_mul_inl, inl_mul_coe, smul_one_mul, inl_smul, coe_smul, smul_one_smul] }
#align unitization.algebra Unitization.algebra

/- warning: unitization.algebra_map_eq_inl_comp -> Unitization.algebraMap_eq_inl_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.algebra_map_eq_inl_comp Unitization.algebraMap_eq_inl_compₓ'. -/
theorem algebraMap_eq_inl_comp : ⇑(algebraMap S (Unitization R A)) = inl ∘ algebraMap S R :=
  rfl
#align unitization.algebra_map_eq_inl_comp Unitization.algebraMap_eq_inl_comp

/- warning: unitization.algebra_map_eq_inl_ring_hom_comp -> Unitization.algebraMap_eq_inlRingHom_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.algebra_map_eq_inl_ring_hom_comp Unitization.algebraMap_eq_inlRingHom_compₓ'. -/
theorem algebraMap_eq_inlRingHom_comp :
    algebraMap S (Unitization R A) = (inlRingHom R A).comp (algebraMap S R) :=
  rfl
#align unitization.algebra_map_eq_inl_ring_hom_comp Unitization.algebraMap_eq_inlRingHom_comp

/- warning: unitization.algebra_map_eq_inl -> Unitization.algebraMap_eq_inl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.algebra_map_eq_inl Unitization.algebraMap_eq_inlₓ'. -/
theorem algebraMap_eq_inl : ⇑(algebraMap R (Unitization R A)) = inl :=
  rfl
#align unitization.algebra_map_eq_inl Unitization.algebraMap_eq_inl

/- warning: unitization.algebra_map_eq_inl_hom -> Unitization.algebraMap_eq_inl_hom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.algebra_map_eq_inl_hom Unitization.algebraMap_eq_inl_homₓ'. -/
theorem algebraMap_eq_inl_hom : algebraMap R (Unitization R A) = inlRingHom R A :=
  rfl
#align unitization.algebra_map_eq_inl_hom Unitization.algebraMap_eq_inl_hom

/- warning: unitization.fst_hom -> Unitization.fstHom is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_2 : CommSemiring.{u1} R] [_inst_3 : NonUnitalSemiring.{u2} A] [_inst_4 : Module.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))] [_inst_5 : IsScalarTower.{u1, u2, u2} R A A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)) _inst_4)))) (Mul.toSMul.{u2} A (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)))) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)) _inst_4))))] [_inst_6 : SMulCommClass.{u1, u2, u2} R A A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)) _inst_4)))) (Mul.toSMul.{u2} A (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))], AlgHom.{u1, max u1 u2, u1} R (Unitization.{u1, u2} R A) R _inst_2 (Unitization.semiring.{u1, u2} R A _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (CommSemiring.toSemiring.{u1} R _inst_2) (Unitization.algebra.{u1, u1, u2} R R A _inst_2 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 (Algebra.id.{u1} R _inst_2) (Module.toDistribMulAction.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)) _inst_4) (Unitization.fstHom._proof_1.{u1, u2} R A _inst_2 _inst_3 _inst_4)) (Algebra.id.{u1} R _inst_2)
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_2 : CommSemiring.{u1} R] [_inst_3 : NonUnitalSemiring.{u2} A] [_inst_4 : Module.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))] [_inst_5 : IsScalarTower.{u1, u2, u2} R A A (SMulZeroClass.toSMul.{u1, u2} R A (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (SMulWithZero.toSMulZeroClass.{u1, u2} R A (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_2)) (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)) _inst_4)))) (SMulZeroClass.toSMul.{u2, u2} A A (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (SMulWithZero.toSMulZeroClass.{u2, u2} A A (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (MulZeroClass.toSMulWithZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3))))) (SMulZeroClass.toSMul.{u1, u2} R A (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (SMulWithZero.toSMulZeroClass.{u1, u2} R A (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_2)) (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)) _inst_4))))] [_inst_6 : SMulCommClass.{u1, u2, u2} R A A (SMulZeroClass.toSMul.{u1, u2} R A (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (SMulWithZero.toSMulZeroClass.{u1, u2} R A (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_2)) (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)) _inst_4)))) (SMulZeroClass.toSMul.{u2, u2} A A (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (SMulWithZero.toSMulZeroClass.{u2, u2} A A (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (MulZeroClass.toSMulWithZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)))))], AlgHom.{u1, max u2 u1, u1} R (Unitization.{u1, u2} R A) R _inst_2 (Unitization.semiring.{u1, u2} R A _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (CommSemiring.toSemiring.{u1} R _inst_2) (Unitization.algebra.{u1, u1, u2} R R A _inst_2 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 (Algebra.id.{u1} R _inst_2) (Module.toDistribMulAction.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)) _inst_4) (IsScalarTower.left.{u1, u2} R A (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (MulActionWithZero.toMulAction.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (SemigroupWithZero.toZero.{u2} A (NonUnitalSemiring.toSemigroupWithZero.{u2} A _inst_3)) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A _inst_3)) _inst_4)))) (Algebra.id.{u1} R _inst_2)
Case conversion may be inaccurate. Consider using '#align unitization.fst_hom Unitization.fstHomₓ'. -/
/-- The canonical `R`-algebra projection `unitization R A → R`. -/
@[simps]
def fstHom : Unitization R A →ₐ[R] R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero
  map_add' := fst_add
  commutes' := fst_inl A
#align unitization.fst_hom Unitization.fstHom

end Algebra

section coe

#print Unitization.inrNonUnitalAlgHom /-
/-- The coercion from a non-unital `R`-algebra `A` to its unitization `unitization R A`
realized as a non-unital algebra homomorphism. -/
@[simps]
def inrNonUnitalAlgHom (R A : Type _) [CommSemiring R] [NonUnitalSemiring A] [Module R A] :
    A →ₙₐ[R] Unitization R A where
  toFun := coe
  map_smul' := inr_smul R
  map_zero' := inr_zero R
  map_add' := inr_add R
  map_mul' := inr_mul R
#align unitization.coe_non_unital_alg_hom Unitization.inrNonUnitalAlgHom
-/

end coe

section AlgHom

variable {S R A : Type _} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type _} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type _} [Ring C] [Algebra R C]

/- warning: unitization.alg_hom_ext -> Unitization.algHom_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.alg_hom_ext Unitization.algHom_extₓ'. -/
theorem algHom_ext {φ ψ : Unitization R A →ₐ[S] B} (h : ∀ a : A, φ a = ψ a)
    (h' : ∀ r, φ (algebraMap R (Unitization R A) r) = ψ (algebraMap R (Unitization R A) r)) :
    φ = ψ := by
  ext
  induction x using Unitization.ind
  simp only [map_add, ← algebra_map_eq_inl, h, h']
#align unitization.alg_hom_ext Unitization.algHom_ext

/- warning: unitization.alg_hom_ext' -> Unitization.algHom_ext' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.alg_hom_ext' Unitization.algHom_ext'ₓ'. -/
/-- See note [partially-applied ext lemmas] -/
@[ext]
theorem algHom_ext' {φ ψ : Unitization R A →ₐ[R] C}
    (h :
      φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A) =
        ψ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)) :
    φ = ψ :=
  algHom_ext (NonUnitalAlgHom.congr_fun h) (by simp [AlgHom.commutes])
#align unitization.alg_hom_ext' Unitization.algHom_ext'

/- warning: unitization.lift -> Unitization.lift is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.lift Unitization.liftₓ'. -/
/-- Non-unital algebra homomorphisms from `A` into a unital `R`-algebra `C` lift uniquely to
`unitization R A →ₐ[R] C`. This is the universal property of the unitization. -/
@[simps apply_apply]
def lift : (A →ₙₐ[R] C) ≃ (Unitization R A →ₐ[R] C)
    where
  toFun φ :=
    { toFun := fun x => algebraMap R C x.fst + φ x.snd
      map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero]
      map_mul' := fun x y => by
        induction x using Unitization.ind
        induction y using Unitization.ind
        simp only [mul_add, add_mul, coe_mul, fst_add, fst_mul, fst_inl, fst_coe,
          MulZeroClass.mul_zero, add_zero, MulZeroClass.zero_mul, map_mul, snd_add, snd_mul,
          snd_inl, smul_zero, snd_coe, zero_add, φ.map_add, φ.map_smul, φ.map_mul, zero_smul,
          zero_add]
        rw [← Algebra.commutes _ (φ x_a)]
        simp only [Algebra.algebraMap_eq_smul_one, smul_one_mul, add_assoc]
      map_zero' := by simp only [fst_zero, map_zero, snd_zero, φ.map_zero, add_zero]
      map_add' := fun x y => by
        induction x using Unitization.ind
        induction y using Unitization.ind
        simp only [fst_add, fst_inl, fst_coe, add_zero, map_add, snd_add, snd_inl, snd_coe,
          zero_add, φ.map_add]
        rw [add_add_add_comm]
      commutes' := fun r => by
        simp only [algebra_map_eq_inl, fst_inl, snd_inl, φ.map_zero, add_zero] }
  invFun φ := φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)
  left_inv φ := by ext; simp
  right_inv φ := Unitization.algHom_ext' (by ext; simp)
#align unitization.lift Unitization.lift

/- warning: unitization.lift_symm_apply -> Unitization.lift_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unitization.lift_symm_apply Unitization.lift_symm_applyₓ'. -/
theorem lift_symm_apply (φ : Unitization R A →ₐ[R] C) (a : A) : Unitization.lift.symm φ a = φ a :=
  rfl
#align unitization.lift_symm_apply Unitization.lift_symm_apply

end AlgHom

end Unitization

