/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.smul_with_zero
! leanprover-community/mathlib commit 9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.Ring.Opposite
import Mathbin.GroupTheory.GroupAction.Opposite
import Mathbin.GroupTheory.GroupAction.Prod

/-!
# Introduce `smul_with_zero`

In analogy with the usual monoid action on a Type `M`, we introduce an action of a
`monoid_with_zero` on a Type with `0`.

In particular, for Types `R` and `M`, both containing `0`, we define `smul_with_zero R M` to
be the typeclass where the products `r • 0` and `0 • m` vanish for all `r : R` and all `m : M`.

Moreover, in the case in which `R` is a `monoid_with_zero`, we introduce the typeclass
`mul_action_with_zero R M`, mimicking group actions and having an absorbing `0` in `R`.
Thus, the action is required to be compatible with

* the unit of the monoid, acting as the identity;
* the zero of the monoid_with_zero, acting as zero;
* associativity of the monoid.

We also add an `instance`:

* any `monoid_with_zero` has a `mul_action_with_zero R R` acting on itself.

## Main declarations

* `smul_monoid_with_zero_hom`: Scalar multiplication bundled as a morphism of monoids with zero.
-/


variable {R R' M M' : Type _}

section Zero

variable (R M)

#print SMulWithZero /-
/-- `smul_with_zero` is a class consisting of a Type `R` with `0 ∈ R` and a scalar multiplication
of `R` on a Type `M` with `0`, such that the equality `r • m = 0` holds if at least one among `r`
or `m` equals `0`. -/
class SMulWithZero [Zero R] [Zero M] extends SMulZeroClass R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
#align smul_with_zero SMulWithZero
-/

/- warning: mul_zero_class.to_smul_with_zero -> MulZeroClass.toSMulWithZero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : MulZeroClass.{u1} R], SMulWithZero.{u1, u1} R R (MulZeroClass.toHasZero.{u1} R _inst_1) (MulZeroClass.toHasZero.{u1} R _inst_1)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : MulZeroClass.{u1} R], SMulWithZero.{u1, u1} R R (MulZeroClass.toZero.{u1} R _inst_1) (MulZeroClass.toZero.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align mul_zero_class.to_smul_with_zero MulZeroClass.toSMulWithZeroₓ'. -/
instance MulZeroClass.toSMulWithZero [MulZeroClass R] : SMulWithZero R R
    where
  smul := (· * ·)
  smul_zero := mul_zero
  zero_smul := zero_mul
#align mul_zero_class.to_smul_with_zero MulZeroClass.toSMulWithZero

/- warning: mul_zero_class.to_opposite_smul_with_zero -> MulZeroClass.toOppositeSMulWithZero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : MulZeroClass.{u1} R], SMulWithZero.{u1, u1} (MulOpposite.{u1} R) R (MulOpposite.hasZero.{u1} R (MulZeroClass.toHasZero.{u1} R _inst_1)) (MulZeroClass.toHasZero.{u1} R _inst_1)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : MulZeroClass.{u1} R], SMulWithZero.{u1, u1} (MulOpposite.{u1} R) R (MulOpposite.instZeroMulOpposite.{u1} R (MulZeroClass.toZero.{u1} R _inst_1)) (MulZeroClass.toZero.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align mul_zero_class.to_opposite_smul_with_zero MulZeroClass.toOppositeSMulWithZeroₓ'. -/
/-- Like `mul_zero_class.to_smul_with_zero`, but multiplies on the right. -/
instance MulZeroClass.toOppositeSMulWithZero [MulZeroClass R] : SMulWithZero Rᵐᵒᵖ R
    where
  smul := (· • ·)
  smul_zero r := zero_mul _
  zero_smul := mul_zero
#align mul_zero_class.to_opposite_smul_with_zero MulZeroClass.toOppositeSMulWithZero

variable (R) {M} [Zero R] [Zero M] [SMulWithZero R M]

/- warning: zero_smul -> zero_smul is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {M : Type.{u2}} [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} M] [_inst_3 : SMulWithZero.{u1, u2} R M _inst_1 _inst_2] (m : M), Eq.{succ u2} M (HasSmul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R _inst_1))) m) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_2)))
but is expected to have type
  forall (R : Type.{u1}) {M : Type.{u2}} [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} M] [_inst_3 : SMulWithZero.{u1, u2} R M _inst_1 _inst_2] (m : M), Eq.{succ u2} M (HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M _inst_2 (SMulWithZero.toSMulZeroClass.{u1, u2} R M _inst_1 _inst_2 _inst_3))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R _inst_1)) m) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M _inst_2))
Case conversion may be inaccurate. Consider using '#align zero_smul zero_smulₓ'. -/
@[simp]
theorem zero_smul (m : M) : (0 : R) • m = 0 :=
  SMulWithZero.zero_smul m
#align zero_smul zero_smul

variable {R M} [Zero R'] [Zero M'] [HasSmul R M']

/- warning: function.injective.smul_with_zero -> Function.Injective.smulWithZero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {M' : Type.{u3}} [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} M] [_inst_3 : SMulWithZero.{u1, u2} R M _inst_1 _inst_2] [_inst_5 : Zero.{u3} M'] [_inst_6 : HasSmul.{u1, u3} R M'] (f : ZeroHom.{u3, u2} M' M _inst_5 _inst_2), (Function.Injective.{succ u3, succ u2} M' M (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (ZeroHom.{u3, u2} M' M _inst_5 _inst_2) (fun (_x : ZeroHom.{u3, u2} M' M _inst_5 _inst_2) => M' -> M) (ZeroHom.hasCoeToFun.{u3, u2} M' M _inst_5 _inst_2) f)) -> (forall (a : R) (b : M'), Eq.{succ u2} M (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (ZeroHom.{u3, u2} M' M _inst_5 _inst_2) (fun (_x : ZeroHom.{u3, u2} M' M _inst_5 _inst_2) => M' -> M) (ZeroHom.hasCoeToFun.{u3, u2} M' M _inst_5 _inst_2) f (HasSmul.smul.{u1, u3} R M' _inst_6 a b)) (HasSmul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} R M _inst_1 _inst_2 _inst_3)) a (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (ZeroHom.{u3, u2} M' M _inst_5 _inst_2) (fun (_x : ZeroHom.{u3, u2} M' M _inst_5 _inst_2) => M' -> M) (ZeroHom.hasCoeToFun.{u3, u2} M' M _inst_5 _inst_2) f b))) -> (SMulWithZero.{u1, u3} R M' _inst_1 _inst_5)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {M' : Type.{u3}} [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} M] [_inst_3 : SMulWithZero.{u1, u2} R M _inst_1 _inst_2] [_inst_5 : Zero.{u3} M'] [_inst_6 : SMul.{u1, u3} R M'] (f : ZeroHom.{u3, u2} M' M _inst_5 _inst_2), (Function.Injective.{succ u3, succ u2} M' M (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_2) M' (fun (_x : M') => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) _x) (ZeroHomClass.toFunLike.{max u2 u3, u3, u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_2) M' M _inst_5 _inst_2 (ZeroHom.zeroHomClass.{u3, u2} M' M _inst_5 _inst_2)) f)) -> (forall (a : R) (b : M'), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) (HSMul.hSMul.{u1, u3, u3} R M' M' (instHSMul.{u1, u3} R M' _inst_6) a b)) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_2) M' (fun (_x : M') => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) _x) (ZeroHomClass.toFunLike.{max u2 u3, u3, u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_2) M' M _inst_5 _inst_2 (ZeroHom.zeroHomClass.{u3, u2} M' M _inst_5 _inst_2)) f (HSMul.hSMul.{u1, u3, u3} R M' M' (instHSMul.{u1, u3} R M' _inst_6) a b)) (HSMul.hSMul.{u1, u2, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) (instHSMul.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) (SMulZeroClass.toSMul.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) _inst_2 (SMulWithZero.toSMulZeroClass.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) _inst_1 _inst_2 _inst_3))) a (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_2) M' (fun (_x : M') => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) _x) (ZeroHomClass.toFunLike.{max u2 u3, u3, u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_2) M' M _inst_5 _inst_2 (ZeroHom.zeroHomClass.{u3, u2} M' M _inst_5 _inst_2)) f b))) -> (SMulWithZero.{u1, u3} R M' _inst_1 _inst_5)
Case conversion may be inaccurate. Consider using '#align function.injective.smul_with_zero Function.Injective.smulWithZeroₓ'. -/
/-- Pullback a `smul_with_zero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.smulWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : SMulWithZero R M'
    where
  smul := (· • ·)
  zero_smul a := hf <| by simp [smul]
  smul_zero a := hf <| by simp [smul]
#align function.injective.smul_with_zero Function.Injective.smulWithZero

/- warning: function.surjective.smul_with_zero -> Function.Surjective.smulWithZero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {M' : Type.{u3}} [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} M] [_inst_3 : SMulWithZero.{u1, u2} R M _inst_1 _inst_2] [_inst_5 : Zero.{u3} M'] [_inst_6 : HasSmul.{u1, u3} R M'] (f : ZeroHom.{u2, u3} M M' _inst_2 _inst_5), (Function.Surjective.{succ u2, succ u3} M M' (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (ZeroHom.{u2, u3} M M' _inst_2 _inst_5) (fun (_x : ZeroHom.{u2, u3} M M' _inst_2 _inst_5) => M -> M') (ZeroHom.hasCoeToFun.{u2, u3} M M' _inst_2 _inst_5) f)) -> (forall (a : R) (b : M), Eq.{succ u3} M' (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (ZeroHom.{u2, u3} M M' _inst_2 _inst_5) (fun (_x : ZeroHom.{u2, u3} M M' _inst_2 _inst_5) => M -> M') (ZeroHom.hasCoeToFun.{u2, u3} M M' _inst_2 _inst_5) f (HasSmul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} R M _inst_1 _inst_2 _inst_3)) a b)) (HasSmul.smul.{u1, u3} R M' _inst_6 a (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (ZeroHom.{u2, u3} M M' _inst_2 _inst_5) (fun (_x : ZeroHom.{u2, u3} M M' _inst_2 _inst_5) => M -> M') (ZeroHom.hasCoeToFun.{u2, u3} M M' _inst_2 _inst_5) f b))) -> (SMulWithZero.{u1, u3} R M' _inst_1 _inst_5)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {M' : Type.{u3}} [_inst_1 : Zero.{u1} R] [_inst_2 : Zero.{u2} M] [_inst_3 : SMulWithZero.{u1, u2} R M _inst_1 _inst_2] [_inst_5 : Zero.{u3} M'] [_inst_6 : SMul.{u1, u3} R M'] (f : ZeroHom.{u2, u3} M M' _inst_2 _inst_5), (Function.Surjective.{succ u2, succ u3} M M' (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (ZeroHom.{u2, u3} M M' _inst_2 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') _x) (ZeroHomClass.toFunLike.{max u2 u3, u2, u3} (ZeroHom.{u2, u3} M M' _inst_2 _inst_5) M M' _inst_2 _inst_5 (ZeroHom.zeroHomClass.{u2, u3} M M' _inst_2 _inst_5)) f)) -> (forall (a : R) (b : M), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') (HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M _inst_2 (SMulWithZero.toSMulZeroClass.{u1, u2} R M _inst_1 _inst_2 _inst_3))) a b)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (ZeroHom.{u2, u3} M M' _inst_2 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') _x) (ZeroHomClass.toFunLike.{max u2 u3, u2, u3} (ZeroHom.{u2, u3} M M' _inst_2 _inst_5) M M' _inst_2 _inst_5 (ZeroHom.zeroHomClass.{u2, u3} M M' _inst_2 _inst_5)) f (HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M _inst_2 (SMulWithZero.toSMulZeroClass.{u1, u2} R M _inst_1 _inst_2 _inst_3))) a b)) (HSMul.hSMul.{u1, u3, u3} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') b) (instHSMul.{u1, u3} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') b) _inst_6) a (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (ZeroHom.{u2, u3} M M' _inst_2 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') _x) (ZeroHomClass.toFunLike.{max u2 u3, u2, u3} (ZeroHom.{u2, u3} M M' _inst_2 _inst_5) M M' _inst_2 _inst_5 (ZeroHom.zeroHomClass.{u2, u3} M M' _inst_2 _inst_5)) f b))) -> (SMulWithZero.{u1, u3} R M' _inst_1 _inst_5)
Case conversion may be inaccurate. Consider using '#align function.surjective.smul_with_zero Function.Surjective.smulWithZeroₓ'. -/
/-- Pushforward a `smul_with_zero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.smulWithZero (f : ZeroHom M M') (hf : Function.Surjective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : SMulWithZero R M'
    where
  smul := (· • ·)
  zero_smul m := by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by simp only [← f.map_zero, ← smul, smul_zero]
#align function.surjective.smul_with_zero Function.Surjective.smulWithZero

variable (M)

#print SMulWithZero.compHom /-
/-- Compose a `smul_with_zero` with a `zero_hom`, with action `f r' • m` -/
def SMulWithZero.compHom (f : ZeroHom R' R) : SMulWithZero R' M
    where
  smul := (· • ·) ∘ f
  smul_zero m := by simp
  zero_smul m := by simp
#align smul_with_zero.comp_hom SMulWithZero.compHom
-/

end Zero

/- warning: add_monoid.nat_smul_with_zero -> AddMonoid.natSMulWithZero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : AddMonoid.{u1} M], SMulWithZero.{0, u1} Nat M Nat.hasZero (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : AddMonoid.{u1} M], SMulWithZero.{0, u1} Nat M (Zero.ofOfNat0.{0} Nat (instOfNatNat 0)) (AddMonoid.toZero.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align add_monoid.nat_smul_with_zero AddMonoid.natSMulWithZeroₓ'. -/
instance AddMonoid.natSMulWithZero [AddMonoid M] : SMulWithZero ℕ M
    where
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
#align add_monoid.nat_smul_with_zero AddMonoid.natSMulWithZero

/- warning: add_group.int_smul_with_zero -> AddGroup.intSMulWithZero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : AddGroup.{u1} M], SMulWithZero.{0, u1} Int M Int.hasZero (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M _inst_1))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : AddGroup.{u1} M], SMulWithZero.{0, u1} Int M (Zero.ofOfNat0.{0} Int (instOfNatInt 0)) (NegZeroClass.toZero.{u1} M (SubNegZeroMonoid.toNegZeroClass.{u1} M (SubtractionMonoid.toSubNegZeroMonoid.{u1} M (AddGroup.toSubtractionMonoid.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align add_group.int_smul_with_zero AddGroup.intSMulWithZeroₓ'. -/
instance AddGroup.intSMulWithZero [AddGroup M] : SMulWithZero ℤ M
    where
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
#align add_group.int_smul_with_zero AddGroup.intSMulWithZero

section MonoidWithZero

variable [MonoidWithZero R] [MonoidWithZero R'] [Zero M]

variable (R M)

#print MulActionWithZero /-
/-- An action of a monoid with zero `R` on a Type `M`, also with `0`, extends `mul_action` and
is compatible with `0` (both in `R` and in `M`), with `1 ∈ R`, and with associativity of
multiplication on the monoid `M`. -/
class MulActionWithZero extends MulAction R M where
  -- these fields are copied from `smul_with_zero`, as `extends` behaves poorly
  smul_zero : ∀ r : R, r • (0 : M) = 0
  zero_smul : ∀ m : M, (0 : R) • m = 0
#align mul_action_with_zero MulActionWithZero
-/

/- warning: mul_action_with_zero.to_smul_with_zero -> MulActionWithZero.toSMulWithZero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : MonoidWithZero.{u1} R] [_inst_3 : Zero.{u2} M] [m : MulActionWithZero.{u1, u2} R M _inst_1 _inst_3], SMulWithZero.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) _inst_3
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : MonoidWithZero.{u1} R] [_inst_3 : Zero.{u2} M] [m : MulActionWithZero.{u1, u2} R M _inst_1 _inst_3], SMulWithZero.{u1, u2} R M (MonoidWithZero.toZero.{u1} R _inst_1) _inst_3
Case conversion may be inaccurate. Consider using '#align mul_action_with_zero.to_smul_with_zero MulActionWithZero.toSMulWithZeroₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) MulActionWithZero.toSMulWithZero [m : MulActionWithZero R M] :
    SMulWithZero R M :=
  { m with }
#align mul_action_with_zero.to_smul_with_zero MulActionWithZero.toSMulWithZero

/- warning: monoid_with_zero.to_mul_action_with_zero -> MonoidWithZero.toMulActionWithZero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} R], MulActionWithZero.{u1, u1} R R _inst_1 (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} R], MulActionWithZero.{u1, u1} R R _inst_1 (MonoidWithZero.toZero.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero.to_mul_action_with_zero MonoidWithZero.toMulActionWithZeroₓ'. -/
/-- See also `semiring.to_module` -/
instance MonoidWithZero.toMulActionWithZero : MulActionWithZero R R :=
  { MulZeroClass.toSMulWithZero R, Monoid.toMulAction R with }
#align monoid_with_zero.to_mul_action_with_zero MonoidWithZero.toMulActionWithZero

/- warning: monoid_with_zero.to_opposite_mul_action_with_zero -> MonoidWithZero.toOppositeMulActionWithZero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} R], MulActionWithZero.{u1, u1} (MulOpposite.{u1} R) R (MulOpposite.monoidWithZero.{u1} R _inst_1) (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} R], MulActionWithZero.{u1, u1} (MulOpposite.{u1} R) R (MulOpposite.instMonoidWithZeroMulOpposite.{u1} R _inst_1) (MonoidWithZero.toZero.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero.to_opposite_mul_action_with_zero MonoidWithZero.toOppositeMulActionWithZeroₓ'. -/
/-- Like `monoid_with_zero.to_mul_action_with_zero`, but multiplies on the right. See also
`semiring.to_opposite_module` -/
instance MonoidWithZero.toOppositeMulActionWithZero : MulActionWithZero Rᵐᵒᵖ R :=
  { MulZeroClass.toOppositeSMulWithZero R, Monoid.toOppositeMulAction R with }
#align monoid_with_zero.to_opposite_mul_action_with_zero MonoidWithZero.toOppositeMulActionWithZero

variable {R M} [MulActionWithZero R M] [Zero M'] [HasSmul R M']

/- warning: function.injective.mul_action_with_zero -> Function.Injective.mulActionWithZero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {M' : Type.{u3}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_3 : Zero.{u2} M] [_inst_4 : MulActionWithZero.{u1, u2} R M _inst_1 _inst_3] [_inst_5 : Zero.{u3} M'] [_inst_6 : HasSmul.{u1, u3} R M'] (f : ZeroHom.{u3, u2} M' M _inst_5 _inst_3), (Function.Injective.{succ u3, succ u2} M' M (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (ZeroHom.{u3, u2} M' M _inst_5 _inst_3) (fun (_x : ZeroHom.{u3, u2} M' M _inst_5 _inst_3) => M' -> M) (ZeroHom.hasCoeToFun.{u3, u2} M' M _inst_5 _inst_3) f)) -> (forall (a : R) (b : M'), Eq.{succ u2} M (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (ZeroHom.{u3, u2} M' M _inst_5 _inst_3) (fun (_x : ZeroHom.{u3, u2} M' M _inst_5 _inst_3) => M' -> M) (ZeroHom.hasCoeToFun.{u3, u2} M' M _inst_5 _inst_3) f (HasSmul.smul.{u1, u3} R M' _inst_6 a b)) (HasSmul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M _inst_3 (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) _inst_3 (MulActionWithZero.toSMulWithZero.{u1, u2} R M _inst_1 _inst_3 _inst_4))) a (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (ZeroHom.{u3, u2} M' M _inst_5 _inst_3) (fun (_x : ZeroHom.{u3, u2} M' M _inst_5 _inst_3) => M' -> M) (ZeroHom.hasCoeToFun.{u3, u2} M' M _inst_5 _inst_3) f b))) -> (MulActionWithZero.{u1, u3} R M' _inst_1 _inst_5)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {M' : Type.{u3}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_3 : Zero.{u2} M] [_inst_4 : MulActionWithZero.{u1, u2} R M _inst_1 _inst_3] [_inst_5 : Zero.{u3} M'] [_inst_6 : SMul.{u1, u3} R M'] (f : ZeroHom.{u3, u2} M' M _inst_5 _inst_3), (Function.Injective.{succ u3, succ u2} M' M (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_3) M' (fun (_x : M') => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) _x) (ZeroHomClass.toFunLike.{max u2 u3, u3, u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_3) M' M _inst_5 _inst_3 (ZeroHom.zeroHomClass.{u3, u2} M' M _inst_5 _inst_3)) f)) -> (forall (a : R) (b : M'), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) (HSMul.hSMul.{u1, u3, u3} R M' M' (instHSMul.{u1, u3} R M' _inst_6) a b)) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_3) M' (fun (_x : M') => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) _x) (ZeroHomClass.toFunLike.{max u2 u3, u3, u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_3) M' M _inst_5 _inst_3 (ZeroHom.zeroHomClass.{u3, u2} M' M _inst_5 _inst_3)) f (HSMul.hSMul.{u1, u3, u3} R M' M' (instHSMul.{u1, u3} R M' _inst_6) a b)) (HSMul.hSMul.{u1, u2, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) (instHSMul.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) (SMulZeroClass.toSMul.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) _inst_3 (SMulWithZero.toSMulZeroClass.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) (MonoidWithZero.toZero.{u1} R _inst_1) _inst_3 (MulActionWithZero.toSMulWithZero.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) b) _inst_1 _inst_3 _inst_4)))) a (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_3) M' (fun (_x : M') => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M') => M) _x) (ZeroHomClass.toFunLike.{max u2 u3, u3, u2} (ZeroHom.{u3, u2} M' M _inst_5 _inst_3) M' M _inst_5 _inst_3 (ZeroHom.zeroHomClass.{u3, u2} M' M _inst_5 _inst_3)) f b))) -> (MulActionWithZero.{u1, u3} R M' _inst_1 _inst_5)
Case conversion may be inaccurate. Consider using '#align function.injective.mul_action_with_zero Function.Injective.mulActionWithZeroₓ'. -/
/-- Pullback a `mul_action_with_zero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulActionWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : MulActionWithZero R M' :=
  { hf.MulAction f smul, hf.SmulWithZero f smul with }
#align function.injective.mul_action_with_zero Function.Injective.mulActionWithZero

/- warning: function.surjective.mul_action_with_zero -> Function.Surjective.mulActionWithZero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {M' : Type.{u3}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_3 : Zero.{u2} M] [_inst_4 : MulActionWithZero.{u1, u2} R M _inst_1 _inst_3] [_inst_5 : Zero.{u3} M'] [_inst_6 : HasSmul.{u1, u3} R M'] (f : ZeroHom.{u2, u3} M M' _inst_3 _inst_5), (Function.Surjective.{succ u2, succ u3} M M' (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (ZeroHom.{u2, u3} M M' _inst_3 _inst_5) (fun (_x : ZeroHom.{u2, u3} M M' _inst_3 _inst_5) => M -> M') (ZeroHom.hasCoeToFun.{u2, u3} M M' _inst_3 _inst_5) f)) -> (forall (a : R) (b : M), Eq.{succ u3} M' (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (ZeroHom.{u2, u3} M M' _inst_3 _inst_5) (fun (_x : ZeroHom.{u2, u3} M M' _inst_3 _inst_5) => M -> M') (ZeroHom.hasCoeToFun.{u2, u3} M M' _inst_3 _inst_5) f (HasSmul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M _inst_3 (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) _inst_3 (MulActionWithZero.toSMulWithZero.{u1, u2} R M _inst_1 _inst_3 _inst_4))) a b)) (HasSmul.smul.{u1, u3} R M' _inst_6 a (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (ZeroHom.{u2, u3} M M' _inst_3 _inst_5) (fun (_x : ZeroHom.{u2, u3} M M' _inst_3 _inst_5) => M -> M') (ZeroHom.hasCoeToFun.{u2, u3} M M' _inst_3 _inst_5) f b))) -> (MulActionWithZero.{u1, u3} R M' _inst_1 _inst_5)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {M' : Type.{u3}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_3 : Zero.{u2} M] [_inst_4 : MulActionWithZero.{u1, u2} R M _inst_1 _inst_3] [_inst_5 : Zero.{u3} M'] [_inst_6 : SMul.{u1, u3} R M'] (f : ZeroHom.{u2, u3} M M' _inst_3 _inst_5), (Function.Surjective.{succ u2, succ u3} M M' (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (ZeroHom.{u2, u3} M M' _inst_3 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') _x) (ZeroHomClass.toFunLike.{max u2 u3, u2, u3} (ZeroHom.{u2, u3} M M' _inst_3 _inst_5) M M' _inst_3 _inst_5 (ZeroHom.zeroHomClass.{u2, u3} M M' _inst_3 _inst_5)) f)) -> (forall (a : R) (b : M), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') (HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M _inst_3 (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R _inst_1) _inst_3 (MulActionWithZero.toSMulWithZero.{u1, u2} R M _inst_1 _inst_3 _inst_4)))) a b)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (ZeroHom.{u2, u3} M M' _inst_3 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') _x) (ZeroHomClass.toFunLike.{max u2 u3, u2, u3} (ZeroHom.{u2, u3} M M' _inst_3 _inst_5) M M' _inst_3 _inst_5 (ZeroHom.zeroHomClass.{u2, u3} M M' _inst_3 _inst_5)) f (HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M _inst_3 (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R _inst_1) _inst_3 (MulActionWithZero.toSMulWithZero.{u1, u2} R M _inst_1 _inst_3 _inst_4)))) a b)) (HSMul.hSMul.{u1, u3, u3} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') b) (instHSMul.{u1, u3} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') b) _inst_6) a (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (ZeroHom.{u2, u3} M M' _inst_3 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => M') _x) (ZeroHomClass.toFunLike.{max u2 u3, u2, u3} (ZeroHom.{u2, u3} M M' _inst_3 _inst_5) M M' _inst_3 _inst_5 (ZeroHom.zeroHomClass.{u2, u3} M M' _inst_3 _inst_5)) f b))) -> (MulActionWithZero.{u1, u3} R M' _inst_1 _inst_5)
Case conversion may be inaccurate. Consider using '#align function.surjective.mul_action_with_zero Function.Surjective.mulActionWithZeroₓ'. -/
/-- Pushforward a `mul_action_with_zero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulActionWithZero (f : ZeroHom M M') (hf : Function.Surjective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : MulActionWithZero R M' :=
  { hf.MulAction f smul, hf.SmulWithZero f smul with }
#align function.surjective.mul_action_with_zero Function.Surjective.mulActionWithZero

variable (M)

#print MulActionWithZero.compHom /-
/-- Compose a `mul_action_with_zero` with a `monoid_with_zero_hom`, with action `f r' • m` -/
def MulActionWithZero.compHom (f : R' →*₀ R) : MulActionWithZero R' M :=
  { SMulWithZero.compHom M f.toZeroHom with
    smul := (· • ·) ∘ f
    mul_smul := fun r s m => by simp [mul_smul]
    one_smul := fun m => by simp }
#align mul_action_with_zero.comp_hom MulActionWithZero.compHom
-/

end MonoidWithZero

section GroupWithZero

variable {α β : Type _} [GroupWithZero α] [GroupWithZero β] [MulActionWithZero α β]

/- warning: smul_inv₀ -> smul_inv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : GroupWithZero.{u2} β] [_inst_3 : MulActionWithZero.{u1, u2} α β (GroupWithZero.toMonoidWithZero.{u1} α _inst_1) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2))))] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (SMulZeroClass.toHasSmul.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (GroupWithZero.toMonoidWithZero.{u1} α _inst_1) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) _inst_3))) (Mul.toSMul.{u2} β (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))))] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (SMulZeroClass.toHasSmul.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (GroupWithZero.toMonoidWithZero.{u1} α _inst_1) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) _inst_3))) (Mul.toSMul.{u2} β (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2))))) (SMulZeroClass.toHasSmul.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (GroupWithZero.toMonoidWithZero.{u1} α _inst_1) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) _inst_3)))] (c : α) (x : β), Eq.{succ u2} β (Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (GroupWithZero.toDivInvMonoid.{u2} β _inst_2)) (HasSmul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (GroupWithZero.toMonoidWithZero.{u1} α _inst_1) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) _inst_3))) c x)) (HasSmul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (GroupWithZero.toMonoidWithZero.{u1} α _inst_1) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (GroupWithZero.toMonoidWithZero.{u2} β _inst_2)))) _inst_3))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) c) (Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (GroupWithZero.toDivInvMonoid.{u2} β _inst_2)) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : GroupWithZero.{u1} β] [_inst_3 : MulActionWithZero.{u2, u1} α β (GroupWithZero.toMonoidWithZero.{u2} α _inst_1) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2))] [_inst_4 : SMulCommClass.{u2, u1, u1} α β β (SMulZeroClass.toSMul.{u2, u1} α β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} α β (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} α β (GroupWithZero.toMonoidWithZero.{u2} α _inst_1) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) _inst_3))) (SMulZeroClass.toSMul.{u1, u1} β β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u1} β β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (MulZeroClass.toSMulWithZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2))))))] [_inst_5 : IsScalarTower.{u2, u1, u1} α β β (SMulZeroClass.toSMul.{u2, u1} α β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} α β (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} α β (GroupWithZero.toMonoidWithZero.{u2} α _inst_1) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) _inst_3))) (SMulZeroClass.toSMul.{u1, u1} β β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u1} β β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (MulZeroClass.toSMulWithZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)))))) (SMulZeroClass.toSMul.{u2, u1} α β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} α β (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} α β (GroupWithZero.toMonoidWithZero.{u2} α _inst_1) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) _inst_3)))] (c : α) (x : β), Eq.{succ u1} β (Inv.inv.{u1} β (GroupWithZero.toInv.{u1} β _inst_2) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (SMulZeroClass.toSMul.{u2, u1} α β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} α β (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} α β (GroupWithZero.toMonoidWithZero.{u2} α _inst_1) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) _inst_3)))) c x)) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (SMulZeroClass.toSMul.{u2, u1} α β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} α β (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} α β (GroupWithZero.toMonoidWithZero.{u2} α _inst_1) (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β _inst_2)) _inst_3)))) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_1) c) (Inv.inv.{u1} β (GroupWithZero.toInv.{u1} β _inst_2) x))
Case conversion may be inaccurate. Consider using '#align smul_inv₀ smul_inv₀ₓ'. -/
theorem smul_inv₀ [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) :
    (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine' inv_eq_of_mul_eq_one_left _
    rw [smul_mul_smul, inv_mul_cancel hc, inv_mul_cancel hx, one_smul]
#align smul_inv₀ smul_inv₀

end GroupWithZero

/- warning: smul_monoid_with_zero_hom -> smulMonoidWithZeroHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MonoidWithZero.{u1} α] [_inst_2 : MulZeroOneClass.{u2} β] [_inst_3 : MulActionWithZero.{u1, u2} α β _inst_1 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2))] [_inst_4 : IsScalarTower.{u1, u2, u2} α β β (SMulZeroClass.toHasSmul.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} α β _inst_1 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)) _inst_3))) (Mul.toSMul.{u2} β (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2))) (SMulZeroClass.toHasSmul.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} α β _inst_1 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)) _inst_3)))] [_inst_5 : SMulCommClass.{u1, u2, u2} α β β (SMulZeroClass.toHasSmul.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} α β _inst_1 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)) _inst_3))) (Mul.toSMul.{u2} β (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)))], MonoidWithZeroHom.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.mulZeroOneClass.{u1, u2} α β (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1) _inst_2) _inst_2
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MonoidWithZero.{u1} α] [_inst_2 : MulZeroOneClass.{u2} β] [_inst_3 : MulActionWithZero.{u1, u2} α β _inst_1 (MulZeroOneClass.toZero.{u2} β _inst_2)] [_inst_4 : IsScalarTower.{u1, u2, u2} α β β (SMulZeroClass.toSMul.{u1, u2} α β (MulZeroOneClass.toZero.{u2} β _inst_2) (SMulWithZero.toSMulZeroClass.{u1, u2} α β (MonoidWithZero.toZero.{u1} α _inst_1) (MulZeroOneClass.toZero.{u2} β _inst_2) (MulActionWithZero.toSMulWithZero.{u1, u2} α β _inst_1 (MulZeroOneClass.toZero.{u2} β _inst_2) _inst_3))) (SMulZeroClass.toSMul.{u2, u2} β β (MulZeroOneClass.toZero.{u2} β _inst_2) (SMulWithZero.toSMulZeroClass.{u2, u2} β β (MulZeroOneClass.toZero.{u2} β _inst_2) (MulZeroOneClass.toZero.{u2} β _inst_2) (MulZeroClass.toSMulWithZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2)))) (SMulZeroClass.toSMul.{u1, u2} α β (MulZeroOneClass.toZero.{u2} β _inst_2) (SMulWithZero.toSMulZeroClass.{u1, u2} α β (MonoidWithZero.toZero.{u1} α _inst_1) (MulZeroOneClass.toZero.{u2} β _inst_2) (MulActionWithZero.toSMulWithZero.{u1, u2} α β _inst_1 (MulZeroOneClass.toZero.{u2} β _inst_2) _inst_3)))] [_inst_5 : SMulCommClass.{u1, u2, u2} α β β (SMulZeroClass.toSMul.{u1, u2} α β (MulZeroOneClass.toZero.{u2} β _inst_2) (SMulWithZero.toSMulZeroClass.{u1, u2} α β (MonoidWithZero.toZero.{u1} α _inst_1) (MulZeroOneClass.toZero.{u2} β _inst_2) (MulActionWithZero.toSMulWithZero.{u1, u2} α β _inst_1 (MulZeroOneClass.toZero.{u2} β _inst_2) _inst_3))) (SMulZeroClass.toSMul.{u2, u2} β β (MulZeroOneClass.toZero.{u2} β _inst_2) (SMulWithZero.toSMulZeroClass.{u2, u2} β β (MulZeroOneClass.toZero.{u2} β _inst_2) (MulZeroOneClass.toZero.{u2} β _inst_2) (MulZeroClass.toSMulWithZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β _inst_2))))], MonoidWithZeroHom.{max u2 u1, u2} (Prod.{u1, u2} α β) β (Prod.instMulZeroOneClassProd.{u1, u2} α β (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1) _inst_2) _inst_2
Case conversion may be inaccurate. Consider using '#align smul_monoid_with_zero_hom smulMonoidWithZeroHomₓ'. -/
/-- Scalar multiplication as a monoid homomorphism with zero. -/
@[simps]
def smulMonoidWithZeroHom {α β : Type _} [MonoidWithZero α] [MulZeroOneClass β]
    [MulActionWithZero α β] [IsScalarTower α β β] [SMulCommClass α β β] : α × β →*₀ β :=
  { smulMonoidHom with map_zero' := smul_zero _ }
#align smul_monoid_with_zero_hom smulMonoidWithZeroHom

