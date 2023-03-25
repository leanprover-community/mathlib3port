/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module number_theory.zsqrtd.to_real
! leanprover-community/mathlib commit 97eab48559068f3d6313da387714ef25768fb730
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Sqrt
import Mathbin.NumberTheory.Zsqrtd.Basic

/-!
# Image of `zsqrtd` in `ℝ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `zsqrtd.to_real` and related lemmas.
It is in a separate file to avoid pulling in all of `data.real` into `data.zsqrtd`.
-/


namespace Zsqrtd

#print Zsqrtd.toReal /-
/-- The image of `zsqrtd` in `ℝ`, using `real.sqrt` which takes the positive root of `d`.

If the negative root is desired, use `to_real h a.conj`. -/
@[simps]
noncomputable def toReal {d : ℤ} (h : 0 ≤ d) : ℤ√d →+* ℝ :=
  lift ⟨Real.sqrt d, Real.mul_self_sqrt (Int.cast_nonneg.mpr h)⟩
#align zsqrtd.to_real Zsqrtd.toReal
-/

/- warning: zsqrtd.to_real_injective -> Zsqrtd.toReal_injective is a dubious translation:
lean 3 declaration is
  forall {d : Int} (h0d : LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) d), (forall (n : Int), Ne.{1} Int d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) n n)) -> (Function.Injective.{1, 1} (Zsqrtd d) Real (coeFn.{1, 1} (RingHom.{0, 0} (Zsqrtd d) Real (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (fun (_x : RingHom.{0, 0} (Zsqrtd d) Real (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) => (Zsqrtd d) -> Real) (RingHom.hasCoeToFun.{0, 0} (Zsqrtd d) Real (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (Zsqrtd.toReal d h0d)))
but is expected to have type
  forall {d : Int} (h0d : LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) d), (forall (n : Int), Ne.{1} Int d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) n n)) -> (Function.Injective.{1, 1} (Zsqrtd d) Real (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} (Zsqrtd d) Real (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (Zsqrtd d) (fun (_x : Zsqrtd d) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Zsqrtd d) => Real) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} (Zsqrtd d) Real (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (Zsqrtd d) Real (NonUnitalNonAssocSemiring.toMul.{0} (Zsqrtd d) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))))) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} (Zsqrtd d) Real (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (Zsqrtd d) Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} (Zsqrtd d) Real (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (Zsqrtd d) Real (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)) (RingHom.instRingHomClassRingHom.{0, 0} (Zsqrtd d) Real (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)))))) (Zsqrtd.toReal d h0d)))
Case conversion may be inaccurate. Consider using '#align zsqrtd.to_real_injective Zsqrtd.toReal_injectiveₓ'. -/
theorem toReal_injective {d : ℤ} (h0d : 0 ≤ d) (hd : ∀ n : ℤ, d ≠ n * n) :
    Function.Injective (toReal h0d) :=
  lift_injective _ hd
#align zsqrtd.to_real_injective Zsqrtd.toReal_injective

end Zsqrtd

