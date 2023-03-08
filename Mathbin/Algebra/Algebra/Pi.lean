/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.algebra.pi
! leanprover-community/mathlib commit 832f7b9162039c28b9361289c8681f155cae758f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Equiv

/-!
# The R-algebra structure on families of R-algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

## Main defintions

* `pi.algebra`
* `pi.eval_alg_hom`
* `pi.const_alg_hom`
-/


universe u v w

namespace Pi

variable {I : Type u}

-- The indexing type
variable {R : Type _}

-- The scalar type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

variable (I f)

#print Pi.algebra /-
instance algebra {r : CommSemiring R} [s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] :
    Algebra R (∀ i : I, f i) :=
  {
    (Pi.ringHom fun i => algebraMap R (f i) :
      R →+* ∀ i : I,
          f i) with
    commutes' := fun a f => by ext; simp [Algebra.commutes]
    smul_def' := fun a f => by ext; simp [Algebra.smul_def] }
#align pi.algebra Pi.algebra
-/

/- warning: pi.algebra_map_def -> Pi.algebraMap_def is a dubious translation:
lean 3 declaration is
  forall (I : Type.{u1}) {R : Type.{u3}} (f : I -> Type.{u2}) {r : CommSemiring.{u3} R} [s : forall (i : I), Semiring.{u2} (f i)] [_inst_1 : forall (i : I), Algebra.{u3, u2} R (f i) r (s i)] (a : R), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ u3) (succ (max u1 u2))} (RingHom.{u3, max u1 u2} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{max u1 u2} (forall (i : I), f i) (Pi.semiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => s i)))) (fun (_x : RingHom.{u3, max u1 u2} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{max u1 u2} (forall (i : I), f i) (Pi.semiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => s i)))) => R -> (forall (i : I), f i)) (RingHom.hasCoeToFun.{u3, max u1 u2} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{max u1 u2} (forall (i : I), f i) (Pi.semiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => s i)))) (algebraMap.{u3, max u1 u2} R (forall (i : I), f i) r (Pi.semiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => s i)) (Pi.algebra.{u1, u2, u3} I R (fun (i : I) => f i) r (fun (i : I) => s i) (fun (i : I) => _inst_1 i))) a) (fun (i : I) => coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (RingHom.{u3, u2} R (f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{u2} (f i) (s i))) (fun (_x : RingHom.{u3, u2} R (f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{u2} (f i) (s i))) => R -> (f i)) (RingHom.hasCoeToFun.{u3, u2} R (f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{u2} (f i) (s i))) (algebraMap.{u3, u2} R (f i) r (s i) (_inst_1 i)) a)
but is expected to have type
  forall (I : Type.{u2}) {R : Type.{u1}} (f : I -> Type.{u3}) {r : CommSemiring.{u1} R} [s : forall (i : I), Semiring.{u3} (f i)] [_inst_1 : forall (i : I), Algebra.{u1, u3} R (f i) r (s i)] (a : R), Eq.{max (succ u2) (succ u3)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : R) => forall (i : I), f i) a) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u1, max (succ u2) (succ u3)} (RingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : R) => forall (i : I), f i) _x) (MulHomClass.toFunLike.{max (max u2 u3) u1, u1, max u2 u3} (RingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) R (forall (i : I), f i) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)))) (NonUnitalNonAssocSemiring.toMul.{max u2 u3} (forall (i : I), f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u2 u3) u1, u1, max u2 u3} (RingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) R (forall (i : I), f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u2 u3) u1, u1, max u2 u3} (RingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i))) (RingHom.instRingHomClassRingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i))))))) (algebraMap.{u1, max u2 u3} R (forall (i : I), f i) r (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)) (Pi.algebra.{u2, u3, u1} I R (fun (i : I) => f i) r (fun (i : I) => s i) (fun (i : I) => _inst_1 i))) a) (fun (i : I) => FunLike.coe.{max (succ u3) (succ u1), succ u1, succ u3} (RingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : R) => f i) _x) (MulHomClass.toFunLike.{max u3 u1, u1, u3} (RingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) R (f i) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)))) (NonUnitalNonAssocSemiring.toMul.{u3} (f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} (f i) (Semiring.toNonAssocSemiring.{u3} (f i) (s i)))) (NonUnitalRingHomClass.toMulHomClass.{max u3 u1, u1, u3} (RingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) R (f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} (f i) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) (RingHomClass.toNonUnitalRingHomClass.{max u3 u1, u1, u3} (RingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i)) (RingHom.instRingHomClassRingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i)))))) (algebraMap.{u1, u3} R (f i) r (s i) (_inst_1 i)) a)
Case conversion may be inaccurate. Consider using '#align pi.algebra_map_def Pi.algebraMap_defₓ'. -/
theorem algebraMap_def {r : CommSemiring R} [s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)]
    (a : R) : algebraMap R (∀ i, f i) a = fun i => algebraMap R (f i) a :=
  rfl
#align pi.algebra_map_def Pi.algebraMap_def

/- warning: pi.algebra_map_apply -> Pi.algebraMap_apply is a dubious translation:
lean 3 declaration is
  forall (I : Type.{u1}) {R : Type.{u3}} (f : I -> Type.{u2}) {r : CommSemiring.{u3} R} [s : forall (i : I), Semiring.{u2} (f i)] [_inst_1 : forall (i : I), Algebra.{u3, u2} R (f i) r (s i)] (a : R) (i : I), Eq.{succ u2} (f i) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ u3) (succ (max u1 u2))} (RingHom.{u3, max u1 u2} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{max u1 u2} (forall (i : I), f i) (Pi.semiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => s i)))) (fun (_x : RingHom.{u3, max u1 u2} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{max u1 u2} (forall (i : I), f i) (Pi.semiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => s i)))) => R -> (forall (i : I), f i)) (RingHom.hasCoeToFun.{u3, max u1 u2} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{max u1 u2} (forall (i : I), f i) (Pi.semiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => s i)))) (algebraMap.{u3, max u1 u2} R (forall (i : I), f i) r (Pi.semiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => s i)) (Pi.algebra.{u1, u2, u3} I R (fun (i : I) => f i) r (fun (i : I) => s i) (fun (i : I) => _inst_1 i))) a i) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (RingHom.{u3, u2} R (f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{u2} (f i) (s i))) (fun (_x : RingHom.{u3, u2} R (f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{u2} (f i) (s i))) => R -> (f i)) (RingHom.hasCoeToFun.{u3, u2} R (f i) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R r)) (Semiring.toNonAssocSemiring.{u2} (f i) (s i))) (algebraMap.{u3, u2} R (f i) r (s i) (_inst_1 i)) a)
but is expected to have type
  forall (I : Type.{u2}) {R : Type.{u1}} (f : I -> Type.{u3}) {r : CommSemiring.{u1} R} [s : forall (i : I), Semiring.{u3} (f i)] [_inst_1 : forall (i : I), Algebra.{u1, u3} R (f i) r (s i)] (a : R) (i : I), Eq.{succ u3} (f i) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u1, max (succ u2) (succ u3)} (RingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : R) => forall (i : I), f i) _x) (MulHomClass.toFunLike.{max (max u2 u3) u1, u1, max u2 u3} (RingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) R (forall (i : I), f i) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)))) (NonUnitalNonAssocSemiring.toMul.{max u2 u3} (forall (i : I), f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u2 u3) u1, u1, max u2 u3} (RingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) R (forall (i : I), f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u2 u3) u1, u1, max u2 u3} (RingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)))) R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i))) (RingHom.instRingHomClassRingHom.{u1, max u2 u3} R (forall (i : I), f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{max u2 u3} (forall (i : I), f i) (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i))))))) (algebraMap.{u1, max u2 u3} R (forall (i : I), f i) r (Pi.semiring.{u2, u3} I (fun (i : I) => f i) (fun (i : I) => s i)) (Pi.algebra.{u2, u3, u1} I R (fun (i : I) => f i) r (fun (i : I) => s i) (fun (i : I) => _inst_1 i))) a i) (FunLike.coe.{max (succ u3) (succ u1), succ u1, succ u3} (RingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : R) => f i) _x) (MulHomClass.toFunLike.{max u3 u1, u1, u3} (RingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) R (f i) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)))) (NonUnitalNonAssocSemiring.toMul.{u3} (f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} (f i) (Semiring.toNonAssocSemiring.{u3} (f i) (s i)))) (NonUnitalRingHomClass.toMulHomClass.{max u3 u1, u1, u3} (RingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) R (f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} (f i) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) (RingHomClass.toNonUnitalRingHomClass.{max u3 u1, u1, u3} (RingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i))) R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i)) (RingHom.instRingHomClassRingHom.{u1, u3} R (f i) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R r)) (Semiring.toNonAssocSemiring.{u3} (f i) (s i)))))) (algebraMap.{u1, u3} R (f i) r (s i) (_inst_1 i)) a)
Case conversion may be inaccurate. Consider using '#align pi.algebra_map_apply Pi.algebraMap_applyₓ'. -/
@[simp]
theorem algebraMap_apply {r : CommSemiring R} [s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)]
    (a : R) (i : I) : algebraMap R (∀ i, f i) a i = algebraMap R (f i) a :=
  rfl
#align pi.algebra_map_apply Pi.algebraMap_apply

-- One could also build a `Π i, R i`-algebra structure on `Π i, A i`,
-- when each `A i` is an `R i`-algebra, although I'm not sure that it's useful.
variable {I} (R) (f)

#print Pi.evalAlgHom /-
/-- `function.eval` as an `alg_hom`. The name matches `pi.eval_ring_hom`, `pi.eval_monoid_hom`,
etc. -/
@[simps]
def evalAlgHom {r : CommSemiring R} [∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] (i : I) :
    (∀ i, f i) →ₐ[R] f i :=
  { Pi.evalRingHom f i with
    toFun := fun f => f i
    commutes' := fun r => rfl }
#align pi.eval_alg_hom Pi.evalAlgHom
-/

variable (A B : Type _) [CommSemiring R] [Semiring B] [Algebra R B]

#print Pi.constAlgHom /-
/-- `function.const` as an `alg_hom`. The name matches `pi.const_ring_hom`, `pi.const_monoid_hom`,
etc. -/
@[simps]
def constAlgHom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun r => rfl }
#align pi.const_alg_hom Pi.constAlgHom
-/

/- warning: pi.const_ring_hom_eq_algebra_map -> Pi.constRingHom_eq_algebraMap is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R], Eq.{max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} R (A -> R) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Pi.nonAssocSemiring.{u2, u1} A (fun (ᾰ : A) => R) (fun (i : A) => Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Pi.constRingHom.{u2, u1} A R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (algebraMap.{u1, max u2 u1} R (A -> R) _inst_1 (Pi.semiring.{u2, u1} A (fun (ᾰ : A) => R) (fun (i : A) => CommSemiring.toSemiring.{u1} R _inst_1)) (Pi.algebra.{u2, u1, u1} A R (fun (ᾰ : A) => R) _inst_1 (fun (i : A) => CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : A) => Algebra.id.{u1} R _inst_1)))
but is expected to have type
  forall (R : Type.{u2}) (A : Type.{u1}) [_inst_1 : CommSemiring.{u2} R], Eq.{max (succ u2) (succ u1)} (RingHom.{u2, max u1 u2} R (A -> R) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Pi.nonAssocSemiring.{u1, u2} A (fun (ᾰ : A) => R) (fun (i : A) => Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Pi.constRingHom.{u1, u2} A R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (algebraMap.{u2, max u2 u1} R (A -> R) _inst_1 (Pi.semiring.{u1, u2} A (fun (ᾰ : A) => R) (fun (i : A) => CommSemiring.toSemiring.{u2} R _inst_1)) (Pi.algebra.{u1, u2, u2} A R (fun (ᾰ : A) => R) _inst_1 (fun (i : A) => CommSemiring.toSemiring.{u2} R _inst_1) (fun (i : A) => Algebra.id.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align pi.const_ring_hom_eq_algebra_map Pi.constRingHom_eq_algebraMapₓ'. -/
/-- When `R` is commutative and permits an `algebra_map`, `pi.const_ring_hom` is equal to that
map. -/
@[simp]
theorem constRingHom_eq_algebraMap : constRingHom A R = algebraMap R (A → R) :=
  rfl
#align pi.const_ring_hom_eq_algebra_map Pi.constRingHom_eq_algebraMap

/- warning: pi.const_alg_hom_eq_algebra_of_id -> Pi.constAlgHom_eq_algebra_ofId is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R], Eq.{max (succ u1) (succ (max u2 u1))} (AlgHom.{u1, u1, max u2 u1} R R (A -> R) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Pi.semiring.{u2, u1} A (fun (ᾰ : A) => R) (fun (i : A) => CommSemiring.toSemiring.{u1} R _inst_1)) (Algebra.id.{u1} R _inst_1) (Pi.algebra.{u2, u1, u1} A R (fun (ᾰ : A) => R) _inst_1 (fun (i : A) => CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : A) => Algebra.id.{u1} R _inst_1))) (Pi.constAlgHom.{u1, u2, u1} R A R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Algebra.ofId.{u1, max u2 u1} R (A -> R) _inst_1 (Pi.semiring.{u2, u1} A (fun (ᾰ : A) => R) (fun (i : A) => CommSemiring.toSemiring.{u1} R _inst_1)) (Pi.algebra.{u2, u1, u1} A R (fun (ᾰ : A) => R) _inst_1 (fun (i : A) => CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : A) => Algebra.id.{u1} R _inst_1)))
but is expected to have type
  forall (R : Type.{u2}) (A : Type.{u1}) [_inst_1 : CommSemiring.{u2} R], Eq.{max (succ u2) (succ u1)} (AlgHom.{u2, u2, max u1 u2} R R (A -> R) _inst_1 (CommSemiring.toSemiring.{u2} R _inst_1) (Pi.semiring.{u1, u2} A (fun (ᾰ : A) => R) (fun (i : A) => CommSemiring.toSemiring.{u2} R _inst_1)) (Algebra.id.{u2} R _inst_1) (Pi.algebra.{u1, u2, u2} A R (fun (ᾰ : A) => R) _inst_1 (fun (i : A) => CommSemiring.toSemiring.{u2} R _inst_1) (fun (i : A) => Algebra.id.{u2} R _inst_1))) (Pi.constAlgHom.{u2, u1, u2} R A R _inst_1 (CommSemiring.toSemiring.{u2} R _inst_1) (Algebra.id.{u2} R _inst_1)) (Algebra.ofId.{u2, max u2 u1} R (A -> R) _inst_1 (Pi.semiring.{u1, u2} A (fun (ᾰ : A) => R) (fun (i : A) => CommSemiring.toSemiring.{u2} R _inst_1)) (Pi.algebra.{u1, u2, u2} A R (fun (ᾰ : A) => R) _inst_1 (fun (i : A) => CommSemiring.toSemiring.{u2} R _inst_1) (fun (i : A) => Algebra.id.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align pi.const_alg_hom_eq_algebra_of_id Pi.constAlgHom_eq_algebra_ofIdₓ'. -/
@[simp]
theorem constAlgHom_eq_algebra_ofId : constAlgHom R A R = Algebra.ofId R (A → R) :=
  rfl
#align pi.const_alg_hom_eq_algebra_of_id Pi.constAlgHom_eq_algebra_ofId

end Pi

#print Function.algebra /-
/-- A special case of `pi.algebra` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this, -/
instance Function.algebra {R : Type _} (I : Type _) (A : Type _) [CommSemiring R] [Semiring A]
    [Algebra R A] : Algebra R (I → A) :=
  Pi.algebra _ _
#align function.algebra Function.algebra
-/

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {I : Type _}

variable [CommSemiring R] [Semiring A] [Semiring B]

variable [Algebra R A] [Algebra R B]

#print AlgHom.compLeft /-
/-- `R`-algebra homomorphism between the function spaces `I → A` and `I → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps]
protected def compLeft (f : A →ₐ[R] B) (I : Type _) : (I → A) →ₐ[R] I → B :=
  { f.toRingHom.compLeft I with
    toFun := fun h => f ∘ h
    commutes' := fun c => by
      ext
      exact f.commutes' c }
#align alg_hom.comp_left AlgHom.compLeft
-/

end AlgHom

namespace AlgEquiv

#print AlgEquiv.piCongrRight /-
/-- A family of algebra equivalences `Π j, (A₁ j ≃ₐ A₂ j)` generates a
multiplicative equivalence between `Π j, A₁ j` and `Π j, A₂ j`.

This is the `alg_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`alg_equiv.arrow_congr`.
-/
@[simps apply]
def piCongrRight {R ι : Type _} {A₁ A₂ : ι → Type _} [CommSemiring R] [∀ i, Semiring (A₁ i)]
    [∀ i, Semiring (A₂ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (∀ i, A₁ i) ≃ₐ[R] ∀ i, A₂ i :=
  {
    @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i =>
      (e i).toRingEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j)
    commutes' := fun r => by
      ext i
      simp }
#align alg_equiv.Pi_congr_right AlgEquiv.piCongrRight
-/

/- warning: alg_equiv.Pi_congr_right_refl -> AlgEquiv.piCongrRight_refl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} {A : ι -> Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : forall (i : ι), Semiring.{u3} (A i)] [_inst_3 : forall (i : ι), Algebra.{u1, u3} R (A i) _inst_1 (_inst_2 i)], Eq.{succ (max u2 u3)} (AlgEquiv.{u1, max u2 u3, max u2 u3} R (forall (i : ι), A i) (forall (i : ι), A i) _inst_1 (Pi.semiring.{u2, u3} ι (fun (i : ι) => A i) (fun (i : ι) => _inst_2 i)) (Pi.semiring.{u2, u3} ι (fun (i : ι) => A i) (fun (i : ι) => _inst_2 i)) (Pi.algebra.{u2, u3, u1} ι R (fun (i : ι) => A i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Pi.algebra.{u2, u3, u1} ι R (fun (i : ι) => A i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (AlgEquiv.piCongrRight.{u1, u2, u3, u3} R ι (fun (i : ι) => A i) (fun (i : ι) => A i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => AlgEquiv.refl.{u1, u3} R (A i) _inst_1 (_inst_2 i) (_inst_3 i))) (AlgEquiv.refl.{u1, max u2 u3} R (forall (i : ι), A i) _inst_1 (Pi.semiring.{u2, u3} ι (fun (i : ι) => A i) (fun (i : ι) => _inst_2 i)) (Pi.algebra.{u2, u3, u1} ι R (fun (i : ι) => A i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))
but is expected to have type
  forall {R : Type.{u3}} {ι : Type.{u2}} {A : ι -> Type.{u1}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : forall (i : ι), Semiring.{u1} (A i)] [_inst_3 : forall (i : ι), Algebra.{u3, u1} R (A i) _inst_1 (_inst_2 i)], Eq.{max (succ u2) (succ u1)} (AlgEquiv.{u3, max u2 u1, max u2 u1} R (forall (i : ι), A i) (forall (i : ι), A i) _inst_1 (Pi.semiring.{u2, u1} ι (fun (i : ι) => A i) (fun (i : ι) => _inst_2 i)) (Pi.semiring.{u2, u1} ι (fun (i : ι) => A i) (fun (i : ι) => _inst_2 i)) (Pi.algebra.{u2, u1, u3} ι R (fun (i : ι) => A i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Pi.algebra.{u2, u1, u3} ι R (fun (i : ι) => A i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (AlgEquiv.piCongrRight.{u3, u2, u1, u1} R ι (fun (i : ι) => A i) (fun (i : ι) => A i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => AlgEquiv.refl.{u3, u1} R (A i) _inst_1 (_inst_2 i) (_inst_3 i))) (AlgEquiv.refl.{u3, max u2 u1} R (forall (i : ι), A i) _inst_1 (Pi.semiring.{u2, u1} ι (fun (i : ι) => A i) (fun (i : ι) => _inst_2 i)) (Pi.algebra.{u2, u1, u3} ι R (fun (i : ι) => A i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))
Case conversion may be inaccurate. Consider using '#align alg_equiv.Pi_congr_right_refl AlgEquiv.piCongrRight_reflₓ'. -/
@[simp]
theorem piCongrRight_refl {R ι : Type _} {A : ι → Type _} [CommSemiring R] [∀ i, Semiring (A i)]
    [∀ i, Algebra R (A i)] :
    (piCongrRight fun i => (AlgEquiv.refl : A i ≃ₐ[R] A i)) = AlgEquiv.refl :=
  rfl
#align alg_equiv.Pi_congr_right_refl AlgEquiv.piCongrRight_refl

/- warning: alg_equiv.Pi_congr_right_symm -> AlgEquiv.piCongrRight_symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} {A₁ : ι -> Type.{u3}} {A₂ : ι -> Type.{u4}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : forall (i : ι), Semiring.{u3} (A₁ i)] [_inst_3 : forall (i : ι), Semiring.{u4} (A₂ i)] [_inst_4 : forall (i : ι), Algebra.{u1, u3} R (A₁ i) _inst_1 (_inst_2 i)] [_inst_5 : forall (i : ι), Algebra.{u1, u4} R (A₂ i) _inst_1 (_inst_3 i)] (e : forall (i : ι), AlgEquiv.{u1, u3, u4} R (A₁ i) (A₂ i) _inst_1 (_inst_2 i) (_inst_3 i) (_inst_4 i) (_inst_5 i)), Eq.{max (succ (max u2 u4)) (succ (max u2 u3))} (AlgEquiv.{u1, max u2 u4, max u2 u3} R (forall (i : ι), A₂ i) (forall (i : ι), A₁ i) _inst_1 (Pi.semiring.{u2, u4} ι (fun (i : ι) => A₂ i) (fun (i : ι) => _inst_3 i)) (Pi.semiring.{u2, u3} ι (fun (i : ι) => A₁ i) (fun (i : ι) => _inst_2 i)) (Pi.algebra.{u2, u4, u1} ι R (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_5 i)) (Pi.algebra.{u2, u3, u1} ι R (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_4 i))) (AlgEquiv.symm.{u1, max u2 u3, max u2 u4} R (forall (i : ι), A₁ i) (forall (i : ι), A₂ i) _inst_1 (Pi.semiring.{u2, u3} ι (fun (i : ι) => A₁ i) (fun (i : ι) => _inst_2 i)) (Pi.semiring.{u2, u4} ι (fun (i : ι) => A₂ i) (fun (i : ι) => _inst_3 i)) (Pi.algebra.{u2, u3, u1} ι R (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_4 i)) (Pi.algebra.{u2, u4, u1} ι R (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_5 i)) (AlgEquiv.piCongrRight.{u1, u2, u3, u4} R ι (fun (i : ι) => A₁ i) (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) e)) (AlgEquiv.piCongrRight.{u1, u2, u4, u3} R ι (fun (i : ι) => A₂ i) (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => AlgEquiv.symm.{u1, u3, u4} R (A₁ i) (A₂ i) _inst_1 (_inst_2 i) (_inst_3 i) (_inst_4 i) (_inst_5 i) (e i)))
but is expected to have type
  forall {R : Type.{u4}} {ι : Type.{u3}} {A₁ : ι -> Type.{u2}} {A₂ : ι -> Type.{u1}} [_inst_1 : CommSemiring.{u4} R] [_inst_2 : forall (i : ι), Semiring.{u2} (A₁ i)] [_inst_3 : forall (i : ι), Semiring.{u1} (A₂ i)] [_inst_4 : forall (i : ι), Algebra.{u4, u2} R (A₁ i) _inst_1 (_inst_2 i)] [_inst_5 : forall (i : ι), Algebra.{u4, u1} R (A₂ i) _inst_1 (_inst_3 i)] (e : forall (i : ι), AlgEquiv.{u4, u2, u1} R (A₁ i) (A₂ i) _inst_1 (_inst_2 i) (_inst_3 i) (_inst_4 i) (_inst_5 i)), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (AlgEquiv.{u4, max u3 u1, max u3 u2} R (forall (i : ι), A₂ i) (forall (i : ι), A₁ i) _inst_1 (Pi.semiring.{u3, u1} ι (fun (i : ι) => A₂ i) (fun (i : ι) => _inst_3 i)) (Pi.semiring.{u3, u2} ι (fun (i : ι) => A₁ i) (fun (i : ι) => _inst_2 i)) (Pi.algebra.{u3, u1, u4} ι R (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_5 i)) (Pi.algebra.{u3, u2, u4} ι R (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_4 i))) (AlgEquiv.symm.{u4, max u3 u2, max u3 u1} R (forall (i : ι), A₁ i) (forall (i : ι), A₂ i) _inst_1 (Pi.semiring.{u3, u2} ι (fun (i : ι) => A₁ i) (fun (i : ι) => _inst_2 i)) (Pi.semiring.{u3, u1} ι (fun (i : ι) => A₂ i) (fun (i : ι) => _inst_3 i)) (Pi.algebra.{u3, u2, u4} ι R (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_4 i)) (Pi.algebra.{u3, u1, u4} ι R (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_5 i)) (AlgEquiv.piCongrRight.{u4, u3, u2, u1} R ι (fun (i : ι) => A₁ i) (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) e)) (AlgEquiv.piCongrRight.{u4, u3, u1, u2} R ι (fun (i : ι) => A₂ i) (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => AlgEquiv.symm.{u4, u2, u1} R (A₁ i) (A₂ i) _inst_1 (_inst_2 i) (_inst_3 i) (_inst_4 i) (_inst_5 i) (e i)))
Case conversion may be inaccurate. Consider using '#align alg_equiv.Pi_congr_right_symm AlgEquiv.piCongrRight_symmₓ'. -/
@[simp]
theorem piCongrRight_symm {R ι : Type _} {A₁ A₂ : ι → Type _} [CommSemiring R]
    [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl
#align alg_equiv.Pi_congr_right_symm AlgEquiv.piCongrRight_symm

/- warning: alg_equiv.Pi_congr_right_trans -> AlgEquiv.piCongrRight_trans is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} {A₁ : ι -> Type.{u3}} {A₂ : ι -> Type.{u4}} {A₃ : ι -> Type.{u5}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : forall (i : ι), Semiring.{u3} (A₁ i)] [_inst_3 : forall (i : ι), Semiring.{u4} (A₂ i)] [_inst_4 : forall (i : ι), Semiring.{u5} (A₃ i)] [_inst_5 : forall (i : ι), Algebra.{u1, u3} R (A₁ i) _inst_1 (_inst_2 i)] [_inst_6 : forall (i : ι), Algebra.{u1, u4} R (A₂ i) _inst_1 (_inst_3 i)] [_inst_7 : forall (i : ι), Algebra.{u1, u5} R (A₃ i) _inst_1 (_inst_4 i)] (e₁ : forall (i : ι), AlgEquiv.{u1, u3, u4} R (A₁ i) (A₂ i) _inst_1 (_inst_2 i) (_inst_3 i) (_inst_5 i) (_inst_6 i)) (e₂ : forall (i : ι), AlgEquiv.{u1, u4, u5} R (A₂ i) (A₃ i) _inst_1 (_inst_3 i) (_inst_4 i) (_inst_6 i) (_inst_7 i)), Eq.{max (succ (max u2 u3)) (succ (max u2 u5))} (AlgEquiv.{u1, max u2 u3, max u2 u5} R (forall (i : ι), A₁ i) (forall (i : ι), A₃ i) _inst_1 (Pi.semiring.{u2, u3} ι (fun (i : ι) => A₁ i) (fun (i : ι) => _inst_2 i)) (Pi.semiring.{u2, u5} ι (fun (i : ι) => A₃ i) (fun (i : ι) => _inst_4 i)) (Pi.algebra.{u2, u3, u1} ι R (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_5 i)) (Pi.algebra.{u2, u5, u1} ι R (fun (i : ι) => A₃ i) _inst_1 (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_7 i))) (AlgEquiv.trans.{u1, max u2 u3, max u2 u4, max u2 u5} R (forall (i : ι), A₁ i) (forall (i : ι), A₂ i) (forall (i : ι), A₃ i) _inst_1 (Pi.semiring.{u2, u3} ι (fun (i : ι) => A₁ i) (fun (i : ι) => _inst_2 i)) (Pi.semiring.{u2, u4} ι (fun (i : ι) => A₂ i) (fun (i : ι) => _inst_3 i)) (Pi.semiring.{u2, u5} ι (fun (i : ι) => A₃ i) (fun (i : ι) => _inst_4 i)) (Pi.algebra.{u2, u3, u1} ι R (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_5 i)) (Pi.algebra.{u2, u4, u1} ι R (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_6 i)) (Pi.algebra.{u2, u5, u1} ι R (fun (i : ι) => A₃ i) _inst_1 (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_7 i)) (AlgEquiv.piCongrRight.{u1, u2, u3, u4} R ι (fun (i : ι) => A₁ i) (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_6 i) e₁) (AlgEquiv.piCongrRight.{u1, u2, u4, u5} R ι (fun (i : ι) => A₂ i) (fun (i : ι) => A₃ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) e₂)) (AlgEquiv.piCongrRight.{u1, u2, u3, u5} R ι (fun (i : ι) => A₁ i) (fun (i : ι) => A₃ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => AlgEquiv.trans.{u1, u3, u4, u5} R (A₁ i) (A₂ i) (A₃ i) _inst_1 (_inst_2 i) (_inst_3 i) (_inst_4 i) (_inst_5 i) (_inst_6 i) (_inst_7 i) (e₁ i) (e₂ i)))
but is expected to have type
  forall {R : Type.{u5}} {ι : Type.{u4}} {A₁ : ι -> Type.{u3}} {A₂ : ι -> Type.{u2}} {A₃ : ι -> Type.{u1}} [_inst_1 : CommSemiring.{u5} R] [_inst_2 : forall (i : ι), Semiring.{u3} (A₁ i)] [_inst_3 : forall (i : ι), Semiring.{u2} (A₂ i)] [_inst_4 : forall (i : ι), Semiring.{u1} (A₃ i)] [_inst_5 : forall (i : ι), Algebra.{u5, u3} R (A₁ i) _inst_1 (_inst_2 i)] [_inst_6 : forall (i : ι), Algebra.{u5, u2} R (A₂ i) _inst_1 (_inst_3 i)] [_inst_7 : forall (i : ι), Algebra.{u5, u1} R (A₃ i) _inst_1 (_inst_4 i)] (e₁ : forall (i : ι), AlgEquiv.{u5, u3, u2} R (A₁ i) (A₂ i) _inst_1 (_inst_2 i) (_inst_3 i) (_inst_5 i) (_inst_6 i)) (e₂ : forall (i : ι), AlgEquiv.{u5, u2, u1} R (A₂ i) (A₃ i) _inst_1 (_inst_3 i) (_inst_4 i) (_inst_6 i) (_inst_7 i)), Eq.{max (max (succ u4) (succ u3)) (succ u1)} (AlgEquiv.{u5, max u4 u3, max u4 u1} R (forall (i : ι), A₁ i) (forall (i : ι), A₃ i) _inst_1 (Pi.semiring.{u4, u3} ι (fun (i : ι) => A₁ i) (fun (i : ι) => _inst_2 i)) (Pi.semiring.{u4, u1} ι (fun (i : ι) => A₃ i) (fun (i : ι) => _inst_4 i)) (Pi.algebra.{u4, u3, u5} ι R (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_5 i)) (Pi.algebra.{u4, u1, u5} ι R (fun (i : ι) => A₃ i) _inst_1 (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_7 i))) (AlgEquiv.trans.{u5, max u4 u3, max u4 u2, max u4 u1} R (forall (i : ι), A₁ i) (forall (i : ι), A₂ i) (forall (i : ι), A₃ i) _inst_1 (Pi.semiring.{u4, u3} ι (fun (i : ι) => A₁ i) (fun (i : ι) => _inst_2 i)) (Pi.semiring.{u4, u2} ι (fun (i : ι) => A₂ i) (fun (i : ι) => _inst_3 i)) (Pi.semiring.{u4, u1} ι (fun (i : ι) => A₃ i) (fun (i : ι) => _inst_4 i)) (Pi.algebra.{u4, u3, u5} ι R (fun (i : ι) => A₁ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_5 i)) (Pi.algebra.{u4, u2, u5} ι R (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_6 i)) (Pi.algebra.{u4, u1, u5} ι R (fun (i : ι) => A₃ i) _inst_1 (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_7 i)) (AlgEquiv.piCongrRight.{u5, u4, u3, u2} R ι (fun (i : ι) => A₁ i) (fun (i : ι) => A₂ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_6 i) e₁) (AlgEquiv.piCongrRight.{u5, u4, u2, u1} R ι (fun (i : ι) => A₂ i) (fun (i : ι) => A₃ i) _inst_1 (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) e₂)) (AlgEquiv.piCongrRight.{u5, u4, u3, u1} R ι (fun (i : ι) => A₁ i) (fun (i : ι) => A₃ i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => AlgEquiv.trans.{u5, u3, u2, u1} R (A₁ i) (A₂ i) (A₃ i) _inst_1 (_inst_2 i) (_inst_3 i) (_inst_4 i) (_inst_5 i) (_inst_6 i) (_inst_7 i) (e₁ i) (e₂ i)))
Case conversion may be inaccurate. Consider using '#align alg_equiv.Pi_congr_right_trans AlgEquiv.piCongrRight_transₓ'. -/
@[simp]
theorem piCongrRight_trans {R ι : Type _} {A₁ A₂ A₃ : ι → Type _} [CommSemiring R]
    [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)] [∀ i, Algebra R (A₁ i)]
    [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)] (e₁ : ∀ i, A₁ i ≃ₐ[R] A₂ i)
    (e₂ : ∀ i, A₂ i ≃ₐ[R] A₃ i) :
    (piCongrRight e₁).trans (piCongrRight e₂) = piCongrRight fun i => (e₁ i).trans (e₂ i) :=
  rfl
#align alg_equiv.Pi_congr_right_trans AlgEquiv.piCongrRight_trans

end AlgEquiv

