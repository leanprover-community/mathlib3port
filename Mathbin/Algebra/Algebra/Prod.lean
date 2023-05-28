/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.algebra.prod
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Hom

/-!
# The R-algebra structure on products of R-algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

## Main defintions

* `pi.algebra`
* `pi.eval_alg_hom`
* `pi.const_alg_hom`
-/


variable {R A B C : Type _}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

namespace Prod

variable (R A B)

open Algebra

/- warning: prod.algebra -> Prod.algebra is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) (B : Type.{u3}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4], Algebra.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4)
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) (B : Type.{u3}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4], Algebra.{u1, max u3 u2} R (Prod.{u2, u3} A B) _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_4)
Case conversion may be inaccurate. Consider using '#align prod.algebra Prod.algebraₓ'. -/
instance algebra : Algebra R (A × B) :=
  { Prod.module,
    RingHom.prod (algebraMap R A)
      (algebraMap R
        B) with
    commutes' := by
      rintro r ⟨a, b⟩
      dsimp
      rw [commutes r a, commutes r b]
    smul_def' := by
      rintro r ⟨a, b⟩
      dsimp
      rw [Algebra.smul_def r a, Algebra.smul_def r b] }
#align prod.algebra Prod.algebra

variable {R A B}

/- warning: prod.algebra_map_apply -> Prod.algebraMap_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4] (r : R), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} A B) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ u1) (succ (max u2 u3))} (RingHom.{u1, max u2 u3} R (Prod.{u2, u3} A B) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u2, u3} A B) (Prod.semiring.{u2, u3} A B _inst_2 _inst_4))) (fun (_x : RingHom.{u1, max u2 u3} R (Prod.{u2, u3} A B) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u2, u3} A B) (Prod.semiring.{u2, u3} A B _inst_2 _inst_4))) => R -> (Prod.{u2, u3} A B)) (RingHom.hasCoeToFun.{u1, max u2 u3} R (Prod.{u2, u3} A B) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u2, u3} A B) (Prod.semiring.{u2, u3} A B _inst_2 _inst_4))) (algebraMap.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) r) (Prod.mk.{u2, u3} A B (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3) r) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (RingHom.{u1, u3} R B (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} B _inst_4)) (fun (_x : RingHom.{u1, u3} R B (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} B _inst_4)) => R -> B) (RingHom.hasCoeToFun.{u1, u3} R B (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} B _inst_4)) (algebraMap.{u1, u3} R B _inst_1 _inst_4 _inst_5) r))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u3}} {B : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u1, u3} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u2} B] [_inst_5 : Algebra.{u1, u2} R B _inst_1 _inst_4] (r : R), Eq.{max (succ u3) (succ u2)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Prod.{u3, u2} A B) r) (FunLike.coe.{max (max (succ u1) (succ u3)) (succ u2), succ u1, max (succ u3) (succ u2)} (RingHom.{u1, max u2 u3} R (Prod.{u3, u2} A B) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u3, u2} A B) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Prod.{u3, u2} A B) _x) (MulHomClass.toFunLike.{max (max u1 u3) u2, u1, max u3 u2} (RingHom.{u1, max u2 u3} R (Prod.{u3, u2} A B) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u3, u2} A B) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4))) R (Prod.{u3, u2} A B) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{max u3 u2} (Prod.{u3, u2} A B) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (Prod.{u3, u2} A B) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u3, u2} A B) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4)))) (NonUnitalRingHomClass.toMulHomClass.{max (max u1 u3) u2, u1, max u3 u2} (RingHom.{u1, max u2 u3} R (Prod.{u3, u2} A B) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u3, u2} A B) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4))) R (Prod.{u3, u2} A B) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (Prod.{u3, u2} A B) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u3, u2} A B) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4))) (RingHomClass.toNonUnitalRingHomClass.{max (max u1 u3) u2, u1, max u3 u2} (RingHom.{u1, max u2 u3} R (Prod.{u3, u2} A B) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u3, u2} A B) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4))) R (Prod.{u3, u2} A B) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u3, u2} A B) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4)) (RingHom.instRingHomClassRingHom.{u1, max u3 u2} R (Prod.{u3, u2} A B) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u3} (Prod.{u3, u2} A B) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4)))))) (algebraMap.{u1, max u2 u3} R (Prod.{u3, u2} A B) _inst_1 (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) r) (Prod.mk.{u3, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) r) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => B) r) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (RingHom.{u1, u3} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} A _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (RingHom.{u1, u3} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} A _inst_2)) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} A _inst_2)) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} A _inst_2)) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} A _inst_2) (RingHom.instRingHomClassRingHom.{u1, u3} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} A _inst_2))))) (algebraMap.{u1, u3} R A _inst_1 _inst_2 _inst_3) r) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R B (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} B _inst_4)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => B) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R B (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} B _inst_4)) R B (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B _inst_4))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R B (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} B _inst_4)) R B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B _inst_4)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R B (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} B _inst_4)) R B (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} B _inst_4) (RingHom.instRingHomClassRingHom.{u1, u2} R B (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} B _inst_4))))) (algebraMap.{u1, u2} R B _inst_1 _inst_4 _inst_5) r))
Case conversion may be inaccurate. Consider using '#align prod.algebra_map_apply Prod.algebraMap_applyₓ'. -/
@[simp]
theorem algebraMap_apply (r : R) : algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r) :=
  rfl
#align prod.algebra_map_apply Prod.algebraMap_apply

end Prod

namespace AlgHom

variable (R A B)

/- warning: alg_hom.fst -> AlgHom.fst is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) (B : Type.{u3}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4], AlgHom.{u1, max u2 u3, u2} R (Prod.{u2, u3} A B) A _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) _inst_2 (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) _inst_3
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) (B : Type.{u3}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4], AlgHom.{u1, max u3 u2, u2} R (Prod.{u2, u3} A B) A _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_4) _inst_2 (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) _inst_3
Case conversion may be inaccurate. Consider using '#align alg_hom.fst AlgHom.fstₓ'. -/
/-- First projection as `alg_hom`. -/
def fst : A × B →ₐ[R] A :=
  { RingHom.fst A B with commutes' := fun r => rfl }
#align alg_hom.fst AlgHom.fst

/- warning: alg_hom.snd -> AlgHom.snd is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) (B : Type.{u3}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4], AlgHom.{u1, max u2 u3, u3} R (Prod.{u2, u3} A B) B _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) _inst_4 (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) _inst_5
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) (B : Type.{u3}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4], AlgHom.{u1, max u3 u2, u3} R (Prod.{u2, u3} A B) B _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_4) _inst_4 (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) _inst_5
Case conversion may be inaccurate. Consider using '#align alg_hom.snd AlgHom.sndₓ'. -/
/-- Second projection as `alg_hom`. -/
def snd : A × B →ₐ[R] B :=
  { RingHom.snd A B with commutes' := fun r => rfl }
#align alg_hom.snd AlgHom.snd

variable {R A B}

/- warning: alg_hom.prod -> AlgHom.prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {C : Type.{u4}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4] [_inst_6 : Semiring.{u4} C] [_inst_7 : Algebra.{u1, u4} R C _inst_1 _inst_6], (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) -> (AlgHom.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7) -> (AlgHom.{u1, u2, max u3 u4} R A (Prod.{u3, u4} B C) _inst_1 _inst_2 (Prod.semiring.{u3, u4} B C _inst_4 _inst_6) _inst_3 (Prod.algebra.{u1, u3, u4} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {C : Type.{u4}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4] [_inst_6 : Semiring.{u4} C] [_inst_7 : Algebra.{u1, u4} R C _inst_1 _inst_6], (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) -> (AlgHom.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7) -> (AlgHom.{u1, u2, max u4 u3} R A (Prod.{u3, u4} B C) _inst_1 _inst_2 (Prod.instSemiringProd.{u3, u4} B C _inst_4 _inst_6) _inst_3 (Prod.algebra.{u1, u3, u4} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7))
Case conversion may be inaccurate. Consider using '#align alg_hom.prod AlgHom.prodₓ'. -/
/-- The `pi.prod` of two morphisms is a morphism. -/
@[simps]
def prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : A →ₐ[R] B × C :=
  { f.toRingHom.Prod g.toRingHom with
    commutes' := fun r => by
      simp only [to_ring_hom_eq_coe, RingHom.toFun_eq_coe, RingHom.prod_apply, coe_to_ring_hom,
        commutes, Prod.algebraMap_apply] }
#align alg_hom.prod AlgHom.prod

/- warning: alg_hom.coe_prod -> AlgHom.coe_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_prod AlgHom.coe_prodₓ'. -/
theorem coe_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : ⇑(f.Prod g) = Pi.prod f g :=
  rfl
#align alg_hom.coe_prod AlgHom.coe_prod

/- warning: alg_hom.fst_prod -> AlgHom.fst_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {C : Type.{u4}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4] [_inst_6 : Semiring.{u4} C] [_inst_7 : Algebra.{u1, u4} R C _inst_1 _inst_6] (f : AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (g : AlgHom.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7), Eq.{max (succ u2) (succ u3)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (AlgHom.comp.{u1, u2, max u3 u4, u3} R A (Prod.{u3, u4} B C) B _inst_1 _inst_2 (Prod.semiring.{u3, u4} B C _inst_4 _inst_6) _inst_4 _inst_3 (Prod.algebra.{u1, u3, u4} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) _inst_5 (AlgHom.fst.{u1, u3, u4} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) (AlgHom.prod.{u1, u2, u3, u4} R A B C _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f g)) f
but is expected to have type
  forall {R : Type.{u4}} {A : Type.{u3}} {B : Type.{u2}} {C : Type.{u1}} [_inst_1 : CommSemiring.{u4} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u4, u3} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u2} B] [_inst_5 : Algebra.{u4, u2} R B _inst_1 _inst_4] [_inst_6 : Semiring.{u1} C] [_inst_7 : Algebra.{u4, u1} R C _inst_1 _inst_6] (f : AlgHom.{u4, u3, u2} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (g : AlgHom.{u4, u3, u1} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7), Eq.{max (succ u3) (succ u2)} (AlgHom.{u4, u3, u2} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (AlgHom.comp.{u4, u3, max u2 u1, u2} R A (Prod.{u2, u1} B C) B _inst_1 _inst_2 (Prod.instSemiringProd.{u2, u1} B C _inst_4 _inst_6) _inst_4 _inst_3 (Prod.algebra.{u4, u2, u1} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) _inst_5 (AlgHom.fst.{u4, u2, u1} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) (AlgHom.prod.{u4, u3, u2, u1} R A B C _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f g)) f
Case conversion may be inaccurate. Consider using '#align alg_hom.fst_prod AlgHom.fst_prodₓ'. -/
@[simp]
theorem fst_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (fst R B C).comp (prod f g) = f := by ext <;> rfl
#align alg_hom.fst_prod AlgHom.fst_prod

/- warning: alg_hom.snd_prod -> AlgHom.snd_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {C : Type.{u4}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4] [_inst_6 : Semiring.{u4} C] [_inst_7 : Algebra.{u1, u4} R C _inst_1 _inst_6] (f : AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (g : AlgHom.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7), Eq.{max (succ u2) (succ u4)} (AlgHom.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7) (AlgHom.comp.{u1, u2, max u3 u4, u4} R A (Prod.{u3, u4} B C) C _inst_1 _inst_2 (Prod.semiring.{u3, u4} B C _inst_4 _inst_6) _inst_6 _inst_3 (Prod.algebra.{u1, u3, u4} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) _inst_7 (AlgHom.snd.{u1, u3, u4} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) (AlgHom.prod.{u1, u2, u3, u4} R A B C _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f g)) g
but is expected to have type
  forall {R : Type.{u4}} {A : Type.{u3}} {B : Type.{u2}} {C : Type.{u1}} [_inst_1 : CommSemiring.{u4} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u4, u3} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u2} B] [_inst_5 : Algebra.{u4, u2} R B _inst_1 _inst_4] [_inst_6 : Semiring.{u1} C] [_inst_7 : Algebra.{u4, u1} R C _inst_1 _inst_6] (f : AlgHom.{u4, u3, u2} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (g : AlgHom.{u4, u3, u1} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7), Eq.{max (succ u3) (succ u1)} (AlgHom.{u4, u3, u1} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7) (AlgHom.comp.{u4, u3, max u2 u1, u1} R A (Prod.{u2, u1} B C) C _inst_1 _inst_2 (Prod.instSemiringProd.{u2, u1} B C _inst_4 _inst_6) _inst_6 _inst_3 (Prod.algebra.{u4, u2, u1} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) _inst_7 (AlgHom.snd.{u4, u2, u1} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) (AlgHom.prod.{u4, u3, u2, u1} R A B C _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f g)) g
Case conversion may be inaccurate. Consider using '#align alg_hom.snd_prod AlgHom.snd_prodₓ'. -/
@[simp]
theorem snd_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (snd R B C).comp (prod f g) = g := by ext <;> rfl
#align alg_hom.snd_prod AlgHom.snd_prod

/- warning: alg_hom.prod_fst_snd -> AlgHom.prod_fst_snd is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4], Eq.{succ (max u2 u3)} (AlgHom.{u1, max u2 u3, max u2 u3} R (Prod.{u2, u3} A B) (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (AlgHom.prod.{u1, max u2 u3, u2, u3} R (Prod.{u2, u3} A B) A B _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) _inst_2 _inst_3 _inst_4 _inst_5 (AlgHom.fst.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (AlgHom.snd.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (OfNat.ofNat.{max u2 u3} (AlgHom.{u1, max u2 u3, max u2 u3} R (Prod.{u2, u3} A B) (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) 1 (OfNat.mk.{max u2 u3} (AlgHom.{u1, max u2 u3, max u2 u3} R (Prod.{u2, u3} A B) (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) 1 (One.one.{max u2 u3} (AlgHom.{u1, max u2 u3, max u2 u3} R (Prod.{u2, u3} A B) (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (MulOneClass.toHasOne.{max u2 u3} (AlgHom.{u1, max u2 u3, max u2 u3} R (Prod.{u2, u3} A B) (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (Monoid.toMulOneClass.{max u2 u3} (AlgHom.{u1, max u2 u3, max u2 u3} R (Prod.{u2, u3} A B) (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (AlgHom.End.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_4) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)))))))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u3}} {B : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u1, u3} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u2} B] [_inst_5 : Algebra.{u1, u2} R B _inst_1 _inst_4], Eq.{max (succ u3) (succ u2)} (AlgHom.{u1, max u3 u2, max u2 u3} R (Prod.{u3, u2} A B) (Prod.{u3, u2} A B) _inst_1 (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (AlgHom.prod.{u1, max u3 u2, u3, u2} R (Prod.{u3, u2} A B) A B _inst_1 (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) _inst_2 _inst_3 _inst_4 _inst_5 (AlgHom.fst.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (AlgHom.snd.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (OfNat.ofNat.{max u3 u2} (AlgHom.{u1, max u3 u2, max u2 u3} R (Prod.{u3, u2} A B) (Prod.{u3, u2} A B) _inst_1 (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) 1 (One.toOfNat1.{max u3 u2} (AlgHom.{u1, max u3 u2, max u2 u3} R (Prod.{u3, u2} A B) (Prod.{u3, u2} A B) _inst_1 (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (Monoid.toOne.{max u3 u2} (AlgHom.{u1, max u3 u2, max u2 u3} R (Prod.{u3, u2} A B) (Prod.{u3, u2} A B) _inst_1 (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (AlgHom.End.{u1, max u3 u2} R (Prod.{u3, u2} A B) _inst_1 (Prod.instSemiringProd.{u3, u2} A B _inst_2 _inst_4) (Prod.algebra.{u1, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)))))
Case conversion may be inaccurate. Consider using '#align alg_hom.prod_fst_snd AlgHom.prod_fst_sndₓ'. -/
@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  FunLike.coe_injective Pi.prod_fst_snd
#align alg_hom.prod_fst_snd AlgHom.prod_fst_snd

/- warning: alg_hom.prod_equiv -> AlgHom.prodEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {C : Type.{u4}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4] [_inst_6 : Semiring.{u4} C] [_inst_7 : Algebra.{u1, u4} R C _inst_1 _inst_6], Equiv.{max (succ (max u2 u3)) (succ (max u2 u4)), max (succ u2) (succ (max u3 u4))} (Prod.{max u2 u3, max u2 u4} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (AlgHom.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7)) (AlgHom.{u1, u2, max u3 u4} R A (Prod.{u3, u4} B C) _inst_1 _inst_2 (Prod.semiring.{u3, u4} B C _inst_4 _inst_6) _inst_3 (Prod.algebra.{u1, u3, u4} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {C : Type.{u4}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Semiring.{u3} B] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_4] [_inst_6 : Semiring.{u4} C] [_inst_7 : Algebra.{u1, u4} R C _inst_1 _inst_6], Equiv.{max (succ (max u4 u2)) (succ (max u3 u2)), max (succ (max u4 u3)) (succ u2)} (Prod.{max u3 u2, max u4 u2} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (AlgHom.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_6 _inst_3 _inst_7)) (AlgHom.{u1, u2, max u4 u3} R A (Prod.{u3, u4} B C) _inst_1 _inst_2 (Prod.instSemiringProd.{u3, u4} B C _inst_4 _inst_6) _inst_3 (Prod.algebra.{u1, u3, u4} R B C _inst_1 _inst_4 _inst_5 _inst_6 _inst_7))
Case conversion may be inaccurate. Consider using '#align alg_hom.prod_equiv AlgHom.prodEquivₓ'. -/
/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →ₐ[R] B) × (A →ₐ[R] C) ≃ (A →ₐ[R] B × C)
    where
  toFun f := f.1.Prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
#align alg_hom.prod_equiv AlgHom.prodEquiv

end AlgHom

