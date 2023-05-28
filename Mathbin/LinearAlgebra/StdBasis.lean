/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module linear_algebra.std_basis
! leanprover-community/mathlib commit 13bce9a6b6c44f6b4c91ac1c1d2a816e2533d395
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basis
import Mathbin.LinearAlgebra.Basis
import Mathbin.LinearAlgebra.Pi

/-!
# The standard basis

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the standard basis `pi.basis (s : ∀ j, basis (ι j) R (M j))`,
which is the `Σ j, ι j`-indexed basis of `Π j, M j`. The basis vectors are given by
`pi.basis s ⟨j, i⟩ j' = linear_map.std_basis R M j' (s j) i = if j = j' then s i else 0`.

The standard basis on `R^η`, i.e. `η → R` is called `pi.basis_fun`.

To give a concrete example, `linear_map.std_basis R (λ (i : fin 3), R) i 1`
gives the `i`th unit basis vector in `R³`, and `pi.basis_fun R (fin 3)` proves
this is a basis over `fin 3 → R`.

## Main definitions

 - `linear_map.std_basis R M`: if `x` is a basis vector of `M i`, then
   `linear_map.std_basis R M i x` is the `i`th standard basis vector of `Π i, M i`.
 - `pi.basis s`: given a basis `s i` for each `M i`, the standard basis on `Π i, M i`
 - `pi.basis_fun R η`: the standard basis on `R^η`, i.e. `η → R`, given by
   `pi.basis_fun R η i j = if i = j then 1 else 0`.
 - `matrix.std_basis R n m`: the standard basis on `matrix n m R`, given by
   `matrix.std_basis R n m (i, j) i' j' = if (i, j) = (i', j') then 1 else 0`.

-/


open Function Submodule

open BigOperators

namespace LinearMap

variable (R : Type _) {ι : Type _} [Semiring R] (φ : ι → Type _) [∀ i, AddCommMonoid (φ i)]
  [∀ i, Module R (φ i)] [DecidableEq ι]

#print LinearMap.stdBasis /-
/-- The standard basis of the product of `φ`. -/
def stdBasis : ∀ i : ι, φ i →ₗ[R] ∀ i, φ i :=
  single
#align linear_map.std_basis LinearMap.stdBasis
-/

/- warning: linear_map.std_basis_apply -> LinearMap.stdBasis_apply is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u3}) [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} ι] (i : ι) (b : φ i), Eq.{max (succ u2) (succ u3)} (forall (i : ι), φ i) (coeFn.{max (succ u3) (succ (max u2 u3)), max (succ u3) (succ (max u2 u3))} (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) ((fun (i : ι) => _inst_2 i) i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => (fun (i : ι) => _inst_2 i) i)) ((fun (i : ι) => _inst_3 i) i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => (fun (i : ι) => _inst_2 i) i) (fun (i : ι) => (fun (i : ι) => _inst_3 i) i))) (fun (_x : LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) ((fun (i : ι) => _inst_2 i) i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => (fun (i : ι) => _inst_2 i) i)) ((fun (i : ι) => _inst_3 i) i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => (fun (i : ι) => _inst_2 i) i) (fun (i : ι) => (fun (i : ι) => _inst_3 i) i))) => (φ i) -> (forall (i : ι), φ i)) (LinearMap.hasCoeToFun.{u1, u1, u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 ((fun (i : ι) => _inst_2 i) i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => (fun (i : ι) => _inst_2 i) i)) ((fun (i : ι) => _inst_3 i) i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => (fun (i : ι) => _inst_2 i) i) (fun (i : ι) => (fun (i : ι) => _inst_3 i) i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.stdBasis.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) b) (Function.update.{succ u2, succ u3} ι (fun (i : ι) => φ i) (fun (a : ι) (b : ι) => _inst_4 a b) (OfNat.ofNat.{max u2 u3} (forall (a : ι), φ a) 0 (OfNat.mk.{max u2 u3} (forall (a : ι), φ a) 0 (Zero.zero.{max u2 u3} (forall (a : ι), φ a) (Pi.instZero.{u2, u3} ι (fun (a : ι) => φ a) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (φ i) (AddMonoid.toAddZeroClass.{u3} (φ i) (AddCommMonoid.toAddMonoid.{u3} (φ i) (_inst_2 i)))))))) i b)
but is expected to have type
  forall (R : Type.{u1}) {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u2}) [_inst_2 : forall (i : ι), AddCommMonoid.{u2} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u2} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u3} ι] (i : ι) (b : φ i), Eq.{max (succ u3) (succ u2)} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : φ i) => forall (i : ι), φ i) b) (FunLike.coe.{max (succ u3) (succ u2), succ u2, max (succ u3) (succ u2)} (LinearMap.{u1, u1, u2, max u3 u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (φ i) (fun (_x : φ i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : φ i) => forall (i : ι), φ i) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u2, max u3 u2} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.stdBasis.{u1, u3, u2} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) b) (Function.update.{succ u3, succ u2} ι (fun (i : ι) => φ i) (fun (a : ι) (b : ι) => _inst_4 a b) (OfNat.ofNat.{max u3 u2} (forall (a : ι), φ a) 0 (Zero.toOfNat0.{max u3 u2} (forall (a : ι), φ a) (Pi.instZero.{u3, u2} ι (fun (a : ι) => φ a) (fun (i : ι) => AddMonoid.toZero.{u2} (φ i) (AddCommMonoid.toAddMonoid.{u2} (φ i) (_inst_2 i)))))) i b)
Case conversion may be inaccurate. Consider using '#align linear_map.std_basis_apply LinearMap.stdBasis_applyₓ'. -/
theorem stdBasis_apply (i : ι) (b : φ i) : stdBasis R φ i b = update 0 i b :=
  rfl
#align linear_map.std_basis_apply LinearMap.stdBasis_apply

/- warning: linear_map.std_basis_apply' -> LinearMap.stdBasis_apply' is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_4 : DecidableEq.{succ u2} ι] (i : ι) (i' : ι), Eq.{succ u1} ((fun (_x : ι) => R) i') (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (LinearMap.{u1, u1, u1, max u2 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((fun (_x : ι) => R) i) (forall (i : ι), (fun (_x : ι) => R) i) ((fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (Pi.addCommMonoid.{u2, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i)) ((fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i) (Pi.module.{u2, u1, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) R _inst_1 (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (fun (i : ι) => (fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i))) (fun (_x : LinearMap.{u1, u1, u1, max u2 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((fun (_x : ι) => R) i) (forall (i : ι), (fun (_x : ι) => R) i) ((fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (Pi.addCommMonoid.{u2, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i)) ((fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i) (Pi.module.{u2, u1, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) R _inst_1 (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (fun (i : ι) => (fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i))) => R -> (forall (i : ι), (fun (_x : ι) => R) i)) (LinearMap.hasCoeToFun.{u1, u1, u1, max u2 u1} R R ((fun (_x : ι) => R) i) (forall (i : ι), (fun (_x : ι) => R) i) _inst_1 _inst_1 ((fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (Pi.addCommMonoid.{u2, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i)) ((fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i) (Pi.module.{u2, u1, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) R _inst_1 (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (fun (i : ι) => (fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.stdBasis.{u1, u2, u1} R ι _inst_1 (fun (_x : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) (fun (i : ι) => Semiring.toModule.{u1} R _inst_1) (fun (a : ι) (b : ι) => _inst_4 a b) i) (OfNat.ofNat.{u1} ((fun (_x : ι) => R) i) 1 (OfNat.mk.{u1} ((fun (_x : ι) => R) i) 1 (One.one.{u1} ((fun (_x : ι) => R) i) (AddMonoidWithOne.toOne.{u1} ((fun (_x : ι) => R) i) (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toAddCommMonoidWithOne.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))))))) i') (ite.{succ u1} ((fun (_x : ι) => R) i') (Eq.{succ u2} ι i i') (_inst_4 i i') (OfNat.ofNat.{u1} ((fun (_x : ι) => R) i') 1 (OfNat.mk.{u1} ((fun (_x : ι) => R) i') 1 (One.one.{u1} ((fun (_x : ι) => R) i') (AddMonoidWithOne.toOne.{u1} ((fun (_x : ι) => R) i') (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} ((fun (_x : ι) => R) i') (NonAssocSemiring.toAddCommMonoidWithOne.{u1} ((fun (_x : ι) => R) i') (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i') _inst_1))))))) (OfNat.ofNat.{u1} ((fun (_x : ι) => R) i') 0 (OfNat.mk.{u1} ((fun (_x : ι) => R) i') 0 (Zero.zero.{u1} ((fun (_x : ι) => R) i') (MulZeroClass.toHasZero.{u1} ((fun (_x : ι) => R) i') (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} ((fun (_x : ι) => R) i') (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i') (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i') _inst_1))))))))
but is expected to have type
  forall (R : Type.{u2}) {ι : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_4 : DecidableEq.{succ u1} ι] (i : ι) (i' : ι), Eq.{succ u2} R (FunLike.coe.{max (succ u2) (succ u1), succ u2, max (succ u2) (succ u1)} (LinearMap.{u2, u2, u2, max u1 u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) R (ι -> R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) _inst_1))) (Pi.addCommMonoid.{u1, u2} ι (fun (i : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) _inst_1)))) (Semiring.toModule.{u2} R _inst_1) (Pi.module.{u1, u2, u2} ι (fun (i : ι) => R) R _inst_1 (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) _inst_1))) (fun (i : ι) => Semiring.toModule.{u2} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : R) => ι -> R) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u2, max u2 u1} R R R (ι -> R) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) _inst_1))) (Pi.addCommMonoid.{u1, u2} ι (fun (i : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) _inst_1)))) (Semiring.toModule.{u2} R _inst_1) (Pi.module.{u1, u2, u2} ι (fun (i : ι) => R) R _inst_1 (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) _inst_1))) (fun (i : ι) => Semiring.toModule.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (LinearMap.stdBasis.{u2, u1, u2} R ι _inst_1 (fun (_x : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) _inst_1))) (fun (i : ι) => Semiring.toModule.{u2} R _inst_1) (fun (a : ι) (b : ι) => _inst_4 a b) i) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R (Semiring.toOne.{u2} R _inst_1))) i') (ite.{succ u2} R (Eq.{succ u1} ι i i') (_inst_4 i i') (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R (Semiring.toOne.{u2} R _inst_1))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align linear_map.std_basis_apply' LinearMap.stdBasis_apply'ₓ'. -/
@[simp]
theorem stdBasis_apply' (i i' : ι) : (stdBasis R (fun _x : ι => R) i) 1 i' = ite (i = i') 1 0 :=
  by
  rw [LinearMap.stdBasis_apply, Function.update_apply, Pi.zero_apply]
  congr 1; rw [eq_iff_iff, eq_comm]
#align linear_map.std_basis_apply' LinearMap.stdBasis_apply'

/- warning: linear_map.coe_std_basis -> LinearMap.coe_stdBasis is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u3}) [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} ι] (i : ι), Eq.{max (succ u3) (succ (max u2 u3))} ((φ i) -> (forall (i : ι), φ i)) (coeFn.{max (succ u3) (succ (max u2 u3)), max (succ u3) (succ (max u2 u3))} (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (fun (_x : LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) => (φ i) -> (forall (i : ι), φ i)) (LinearMap.hasCoeToFun.{u1, u1, u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.stdBasis.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i)) (Pi.single.{u2, u3} ι (fun (i : ι) => φ i) (fun (a : ι) (b : ι) => _inst_4 a b) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (φ i) (AddMonoid.toAddZeroClass.{u3} (φ i) (AddCommMonoid.toAddMonoid.{u3} (φ i) (_inst_2 i)))) i)
but is expected to have type
  forall (R : Type.{u1}) {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u2}) [_inst_2 : forall (i : ι), AddCommMonoid.{u2} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u2} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u3} ι] (i : ι), Eq.{max (succ u3) (succ u2)} (forall (ᾰ : φ i), (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : φ i) => forall (i : ι), φ i) ᾰ) (FunLike.coe.{max (succ u3) (succ u2), succ u2, max (succ u3) (succ u2)} (LinearMap.{u1, u1, u2, max u3 u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (φ i) (fun (_x : φ i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : φ i) => forall (i : ι), φ i) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u2, max u3 u2} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.stdBasis.{u1, u3, u2} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i)) (Pi.single.{u3, u2} ι φ (fun (a : ι) (b : ι) => _inst_4 a b) (fun (i : ι) => AddMonoid.toZero.{u2} (φ i) (AddCommMonoid.toAddMonoid.{u2} (φ i) (_inst_2 i))) i)
Case conversion may be inaccurate. Consider using '#align linear_map.coe_std_basis LinearMap.coe_stdBasisₓ'. -/
theorem coe_stdBasis (i : ι) : ⇑(stdBasis R φ i) = Pi.single i :=
  rfl
#align linear_map.coe_std_basis LinearMap.coe_stdBasis

/- warning: linear_map.std_basis_same -> LinearMap.stdBasis_same is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u3}) [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} ι] (i : ι) (b : φ i), Eq.{succ u3} (φ i) (coeFn.{max (succ u3) (succ (max u2 u3)), max (succ u3) (succ (max u2 u3))} (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) ((fun (i : ι) => _inst_2 i) i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => (fun (i : ι) => _inst_2 i) i)) ((fun (i : ι) => _inst_3 i) i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => (fun (i : ι) => _inst_2 i) i) (fun (i : ι) => (fun (i : ι) => _inst_3 i) i))) (fun (_x : LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) ((fun (i : ι) => _inst_2 i) i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => (fun (i : ι) => _inst_2 i) i)) ((fun (i : ι) => _inst_3 i) i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => (fun (i : ι) => _inst_2 i) i) (fun (i : ι) => (fun (i : ι) => _inst_3 i) i))) => (φ i) -> (forall (i : ι), φ i)) (LinearMap.hasCoeToFun.{u1, u1, u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 ((fun (i : ι) => _inst_2 i) i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => (fun (i : ι) => _inst_2 i) i)) ((fun (i : ι) => _inst_3 i) i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => (fun (i : ι) => _inst_2 i) i) (fun (i : ι) => (fun (i : ι) => _inst_3 i) i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.stdBasis.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) b i) b
but is expected to have type
  forall (R : Type.{u1}) {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u3}) [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} ι] (i : ι) (b : φ i), Eq.{succ u3} (φ i) (FunLike.coe.{max (succ u2) (succ u3), succ u3, max (succ u2) (succ u3)} (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (φ i) (fun (_x : φ i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : φ i) => forall (i : ι), φ i) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.stdBasis.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) b i) b
Case conversion may be inaccurate. Consider using '#align linear_map.std_basis_same LinearMap.stdBasis_sameₓ'. -/
@[simp]
theorem stdBasis_same (i : ι) (b : φ i) : stdBasis R φ i b i = b :=
  Pi.single_eq_same i b
#align linear_map.std_basis_same LinearMap.stdBasis_same

/- warning: linear_map.std_basis_ne -> LinearMap.stdBasis_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.std_basis_ne LinearMap.stdBasis_neₓ'. -/
theorem stdBasis_ne (i j : ι) (h : j ≠ i) (b : φ i) : stdBasis R φ i b j = 0 :=
  Pi.single_eq_of_ne h b
#align linear_map.std_basis_ne LinearMap.stdBasis_ne

/- warning: linear_map.std_basis_eq_pi_diag -> LinearMap.stdBasis_eq_pi_diag is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u3}) [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} ι] (i : ι), Eq.{max (succ u3) (succ (max u2 u3))} (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.stdBasis.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) (LinearMap.pi.{u1, u3, u2, u3} R (φ i) ι _inst_1 (_inst_2 i) (_inst_3 i) (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (LinearMap.diag.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i))
but is expected to have type
  forall (R : Type.{u1}) {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u2}) [_inst_2 : forall (i : ι), AddCommMonoid.{u2} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u2} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u3} ι] (i : ι), Eq.{max (succ u3) (succ u2)} (LinearMap.{u1, u1, u2, max u3 u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.stdBasis.{u1, u3, u2} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) (LinearMap.pi.{u1, u2, u3, u2} R (φ i) ι _inst_1 (_inst_2 i) (_inst_3 i) (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (LinearMap.diag.{u1, u3, u2} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i))
Case conversion may be inaccurate. Consider using '#align linear_map.std_basis_eq_pi_diag LinearMap.stdBasis_eq_pi_diagₓ'. -/
theorem stdBasis_eq_pi_diag (i : ι) : stdBasis R φ i = pi (diag i) :=
  by
  ext (x j)
  convert(update_apply 0 x i j _).symm
  rfl
#align linear_map.std_basis_eq_pi_diag LinearMap.stdBasis_eq_pi_diag

/- warning: linear_map.ker_std_basis -> LinearMap.ker_stdBasis is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u3}) [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} ι] (i : ι), Eq.{succ u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (LinearMap.ker.{u1, u1, u3, max u2 u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.semilinearMapClass.{u1, u1, u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.stdBasis.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i)) (Bot.bot.{u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Submodule.hasBot.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)))
but is expected to have type
  forall (R : Type.{u2}) {ι : Type.{u1}} [_inst_1 : Semiring.{u2} R] (φ : ι -> Type.{u3}) [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u1} ι] (i : ι), Eq.{succ u3} (Submodule.{u2, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (LinearMap.ker.{u2, u2, u3, max u1 u3, max u1 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u1, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u1, u3, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (LinearMap.{u2, u2, u3, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u1, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u1, u3, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.semilinearMapClass.{u2, u2, u3, max u1 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u1, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u1, u3, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (LinearMap.stdBasis.{u2, u1, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i)) (Bot.bot.{u3} (Submodule.{u2, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Submodule.instBotSubmodule.{u2, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)))
Case conversion may be inaccurate. Consider using '#align linear_map.ker_std_basis LinearMap.ker_stdBasisₓ'. -/
theorem ker_stdBasis (i : ι) : ker (stdBasis R φ i) = ⊥ :=
  ker_eq_bot_of_injective <| Pi.single_injective _ _
#align linear_map.ker_std_basis LinearMap.ker_stdBasis

/- warning: linear_map.proj_comp_std_basis -> LinearMap.proj_comp_stdBasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.proj_comp_std_basis LinearMap.proj_comp_stdBasisₓ'. -/
theorem proj_comp_stdBasis (i j : ι) : (proj i).comp (stdBasis R φ j) = diag j i := by
  rw [std_basis_eq_pi_diag, proj_pi]
#align linear_map.proj_comp_std_basis LinearMap.proj_comp_stdBasis

/- warning: linear_map.proj_std_basis_same -> LinearMap.proj_stdBasis_same is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.proj_std_basis_same LinearMap.proj_stdBasis_sameₓ'. -/
theorem proj_stdBasis_same (i : ι) : (proj i).comp (stdBasis R φ i) = id :=
  LinearMap.ext <| stdBasis_same R φ i
#align linear_map.proj_std_basis_same LinearMap.proj_stdBasis_same

/- warning: linear_map.proj_std_basis_ne -> LinearMap.proj_stdBasis_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.proj_std_basis_ne LinearMap.proj_stdBasis_neₓ'. -/
theorem proj_stdBasis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (stdBasis R φ j) = 0 :=
  LinearMap.ext <| stdBasis_ne R φ _ _ h
#align linear_map.proj_std_basis_ne LinearMap.proj_stdBasis_ne

/- warning: linear_map.supr_range_std_basis_le_infi_ker_proj -> LinearMap.iSup_range_stdBasis_le_iInf_ker_proj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.supr_range_std_basis_le_infi_ker_proj LinearMap.iSup_range_stdBasis_le_iInf_ker_projₓ'. -/
theorem iSup_range_stdBasis_le_iInf_ker_proj (I J : Set ι) (h : Disjoint I J) :
    (⨆ i ∈ I, range (stdBasis R φ i)) ≤ ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) :=
  by
  refine' iSup_le fun i => iSup_le fun hi => range_le_iff_comap.2 _
  simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_infi, mem_infi]
  rintro b - j hj
  rw [proj_std_basis_ne R φ j i, zero_apply]
  rintro rfl
  exact h.le_bot ⟨hi, hj⟩
#align linear_map.supr_range_std_basis_le_infi_ker_proj LinearMap.iSup_range_stdBasis_le_iInf_ker_proj

/- warning: linear_map.infi_ker_proj_le_supr_range_std_basis -> LinearMap.iInf_ker_proj_le_iSup_range_stdBasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.infi_ker_proj_le_supr_range_std_basis LinearMap.iInf_ker_proj_le_iSup_range_stdBasisₓ'. -/
theorem iInf_ker_proj_le_iSup_range_stdBasis {I : Finset ι} {J : Set ι} (hu : Set.univ ⊆ ↑I ∪ J) :
    (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i)) ≤ ⨆ i ∈ I, range (stdBasis R φ i) :=
  SetLike.le_def.2
    (by
      intro b hb
      simp only [mem_infi, mem_ker, proj_apply] at hb
      rw [←
        show (∑ i in I, std_basis R φ i (b i)) = b by
          ext i
          rw [Finset.sum_apply, ← std_basis_same R φ i (b i)]
          refine' Finset.sum_eq_single i (fun j hjI ne => std_basis_ne _ _ _ _ Ne.symm _) _
          intro hiI
          rw [std_basis_same]
          exact hb _ ((hu trivial).resolve_left hiI)]
      exact sum_mem_bsupr fun i hi => mem_range_self (std_basis R φ i) (b i))
#align linear_map.infi_ker_proj_le_supr_range_std_basis LinearMap.iInf_ker_proj_le_iSup_range_stdBasis

/- warning: linear_map.supr_range_std_basis_eq_infi_ker_proj -> LinearMap.iSup_range_stdBasis_eq_iInf_ker_proj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.supr_range_std_basis_eq_infi_ker_proj LinearMap.iSup_range_stdBasis_eq_iInf_ker_projₓ'. -/
theorem iSup_range_stdBasis_eq_iInf_ker_proj {I J : Set ι} (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) (hI : Set.Finite I) :
    (⨆ i ∈ I, range (stdBasis R φ i)) = ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) :=
  by
  refine' le_antisymm (supr_range_std_basis_le_infi_ker_proj _ _ _ _ hd) _
  have : Set.univ ⊆ ↑hI.to_finset ∪ J := by rwa [hI.coe_to_finset]
  refine' le_trans (infi_ker_proj_le_supr_range_std_basis R φ this) (iSup_mono fun i => _)
  rw [Set.Finite.mem_toFinset]
  exact le_rfl
#align linear_map.supr_range_std_basis_eq_infi_ker_proj LinearMap.iSup_range_stdBasis_eq_iInf_ker_proj

/- warning: linear_map.supr_range_std_basis -> LinearMap.iSup_range_stdBasis is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u3}) [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} ι] [_inst_5 : Finite.{succ u2} ι], Eq.{succ (max u2 u3)} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (iSup.{max u2 u3, succ u2} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (ConditionallyCompleteLattice.toHasSup.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.completeLattice.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))) ι (fun (i : ι) => LinearMap.range.{u1, u1, u3, max u2 u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.semilinearMapClass.{u1, u1, u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (RingHomSurjective.ids.{u1} R _inst_1) (LinearMap.stdBasis.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i))) (Top.top.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.hasTop.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))
but is expected to have type
  forall (R : Type.{u1}) {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] (φ : ι -> Type.{u2}) [_inst_2 : forall (i : ι), AddCommMonoid.{u2} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u2} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u3} ι] [_inst_5 : Finite.{succ u3} ι], Eq.{max (succ u3) (succ u2)} (Submodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (iSup.{max u3 u2, succ u3} (Submodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (ConditionallyCompleteLattice.toSupSet.{max u3 u2} (Submodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (CompleteLattice.toConditionallyCompleteLattice.{max u3 u2} (Submodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.completeLattice.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))) ι (fun (i : ι) => LinearMap.range.{u1, u1, u2, max u3 u2, max u3 u2} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u2, max u3 u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.semilinearMapClass.{u1, u1, u2, max u3 u2} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (RingHomSurjective.ids.{u1} R _inst_1) (LinearMap.stdBasis.{u1, u3, u2} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i))) (Top.top.{max u3 u2} (Submodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.instTopSubmodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u2, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))
Case conversion may be inaccurate. Consider using '#align linear_map.supr_range_std_basis LinearMap.iSup_range_stdBasisₓ'. -/
theorem iSup_range_stdBasis [Finite ι] : (⨆ i, range (stdBasis R φ i)) = ⊤ :=
  by
  cases nonempty_fintype ι
  convert top_unique (infi_emptyset.ge.trans <| infi_ker_proj_le_supr_range_std_basis R φ _)
  ·
    exact
      funext fun i =>
        ((@iSup_pos _ _ _ fun h => range <| std_basis R φ i) <| Finset.mem_univ i).symm
  · rw [Finset.coe_univ, Set.union_empty]
#align linear_map.supr_range_std_basis LinearMap.iSup_range_stdBasis

/- warning: linear_map.disjoint_std_basis_std_basis -> LinearMap.disjoint_stdBasis_stdBasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.disjoint_std_basis_std_basis LinearMap.disjoint_stdBasis_stdBasisₓ'. -/
theorem disjoint_stdBasis_stdBasis (I J : Set ι) (h : Disjoint I J) :
    Disjoint (⨆ i ∈ I, range (stdBasis R φ i)) (⨆ i ∈ J, range (stdBasis R φ i)) :=
  by
  refine'
    Disjoint.mono (supr_range_std_basis_le_infi_ker_proj _ _ _ _ <| disjoint_compl_right)
      (supr_range_std_basis_le_infi_ker_proj _ _ _ _ <| disjoint_compl_right) _
  simp only [disjoint_iff_inf_le, SetLike.le_def, mem_infi, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff]
  rintro b ⟨hI, hJ⟩ i
  classical
    by_cases hiI : i ∈ I
    · by_cases hiJ : i ∈ J
      · exact (h.le_bot ⟨hiI, hiJ⟩).elim
      · exact hJ i hiJ
    · exact hI i hiI
#align linear_map.disjoint_std_basis_std_basis LinearMap.disjoint_stdBasis_stdBasis

/- warning: linear_map.std_basis_eq_single -> LinearMap.stdBasis_eq_single is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_4 : DecidableEq.{succ u2} ι] {a : R}, Eq.{max (succ u2) (succ u1)} (ι -> (forall (i : ι), (fun (_x : ι) => R) i)) (fun (i : ι) => coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (LinearMap.{u1, u1, u1, max u2 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((fun (_x : ι) => R) i) (forall (i : ι), (fun (_x : ι) => R) i) ((fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (Pi.addCommMonoid.{u2, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i)) ((fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i) (Pi.module.{u2, u1, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) R _inst_1 (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (fun (i : ι) => (fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i))) (fun (_x : LinearMap.{u1, u1, u1, max u2 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((fun (_x : ι) => R) i) (forall (i : ι), (fun (_x : ι) => R) i) ((fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (Pi.addCommMonoid.{u2, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i)) ((fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i) (Pi.module.{u2, u1, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) R _inst_1 (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (fun (i : ι) => (fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i))) => R -> (forall (i : ι), (fun (_x : ι) => R) i)) (LinearMap.hasCoeToFun.{u1, u1, u1, max u2 u1} R R ((fun (_x : ι) => R) i) (forall (i : ι), (fun (_x : ι) => R) i) _inst_1 _inst_1 ((fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (Pi.addCommMonoid.{u2, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i)) ((fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i) (Pi.module.{u2, u1, u1} ι (fun (i : ι) => (fun (_x : ι) => R) i) R _inst_1 (fun (i : ι) => (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) i) (fun (i : ι) => (fun (i : ι) => Semiring.toModule.{u1} R _inst_1) i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.stdBasis.{u1, u2, u1} R ι _inst_1 (fun (_x : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u1} ((fun (_x : ι) => R) i) _inst_1))) (fun (i : ι) => Semiring.toModule.{u1} R _inst_1) (fun (a : ι) (b : ι) => _inst_4 a b) i) a) (fun (i : ι) => coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (fun (_x : Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) => ι -> R) (Finsupp.coeFun.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Finsupp.single.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) i a))
but is expected to have type
  forall (R : Type.{u2}) {ι : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_4 : DecidableEq.{succ u1} ι] {a : R}, Eq.{max (succ u2) (succ u1)} (ι -> ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : R) => ι -> R) a)) (fun (i : ι) => FunLike.coe.{max (succ u2) (succ u1), succ u2, max (succ u2) (succ u1)} (LinearMap.{u2, u2, u2, max u1 u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) R (ι -> R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) _inst_1))) (Pi.addCommMonoid.{u1, u2} ι (fun (i : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) _inst_1)))) (Semiring.toModule.{u2} R _inst_1) (Pi.module.{u1, u2, u2} ι (fun (i : ι) => R) R _inst_1 (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) _inst_1))) (fun (i : ι) => Semiring.toModule.{u2} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : R) => ι -> R) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u2, max u2 u1} R R R (ι -> R) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) _inst_1))) (Pi.addCommMonoid.{u1, u2} ι (fun (i : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) _inst_1)))) (Semiring.toModule.{u2} R _inst_1) (Pi.module.{u1, u2, u2} ι (fun (i : ι) => R) R _inst_1 (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.2287 : ι) => R) i) _inst_1))) (fun (i : ι) => Semiring.toModule.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (LinearMap.stdBasis.{u2, u1, u2} R ι _inst_1 (fun (_x : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (_x : ι) => R) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) (Semiring.toNonAssocSemiring.{u2} ((fun (_x : ι) => R) i) _inst_1))) (fun (i : ι) => Semiring.toModule.{u2} R _inst_1) (fun (a : ι) (b : ι) => _inst_4 a b) i) a) (fun (i : ι) => FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} ι R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1))) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => R) _x) (Finsupp.funLike.{u1, u2} ι R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1))) (Finsupp.single.{u1, u2} ι R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) i a))
Case conversion may be inaccurate. Consider using '#align linear_map.std_basis_eq_single LinearMap.stdBasis_eq_singleₓ'. -/
theorem stdBasis_eq_single {a : R} :
    (fun i : ι => (stdBasis R (fun _ : ι => R) i) a) = fun i : ι => Finsupp.single i a :=
  funext fun i => (Finsupp.single_eq_pi_single i a).symm
#align linear_map.std_basis_eq_single LinearMap.stdBasis_eq_single

end LinearMap

namespace Pi

open LinearMap

open Set

variable {R : Type _}

section Module

variable {η : Type _} {ιs : η → Type _} {Ms : η → Type _}

/- warning: pi.linear_independent_std_basis -> Pi.linearIndependent_stdBasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align pi.linear_independent_std_basis Pi.linearIndependent_stdBasisₓ'. -/
theorem linearIndependent_stdBasis [Ring R] [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]
    [DecidableEq η] (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σj, ιs j => stdBasis R Ms ji.1 (v ji.1 ji.2) :=
  by
  have hs' : ∀ j : η, LinearIndependent R fun i : ιs j => std_basis R Ms j (v j i) :=
    by
    intro j
    exact (hs j).map' _ (ker_std_basis _ _ _)
  apply linearIndependent_iUnion_finite hs'
  · intro j J _ hiJ
    simp [(Set.iUnion.equations._eqn_1 _).symm, Submodule.span_image, Submodule.span_iUnion]
    have h₀ :
      ∀ j, span R (range fun i : ιs j => std_basis R Ms j (v j i)) ≤ range (std_basis R Ms j) :=
      by
      intro j
      rw [span_le, LinearMap.range_coe]
      apply range_comp_subset_range
    have h₁ :
      span R (range fun i : ιs j => std_basis R Ms j (v j i)) ≤
        ⨆ i ∈ {j}, range (std_basis R Ms i) :=
      by
      rw [@iSup_singleton _ _ _ fun i => LinearMap.range (std_basis R (fun j : η => Ms j) i)]
      apply h₀
    have h₂ :
      (⨆ j ∈ J, span R (range fun i : ιs j => std_basis R Ms j (v j i))) ≤
        ⨆ j ∈ J, range (std_basis R (fun j : η => Ms j) j) :=
      iSup₂_mono fun i _ => h₀ i
    have h₃ : Disjoint (fun i : η => i ∈ {j}) J := by
      convert Set.disjoint_singleton_left.2 hiJ using 0
    exact (disjoint_std_basis_std_basis _ _ _ _ h₃).mono h₁ h₂
#align pi.linear_independent_std_basis Pi.linearIndependent_stdBasis

variable [Semiring R] [∀ i, AddCommMonoid (Ms i)] [∀ i, Module R (Ms i)]

variable [Fintype η]

section

open LinearEquiv

#print Pi.basis /-
/-- `pi.basis (s : ∀ j, basis (ιs j) R (Ms j))` is the `Σ j, ιs j`-indexed basis on `Π j, Ms j`
given by `s j` on each component.

For the standard basis over `R` on the finite-dimensional space `η → R` see `pi.basis_fun`.
-/
protected noncomputable def basis (s : ∀ j, Basis (ιs j) R (Ms j)) :
    Basis (Σj, ιs j) R (∀ j, Ms j) :=
  by
  -- The `add_comm_monoid (Π j, Ms j)` instance was hard to find.
  -- Defining this in tactic mode seems to shake up instance search enough that it works by itself.
  refine' Basis.ofRepr (_ ≪≫ₗ (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)
  exact LinearEquiv.piCongrRight fun j => (s j).repr
#align pi.basis Pi.basis
-/

/- warning: pi.basis_repr_std_basis -> Pi.basis_repr_stdBasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align pi.basis_repr_std_basis Pi.basis_repr_stdBasisₓ'. -/
@[simp]
theorem basis_repr_stdBasis [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (j i) :
    (Pi.basis s).repr (stdBasis R _ j (s j i)) = Finsupp.single ⟨j, i⟩ 1 :=
  by
  ext ⟨j', i'⟩
  by_cases hj : j = j'
  · subst hj
    simp only [Pi.basis, LinearEquiv.trans_apply, Basis.repr_self, std_basis_same,
      LinearEquiv.piCongrRight, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply]
    symm
    exact
      Finsupp.single_apply_left
        (fun i i' (h : (⟨j, i⟩ : Σj, ιs j) = ⟨j, i'⟩) => eq_of_hEq (Sigma.mk.inj h).2) _ _ _
  simp only [Pi.basis, LinearEquiv.trans_apply, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
    LinearEquiv.piCongrRight]
  dsimp
  rw [std_basis_ne _ _ _ _ (Ne.symm hj), LinearEquiv.map_zero, Finsupp.zero_apply,
    Finsupp.single_eq_of_ne]
  rintro ⟨⟩
  contradiction
#align pi.basis_repr_std_basis Pi.basis_repr_stdBasis

/- warning: pi.basis_apply -> Pi.basis_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align pi.basis_apply Pi.basis_applyₓ'. -/
@[simp]
theorem basis_apply [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (ji) :
    Pi.basis s ji = stdBasis R _ ji.1 (s ji.1 ji.2) :=
  Basis.apply_eq_iff.mpr (by simp)
#align pi.basis_apply Pi.basis_apply

/- warning: pi.basis_repr -> Pi.basis_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align pi.basis_repr Pi.basis_reprₓ'. -/
@[simp]
theorem basis_repr (s : ∀ j, Basis (ιs j) R (Ms j)) (x) (ji) :
    (Pi.basis s).repr x ji = (s ji.1).repr (x ji.1) ji.2 :=
  rfl
#align pi.basis_repr Pi.basis_repr

end

section

variable (R η)

#print Pi.basisFun /-
/-- The basis on `η → R` where the `i`th basis vector is `function.update 0 i 1`. -/
noncomputable def basisFun : Basis η R (∀ j : η, R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)
#align pi.basis_fun Pi.basisFun
-/

/- warning: pi.basis_fun_apply -> Pi.basisFun_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align pi.basis_fun_apply Pi.basisFun_applyₓ'. -/
@[simp]
theorem basisFun_apply [DecidableEq η] (i) : basisFun R η i = stdBasis R (fun i : η => R) i 1 := by
  simp only [basis_fun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    std_basis_apply]
#align pi.basis_fun_apply Pi.basisFun_apply

/- warning: pi.basis_fun_repr -> Pi.basisFun_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align pi.basis_fun_repr Pi.basisFun_reprₓ'. -/
@[simp]
theorem basisFun_repr (x : η → R) (i : η) : (Pi.basisFun R η).repr x i = x i := by simp [basis_fun]
#align pi.basis_fun_repr Pi.basisFun_repr

/- warning: pi.basis_fun_equiv_fun -> Pi.basisFun_equivFun is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (η : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_4 : Fintype.{u2} η], Eq.{succ (max u2 u1)} (LinearEquiv.{u1, u1, max u2 u1, max u2 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (η -> R) (η -> R) (Pi.addCommMonoid.{u2, u1} η (fun (j : η) => R) (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u2, u1} η (fun (ᾰ : η) => R) (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} η R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u2, u1, u1} η R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) (Basis.equivFun.{u2, u1, max u2 u1} η R (η -> R) _inst_1 (Pi.addCommMonoid.{u2, u1} η (fun (j : η) => R) (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} η R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) _inst_4 (Pi.basisFun.{u1, u2} R η _inst_1 _inst_4)) (LinearEquiv.refl.{u1, max u2 u1} R (η -> R) _inst_1 (Pi.addCommMonoid.{u2, u1} η (fun (j : η) => R) (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} η R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)))
but is expected to have type
  forall (R : Type.{u2}) (η : Type.{u1}) [_inst_1 : Semiring.{u2} R] [_inst_4 : Fintype.{u1} η], Eq.{max (succ u2) (succ u1)} (LinearEquiv.{u2, u2, max u2 u1, max u1 u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) (η -> R) (η -> R) (Pi.addCommMonoid.{u1, u2} η (fun (j : η) => R) (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (Pi.addCommMonoid.{u1, u2} η (fun (ᾰ : η) => R) (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (Pi.module.{u1, u2, u2} η (fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.3573 : η) => R) R _inst_1 (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (fun (i : η) => Semiring.toModule.{u2} R _inst_1)) (Pi.module.{u1, u2, u2} η (fun (a._@.Mathlib.LinearAlgebra.Basis._hyg.11185 : η) => R) R _inst_1 (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (fun (i : η) => Semiring.toModule.{u2} R _inst_1))) (Basis.equivFun.{u1, u2, max u2 u1} η R (η -> R) _inst_1 (Pi.addCommMonoid.{u1, u2} η (fun (j : η) => R) (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (Pi.module.{u1, u2, u2} η (fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.3573 : η) => R) R _inst_1 (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (fun (i : η) => Semiring.toModule.{u2} R _inst_1)) _inst_4 (Pi.basisFun.{u2, u1} R η _inst_1 _inst_4)) (LinearEquiv.refl.{u2, max u2 u1} R (η -> R) _inst_1 (Pi.addCommMonoid.{u1, u2} η (fun (j : η) => R) (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (Pi.module.{u1, u2, u2} η (fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.3573 : η) => R) R _inst_1 (fun (i : η) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (fun (i : η) => Semiring.toModule.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align pi.basis_fun_equiv_fun Pi.basisFun_equivFunₓ'. -/
@[simp]
theorem basisFun_equivFun : (Pi.basisFun R η).equivFun = LinearEquiv.refl _ _ :=
  Basis.equivFun_ofEquivFun _
#align pi.basis_fun_equiv_fun Pi.basisFun_equivFun

end

end Module

end Pi

namespace Matrix

variable (R : Type _) (m n : Type _) [Fintype m] [Fintype n] [Semiring R]

#print Matrix.stdBasis /-
/-- The standard basis of `matrix m n R`. -/
noncomputable def stdBasis : Basis (m × n) R (Matrix m n R) :=
  Basis.reindex (Pi.basis fun i : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
#align matrix.std_basis Matrix.stdBasis
-/

variable {n m}

#print Matrix.stdBasis_eq_stdBasisMatrix /-
theorem stdBasis_eq_stdBasisMatrix (i : n) (j : m) [DecidableEq n] [DecidableEq m] :
    stdBasis R n m (i, j) = stdBasisMatrix i j (1 : R) :=
  by
  ext (a b)
  by_cases hi : i = a <;> by_cases hj : j = b
  · simp [std_basis, hi, hj]
  · simp [std_basis, hi, hj, Ne.symm hj, LinearMap.stdBasis_ne]
  · simp [std_basis, hi, hj, Ne.symm hi, LinearMap.stdBasis_ne]
  · simp [std_basis, hi, hj, Ne.symm hj, Ne.symm hi, LinearMap.stdBasis_ne]
#align matrix.std_basis_eq_std_basis_matrix Matrix.stdBasis_eq_stdBasisMatrix
-/

end Matrix

