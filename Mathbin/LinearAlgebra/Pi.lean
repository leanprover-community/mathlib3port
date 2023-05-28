/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.pi
! leanprover-community/mathlib commit 1ead22342e1a078bd44744ace999f85756555d35
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Basic
import Mathbin.Logic.Equiv.Fin

/-!
# Pi types of modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines constructors for linear maps whose domains or codomains are pi types.

It contains theorems relating these to each other, as well as to `linear_map.ker`.

## Main definitions

- pi types in the codomain:
  - `linear_map.pi`
  - `linear_map.single`
- pi types in the domain:
  - `linear_map.proj`
- `linear_map.diag`

-/


universe u v w x y z u' v' w' x' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}

variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x} {ι' : Type x'}

open Function Submodule

open BigOperators

namespace LinearMap

universe i

variable [Semiring R] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
  {φ : ι → Type i} [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

#print LinearMap.pi /-
/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi (f : ∀ i, M₂ →ₗ[R] φ i) : M₂ →ₗ[R] ∀ i, φ i :=
  {
    Pi.addHom fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun c d => funext fun i => (f i).map_smul _ _ }
#align linear_map.pi LinearMap.pi
-/

/- warning: linear_map.pi_apply -> LinearMap.pi_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.pi_apply LinearMap.pi_applyₓ'. -/
@[simp]
theorem pi_apply (f : ∀ i, M₂ →ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i c :=
  rfl
#align linear_map.pi_apply LinearMap.pi_apply

/- warning: linear_map.ker_pi -> LinearMap.ker_pi is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M₂ : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M₂] [_inst_3 : Module.{u1, u2} R M₂ _inst_1 _inst_2] {φ : ι -> Type.{u4}} [_inst_6 : forall (i : ι), AddCommMonoid.{u4} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u4} R (φ i) _inst_1 (_inst_6 i)] (f : forall (i : ι), LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)), Eq.{succ u2} (Submodule.{u1, u2} R M₂ _inst_1 _inst_2 _inst_3) (LinearMap.ker.{u1, u1, u2, max u3 u4, max u2 u3 u4} R R M₂ (forall (i : ι), φ i) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u2, max u3 u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.semilinearMapClass.{u1, u1, u2, max u3 u4} R R M₂ (forall (i : ι), φ i) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.pi.{u1, u2, u3, u4} R M₂ ι _inst_1 _inst_2 _inst_3 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) f)) (iInf.{u2, succ u3} (Submodule.{u1, u2} R M₂ _inst_1 _inst_2 _inst_3) (Submodule.hasInf.{u1, u2} R M₂ _inst_1 _inst_2 _inst_3) ι (fun (i : ι) => LinearMap.ker.{u1, u1, u2, u4, max u2 u4} R R M₂ (φ i) _inst_1 _inst_1 _inst_2 (_inst_6 i) _inst_3 (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) (LinearMap.semilinearMapClass.{u1, u1, u2, u4} R R M₂ (φ i) _inst_1 _inst_1 _inst_2 (_inst_6 i) _inst_3 (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (f i)))
but is expected to have type
  forall {R : Type.{u1}} {M₂ : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M₂] [_inst_3 : Module.{u1, u2} R M₂ _inst_1 _inst_2] {φ : ι -> Type.{u4}} [_inst_6 : forall (i : ι), AddCommMonoid.{u4} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u4} R (φ i) _inst_1 (_inst_6 i)] (f : forall (i : ι), LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)), Eq.{succ u2} (Submodule.{u1, u2} R M₂ _inst_1 _inst_2 _inst_3) (LinearMap.ker.{u1, u1, u2, max u4 u3, max (max u4 u3) u2} R R M₂ (forall (i : ι), φ i) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u2, max u4 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.semilinearMapClass.{u1, u1, u2, max u4 u3} R R M₂ (forall (i : ι), φ i) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.pi.{u1, u2, u3, u4} R M₂ ι _inst_1 _inst_2 _inst_3 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) f)) (iInf.{u2, succ u3} (Submodule.{u1, u2} R M₂ _inst_1 _inst_2 _inst_3) (Submodule.instInfSetSubmodule.{u1, u2} R M₂ _inst_1 _inst_2 _inst_3) ι (fun (i : ι) => LinearMap.ker.{u1, u1, u2, u4, max u4 u2} R R M₂ (φ i) _inst_1 _inst_1 _inst_2 (_inst_6 i) _inst_3 (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) (LinearMap.semilinearMapClass.{u1, u1, u2, u4} R R M₂ (φ i) _inst_1 _inst_1 _inst_2 (_inst_6 i) _inst_3 (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (f i)))
Case conversion may be inaccurate. Consider using '#align linear_map.ker_pi LinearMap.ker_piₓ'. -/
theorem ker_pi (f : ∀ i, M₂ →ₗ[R] φ i) : ker (pi f) = ⨅ i : ι, ker (f i) := by
  ext c <;> simp [funext_iff] <;> rfl
#align linear_map.ker_pi LinearMap.ker_pi

/- warning: linear_map.pi_eq_zero -> LinearMap.pi_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M₂ : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M₂] [_inst_3 : Module.{u1, u2} R M₂ _inst_1 _inst_2] {φ : ι -> Type.{u4}} [_inst_6 : forall (i : ι), AddCommMonoid.{u4} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u4} R (φ i) _inst_1 (_inst_6 i)] (f : forall (i : ι), LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)), Iff (Eq.{max (succ u2) (succ (max u3 u4))} (LinearMap.{u1, u1, u2, max u3 u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.pi.{u1, u2, u3, u4} R M₂ ι _inst_1 _inst_2 _inst_3 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) f) (OfNat.ofNat.{max u2 u3 u4} (LinearMap.{u1, u1, u2, max u3 u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) 0 (OfNat.mk.{max u2 u3 u4} (LinearMap.{u1, u1, u2, max u3 u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) 0 (Zero.zero.{max u2 u3 u4} (LinearMap.{u1, u1, u2, max u3 u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.hasZero.{u1, u1, u2, max u3 u4} R R M₂ (forall (i : ι), φ i) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) (forall (i : ι), Eq.{max (succ u2) (succ u4)} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) (f i) (OfNat.ofNat.{max u2 u4} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) 0 (OfNat.mk.{max u2 u4} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) 0 (Zero.zero.{max u2 u4} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) (LinearMap.hasZero.{u1, u1, u2, u4} R R M₂ (φ i) _inst_1 _inst_1 _inst_2 (_inst_6 i) _inst_3 (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} {M₂ : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M₂] [_inst_3 : Module.{u1, u2} R M₂ _inst_1 _inst_2] {φ : ι -> Type.{u4}} [_inst_6 : forall (i : ι), AddCommMonoid.{u4} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u4} R (φ i) _inst_1 (_inst_6 i)] (f : forall (i : ι), LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)), Iff (Eq.{max (max (succ u4) (succ u2)) (succ u3)} (LinearMap.{u1, u1, u2, max u4 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.pi.{u1, u2, u3, u4} R M₂ ι _inst_1 _inst_2 _inst_3 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) f) (OfNat.ofNat.{max (max u4 u2) u3} (LinearMap.{u1, u1, u2, max u4 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) 0 (Zero.toOfNat0.{max (max u4 u2) u3} (LinearMap.{u1, u1, u2, max u4 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.instZeroLinearMap.{u1, u1, u2, max u4 u3} R R M₂ (forall (i : ι), φ i) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) (forall (i : ι), Eq.{max (succ u4) (succ u2)} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) (f i) (OfNat.ofNat.{max u4 u2} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) 0 (Zero.toOfNat0.{max u4 u2} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) (LinearMap.instZeroLinearMap.{u1, u1, u2, u4} R R M₂ (φ i) _inst_1 _inst_1 _inst_2 (_inst_6 i) _inst_3 (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align linear_map.pi_eq_zero LinearMap.pi_eq_zeroₓ'. -/
theorem pi_eq_zero (f : ∀ i, M₂ →ₗ[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [LinearMap.ext_iff, pi_apply, funext_iff] <;>
    exact ⟨fun h a b => h b a, fun h a b => h b a⟩
#align linear_map.pi_eq_zero LinearMap.pi_eq_zero

/- warning: linear_map.pi_zero -> LinearMap.pi_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M₂ : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M₂] [_inst_3 : Module.{u1, u2} R M₂ _inst_1 _inst_2] {φ : ι -> Type.{u4}} [_inst_6 : forall (i : ι), AddCommMonoid.{u4} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u4} R (φ i) _inst_1 (_inst_6 i)], Eq.{max (succ u2) (succ (max u3 u4))} (LinearMap.{u1, u1, u2, max u3 u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.pi.{u1, u2, u3, u4} R M₂ ι _inst_1 _inst_2 _inst_3 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => OfNat.ofNat.{max u2 u4} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) 0 (OfNat.mk.{max u2 u4} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) 0 (Zero.zero.{max u2 u4} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) (LinearMap.hasZero.{u1, u1, u2, u4} R R M₂ (φ i) _inst_1 _inst_1 _inst_2 (_inst_6 i) _inst_3 (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) (OfNat.ofNat.{max u2 u3 u4} (LinearMap.{u1, u1, u2, max u3 u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) 0 (OfNat.mk.{max u2 u3 u4} (LinearMap.{u1, u1, u2, max u3 u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) 0 (Zero.zero.{max u2 u3 u4} (LinearMap.{u1, u1, u2, max u3 u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.hasZero.{u1, u1, u2, max u3 u4} R R M₂ (forall (i : ι), φ i) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} {M₂ : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M₂] [_inst_3 : Module.{u1, u2} R M₂ _inst_1 _inst_2] {φ : ι -> Type.{u4}} [_inst_6 : forall (i : ι), AddCommMonoid.{u4} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u4} R (φ i) _inst_1 (_inst_6 i)], Eq.{max (max (succ u4) (succ u2)) (succ u3)} (LinearMap.{u1, u1, u2, max u4 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.pi.{u1, u2, u3, u4} R M₂ ι _inst_1 _inst_2 _inst_3 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => OfNat.ofNat.{max u4 u2} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) 0 (Zero.toOfNat0.{max u4 u2} (LinearMap.{u1, u1, u2, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (φ i) _inst_2 (_inst_6 i) _inst_3 (_inst_7 i)) (LinearMap.instZeroLinearMap.{u1, u1, u2, u4} R R M₂ (φ i) _inst_1 _inst_1 _inst_2 (_inst_6 i) _inst_3 (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) (OfNat.ofNat.{max (max u4 u2) u3} (LinearMap.{u1, u1, u2, max u4 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) 0 (Zero.toOfNat0.{max (max u4 u2) u3} (LinearMap.{u1, u1, u2, max u4 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M₂ (forall (i : ι), φ i) _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (LinearMap.instZeroLinearMap.{u1, u1, u2, max u4 u3} R R M₂ (forall (i : ι), φ i) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{u3, u4} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) _inst_3 (Pi.module.{u3, u4, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align linear_map.pi_zero LinearMap.pi_zeroₓ'. -/
theorem pi_zero : pi (fun i => 0 : ∀ i, M₂ →ₗ[R] φ i) = 0 := by ext <;> rfl
#align linear_map.pi_zero LinearMap.pi_zero

#print LinearMap.pi_comp /-
theorem pi_comp (f : ∀ i, M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl
#align linear_map.pi_comp LinearMap.pi_comp
-/

#print LinearMap.proj /-
/-- The projections from a family of modules are linear maps.

Note:  known here as `linear_map.proj`, this construction is in other categories called `eval`, for
example `pi.eval_monoid_hom`, `pi.eval_ring_hom`. -/
def proj (i : ι) : (∀ i, φ i) →ₗ[R] φ i
    where
  toFun := Function.eval i
  map_add' f g := rfl
  map_smul' c f := rfl
#align linear_map.proj LinearMap.proj
-/

/- warning: linear_map.coe_proj -> LinearMap.coe_proj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_6 i)] (i : ι), Eq.{max (succ (max u2 u3)) (succ u3)} ((forall (i : ι), φ i) -> (φ i)) (coeFn.{max (succ (max u2 u3)) (succ u3), max (succ (max u2 u3)) (succ u3)} (LinearMap.{u1, u1, max u2 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i)) (fun (_x : LinearMap.{u1, u1, max u2 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i)) => (forall (i : ι), φ i) -> (φ i)) (LinearMap.hasCoeToFun.{u1, u1, max u2 u3, u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.proj.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) i)) (Function.eval.{succ u2, succ u3} ι (fun (x : ι) => φ x) i)
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_6 i)] (i : ι), Eq.{max (succ u3) (succ u2)} (forall (ᾰ : forall (i : ι), φ i), (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : forall (i : ι), φ i) => φ i) ᾰ) (FunLike.coe.{max (succ u3) (succ u2), max (succ u3) (succ u2), succ u3} (LinearMap.{u1, u1, max u3 u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i)) (forall (i : ι), φ i) (fun (_x : forall (i : ι), φ i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : forall (i : ι), φ i) => φ i) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, max u3 u2, u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.proj.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) i)) (Function.eval.{succ u2, succ u3} ι (fun (x : ι) => φ x) i)
Case conversion may be inaccurate. Consider using '#align linear_map.coe_proj LinearMap.coe_projₓ'. -/
@[simp]
theorem coe_proj (i : ι) : ⇑(proj i : (∀ i, φ i) →ₗ[R] φ i) = Function.eval i :=
  rfl
#align linear_map.coe_proj LinearMap.coe_proj

/- warning: linear_map.proj_apply -> LinearMap.proj_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_6 i)] (i : ι) (b : forall (i : ι), φ i), Eq.{succ u3} ((fun (i : ι) => φ i) i) (coeFn.{max (succ (max u2 u3)) (succ u3), max (succ (max u2 u3)) (succ u3)} (LinearMap.{u1, u1, max u2 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), (fun (i : ι) => φ i) i) ((fun (i : ι) => φ i) i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => (fun (i : ι) => φ i) i) (fun (i : ι) => (fun (i : ι) => _inst_6 i) i)) ((fun (i : ι) => _inst_6 i) i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => (fun (i : ι) => φ i) i) R _inst_1 (fun (i : ι) => (fun (i : ι) => _inst_6 i) i) (fun (i : ι) => (fun (i : ι) => _inst_7 i) i)) ((fun (i : ι) => _inst_7 i) i)) (fun (_x : LinearMap.{u1, u1, max u2 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), (fun (i : ι) => φ i) i) ((fun (i : ι) => φ i) i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => (fun (i : ι) => φ i) i) (fun (i : ι) => (fun (i : ι) => _inst_6 i) i)) ((fun (i : ι) => _inst_6 i) i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => (fun (i : ι) => φ i) i) R _inst_1 (fun (i : ι) => (fun (i : ι) => _inst_6 i) i) (fun (i : ι) => (fun (i : ι) => _inst_7 i) i)) ((fun (i : ι) => _inst_7 i) i)) => (forall (i : ι), (fun (i : ι) => φ i) i) -> ((fun (i : ι) => φ i) i)) (LinearMap.hasCoeToFun.{u1, u1, max u2 u3, u3} R R (forall (i : ι), (fun (i : ι) => φ i) i) ((fun (i : ι) => φ i) i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => (fun (i : ι) => φ i) i) (fun (i : ι) => (fun (i : ι) => _inst_6 i) i)) ((fun (i : ι) => _inst_6 i) i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => (fun (i : ι) => φ i) i) R _inst_1 (fun (i : ι) => (fun (i : ι) => _inst_6 i) i) (fun (i : ι) => (fun (i : ι) => _inst_7 i) i)) ((fun (i : ι) => _inst_7 i) i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.proj.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) i) b) (b i)
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_6 i)] (i : ι) (b : forall (i : ι), φ i), Eq.{succ u3} ((fun (i_1 : forall (i : ι), φ i) => φ i) b) (FunLike.coe.{max (succ u3) (succ u2), max (succ u3) (succ u2), succ u3} (LinearMap.{u1, u1, max u3 u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i)) (forall (i : ι), φ i) (fun (_x : forall (i : ι), φ i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : forall (i : ι), φ i) => φ i) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, max u3 u2, u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.proj.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) i) b) (b i)
Case conversion may be inaccurate. Consider using '#align linear_map.proj_apply LinearMap.proj_applyₓ'. -/
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →ₗ[R] φ i) b = b i :=
  rfl
#align linear_map.proj_apply LinearMap.proj_apply

#print LinearMap.proj_pi /-
theorem proj_pi (f : ∀ i, M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext fun c => rfl
#align linear_map.proj_pi LinearMap.proj_pi
-/

/- warning: linear_map.infi_ker_proj -> LinearMap.iInf_ker_proj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_6 i)], Eq.{succ (max u2 u3)} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (iInf.{max u2 u3, succ u2} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (Submodule.hasInf.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) ι (fun (i : ι) => LinearMap.ker.{u1, u1, max u2 u3, u3, max u2 u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, max u2 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i)) (LinearMap.semilinearMapClass.{u1, u1, max u2 u3, u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.proj.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) i))) (Bot.bot.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (Submodule.hasBot.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))))
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_6 i)], Eq.{max (succ u3) (succ u2)} (Submodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (iInf.{max u3 u2, succ u2} (Submodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (Submodule.instInfSetSubmodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) ι (fun (i : ι) => LinearMap.ker.{u1, u1, max u3 u2, u3, max u3 u2} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, max u3 u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i)) (LinearMap.semilinearMapClass.{u1, u1, max u3 u2, u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_6 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (_inst_7 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.proj.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) i))) (Bot.bot.{max u3 u2} (Submodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (Submodule.instBotSubmodule.{u1, max u3 u2} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))))
Case conversion may be inaccurate. Consider using '#align linear_map.infi_ker_proj LinearMap.iInf_ker_projₓ'. -/
theorem iInf_ker_proj : (⨅ i, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) : Submodule R (∀ i, φ i)) = ⊥ :=
  bot_unique <|
    SetLike.le_def.2 fun a h =>
      by
      simp only [mem_infi, mem_ker, proj_apply] at h
      exact (mem_bot _).2 (funext fun i => h i)
#align linear_map.infi_ker_proj LinearMap.iInf_ker_proj

#print LinearMap.compLeft /-
/-- Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linear map `f`
between `M₂` and `M₃`. -/
@[simps]
protected def compLeft (f : M₂ →ₗ[R] M₃) (I : Type _) : (I → M₂) →ₗ[R] I → M₃ :=
  { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }
#align linear_map.comp_left LinearMap.compLeft
-/

/- warning: linear_map.apply_single -> LinearMap.apply_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.apply_single LinearMap.apply_singleₓ'. -/
theorem apply_single [AddCommMonoid M] [Module R M] [DecidableEq ι] (f : ∀ i, φ i →ₗ[R] M) (i j : ι)
    (x : φ i) : f j (Pi.single i x j) = Pi.single i (f i x) j :=
  Pi.apply_single (fun i => f i) (fun i => (f i).map_zero) _ _ _
#align linear_map.apply_single LinearMap.apply_single

#print LinearMap.single /-
/-- The `linear_map` version of `add_monoid_hom.single` and `pi.single`. -/
def single [DecidableEq ι] (i : ι) : φ i →ₗ[R] ∀ i, φ i :=
  { AddMonoidHom.single φ i with
    toFun := Pi.single i
    map_smul' := Pi.single_smul i }
#align linear_map.single LinearMap.single
-/

/- warning: linear_map.coe_single -> LinearMap.coe_single is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_6 i)] [_inst_8 : DecidableEq.{succ u2} ι] (i : ι), Eq.{max (succ u3) (succ (max u2 u3))} ((φ i) -> (forall (i : ι), φ i)) (coeFn.{max (succ u3) (succ (max u2 u3)), max (succ u3) (succ (max u2 u3))} (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_6 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_7 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (fun (_x : LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_6 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_7 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) => (φ i) -> (forall (i : ι), φ i)) (LinearMap.hasCoeToFun.{u1, u1, u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_6 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_7 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.single.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) (fun (a : ι) (b : ι) => _inst_8 a b) i)) (Pi.single.{u2, u3} ι (fun (i : ι) => φ i) (fun (a : ι) (b : ι) => _inst_8 a b) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (φ i) (AddMonoid.toAddZeroClass.{u3} (φ i) (AddCommMonoid.toAddMonoid.{u3} (φ i) (_inst_6 i)))) i)
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_7 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_6 i)] [_inst_8 : DecidableEq.{succ u2} ι] (i : ι), Eq.{max (succ u3) (succ u2)} (forall (ᾰ : φ i), (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : φ i) => forall (i : ι), φ i) ᾰ) (FunLike.coe.{max (succ u3) (succ u2), succ u3, max (succ u3) (succ u2)} (LinearMap.{u1, u1, u3, max u3 u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_6 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_7 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i))) (φ i) (fun (_x : φ i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : φ i) => forall (i : ι), φ i) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u3, max u3 u2} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_6 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_6 i)) (_inst_7 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.single.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) (fun (a : ι) (b : ι) => _inst_8 a b) i)) (Pi.single.{u2, u3} ι φ (fun (a : ι) (b : ι) => _inst_8 a b) (fun (i : ι) => AddMonoid.toZero.{u3} (φ i) (AddCommMonoid.toAddMonoid.{u3} (φ i) (_inst_6 i))) i)
Case conversion may be inaccurate. Consider using '#align linear_map.coe_single LinearMap.coe_singleₓ'. -/
@[simp]
theorem coe_single [DecidableEq ι] (i : ι) : ⇑(single i : φ i →ₗ[R] ∀ i, φ i) = Pi.single i :=
  rfl
#align linear_map.coe_single LinearMap.coe_single

variable (R φ)

#print LinearMap.lsum /-
/-- The linear equivalence between linear functions on a finite product of modules and
families of functions on these modules. See note [bundled maps over different rings]. -/
@[simps]
def lsum (S) [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι] [Semiring S] [Module S M]
    [SMulCommClass R S M] : (∀ i, φ i →ₗ[R] M) ≃ₗ[S] (∀ i, φ i) →ₗ[R] M
    where
  toFun f := ∑ i : ι, (f i).comp (proj i)
  invFun f i := f.comp (single i)
  map_add' f g := by simp only [Pi.add_apply, add_comp, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_comp, Finset.smul_sum, RingHom.id_apply]
  left_inv f := by
    ext (i x)
    simp [apply_single]
  right_inv f := by
    ext
    suffices f (∑ j, Pi.single j (x j)) = f x by simpa [apply_single]
    rw [Finset.univ_sum_single]
#align linear_map.lsum LinearMap.lsum
-/

/- warning: linear_map.lsum_single -> LinearMap.lsum_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.lsum_single LinearMap.lsum_singleₓ'. -/
@[simp]
theorem lsum_single {ι R : Type _} [Fintype ι] [DecidableEq ι] [CommRing R] {M : ι → Type _}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    LinearMap.lsum R M R LinearMap.single = LinearMap.id :=
  LinearMap.ext fun x => by simp [Finset.univ_sum_single]
#align linear_map.lsum_single LinearMap.lsum_single

variable {R φ}

section Ext

variable [Finite ι] [DecidableEq ι] [AddCommMonoid M] [Module R M] {f g : (∀ i, φ i) →ₗ[R] M}

/- warning: linear_map.pi_ext -> LinearMap.pi_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.pi_ext LinearMap.pi_extₓ'. -/
theorem pi_ext (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) : f = g :=
  toAddMonoidHom_injective <| AddMonoidHom.functions_ext _ _ _ h
#align linear_map.pi_ext LinearMap.pi_ext

/- warning: linear_map.pi_ext_iff -> LinearMap.pi_ext_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.pi_ext_iff LinearMap.pi_ext_iffₓ'. -/
theorem pi_ext_iff : f = g ↔ ∀ i x, f (Pi.single i x) = g (Pi.single i x) :=
  ⟨fun h i x => h ▸ rfl, pi_ext⟩
#align linear_map.pi_ext_iff LinearMap.pi_ext_iff

#print LinearMap.pi_ext' /-
/-- This is used as the ext lemma instead of `linear_map.pi_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
theorem pi_ext' (h : ∀ i, f.comp (single i) = g.comp (single i)) : f = g :=
  by
  refine' pi_ext fun i x => _
  convert LinearMap.congr_fun (h i) x
#align linear_map.pi_ext' LinearMap.pi_ext'
-/

#print LinearMap.pi_ext'_iff /-
theorem pi_ext'_iff : f = g ↔ ∀ i, f.comp (single i) = g.comp (single i) :=
  ⟨fun h i => h ▸ rfl, pi_ext'⟩
#align linear_map.pi_ext'_iff LinearMap.pi_ext'_iff
-/

end Ext

section

variable (R φ)

/- warning: linear_map.infi_ker_proj_equiv -> LinearMap.iInfKerProjEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.infi_ker_proj_equiv LinearMap.iInfKerProjEquivₓ'. -/
/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) : Submodule R (∀ i, φ i)) ≃ₗ[R] ∀ i : I, φ i :=
  by
  refine'
    LinearEquiv.ofLinear (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (cod_restrict _ (pi fun i => if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) _) _ _
  · intro b
    simp only [mem_infi, mem_ker, funext_iff, proj_apply, pi_apply]
    intro j hjJ
    have : j ∉ I := fun hjI => hd.le_bot ⟨hjI, hjJ⟩
    rw [dif_neg this, zero_apply]
  · simp only [pi_comp, comp_assoc, subtype_comp_cod_restrict, proj_pi, Subtype.coe_prop]
    ext (b⟨j, hj⟩)
    simp only [dif_pos, Function.comp_apply, Function.eval_apply, LinearMap.codRestrict_apply,
      LinearMap.coe_comp, LinearMap.coe_proj, LinearMap.pi_apply, Submodule.subtype_apply,
      Subtype.coe_prop]
    rfl
  · ext1 ⟨b, hb⟩
    apply Subtype.ext
    ext j
    have hb : ∀ i ∈ J, b i = 0 := by
      simpa only [mem_infi, mem_ker, proj_apply] using (mem_infi _).1 hb
    simp only [comp_apply, pi_apply, id_apply, proj_apply, subtype_apply, cod_restrict_apply]
    split_ifs
    · rfl
    · exact (hb _ <| (hu trivial).resolve_left h).symm
#align linear_map.infi_ker_proj_equiv LinearMap.iInfKerProjEquiv

end

section

variable [DecidableEq ι]

#print LinearMap.diag /-
/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
def diag (i j : ι) : φ i →ₗ[R] φ j :=
  @Function.update ι (fun j => φ i →ₗ[R] φ j) _ 0 i id j
#align linear_map.diag LinearMap.diag
-/

/- warning: linear_map.update_apply -> LinearMap.update_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.update_apply LinearMap.update_applyₓ'. -/
theorem update_apply (f : ∀ i, M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
    (update f i b j) c = update (fun i => f i c) i (b c) j :=
  by
  by_cases j = i
  · rw [h, update_same, update_same]
  · rw [update_noteq h, update_noteq h]
#align linear_map.update_apply LinearMap.update_apply

end

end LinearMap

namespace Submodule

variable [Semiring R] {φ : ι → Type _} [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

open LinearMap

#print Submodule.pi /-
/-- A version of `set.pi` for submodules. Given an index set `I` and a family of submodules
`p : Π i, submodule R (φ i)`, `pi I s` is the submodule of dependent functions `f : Π i, φ i`
such that `f i` belongs to `p a` whenever `i ∈ I`. -/
def pi (I : Set ι) (p : ∀ i, Submodule R (φ i)) : Submodule R (∀ i, φ i)
    where
  carrier := Set.pi I fun i => p i
  zero_mem' i hi := (p i).zero_mem
  add_mem' x y hx hy i hi := (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' c x hx i hi := (p i).smul_mem c (hx i hi)
#align submodule.pi Submodule.pi
-/

variable {I : Set ι} {p q : ∀ i, Submodule R (φ i)} {x : ∀ i, φ i}

/- warning: submodule.mem_pi -> Submodule.mem_pi is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] {I : Set.{u2} ι} {p : forall (i : ι), Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)} {x : forall (i : ι), φ i}, Iff (Membership.Mem.{max u2 u3, max u2 u3} (forall (i : ι), φ i) (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (SetLike.hasMem.{max u2 u3, max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (forall (i : ι), φ i) (Submodule.setLike.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))) x (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) I p)) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) -> (Membership.Mem.{u3, u3} (φ i) (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (SetLike.hasMem.{u3, u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (φ i) (Submodule.setLike.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i))) (x i) (p i)))
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)] {I : Set.{u3} ι} {p : forall (i : ι), Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)} {x : forall (i : ι), φ i}, Iff (Membership.mem.{max u3 u1, max u1 u3} (forall (i : ι), φ i) (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (SetLike.instMembership.{max u3 u1, max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (forall (i : ι), φ i) (Submodule.setLike.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))) x (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) I p)) (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i I) -> (Membership.mem.{u1, u1} (φ i) (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (φ i) (Submodule.setLike.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i))) (x i) (p i)))
Case conversion may be inaccurate. Consider using '#align submodule.mem_pi Submodule.mem_piₓ'. -/
@[simp]
theorem mem_pi : x ∈ pi I p ↔ ∀ i ∈ I, x i ∈ p i :=
  Iff.rfl
#align submodule.mem_pi Submodule.mem_pi

/- warning: submodule.coe_pi -> Submodule.coe_pi is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] {I : Set.{u2} ι} {p : forall (i : ι), Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)}, Eq.{succ (max u2 u3)} (Set.{max u2 u3} (forall (i : ι), φ i)) ((fun (a : Type.{max u2 u3}) (b : Type.{max u2 u3}) [self : HasLiftT.{succ (max u2 u3), succ (max u2 u3)} a b] => self.0) (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Set.{max u2 u3} (forall (i : ι), φ i)) (HasLiftT.mk.{succ (max u2 u3), succ (max u2 u3)} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Set.{max u2 u3} (forall (i : ι), φ i)) (CoeTCₓ.coe.{succ (max u2 u3), succ (max u2 u3)} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Set.{max u2 u3} (forall (i : ι), φ i)) (SetLike.Set.hasCoeT.{max u2 u3, max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (forall (i : ι), φ i) (Submodule.setLike.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))))) (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) I p)) (Set.pi.{u2, u3} ι (fun (i : ι) => φ i) I (fun (i : ι) => (fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Set.{u3} (φ i)) (HasLiftT.mk.{succ u3, succ u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Set.{u3} (φ i)) (CoeTCₓ.coe.{succ u3, succ u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Set.{u3} (φ i)) (SetLike.Set.hasCoeT.{u3, u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (φ i) (Submodule.setLike.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i))))) (p i)))
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)] {I : Set.{u3} ι} {p : forall (i : ι), Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)}, Eq.{max (succ u3) (succ u1)} (Set.{max u3 u1} (forall (i : ι), φ i)) (SetLike.coe.{max u3 u1, max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (forall (i : ι), φ i) (Submodule.setLike.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) I p)) (Set.pi.{u3, u1} ι (fun (i : ι) => φ i) I (fun (i : ι) => SetLike.coe.{u1, u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (φ i) (Submodule.setLike.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (p i)))
Case conversion may be inaccurate. Consider using '#align submodule.coe_pi Submodule.coe_piₓ'. -/
@[simp, norm_cast]
theorem coe_pi : (pi I p : Set (∀ i, φ i)) = Set.pi I fun i => p i :=
  rfl
#align submodule.coe_pi Submodule.coe_pi

/- warning: submodule.pi_empty -> Submodule.pi_empty is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] (p : forall (i : ι), Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)), Eq.{succ (max u2 u3)} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} ι) (Set.hasEmptyc.{u2} ι)) p) (Top.top.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.hasTop.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)] (p : forall (i : ι), Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)), Eq.{max (succ u3) (succ u1)} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (EmptyCollection.emptyCollection.{u3} (Set.{u3} ι) (Set.instEmptyCollectionSet.{u3} ι)) p) (Top.top.{max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.instTopSubmodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))
Case conversion may be inaccurate. Consider using '#align submodule.pi_empty Submodule.pi_emptyₓ'. -/
@[simp]
theorem pi_empty (p : ∀ i, Submodule R (φ i)) : pi ∅ p = ⊤ :=
  SetLike.coe_injective <| Set.empty_pi _
#align submodule.pi_empty Submodule.pi_empty

/- warning: submodule.pi_top -> Submodule.pi_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] (s : Set.{u2} ι), Eq.{succ (max u2 u3)} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) s (fun (i : ι) => Top.top.{u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Submodule.hasTop.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)))) (Top.top.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.hasTop.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)] (s : Set.{u3} ι), Eq.{max (succ u3) (succ u1)} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) s (fun (i : ι) => Top.top.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Submodule.instTopSubmodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)))) (Top.top.{max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.instTopSubmodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))
Case conversion may be inaccurate. Consider using '#align submodule.pi_top Submodule.pi_topₓ'. -/
@[simp]
theorem pi_top (s : Set ι) : (pi s fun i : ι => (⊤ : Submodule R (φ i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _
#align submodule.pi_top Submodule.pi_top

/- warning: submodule.pi_mono -> Submodule.pi_mono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] {p : forall (i : ι), Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)} {q : forall (i : ι), Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)} {s : Set.{u2} ι}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (LE.le.{u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Preorder.toHasLe.{u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (PartialOrder.toPreorder.{u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (SetLike.partialOrder.{u3, u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (φ i) (Submodule.setLike.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i))))) (p i) (q i))) -> (LE.le.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Preorder.toHasLe.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (PartialOrder.toPreorder.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (SetLike.partialOrder.{max u2 u3, max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (forall (i : ι), φ i) (Submodule.setLike.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))))) (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) s p) (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) s q))
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)] {p : forall (i : ι), Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)} {q : forall (i : ι), Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)} {s : Set.{u3} ι}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) -> (LE.le.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Preorder.toLE.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Submodule.completeLattice.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)))))) (p i) (q i))) -> (LE.le.{max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Preorder.toLE.{max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (PartialOrder.toPreorder.{max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.completeLattice.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))))) (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) s p) (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) s q))
Case conversion may be inaccurate. Consider using '#align submodule.pi_mono Submodule.pi_monoₓ'. -/
theorem pi_mono {s : Set ι} (h : ∀ i ∈ s, p i ≤ q i) : pi s p ≤ pi s q :=
  Set.pi_mono h
#align submodule.pi_mono Submodule.pi_mono

/- warning: submodule.binfi_comap_proj -> Submodule.biInf_comap_proj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] {I : Set.{u2} ι} {p : forall (i : ι), Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)}, Eq.{succ (max u2 u3)} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (iInf.{max u2 u3, succ u2} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.hasInf.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) ι (fun (i : ι) => iInf.{max u2 u3, 0} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.hasInf.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) => Submodule.comap.{u1, u1, max u2 u3, u3, max u2 u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, max u2 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i)) (LinearMap.semilinearMapClass.{u1, u1, max u2 u3, u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.proj.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) i) (p i)))) (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) I p)
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)] {I : Set.{u3} ι} {p : forall (i : ι), Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)}, Eq.{max (succ u3) (succ u1)} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (iInf.{max u3 u1, succ u3} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.instInfSetSubmodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) ι (fun (i : ι) => iInf.{max u3 u1, 0} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.instInfSetSubmodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i I) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i I) => Submodule.comap.{u2, u2, max u3 u1, u1, max u3 u1} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (LinearMap.{u2, u2, max u1 u3, u1} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i)) (LinearMap.semilinearMapClass.{u2, u2, max u3 u1, u1} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (LinearMap.proj.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) i) (p i)))) (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) I p)
Case conversion may be inaccurate. Consider using '#align submodule.binfi_comap_proj Submodule.biInf_comap_projₓ'. -/
theorem biInf_comap_proj : (⨅ i ∈ I, comap (proj i : (∀ i, φ i) →ₗ[R] φ i) (p i)) = pi I p :=
  by
  ext x
  simp
#align submodule.binfi_comap_proj Submodule.biInf_comap_proj

/- warning: submodule.infi_comap_proj -> Submodule.iInf_comap_proj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] {p : forall (i : ι), Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)}, Eq.{succ (max u2 u3)} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (iInf.{max u2 u3, succ u2} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.hasInf.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) ι (fun (i : ι) => Submodule.comap.{u1, u1, max u2 u3, u3, max u2 u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, max u2 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i)) (LinearMap.semilinearMapClass.{u1, u1, max u2 u3, u3} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.proj.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) i) (p i))) (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (Set.univ.{u2} ι) p)
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)] {p : forall (i : ι), Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)}, Eq.{max (succ u3) (succ u1)} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (iInf.{max u3 u1, succ u3} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.instInfSetSubmodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) ι (fun (i : ι) => Submodule.comap.{u2, u2, max u3 u1, u1, max u3 u1} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (LinearMap.{u2, u2, max u1 u3, u1} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (forall (i : ι), φ i) (φ i) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i)) (LinearMap.semilinearMapClass.{u2, u2, max u3 u1, u1} R R (forall (i : ι), φ i) (φ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (LinearMap.proj.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) i) (p i))) (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (Set.univ.{u3} ι) p)
Case conversion may be inaccurate. Consider using '#align submodule.infi_comap_proj Submodule.iInf_comap_projₓ'. -/
theorem iInf_comap_proj : (⨅ i, comap (proj i : (∀ i, φ i) →ₗ[R] φ i) (p i)) = pi Set.univ p :=
  by
  ext x
  simp
#align submodule.infi_comap_proj Submodule.iInf_comap_proj

/- warning: submodule.supr_map_single -> Submodule.iSup_map_single is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] {p : forall (i : ι), Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)} [_inst_4 : DecidableEq.{succ u2} ι] [_inst_5 : Finite.{succ u2} ι], Eq.{succ (max u2 u3)} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (iSup.{max u2 u3, succ u2} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (ConditionallyCompleteLattice.toHasSup.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u3} (Submodule.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.completeLattice.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))) ι (fun (i : ι) => Submodule.map.{u1, u1, u3, max u2 u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomSurjective.ids.{u1} R _inst_1) (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.semilinearMapClass.{u1, u1, u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.single.{u1, u2, u3} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) (p i))) (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (Set.univ.{u2} ι) p)
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)] {p : forall (i : ι), Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)} [_inst_4 : DecidableEq.{succ u3} ι] [_inst_5 : Finite.{succ u3} ι], Eq.{max (succ u3) (succ u1)} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (iSup.{max u3 u1, succ u3} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (ConditionallyCompleteLattice.toSupSet.{max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (CompleteLattice.toConditionallyCompleteLattice.{max u3 u1} (Submodule.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (Submodule.completeLattice.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))))) ι (fun (i : ι) => Submodule.map.{u2, u2, u1, max u3 u1, max u3 u1} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomSurjective.ids.{u2} R _inst_1) (LinearMap.{u2, u2, u1, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.semilinearMapClass.{u2, u2, u1, max u3 u1} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (LinearMap.single.{u2, u3, u1} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) (p i))) (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (Set.univ.{u3} ι) p)
Case conversion may be inaccurate. Consider using '#align submodule.supr_map_single Submodule.iSup_map_singleₓ'. -/
theorem iSup_map_single [DecidableEq ι] [Finite ι] :
    (⨆ i, map (LinearMap.single i : φ i →ₗ[R] ∀ i, φ i) (p i)) = pi Set.univ p :=
  by
  cases nonempty_fintype ι
  refine' (iSup_le fun i => _).antisymm _
  · rintro _ ⟨x, hx : x ∈ p i, rfl⟩ j -
    rcases em (j = i) with (rfl | hj) <;> simp [*]
  · intro x hx
    rw [← Finset.univ_sum_single x]
    exact sum_mem_supr fun i => mem_map_of_mem (hx i trivial)
#align submodule.supr_map_single Submodule.iSup_map_single

/- warning: submodule.le_comap_single_pi -> Submodule.le_comap_single_pi is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} ι] (p : forall (i : ι), Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) {i : ι}, LE.le.{u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Preorder.toHasLe.{u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (PartialOrder.toPreorder.{u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (SetLike.partialOrder.{u3, u3} (Submodule.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (φ i) (Submodule.setLike.{u1, u3} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i))))) (p i) (Submodule.comap.{u1, u1, u3, max u2 u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.semilinearMapClass.{u1, u1, u3, max u2 u3} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.single.{u1, u2, u3} R ι _inst_1 φ (fun {i : ι} => _inst_2 i) (fun {i : ι} => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) (Submodule.pi.{u1, u2, u3} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (Set.univ.{u2} ι) p))
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u3} ι] (p : forall (i : ι), Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) {i : ι}, LE.le.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Preorder.toLE.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submodule.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)) (Submodule.completeLattice.{u2, u1} R (φ i) _inst_1 (_inst_2 i) (_inst_3 i)))))) (p i) (Submodule.comap.{u2, u2, u1, max u1 u3, max u3 u1} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (LinearMap.{u2, u2, u1, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (φ i) (forall (i : ι), φ i) (_inst_2 i) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearMap.semilinearMapClass.{u2, u2, u1, max u3 u1} R R (φ i) (forall (i : ι), φ i) _inst_1 _inst_1 (_inst_2 i) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (LinearMap.single.{u2, u3, u1} R ι _inst_1 φ (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (a : ι) (b : ι) => _inst_4 a b) i) (Submodule.pi.{u2, u3, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (Set.univ.{u3} ι) p))
Case conversion may be inaccurate. Consider using '#align submodule.le_comap_single_pi Submodule.le_comap_single_piₓ'. -/
theorem le_comap_single_pi [DecidableEq ι] (p : ∀ i, Submodule R (φ i)) {i} :
    p i ≤ Submodule.comap (LinearMap.single i : φ i →ₗ[R] _) (Submodule.pi Set.univ p) :=
  by
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_pi]
  rintro j -
  by_cases h : j = i
  · rwa [h, LinearMap.coe_single, Pi.single_eq_same]
  · rw [LinearMap.coe_single, Pi.single_eq_of_ne h]
    exact (p j).zero_mem
#align submodule.le_comap_single_pi Submodule.le_comap_single_pi

end Submodule

namespace LinearEquiv

variable [Semiring R] {φ ψ χ : ι → Type _} [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

variable [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)]

variable [∀ i, AddCommMonoid (χ i)] [∀ i, Module R (χ i)]

#print LinearEquiv.piCongrRight /-
/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.

This is `equiv.Pi_congr_right` as a `linear_equiv` -/
@[simps apply]
def piCongrRight (e : ∀ i, φ i ≃ₗ[R] ψ i) : (∀ i, φ i) ≃ₗ[R] ∀ i, ψ i :=
  {
    AddEquiv.piCongrRight fun j =>
      (e j).toAddEquiv with
    toFun := fun f i => e i (f i)
    invFun := fun f i => (e i).symm (f i)
    map_smul' := fun c f => by
      ext
      simp }
#align linear_equiv.Pi_congr_right LinearEquiv.piCongrRight
-/

/- warning: linear_equiv.Pi_congr_right_refl -> LinearEquiv.piCongrRight_refl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)], Eq.{succ (max u2 u3)} (LinearEquiv.{u1, u1, max u2 u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (forall (i : ι), φ i) (forall (i : ι), φ i) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearEquiv.piCongrRight.{u1, u2, u3, u3} R ι _inst_1 (fun (j : ι) => φ j) (fun (j : ι) => φ j) (fun (j : ι) => _inst_2 j) (fun (j : ι) => _inst_3 j) (fun (j : ι) => _inst_2 j) (fun (j : ι) => _inst_3 j) (fun (j : ι) => LinearEquiv.refl.{u1, u3} R (φ j) _inst_1 (_inst_2 j) (_inst_3 j))) (LinearEquiv.refl.{u1, max u2 u3} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u2} R] {φ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u1} (φ i)] [_inst_3 : forall (i : ι), Module.{u2, u1} R (φ i) _inst_1 (_inst_2 i)], Eq.{max (succ u3) (succ u1)} (LinearEquiv.{u2, u2, max u3 u1, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) (forall (i : ι), φ i) (forall (i : ι), φ i) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearEquiv.piCongrRight.{u2, u3, u1, u1} R ι _inst_1 (fun (j : ι) => φ j) (fun (j : ι) => φ j) (fun (j : ι) => _inst_2 j) (fun (j : ι) => _inst_3 j) (fun (j : ι) => _inst_2 j) (fun (j : ι) => _inst_3 j) (fun (j : ι) => LinearEquiv.refl.{u2, u1} R (φ j) _inst_1 (_inst_2 j) (_inst_3 j))) (LinearEquiv.refl.{u2, max u3 u1} R (forall (i : ι), φ i) _inst_1 (Pi.addCommMonoid.{u3, u1} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u3, u1, u2} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))
Case conversion may be inaccurate. Consider using '#align linear_equiv.Pi_congr_right_refl LinearEquiv.piCongrRight_reflₓ'. -/
@[simp]
theorem piCongrRight_refl : (piCongrRight fun j => refl R (φ j)) = refl _ _ :=
  rfl
#align linear_equiv.Pi_congr_right_refl LinearEquiv.piCongrRight_refl

/- warning: linear_equiv.Pi_congr_right_symm -> LinearEquiv.piCongrRight_symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R] {φ : ι -> Type.{u3}} {ψ : ι -> Type.{u4}} [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (φ i)] [_inst_3 : forall (i : ι), Module.{u1, u3} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : forall (i : ι), AddCommMonoid.{u4} (ψ i)] [_inst_5 : forall (i : ι), Module.{u1, u4} R (ψ i) _inst_1 (_inst_4 i)] (e : forall (i : ι), LinearEquiv.{u1, u1, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (φ i) (ψ i) (_inst_2 i) (_inst_4 i) (_inst_3 i) (_inst_5 i)), Eq.{max (succ (max u2 u4)) (succ (max u2 u3))} (LinearEquiv.{u1, u1, max u2 u4, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (forall (i : ι), ψ i) (forall (i : ι), φ i) (Pi.addCommMonoid.{u2, u4} ι (fun (i : ι) => ψ i) (fun (i : ι) => _inst_4 i)) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u2, u4, u1} ι (fun (i : ι) => ψ i) R _inst_1 (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearEquiv.symm.{u1, u1, max u2 u3, max u2 u4} R R (forall (i : ι), φ i) (forall (i : ι), ψ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.addCommMonoid.{u2, u4} ι (fun (i : ι) => ψ i) (fun (i : ι) => _inst_4 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Pi.module.{u2, u4, u1} ι (fun (i : ι) => ψ i) R _inst_1 (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (LinearEquiv.piCongrRight.{u1, u2, u3, u4} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => ψ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) e)) (LinearEquiv.piCongrRight.{u1, u2, u4, u3} R ι _inst_1 (fun (i : ι) => ψ i) (fun (i : ι) => φ i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => LinearEquiv.symm.{u1, u1, u3, u4} R R (φ i) (ψ i) _inst_1 _inst_1 (_inst_2 i) (_inst_4 i) (_inst_3 i) (_inst_5 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (e i)))
but is expected to have type
  forall {R : Type.{u3}} {ι : Type.{u4}} [_inst_1 : Semiring.{u3} R] {φ : ι -> Type.{u2}} {ψ : ι -> Type.{u1}} [_inst_2 : forall (i : ι), AddCommMonoid.{u2} (φ i)] [_inst_3 : forall (i : ι), Module.{u3, u2} R (φ i) _inst_1 (_inst_2 i)] [_inst_4 : forall (i : ι), AddCommMonoid.{u1} (ψ i)] [_inst_5 : forall (i : ι), Module.{u3, u1} R (ψ i) _inst_1 (_inst_4 i)] (e : forall (i : ι), LinearEquiv.{u3, u3, u2, u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (φ i) (ψ i) (_inst_2 i) (_inst_4 i) (_inst_3 i) (_inst_5 i)), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (LinearEquiv.{u3, u3, max u4 u1, max u4 u2} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (forall (i : ι), ψ i) (forall (i : ι), φ i) (Pi.addCommMonoid.{u4, u1} ι (fun (i : ι) => ψ i) (fun (i : ι) => _inst_4 i)) (Pi.addCommMonoid.{u4, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.module.{u4, u1, u3} ι (fun (i : ι) => ψ i) R _inst_1 (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) (Pi.module.{u4, u2, u3} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (LinearEquiv.symm.{u3, u3, max u4 u2, max u4 u1} R R (forall (i : ι), φ i) (forall (i : ι), ψ i) _inst_1 _inst_1 (Pi.addCommMonoid.{u4, u2} ι (fun (i : ι) => φ i) (fun (i : ι) => _inst_2 i)) (Pi.addCommMonoid.{u4, u1} ι (fun (i : ι) => ψ i) (fun (i : ι) => _inst_4 i)) (Pi.module.{u4, u2, u3} ι (fun (i : ι) => φ i) R _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Pi.module.{u4, u1, u3} ι (fun (i : ι) => ψ i) R _inst_1 (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (LinearEquiv.piCongrRight.{u3, u4, u2, u1} R ι _inst_1 (fun (i : ι) => φ i) (fun (i : ι) => ψ i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) e)) (LinearEquiv.piCongrRight.{u3, u4, u1, u2} R ι _inst_1 (fun (i : ι) => ψ i) (fun (i : ι) => φ i) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => LinearEquiv.symm.{u3, u3, u2, u1} R R (φ i) (ψ i) _inst_1 _inst_1 (_inst_2 i) (_inst_4 i) (_inst_3 i) (_inst_5 i) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (e i)))
Case conversion may be inaccurate. Consider using '#align linear_equiv.Pi_congr_right_symm LinearEquiv.piCongrRight_symmₓ'. -/
@[simp]
theorem piCongrRight_symm (e : ∀ i, φ i ≃ₗ[R] ψ i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl
#align linear_equiv.Pi_congr_right_symm LinearEquiv.piCongrRight_symm

/- warning: linear_equiv.Pi_congr_right_trans -> LinearEquiv.piCongrRight_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.Pi_congr_right_trans LinearEquiv.piCongrRight_transₓ'. -/
@[simp]
theorem piCongrRight_trans (e : ∀ i, φ i ≃ₗ[R] ψ i) (f : ∀ i, ψ i ≃ₗ[R] χ i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl
#align linear_equiv.Pi_congr_right_trans LinearEquiv.piCongrRight_trans

variable (R φ)

#print LinearEquiv.piCongrLeft' /-
/-- Transport dependent functions through an equivalence of the base space.

This is `equiv.Pi_congr_left'` as a `linear_equiv`. -/
@[simps (config := { simpRhs := true })]
def piCongrLeft' (e : ι ≃ ι') : (∀ i', φ i') ≃ₗ[R] ∀ i, φ <| e.symm i :=
  { Equiv.piCongrLeft' φ e with
    map_add' := fun x y => rfl
    map_smul' := fun x y => rfl }
#align linear_equiv.Pi_congr_left' LinearEquiv.piCongrLeft'
-/

#print LinearEquiv.piCongrLeft /-
/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".

This is `equiv.Pi_congr_left` as a `linear_equiv` -/
def piCongrLeft (e : ι' ≃ ι) : (∀ i', φ (e i')) ≃ₗ[R] ∀ i, φ i :=
  (piCongrLeft' R φ e.symm).symm
#align linear_equiv.Pi_congr_left LinearEquiv.piCongrLeft
-/

/- warning: linear_equiv.pi_option_equiv_prod -> LinearEquiv.piOptionEquivProd is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {ι : Type.{u2}} {M : (Option.{u2} ι) -> Type.{u3}} [_inst_8 : forall (i : Option.{u2} ι), AddCommGroup.{u3} (M i)] [_inst_9 : forall (i : Option.{u2} ι), Module.{u1, u3} R (M i) _inst_1 (AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_8 i))], LinearEquiv.{u1, u1, max u2 u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (forall (i : Option.{u2} ι), M i) (Prod.{u3, max u2 u3} (M (Option.none.{u2} ι)) (forall (i : ι), M (Option.some.{u2} ι i))) (Pi.addCommMonoid.{u2, u3} (Option.{u2} ι) (fun (i : Option.{u2} ι) => M i) (fun (i : Option.{u2} ι) => AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_8 i))) (Prod.addCommMonoid.{u3, max u2 u3} (M (Option.none.{u2} ι)) (forall (i : ι), M (Option.some.{u2} ι i)) (AddCommGroup.toAddCommMonoid.{u3} (M (Option.none.{u2} ι)) (_inst_8 (Option.none.{u2} ι))) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => M (Option.some.{u2} ι i)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (M (Option.some.{u2} ι i)) (_inst_8 (Option.some.{u2} ι i))))) (Pi.module.{u2, u3, u1} (Option.{u2} ι) (fun (i : Option.{u2} ι) => M i) R _inst_1 (fun (i : Option.{u2} ι) => AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_8 i)) (fun (i : Option.{u2} ι) => _inst_9 i)) (Prod.module.{u1, u3, max u2 u3} R (M (Option.none.{u2} ι)) (forall (i : ι), M (Option.some.{u2} ι i)) _inst_1 (AddCommGroup.toAddCommMonoid.{u3} (M (Option.none.{u2} ι)) (_inst_8 (Option.none.{u2} ι))) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => M (Option.some.{u2} ι i)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (M (Option.some.{u2} ι i)) (_inst_8 (Option.some.{u2} ι i)))) (_inst_9 (Option.none.{u2} ι)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => M (Option.some.{u2} ι i)) R _inst_1 (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (M (Option.some.{u2} ι i)) (_inst_8 (Option.some.{u2} ι i))) (fun (i : ι) => _inst_9 (Option.some.{u2} ι i))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {ι : Type.{u2}} {M : (Option.{u2} ι) -> Type.{u3}} [_inst_8 : forall (i : Option.{u2} ι), AddCommGroup.{u3} (M i)] [_inst_9 : forall (i : Option.{u2} ι), Module.{u1, u3} R (M i) _inst_1 (AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_8 i))], LinearEquiv.{u1, u1, max u2 u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (forall (i : Option.{u2} ι), M i) (Prod.{u3, max u2 u3} (M (Option.none.{u2} ι)) (forall (i : ι), M (Option.some.{u2} ι i))) (Pi.addCommMonoid.{u2, u3} (Option.{u2} ι) (fun (i : Option.{u2} ι) => M i) (fun (i : Option.{u2} ι) => AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_8 i))) (Prod.instAddCommMonoidSum.{u3, max u2 u3} (M (Option.none.{u2} ι)) (forall (i : ι), M (Option.some.{u2} ι i)) (AddCommGroup.toAddCommMonoid.{u3} (M (Option.none.{u2} ι)) (_inst_8 (Option.none.{u2} ι))) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => M (Option.some.{u2} ι i)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (M (Option.some.{u2} ι i)) (_inst_8 (Option.some.{u2} ι i))))) (Pi.module.{u2, u3, u1} (Option.{u2} ι) (fun (i : Option.{u2} ι) => M i) R _inst_1 (fun (i : Option.{u2} ι) => AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_8 i)) (fun (i : Option.{u2} ι) => _inst_9 i)) (Prod.module.{u1, u3, max u2 u3} R (M (Option.none.{u2} ι)) (forall (i : ι), M (Option.some.{u2} ι i)) _inst_1 (AddCommGroup.toAddCommMonoid.{u3} (M (Option.none.{u2} ι)) (_inst_8 (Option.none.{u2} ι))) (Pi.addCommMonoid.{u2, u3} ι (fun (i : ι) => M (Option.some.{u2} ι i)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (M (Option.some.{u2} ι i)) (_inst_8 (Option.some.{u2} ι i)))) (_inst_9 (Option.none.{u2} ι)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => M (Option.some.{u2} ι i)) R _inst_1 (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (M (Option.some.{u2} ι i)) (_inst_8 (Option.some.{u2} ι i))) (fun (i : ι) => _inst_9 (Option.some.{u2} ι i))))
Case conversion may be inaccurate. Consider using '#align linear_equiv.pi_option_equiv_prod LinearEquiv.piOptionEquivProdₓ'. -/
/-- This is `equiv.pi_option_equiv_prod` as a `linear_equiv` -/
def piOptionEquivProd {ι : Type _} {M : Option ι → Type _} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] : (∀ i : Option ι, M i) ≃ₗ[R] M none × ∀ i : ι, M (some i) :=
  { Equiv.piOptionEquivProd with
    map_add' := by simp [Function.funext_iff]
    map_smul' := by simp [Function.funext_iff] }
#align linear_equiv.pi_option_equiv_prod LinearEquiv.piOptionEquivProd

variable (ι R M) (S : Type _) [Fintype ι] [DecidableEq ι] [Semiring S] [AddCommMonoid M]
  [Module R M] [Module S M] [SMulCommClass R S M]

#print LinearEquiv.piRing /-
/-- Linear equivalence between linear functions `Rⁿ → M` and `Mⁿ`. The spaces `Rⁿ` and `Mⁿ`
are represented as `ι → R` and `ι → M`, respectively, where `ι` is a finite type.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings]. -/
def piRing : ((ι → R) →ₗ[R] M) ≃ₗ[S] ι → M :=
  (LinearMap.lsum R (fun i : ι => R) S).symm.trans
    (piCongrRight fun i => LinearMap.ringLmapEquivSelf R S M)
#align linear_equiv.pi_ring LinearEquiv.piRing
-/

variable {ι R M}

/- warning: linear_equiv.pi_ring_apply -> LinearEquiv.piRing_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.pi_ring_apply LinearEquiv.piRing_applyₓ'. -/
@[simp]
theorem piRing_apply (f : (ι → R) →ₗ[R] M) (i : ι) : piRing R M ι S f i = f (Pi.single i 1) :=
  rfl
#align linear_equiv.pi_ring_apply LinearEquiv.piRing_apply

/- warning: linear_equiv.pi_ring_symm_apply -> LinearEquiv.piRing_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.pi_ring_symm_apply LinearEquiv.piRing_symm_applyₓ'. -/
@[simp]
theorem piRing_symm_apply (f : ι → M) (g : ι → R) : (piRing R M ι S).symm f g = ∑ i, g i • f i := by
  simp [pi_ring, LinearMap.lsum]
#align linear_equiv.pi_ring_symm_apply LinearEquiv.piRing_symm_apply

/- warning: linear_equiv.sum_arrow_lequiv_prod_arrow -> LinearEquiv.sumArrowLequivProdArrow is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) (R : Type.{u3}) (M : Type.{u4}) [_inst_15 : Semiring.{u3} R] [_inst_16 : AddCommMonoid.{u4} M] [_inst_17 : Module.{u3, u4} R M _inst_15 _inst_16], LinearEquiv.{u3, u3, max (max u1 u2) u4, max (max u1 u4) u2 u4} R R _inst_15 _inst_15 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_15)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_15)) (RingHomInvPair.ids.{u3} R _inst_15) (RingHomInvPair.ids.{u3} R _inst_15) ((Sum.{u1, u2} α β) -> M) (Prod.{max u1 u4, max u2 u4} (α -> M) (β -> M)) (Pi.addCommMonoid.{max u1 u2, u4} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => M) (fun (i : Sum.{u1, u2} α β) => _inst_16)) (Prod.addCommMonoid.{max u1 u4, max u2 u4} (α -> M) (β -> M) (Pi.addCommMonoid.{u1, u4} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_16)) (Pi.addCommMonoid.{u2, u4} β (fun (ᾰ : β) => M) (fun (i : β) => _inst_16))) (Pi.Function.module.{max u1 u2, u3, u4} (Sum.{u1, u2} α β) R M _inst_15 _inst_16 _inst_17) (Prod.module.{u3, max u1 u4, max u2 u4} R (α -> M) (β -> M) _inst_15 (Pi.addCommMonoid.{u1, u4} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_16)) (Pi.addCommMonoid.{u2, u4} β (fun (ᾰ : β) => M) (fun (i : β) => _inst_16)) (Pi.Function.module.{u1, u3, u4} α R M _inst_15 _inst_16 _inst_17) (Pi.Function.module.{u2, u3, u4} β R M _inst_15 _inst_16 _inst_17))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) (R : Type.{u3}) (M : Type.{u4}) [_inst_15 : Semiring.{u3} R] [_inst_16 : AddCommMonoid.{u4} M] [_inst_17 : Module.{u3, u4} R M _inst_15 _inst_16], LinearEquiv.{u3, u3, max (max u1 u2) u4, max (max u2 u4) u1 u4} R R _inst_15 _inst_15 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_15)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_15)) (RingHomInvPair.ids.{u3} R _inst_15) (RingHomInvPair.ids.{u3} R _inst_15) ((Sum.{u1, u2} α β) -> M) (Prod.{max u1 u4, max u2 u4} (α -> M) (β -> M)) (Pi.addCommMonoid.{max u1 u2, u4} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => M) (fun (i : Sum.{u1, u2} α β) => _inst_16)) (Prod.instAddCommMonoidSum.{max u1 u4, max u2 u4} (α -> M) (β -> M) (Pi.addCommMonoid.{u1, u4} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_16)) (Pi.addCommMonoid.{u2, u4} β (fun (ᾰ : β) => M) (fun (i : β) => _inst_16))) (Pi.module.{max u1 u2, u4, u3} (Sum.{u1, u2} α β) (fun (a._@.Mathlib.LinearAlgebra.Pi._hyg.7045 : Sum.{u1, u2} α β) => M) R _inst_15 (fun (i : Sum.{u1, u2} α β) => _inst_16) (fun (i : Sum.{u1, u2} α β) => _inst_17)) (Prod.module.{u3, max u1 u4, max u2 u4} R (α -> M) (β -> M) _inst_15 (Pi.addCommMonoid.{u1, u4} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_16)) (Pi.addCommMonoid.{u2, u4} β (fun (ᾰ : β) => M) (fun (i : β) => _inst_16)) (Pi.module.{u1, u4, u3} α (fun (a._@.Mathlib.LinearAlgebra.Pi._hyg.7055 : α) => M) R _inst_15 (fun (i : α) => _inst_16) (fun (i : α) => _inst_17)) (Pi.module.{u2, u4, u3} β (fun (a._@.Mathlib.LinearAlgebra.Pi._hyg.7060 : β) => M) R _inst_15 (fun (i : β) => _inst_16) (fun (i : β) => _inst_17)))
Case conversion may be inaccurate. Consider using '#align linear_equiv.sum_arrow_lequiv_prod_arrow LinearEquiv.sumArrowLequivProdArrowₓ'. -/
-- TODO additive version?
/-- `equiv.sum_arrow_equiv_prod_arrow` as a linear equivalence.
-/
def sumArrowLequivProdArrow (α β R M : Type _) [Semiring R] [AddCommMonoid M] [Module R M] :
    (Sum α β → M) ≃ₗ[R] (α → M) × (β → M) :=
  {
    Equiv.sumArrowEquivProdArrow α β
      M with
    map_add' := by
      intro f g
      ext <;> rfl
    map_smul' := by
      intro r f
      ext <;> rfl }
#align linear_equiv.sum_arrow_lequiv_prod_arrow LinearEquiv.sumArrowLequivProdArrow

/- warning: linear_equiv.sum_arrow_lequiv_prod_arrow_apply_fst -> LinearEquiv.sumArrowLequivProdArrow_apply_fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.sum_arrow_lequiv_prod_arrow_apply_fst LinearEquiv.sumArrowLequivProdArrow_apply_fstₓ'. -/
@[simp]
theorem sumArrowLequivProdArrow_apply_fst {α β} (f : Sum α β → M) (a : α) :
    (sumArrowLequivProdArrow α β R M f).1 a = f (Sum.inl a) :=
  rfl
#align linear_equiv.sum_arrow_lequiv_prod_arrow_apply_fst LinearEquiv.sumArrowLequivProdArrow_apply_fst

/- warning: linear_equiv.sum_arrow_lequiv_prod_arrow_apply_snd -> LinearEquiv.sumArrowLequivProdArrow_apply_snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.sum_arrow_lequiv_prod_arrow_apply_snd LinearEquiv.sumArrowLequivProdArrow_apply_sndₓ'. -/
@[simp]
theorem sumArrowLequivProdArrow_apply_snd {α β} (f : Sum α β → M) (b : β) :
    (sumArrowLequivProdArrow α β R M f).2 b = f (Sum.inr b) :=
  rfl
#align linear_equiv.sum_arrow_lequiv_prod_arrow_apply_snd LinearEquiv.sumArrowLequivProdArrow_apply_snd

/- warning: linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inl -> LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inl LinearEquiv.sumArrowLequivProdArrow_symm_apply_inlₓ'. -/
@[simp]
theorem sumArrowLequivProdArrow_symm_apply_inl {α β} (f : α → M) (g : β → M) (a : α) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inl a) = f a :=
  rfl
#align linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inl LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl

/- warning: linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inr -> LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inr LinearEquiv.sumArrowLequivProdArrow_symm_apply_inrₓ'. -/
@[simp]
theorem sumArrowLequivProdArrow_symm_apply_inr {α β} (f : α → M) (g : β → M) (b : β) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inr b) = g b :=
  rfl
#align linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inr LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr

#print LinearEquiv.funUnique /-
/-- If `ι` has a unique element, then `ι → M` is linearly equivalent to `M`. -/
@[simps (config :=
      { simpRhs := true
        fullyApplied := false })]
def funUnique (ι R M : Type _) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (ι → M) ≃ₗ[R] M :=
  { Equiv.funUnique ι M with
    map_add' := fun f g => rfl
    map_smul' := fun c f => rfl }
#align linear_equiv.fun_unique LinearEquiv.funUnique
-/

variable (R M)

/- warning: linear_equiv.pi_fin_two -> LinearEquiv.piFinTwo is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] (M : (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> Type.{u2}) [_inst_15 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))), AddCommMonoid.{u2} (M i)] [_inst_16 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))), Module.{u1, u2} R (M i) _inst_1 (_inst_15 i)], LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (forall (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))), M i) (Prod.{u2, u2} (M (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_1))))) (M (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_2)))))) (Pi.addCommMonoid.{0, u2} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => M i) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => _inst_15 i)) (Prod.addCommMonoid.{u2, u2} (M (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_1))))) (M (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_2))))) (_inst_15 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_1))))) (_inst_15 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_2)))))) (Pi.module.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => M i) R _inst_1 (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => _inst_15 i) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => _inst_16 i)) (Prod.module.{u1, u2, u2} R (M (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_1))))) (M (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_2))))) _inst_1 (_inst_15 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_1))))) (_inst_15 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_2))))) (_inst_16 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_1))))) (_inst_16 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) LinearEquiv.piFinTwo._proof_2))))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] (M : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> Type.{u2}) [_inst_15 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), AddCommMonoid.{u2} (M i)] [_inst_16 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), Module.{u1, u2} R (M i) _inst_1 (_inst_15 i)], LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (forall (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), M i) (Prod.{u2, u2} (M (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (M (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (Pi.addCommMonoid.{0, u2} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => M i) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_15 i)) (Prod.instAddCommMonoidSum.{u2, u2} (M (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (M (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_15 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_15 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (Pi.module.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => M i) R _inst_1 (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_15 i) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_16 i)) (Prod.module.{u1, u2, u2} R (M (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (M (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) _inst_1 (_inst_15 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_15 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_16 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_16 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align linear_equiv.pi_fin_two LinearEquiv.piFinTwoₓ'. -/
/-- Linear equivalence between dependent functions `Π i : fin 2, M i` and `M 0 × M 1`. -/
@[simps (config :=
      { simpRhs := true
        fullyApplied := false })]
def piFinTwo (M : Fin 2 → Type v) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (∀ i, M i) ≃ₗ[R] M 0 × M 1 :=
  { piFinTwoEquiv M with
    map_add' := fun f g => rfl
    map_smul' := fun c f => rfl }
#align linear_equiv.pi_fin_two LinearEquiv.piFinTwo

/- warning: linear_equiv.fin_two_arrow -> LinearEquiv.finTwoArrow is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_11 : AddCommMonoid.{u2} M] [_inst_12 : Module.{u1, u2} R M _inst_1 _inst_11], LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> M) (Prod.{u2, u2} M M) (Pi.addCommMonoid.{0, u2} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => M) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => _inst_11)) (Prod.addCommMonoid.{u2, u2} M M _inst_11 _inst_11) (Pi.Function.module.{0, u1, u2} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R M _inst_1 _inst_11 _inst_12) (Prod.module.{u1, u2, u2} R M M _inst_1 _inst_11 _inst_11 _inst_12 _inst_12)
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_11 : AddCommMonoid.{u2} M] [_inst_12 : Module.{u1, u2} R M _inst_1 _inst_11], LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> M) (Prod.{u2, u2} M M) (Pi.addCommMonoid.{0, u2} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => M) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_11)) (Prod.instAddCommMonoidSum.{u2, u2} M M _inst_11 _inst_11) (Pi.module.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a._@.Mathlib.LinearAlgebra.Pi._hyg.8590 : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => M) R _inst_1 (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_11) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_12)) (Prod.module.{u1, u2, u2} R M M _inst_1 _inst_11 _inst_11 _inst_12 _inst_12)
Case conversion may be inaccurate. Consider using '#align linear_equiv.fin_two_arrow LinearEquiv.finTwoArrowₓ'. -/
/-- Linear equivalence between vectors in `M² = fin 2 → M` and `M × M`. -/
@[simps (config :=
      { simpRhs := true
        fullyApplied := false })]
def finTwoArrow : (Fin 2 → M) ≃ₗ[R] M × M :=
  { finTwoArrowEquiv M, piFinTwo R fun _ => M with }
#align linear_equiv.fin_two_arrow LinearEquiv.finTwoArrow

end LinearEquiv

section Extend

variable (R) {η : Type x} [Semiring R] (s : ι → η)

#print Function.ExtendByZero.linearMap /-
/-- `function.extend s f 0` as a bundled linear map. -/
@[simps]
noncomputable def Function.ExtendByZero.linearMap : (ι → R) →ₗ[R] η → R :=
  {
    Function.ExtendByZero.hom R
      s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }
#align function.extend_by_zero.linear_map Function.ExtendByZero.linearMap
-/

end Extend

/-! ### Bundled versions of `matrix.vec_cons` and `matrix.vec_empty`

The idea of these definitions is to be able to define a map as `x ↦ ![f₁ x, f₂ x, f₃ x]`, where
`f₁ f₂ f₃` are already linear maps, as `f₁.vec_cons $ f₂.vec_cons $ f₃.vec_cons $ vec_empty`.

While the same thing could be achieved using `linear_map.pi ![f₁, f₂, f₃]`, this is not
definitionally equal to the result using `linear_map.vec_cons`, as `fin.cases` and function
application do not commute definitionally.

Versions for when `f₁ f₂ f₃` are bilinear maps are also provided.

-/


section Fin

section Semiring

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

#print LinearMap.vecEmpty /-
/-- The linear map defeq to `matrix.vec_empty` -/
def LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃
    where
  toFun m := Matrix.vecEmpty
  map_add' x y := Subsingleton.elim _ _
  map_smul' r x := Subsingleton.elim _ _
#align linear_map.vec_empty LinearMap.vecEmpty
-/

/- warning: linear_map.vec_empty_apply -> LinearMap.vecEmpty_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {M₃ : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_4 : AddCommMonoid.{u3} M₃] [_inst_5 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_7 : Module.{u1, u3} R M₃ _inst_1 _inst_4] (m : M), Eq.{succ u3} ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> M₃) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> M₃) _inst_2 (Pi.addCommMonoid.{0, u3} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => M₃) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => _inst_4)) _inst_5 (Pi.Function.module.{0, u1, u3} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) R M₃ _inst_1 _inst_4 _inst_7)) (fun (_x : LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> M₃) _inst_2 (Pi.addCommMonoid.{0, u3} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => M₃) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => _inst_4)) _inst_5 (Pi.Function.module.{0, u1, u3} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) R M₃ _inst_1 _inst_4 _inst_7)) => M -> (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> M₃) (LinearMap.hasCoeToFun.{u1, u1, u2, u3} R R M ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> M₃) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{0, u3} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => M₃) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => _inst_4)) _inst_5 (Pi.Function.module.{0, u1, u3} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) R M₃ _inst_1 _inst_4 _inst_7) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.vecEmpty.{u1, u2, u3} R M M₃ _inst_1 _inst_2 _inst_4 _inst_5 _inst_7) m) (Matrix.vecEmpty.{u3} M₃)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {M₃ : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_4 : AddCommMonoid.{u3} M₃] [_inst_5 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_7 : Module.{u1, u3} R M₃ _inst_1 _inst_4] (m : M), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> M₃) m) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> M₃) _inst_2 (Pi.addCommMonoid.{0, u3} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (a._@.Mathlib.LinearAlgebra.Pi._hyg.8849 : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => M₃) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => _inst_4)) _inst_5 (Pi.module.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (a._@.Mathlib.LinearAlgebra.Pi._hyg.8849 : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => M₃) R _inst_1 (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => _inst_4) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => _inst_7))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> M₃) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u2, u3} R R M ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> M₃) _inst_1 _inst_1 _inst_2 (Pi.addCommMonoid.{0, u3} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => M₃) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => _inst_4)) _inst_5 (Pi.module.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (a._@.Mathlib.LinearAlgebra.Pi._hyg.8849 : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => M₃) R _inst_1 (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => _inst_4) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => _inst_7)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (LinearMap.vecEmpty.{u1, u2, u3} R M M₃ _inst_1 _inst_2 _inst_4 _inst_5 _inst_7) m) (Matrix.vecEmpty.{u3} M₃)
Case conversion may be inaccurate. Consider using '#align linear_map.vec_empty_apply LinearMap.vecEmpty_applyₓ'. -/
@[simp]
theorem LinearMap.vecEmpty_apply (m : M) : (LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃) m = ![] :=
  rfl
#align linear_map.vec_empty_apply LinearMap.vecEmpty_apply

#print LinearMap.vecCons /-
/-- A linear map into `fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`fin n → M₃`. -/
def LinearMap.vecCons {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) : M →ₗ[R] Fin n.succ → M₂
    where
  toFun m := Matrix.vecCons (f m) (g m)
  map_add' x y := by rw [f.map_add, g.map_add, Matrix.cons_add_cons (f x)]
  map_smul' c x := by rw [f.map_smul, g.map_smul, RingHom.id_apply, Matrix.smul_cons c (f x)]
#align linear_map.vec_cons LinearMap.vecCons
-/

/- warning: linear_map.vec_cons_apply -> LinearMap.vecCons_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.vec_cons_apply LinearMap.vecCons_applyₓ'. -/
@[simp]
theorem LinearMap.vecCons_apply {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) (m : M) :
    f.vecCons g m = Matrix.vecCons (f m) (g m) :=
  rfl
#align linear_map.vec_cons_apply LinearMap.vecCons_apply

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

#print LinearMap.vecEmpty₂ /-
/-- The empty bilinear map defeq to `matrix.vec_empty` -/
@[simps]
def LinearMap.vecEmpty₂ : M →ₗ[R] M₂ →ₗ[R] Fin 0 → M₃
    where
  toFun m := LinearMap.vecEmpty
  map_add' x y := LinearMap.ext fun z => Subsingleton.elim _ _
  map_smul' r x := LinearMap.ext fun z => Subsingleton.elim _ _
#align linear_map.vec_empty₂ LinearMap.vecEmpty₂
-/

#print LinearMap.vecCons₂ /-
/-- A bilinear map into `fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`fin n → M₃` -/
@[simps]
def LinearMap.vecCons₂ {n} (f : M →ₗ[R] M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂ →ₗ[R] Fin n → M₃) :
    M →ₗ[R] M₂ →ₗ[R] Fin n.succ → M₃
    where
  toFun m := LinearMap.vecCons (f m) (g m)
  map_add' x y :=
    LinearMap.ext fun z => by
      simp only [f.map_add, g.map_add, LinearMap.add_apply, LinearMap.vecCons_apply,
        Matrix.cons_add_cons (f x z)]
  map_smul' r x := LinearMap.ext fun z => by simp [Matrix.smul_cons r (f x z)]
#align linear_map.vec_cons₂ LinearMap.vecCons₂
-/

end CommSemiring

end Fin

