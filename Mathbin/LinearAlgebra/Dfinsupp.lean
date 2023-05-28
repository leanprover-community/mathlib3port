/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau

! This file was ported from Lean 3 source module linear_algebra.dfinsupp
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.ToDfinsupp
import Mathbin.LinearAlgebra.Basis

/-!
# Properties of the module `Π₀ i, M i`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `data.dfinsupp`.

In this file we define `linear_map` versions of various maps:

* `dfinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lmk s : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `λ f, f i` as a linear map;

* `dfinsupp.lsum`: `dfinsupp.sum` or `dfinsupp.lift_add_hom` as a `linear_map`;

## Implementation notes

This file should try to mirror `linear_algebra.finsupp` where possible. The API of `finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/


variable {ι : Type _} {R : Type _} {S : Type _} {M : ι → Type _} {N : Type _}

variable [dec_ι : DecidableEq ι]

namespace Dfinsupp

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [AddCommMonoid N] [Module R N]

include dec_ι

/- warning: dfinsupp.lmk -> Dfinsupp.lmk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.lmk Dfinsupp.lmkₓ'. -/
/-- `dfinsupp.mk` as a `linear_map`. -/
def lmk (s : Finset ι) : (∀ i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i
    where
  toFun := mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x
#align dfinsupp.lmk Dfinsupp.lmk

/- warning: dfinsupp.lsingle -> Dfinsupp.lsingle is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} [dec_ι : DecidableEq.{succ u1} ι] [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] (i : ι), LinearMap.{u2, u2, u3, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) (_inst_2 i) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} [dec_ι : DecidableEq.{succ u1} ι] [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] (i : ι), LinearMap.{u2, u2, u3, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u3} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_2 i)))) (_inst_2 i) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))
Case conversion may be inaccurate. Consider using '#align dfinsupp.lsingle Dfinsupp.lsingleₓ'. -/
/-- `dfinsupp.single` as a `linear_map` -/
def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
  { Dfinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }
#align dfinsupp.lsingle Dfinsupp.lsingle

/- warning: dfinsupp.lhom_ext -> Dfinsupp.lhom_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.lhom_ext Dfinsupp.lhom_extₓ'. -/
/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
theorem lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i x, φ (single i x) = ψ (single i x)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h
#align dfinsupp.lhom_ext Dfinsupp.lhom_ext

/- warning: dfinsupp.lhom_ext' -> Dfinsupp.lhom_ext' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.lhom_ext' Dfinsupp.lhom_ext'ₓ'. -/
/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After apply this lemma, if `M = R` then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext]
theorem lhom_ext' ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
    φ = ψ :=
  lhom_ext fun i => LinearMap.congr_fun (h i)
#align dfinsupp.lhom_ext' Dfinsupp.lhom_ext'

omit dec_ι

/- warning: dfinsupp.lapply -> Dfinsupp.lapply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] (i : ι), LinearMap.{u2, u2, max u1 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) (M i) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] (i : ι), LinearMap.{u2, u2, max u3 u1, u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u3} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_2 i)))) (M i) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i)
Case conversion may be inaccurate. Consider using '#align dfinsupp.lapply Dfinsupp.lapplyₓ'. -/
/-- Interpret `λ (f : Π₀ i, M i), f i` as a linear map. -/
def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i
    where
  toFun f := f i
  map_add' f g := add_apply f g i
  map_smul' c f := smul_apply c f i
#align dfinsupp.lapply Dfinsupp.lapply

include dec_ι

/- warning: dfinsupp.lmk_apply -> Dfinsupp.lmk_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.lmk_apply Dfinsupp.lmk_applyₓ'. -/
@[simp]
theorem lmk_apply (s : Finset ι) (x) : (lmk s : _ →ₗ[R] Π₀ i, M i) x = mk s x :=
  rfl
#align dfinsupp.lmk_apply Dfinsupp.lmk_apply

/- warning: dfinsupp.lsingle_apply -> Dfinsupp.lsingle_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} [dec_ι : DecidableEq.{succ u1} ι] [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] (i : ι) (x : M i), Eq.{succ (max u1 u3)} (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) (coeFn.{max (succ u3) (succ (max u1 u3)), max (succ u3) (succ (max u1 u3))} (LinearMap.{u2, u2, u3, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) (_inst_2 i) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (fun (_x : LinearMap.{u2, u2, u3, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) (_inst_2 i) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) => (M i) -> (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i)))))) (LinearMap.hasCoeToFun.{u2, u2, u3, max u1 u3} R R (M i) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) _inst_1 _inst_1 (_inst_2 i) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Dfinsupp.lsingle.{u1, u2, u3} ι R (fun (i : ι) => M i) (fun (a : ι) (b : ι) => dec_ι a b) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) i) x) (Dfinsupp.single.{u1, u3} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => dec_ι a b) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i)))) i x)
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u1}} {M : ι -> Type.{u2}} [dec_ι : DecidableEq.{succ u3} ι] [_inst_1 : Semiring.{u1} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u2} (M i)] [_inst_3 : forall (i : ι), Module.{u1, u2} R (M i) _inst_1 (_inst_2 i)] (i : ι) (x : M i), Eq.{max (succ u3) (succ u2)} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M i) => Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) x) (FunLike.coe.{max (succ u3) (succ u2), succ u2, max (succ u3) (succ u2)} (LinearMap.{u1, u1, u2, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (M i) (Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) (_inst_2 i) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i))) (M i) (fun (_x : M i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M i) => Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u2, max u3 u2} R R (M i) (Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) _inst_1 _inst_1 (_inst_2 i) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_3 i) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Dfinsupp.lsingle.{u3, u1, u2} ι R M (fun (a : ι) (b : ι) => dec_ι a b) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) i) x) (Dfinsupp.single.{u3, u2} ι M (fun (a : ι) (b : ι) => dec_ι a b) (fun (i : ι) => AddMonoid.toZero.{u2} (M i) (AddCommMonoid.toAddMonoid.{u2} (M i) (_inst_2 i))) i x)
Case conversion may be inaccurate. Consider using '#align dfinsupp.lsingle_apply Dfinsupp.lsingle_applyₓ'. -/
@[simp]
theorem lsingle_apply (i : ι) (x : M i) : (lsingle i : _ →ₗ[R] _) x = single i x :=
  rfl
#align dfinsupp.lsingle_apply Dfinsupp.lsingle_apply

omit dec_ι

/- warning: dfinsupp.lapply_apply -> Dfinsupp.lapply_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] (i : ι) (f : Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} ((fun (i : ι) => M i) i) (AddMonoid.toAddZeroClass.{u3} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_2 i))))), Eq.{succ u3} (M i) (coeFn.{max (succ (max u1 u3)) (succ u3), max (succ (max u1 u3)) (succ u3)} (LinearMap.{u2, u2, max u1 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) (M i) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i)) (fun (_x : LinearMap.{u2, u2, max u1 u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) (M i) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i)) => (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) -> (M i)) (LinearMap.hasCoeToFun.{u2, u2, max u1 u3, u3} R R (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) (M i) _inst_1 _inst_1 (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Dfinsupp.lapply.{u1, u2, u3} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) i) f) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} ((fun (i : ι) => M i) i) (AddMonoid.toAddZeroClass.{u3} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_2 i))))) (fun (_x : Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} ((fun (i : ι) => M i) i) (AddMonoid.toAddZeroClass.{u3} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_2 i))))) => forall (i : ι), M i) (Dfinsupp.hasCoeToFun.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} ((fun (i : ι) => M i) i) (AddMonoid.toAddZeroClass.{u3} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_2 i))))) f i)
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u1}} {M : ι -> Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u2} (M i)] [_inst_3 : forall (i : ι), Module.{u1, u2} R (M i) _inst_1 (_inst_2 i)] (i : ι) (f : Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) => M i) f) (FunLike.coe.{max (succ u3) (succ u2), max (succ u3) (succ u2), succ u2} (LinearMap.{u1, u1, max u2 u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) (M i) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i)) (Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) (fun (_x : Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) => M i) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, max u3 u2, u2} R R (Dfinsupp.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i)))) (M i) _inst_1 _inst_1 (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (_inst_2 i) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (_inst_3 i) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Dfinsupp.lapply.{u3, u1, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) i) f) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Dfinsupp.{u3, u2} ι (fun (i : ι) => (fun (i : ι) => M i) i) (fun (i : ι) => (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i))) i)) ι (fun (_x : ι) => (fun (i : ι) => (fun (i : ι) => M i) i) _x) (Dfinsupp.funLike.{u3, u2} ι (fun (i : ι) => (fun (i : ι) => M i) i) (fun (i : ι) => (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => M i) i) (_inst_2 i))) i)) f i)
Case conversion may be inaccurate. Consider using '#align dfinsupp.lapply_apply Dfinsupp.lapply_applyₓ'. -/
@[simp]
theorem lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : _ →ₗ[R] _) f = f i :=
  rfl
#align dfinsupp.lapply_apply Dfinsupp.lapply_apply

section Lsum

/- warning: dfinsupp.add_comm_monoid_of_linear_map -> Dfinsupp.addCommMonoidOfLinearMap is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} {N : Type.{u4}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] [_inst_4 : AddCommMonoid.{u4} N] [_inst_5 : Module.{u2, u4} R N _inst_1 _inst_4], AddCommMonoid.{max u1 u3 u4} (Dfinsupp.{u1, max u3 u4} ι (fun (i : ι) => LinearMap.{u2, u2, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) N (_inst_2 i) _inst_4 (_inst_3 i) _inst_5) (fun (i : ι) => LinearMap.hasZero.{u2, u2, u3, u4} R R (M i) N _inst_1 _inst_1 (_inst_2 i) _inst_4 (_inst_3 i) _inst_5 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} {N : Type.{u4}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] [_inst_4 : AddCommMonoid.{u4} N] [_inst_5 : Module.{u2, u4} R N _inst_1 _inst_4], AddCommMonoid.{max (max u4 u3) u1} (Dfinsupp.{u1, max u4 u3} ι (fun (i : ι) => LinearMap.{u2, u2, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) N (_inst_2 i) _inst_4 (_inst_3 i) _inst_5) (fun (i : ι) => LinearMap.instZeroLinearMap.{u2, u2, u3, u4} R R (M i) N _inst_1 _inst_1 (_inst_2 i) _inst_4 (_inst_3 i) _inst_5 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align dfinsupp.add_comm_monoid_of_linear_map Dfinsupp.addCommMonoidOfLinearMapₓ'. -/
/-- Typeclass inference can't find `dfinsupp.add_comm_monoid` without help for this case.
This instance allows it to be found where it is needed on the LHS of the colon in
`dfinsupp.module_of_linear_map`. -/
instance addCommMonoidOfLinearMap : AddCommMonoid (Π₀ i : ι, M i →ₗ[R] N) :=
  @Dfinsupp.addCommMonoid _ (fun i => M i →ₗ[R] N) _
#align dfinsupp.add_comm_monoid_of_linear_map Dfinsupp.addCommMonoidOfLinearMap

/- warning: dfinsupp.module_of_linear_map -> Dfinsupp.moduleOfLinearMap is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} {M : ι -> Type.{u4}} {N : Type.{u5}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u4} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u4} R (M i) _inst_1 (_inst_2 i)] [_inst_4 : AddCommMonoid.{u5} N] [_inst_5 : Module.{u2, u5} R N _inst_1 _inst_4] [_inst_6 : Semiring.{u3} S] [_inst_7 : Module.{u3, u5} S N _inst_6 _inst_4] [_inst_8 : SMulCommClass.{u2, u3, u5} R S N (SMulZeroClass.toHasSmul.{u2, u5} R N (AddZeroClass.toHasZero.{u5} N (AddMonoid.toAddZeroClass.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u5} R N (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u5} N (AddMonoid.toAddZeroClass.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u5} R N (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddZeroClass.toHasZero.{u5} N (AddMonoid.toAddZeroClass.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4))) (Module.toMulActionWithZero.{u2, u5} R N _inst_1 _inst_4 _inst_5)))) (SMulZeroClass.toHasSmul.{u3, u5} S N (AddZeroClass.toHasZero.{u5} N (AddMonoid.toAddZeroClass.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4))) (SMulWithZero.toSmulZeroClass.{u3, u5} S N (MulZeroClass.toHasZero.{u3} S (MulZeroOneClass.toMulZeroClass.{u3} S (MonoidWithZero.toMulZeroOneClass.{u3} S (Semiring.toMonoidWithZero.{u3} S _inst_6)))) (AddZeroClass.toHasZero.{u5} N (AddMonoid.toAddZeroClass.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4))) (MulActionWithZero.toSMulWithZero.{u3, u5} S N (Semiring.toMonoidWithZero.{u3} S _inst_6) (AddZeroClass.toHasZero.{u5} N (AddMonoid.toAddZeroClass.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4))) (Module.toMulActionWithZero.{u3, u5} S N _inst_6 _inst_4 _inst_7))))], Module.{u3, max u1 u4 u5} S (Dfinsupp.{u1, max u4 u5} ι (fun (i : ι) => LinearMap.{u2, u2, u4, u5} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) N (_inst_2 i) _inst_4 (_inst_3 i) _inst_5) (fun (i : ι) => LinearMap.hasZero.{u2, u2, u4, u5} R R (M i) N _inst_1 _inst_1 (_inst_2 i) _inst_4 (_inst_3 i) _inst_5 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_6 (Dfinsupp.addCommMonoidOfLinearMap.{u1, u2, u4, u5} ι R (fun (i : ι) => M i) N _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) _inst_4 _inst_5)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} {M : ι -> Type.{u4}} {N : Type.{u5}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u4} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u4} R (M i) _inst_1 (_inst_2 i)] [_inst_4 : AddCommMonoid.{u5} N] [_inst_5 : Module.{u2, u5} R N _inst_1 _inst_4] [_inst_6 : Semiring.{u3} S] [_inst_7 : Module.{u3, u5} S N _inst_6 _inst_4] [_inst_8 : SMulCommClass.{u2, u3, u5} R S N (SMulZeroClass.toSMul.{u2, u5} R N (AddMonoid.toZero.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4)) (SMulWithZero.toSMulZeroClass.{u2, u5} R N (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (AddMonoid.toZero.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4)) (MulActionWithZero.toSMulWithZero.{u2, u5} R N (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddMonoid.toZero.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4)) (Module.toMulActionWithZero.{u2, u5} R N _inst_1 _inst_4 _inst_5)))) (SMulZeroClass.toSMul.{u3, u5} S N (AddMonoid.toZero.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4)) (SMulWithZero.toSMulZeroClass.{u3, u5} S N (MonoidWithZero.toZero.{u3} S (Semiring.toMonoidWithZero.{u3} S _inst_6)) (AddMonoid.toZero.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4)) (MulActionWithZero.toSMulWithZero.{u3, u5} S N (Semiring.toMonoidWithZero.{u3} S _inst_6) (AddMonoid.toZero.{u5} N (AddCommMonoid.toAddMonoid.{u5} N _inst_4)) (Module.toMulActionWithZero.{u3, u5} S N _inst_6 _inst_4 _inst_7))))], Module.{u3, max (max u5 u4) u1} S (Dfinsupp.{u1, max u5 u4} ι (fun (i : ι) => LinearMap.{u2, u2, u4, u5} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) N (_inst_2 i) _inst_4 (_inst_3 i) _inst_5) (fun (i : ι) => LinearMap.instZeroLinearMap.{u2, u2, u4, u5} R R (M i) N _inst_1 _inst_1 (_inst_2 i) _inst_4 (_inst_3 i) _inst_5 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_6 (Dfinsupp.addCommMonoidOfLinearMap.{u1, u2, u4, u5} ι R (fun (i : ι) => M i) N _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i) _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align dfinsupp.module_of_linear_map Dfinsupp.moduleOfLinearMapₓ'. -/
/-- Typeclass inference can't find `dfinsupp.module` without help for this case.
This is needed to define `dfinsupp.lsum` below.

The cause seems to be an inability to unify the `Π i, add_comm_monoid (M i →ₗ[R] N)` instance that
we have with the `Π i, has_zero (M i →ₗ[R] N)` instance which appears as a parameter to the
`dfinsupp` type. -/
instance moduleOfLinearMap [Semiring S] [Module S N] [SMulCommClass R S N] :
    Module S (Π₀ i : ι, M i →ₗ[R] N) :=
  @Dfinsupp.module _ _ (fun i => M i →ₗ[R] N) _ _ _
#align dfinsupp.module_of_linear_map Dfinsupp.moduleOfLinearMap

variable (S)

include dec_ι

/- warning: dfinsupp.lsum -> Dfinsupp.lsum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.lsum Dfinsupp.lsumₓ'. -/
/-- The `dfinsupp` version of `finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def lsum [Semiring S] [Module S N] [SMulCommClass R S N] :
    (∀ i, M i →ₗ[R] N) ≃ₗ[S] (Π₀ i, M i) →ₗ[R] N
    where
  toFun F :=
    { toFun := sumAddHom fun i => (F i).toAddMonoidHom
      map_add' := (liftAddHom fun i => (F i).toAddMonoidHom).map_add
      map_smul' := fun c f => by
        dsimp
        apply Dfinsupp.induction f
        · rw [smul_zero, AddMonoidHom.map_zero, smul_zero]
        · intro a b f ha hb hf
          rw [smul_add, AddMonoidHom.map_add, AddMonoidHom.map_add, smul_add, hf, ← single_smul,
            sum_add_hom_single, sum_add_hom_single, LinearMap.toAddMonoidHom_coe,
            LinearMap.map_smul] }
  invFun F i := F.comp (lsingle i)
  left_inv F := by
    ext (x y)
    simp
  right_inv F := by
    ext (x y)
    simp
  map_add' F G := by
    ext (x y)
    simp
  map_smul' c F := by
    ext
    simp
#align dfinsupp.lsum Dfinsupp.lsum

/- warning: dfinsupp.lsum_single -> Dfinsupp.lsum_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.lsum_single Dfinsupp.lsum_singleₓ'. -/
/-- While `simp` can prove this, it is often convenient to avoid unfolding `lsum` into `sum_add_hom`
with `dfinsupp.lsum_apply_apply`. -/
theorem lsum_single [Semiring S] [Module S N] [SMulCommClass R S N] (F : ∀ i, M i →ₗ[R] N) (i)
    (x : M i) : lsum S F (single i x) = F i x :=
  sumAddHom_single _ _ _
#align dfinsupp.lsum_single Dfinsupp.lsum_single

end Lsum

/-! ### Bundled versions of `dfinsupp.map_range`

The names should match the equivalent bundled `finsupp.map_range` definitions.
-/


section MapRange

variable {β β₁ β₂ : ι → Type _}

variable [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (β₁ i)] [∀ i, AddCommMonoid (β₂ i)]

variable [∀ i, Module R (β i)] [∀ i, Module R (β₁ i)] [∀ i, Module R (β₂ i)]

/- warning: dfinsupp.map_range_smul -> Dfinsupp.mapRange_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.map_range_smul Dfinsupp.mapRange_smulₓ'. -/
theorem mapRange_smul (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (r : R)
    (hf' : ∀ i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i) :
    mapRange f hf (r • g) = r • mapRange f hf g :=
  by
  ext
  simp only [map_range_apply f, coe_smul, Pi.smul_apply, hf']
#align dfinsupp.map_range_smul Dfinsupp.mapRange_smul

/- warning: dfinsupp.map_range.linear_map -> Dfinsupp.mapRange.linearMap is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {β₁ : ι -> Type.{u3}} {β₂ : ι -> Type.{u4}} [_inst_7 : forall (i : ι), AddCommMonoid.{u3} (β₁ i)] [_inst_8 : forall (i : ι), AddCommMonoid.{u4} (β₂ i)] [_inst_10 : forall (i : ι), Module.{u2, u3} R (β₁ i) _inst_1 (_inst_7 i)] [_inst_11 : forall (i : ι), Module.{u2, u4} R (β₂ i) _inst_1 (_inst_8 i)], (forall (i : ι), LinearMap.{u2, u2, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (β₁ i) (β₂ i) (_inst_7 i) (_inst_8 i) (_inst_10 i) (_inst_11 i)) -> (LinearMap.{u2, u2, max u1 u3, max u1 u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (β₁ i) (AddMonoid.toAddZeroClass.{u3} (β₁ i) (AddCommMonoid.toAddMonoid.{u3} (β₁ i) (_inst_7 i))))) (Dfinsupp.{u1, u4} ι (fun (i : ι) => β₂ i) (fun (i : ι) => AddZeroClass.toHasZero.{u4} (β₂ i) (AddMonoid.toAddZeroClass.{u4} (β₂ i) (AddCommMonoid.toAddMonoid.{u4} (β₂ i) (_inst_8 i))))) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.addCommMonoid.{u1, u4} ι (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_8 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i)) (Dfinsupp.module.{u1, u4, u2} ι R (fun (i : ι) => β₂ i) _inst_1 (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {β₁ : ι -> Type.{u3}} {β₂ : ι -> Type.{u4}} [_inst_7 : forall (i : ι), AddCommMonoid.{u3} (β₁ i)] [_inst_8 : forall (i : ι), AddCommMonoid.{u4} (β₂ i)] [_inst_10 : forall (i : ι), Module.{u2, u3} R (β₁ i) _inst_1 (_inst_7 i)] [_inst_11 : forall (i : ι), Module.{u2, u4} R (β₂ i) _inst_1 (_inst_8 i)], (forall (i : ι), LinearMap.{u2, u2, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (β₁ i) (β₂ i) (_inst_7 i) (_inst_8 i) (_inst_10 i) (_inst_11 i)) -> (LinearMap.{u2, u2, max u3 u1, max u4 u1} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddMonoid.toZero.{u3} ((fun (i : ι) => β₁ i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => β₁ i) i) (_inst_7 i)))) (Dfinsupp.{u1, u4} ι (fun (i : ι) => β₂ i) (fun (i : ι) => AddMonoid.toZero.{u4} ((fun (i : ι) => β₂ i) i) (AddCommMonoid.toAddMonoid.{u4} ((fun (i : ι) => β₂ i) i) (_inst_8 i)))) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u1, u4} ι (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_8 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i)) (Dfinsupp.module.{u1, u4, u2} ι R (fun (i : ι) => β₂ i) _inst_1 (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i)))
Case conversion may be inaccurate. Consider using '#align dfinsupp.map_range.linear_map Dfinsupp.mapRange.linearMapₓ'. -/
/-- `dfinsupp.map_range` as an `linear_map`. -/
@[simps apply]
def mapRange.linearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] Π₀ i, β₂ i :=
  {
    mapRange.addMonoidHom fun i =>
      (f i).toAddMonoidHom with
    toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
    map_smul' := fun r => mapRange_smul _ _ _ fun i => (f i).map_smul r }
#align dfinsupp.map_range.linear_map Dfinsupp.mapRange.linearMap

/- warning: dfinsupp.map_range.linear_map_id -> Dfinsupp.mapRange.linearMap_id is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {β₂ : ι -> Type.{u3}} [_inst_8 : forall (i : ι), AddCommMonoid.{u3} (β₂ i)] [_inst_11 : forall (i : ι), Module.{u2, u3} R (β₂ i) _inst_1 (_inst_8 i)], Eq.{succ (max u1 u3)} (LinearMap.{u2, u2, max u1 u3, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₂ i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (β₂ i) (AddMonoid.toAddZeroClass.{u3} (β₂ i) (AddCommMonoid.toAddMonoid.{u3} (β₂ i) (_inst_8 i))))) (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₂ i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (β₂ i) (AddMonoid.toAddZeroClass.{u3} (β₂ i) (AddCommMonoid.toAddMonoid.{u3} (β₂ i) (_inst_8 i))))) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_8 i)) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_8 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₂ i) _inst_1 (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₂ i) _inst_1 (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i))) (Dfinsupp.mapRange.linearMap.{u1, u2, u3, u3} ι R _inst_1 (fun (i : ι) => β₂ i) (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i) (fun (i : ι) => _inst_11 i) (fun (i : ι) => LinearMap.id.{u2, u3} R (β₂ i) _inst_1 (_inst_8 i) (_inst_11 i))) (LinearMap.id.{u2, max u1 u3} R (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₂ i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (β₂ i) (AddMonoid.toAddZeroClass.{u3} (β₂ i) (AddCommMonoid.toAddMonoid.{u3} (β₂ i) (_inst_8 i))))) _inst_1 (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_8 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₂ i) _inst_1 (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i)))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} ι] [β₂ : Semiring.{u1} R] {_inst_8 : ι -> Type.{u2}} [_inst_11 : forall (i : ι), AddCommMonoid.{u2} (_inst_8 i)] [inst._@.Mathlib.LinearAlgebra.Dfinsupp._hyg.2484 : forall (i : ι), Module.{u1, u2} R (_inst_8 i) β₂ (_inst_11 i)], Eq.{max (succ u3) (succ u2)} (LinearMap.{u1, u1, max u2 u3, max u2 u3} R R β₂ β₂ (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R β₂)) (Dfinsupp.{u3, u2} ι (fun (i : ι) => _inst_8 i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => _inst_8 i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => _inst_8 i) i) (_inst_11 i)))) (Dfinsupp.{u3, u2} ι (fun (i : ι) => _inst_8 i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => _inst_8 i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => _inst_8 i) i) (_inst_11 i)))) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i)) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i)) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => _inst_8 i) β₂ (fun (i : ι) => _inst_11 i) (fun (i : ι) => inst._@.Mathlib.LinearAlgebra.Dfinsupp._hyg.2484 i)) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => _inst_8 i) β₂ (fun (i : ι) => _inst_11 i) (fun (i : ι) => inst._@.Mathlib.LinearAlgebra.Dfinsupp._hyg.2484 i))) (Dfinsupp.mapRange.linearMap.{u3, u1, u2, u2} ι R β₂ (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i) (fun (i : ι) => _inst_11 i) (fun (i : ι) => inst._@.Mathlib.LinearAlgebra.Dfinsupp._hyg.2484 i) (fun (i : ι) => inst._@.Mathlib.LinearAlgebra.Dfinsupp._hyg.2484 i) (fun (i : ι) => LinearMap.id.{u1, u2} R (_inst_8 i) β₂ (_inst_11 i) (inst._@.Mathlib.LinearAlgebra.Dfinsupp._hyg.2484 i))) (LinearMap.id.{u1, max u3 u2} R (Dfinsupp.{u3, u2} ι (fun (i : ι) => _inst_8 i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => _inst_8 i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => _inst_8 i) i) (_inst_11 i)))) β₂ (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i)) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => _inst_8 i) β₂ (fun (i : ι) => _inst_11 i) (fun (i : ι) => inst._@.Mathlib.LinearAlgebra.Dfinsupp._hyg.2484 i)))
Case conversion may be inaccurate. Consider using '#align dfinsupp.map_range.linear_map_id Dfinsupp.mapRange.linearMap_idₓ'. -/
@[simp]
theorem mapRange.linearMap_id :
    (mapRange.linearMap fun i => (LinearMap.id : β₂ i →ₗ[R] _)) = LinearMap.id :=
  LinearMap.ext mapRange_id
#align dfinsupp.map_range.linear_map_id Dfinsupp.mapRange.linearMap_id

/- warning: dfinsupp.map_range.linear_map_comp -> Dfinsupp.mapRange.linearMap_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.map_range.linear_map_comp Dfinsupp.mapRange.linearMap_compₓ'. -/
theorem mapRange.linearMap_comp (f : ∀ i, β₁ i →ₗ[R] β₂ i) (f₂ : ∀ i, β i →ₗ[R] β₁ i) :
    (mapRange.linearMap fun i => (f i).comp (f₂ i)) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  LinearMap.ext <| mapRange_comp (fun i x => f i x) (fun i x => f₂ i x) _ _ _
#align dfinsupp.map_range.linear_map_comp Dfinsupp.mapRange.linearMap_comp

include dec_ι

/- warning: dfinsupp.sum_map_range_index.linear_map -> Dfinsupp.sum_mapRange_index.linearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.sum_map_range_index.linear_map Dfinsupp.sum_mapRange_index.linearMapₓ'. -/
theorem sum_mapRange_index.linearMap [∀ (i : ι) (x : β₁ i), Decidable (x ≠ 0)]
    [∀ (i : ι) (x : β₂ i), Decidable (x ≠ 0)] {f : ∀ i, β₁ i →ₗ[R] β₂ i} {h : ∀ i, β₂ i →ₗ[R] N}
    {l : Π₀ i, β₁ i} :
    Dfinsupp.lsum ℕ h (mapRange.linearMap f l) = Dfinsupp.lsum ℕ (fun i => (h i).comp (f i)) l := by
  simpa [Dfinsupp.sumAddHom_apply] using
    @sum_map_range_index ι N _ _ _ _ _ _ _ _ (fun i => f i) (fun i => by simp) l (fun i => h i)
      fun i => by simp
#align dfinsupp.sum_map_range_index.linear_map Dfinsupp.sum_mapRange_index.linearMap

omit dec_ι

/- warning: dfinsupp.map_range.linear_equiv -> Dfinsupp.mapRange.linearEquiv is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {β₁ : ι -> Type.{u3}} {β₂ : ι -> Type.{u4}} [_inst_7 : forall (i : ι), AddCommMonoid.{u3} (β₁ i)] [_inst_8 : forall (i : ι), AddCommMonoid.{u4} (β₂ i)] [_inst_10 : forall (i : ι), Module.{u2, u3} R (β₁ i) _inst_1 (_inst_7 i)] [_inst_11 : forall (i : ι), Module.{u2, u4} R (β₂ i) _inst_1 (_inst_8 i)], (forall (i : ι), LinearEquiv.{u2, u2, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) (β₁ i) (β₂ i) (_inst_7 i) (_inst_8 i) (_inst_10 i) (_inst_11 i)) -> (LinearEquiv.{u2, u2, max u1 u3, max u1 u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (β₁ i) (AddMonoid.toAddZeroClass.{u3} (β₁ i) (AddCommMonoid.toAddMonoid.{u3} (β₁ i) (_inst_7 i))))) (Dfinsupp.{u1, u4} ι (fun (i : ι) => β₂ i) (fun (i : ι) => AddZeroClass.toHasZero.{u4} (β₂ i) (AddMonoid.toAddZeroClass.{u4} (β₂ i) (AddCommMonoid.toAddMonoid.{u4} (β₂ i) (_inst_8 i))))) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.addCommMonoid.{u1, u4} ι (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_8 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i)) (Dfinsupp.module.{u1, u4, u2} ι R (fun (i : ι) => β₂ i) _inst_1 (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {β₁ : ι -> Type.{u3}} {β₂ : ι -> Type.{u4}} [_inst_7 : forall (i : ι), AddCommMonoid.{u3} (β₁ i)] [_inst_8 : forall (i : ι), AddCommMonoid.{u4} (β₂ i)] [_inst_10 : forall (i : ι), Module.{u2, u3} R (β₁ i) _inst_1 (_inst_7 i)] [_inst_11 : forall (i : ι), Module.{u2, u4} R (β₂ i) _inst_1 (_inst_8 i)], (forall (i : ι), LinearEquiv.{u2, u2, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) (β₁ i) (β₂ i) (_inst_7 i) (_inst_8 i) (_inst_10 i) (_inst_11 i)) -> (LinearEquiv.{u2, u2, max u3 u1, max u4 u1} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddMonoid.toZero.{u3} ((fun (i : ι) => β₁ i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => β₁ i) i) (_inst_7 i)))) (Dfinsupp.{u1, u4} ι (fun (i : ι) => β₂ i) (fun (i : ι) => AddMonoid.toZero.{u4} ((fun (i : ι) => β₂ i) i) (AddCommMonoid.toAddMonoid.{u4} ((fun (i : ι) => β₂ i) i) (_inst_8 i)))) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u1, u4} ι (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_8 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i)) (Dfinsupp.module.{u1, u4, u2} ι R (fun (i : ι) => β₂ i) _inst_1 (fun (i : ι) => _inst_8 i) (fun (i : ι) => _inst_11 i)))
Case conversion may be inaccurate. Consider using '#align dfinsupp.map_range.linear_equiv Dfinsupp.mapRange.linearEquivₓ'. -/
/-- `dfinsupp.map_range.linear_map` as an `linear_equiv`. -/
@[simps apply]
def mapRange.linearEquiv (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addEquiv fun i => (e i).toAddEquiv,
    mapRange.linearMap fun i =>
      (e i).toLinearMap with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero }
#align dfinsupp.map_range.linear_equiv Dfinsupp.mapRange.linearEquiv

/- warning: dfinsupp.map_range.linear_equiv_refl -> Dfinsupp.mapRange.linearEquiv_refl is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {β₁ : ι -> Type.{u3}} [_inst_7 : forall (i : ι), AddCommMonoid.{u3} (β₁ i)] [_inst_10 : forall (i : ι), Module.{u2, u3} R (β₁ i) _inst_1 (_inst_7 i)], Eq.{succ (max u1 u3)} (LinearEquiv.{u2, u2, max u1 u3, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (β₁ i) (AddMonoid.toAddZeroClass.{u3} (β₁ i) (AddCommMonoid.toAddMonoid.{u3} (β₁ i) (_inst_7 i))))) (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (β₁ i) (AddMonoid.toAddZeroClass.{u3} (β₁ i) (AddCommMonoid.toAddMonoid.{u3} (β₁ i) (_inst_7 i))))) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i))) (Dfinsupp.mapRange.linearEquiv.{u1, u2, u3, u3} ι R _inst_1 (fun (i : ι) => β₁ i) (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i) (fun (i : ι) => _inst_10 i) (fun (i : ι) => LinearEquiv.refl.{u2, u3} R (β₁ i) _inst_1 (_inst_7 i) (_inst_10 i))) (LinearEquiv.refl.{u2, max u1 u3} R (Dfinsupp.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (β₁ i) (AddMonoid.toAddZeroClass.{u3} (β₁ i) (AddCommMonoid.toAddMonoid.{u3} (β₁ i) (_inst_7 i))))) _inst_1 (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i)))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {β₁ : ι -> Type.{u2}} [_inst_7 : forall (i : ι), AddCommMonoid.{u2} (β₁ i)] [_inst_10 : forall (i : ι), Module.{u1, u2} R (β₁ i) _inst_1 (_inst_7 i)], Eq.{max (succ u3) (succ u2)} (LinearEquiv.{u1, u1, max u2 u3, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (Dfinsupp.{u3, u2} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => β₁ i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => β₁ i) i) (_inst_7 i)))) (Dfinsupp.{u3, u2} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => β₁ i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => β₁ i) i) (_inst_7 i)))) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i)) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i))) (Dfinsupp.mapRange.linearEquiv.{u3, u1, u2, u2} ι R _inst_1 (fun (i : ι) => β₁ i) (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i) (fun (i : ι) => _inst_10 i) (fun (i : ι) => LinearEquiv.refl.{u1, u2} R (β₁ i) _inst_1 (_inst_7 i) (_inst_10 i))) (LinearEquiv.refl.{u1, max u3 u2} R (Dfinsupp.{u3, u2} ι (fun (i : ι) => β₁ i) (fun (i : ι) => AddMonoid.toZero.{u2} ((fun (i : ι) => β₁ i) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (i : ι) => β₁ i) i) (_inst_7 i)))) _inst_1 (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u3, u2} ι (fun (i : ι) => β₁ i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.module.{u3, u2, u1} ι R (fun (i : ι) => β₁ i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_10 i)))
Case conversion may be inaccurate. Consider using '#align dfinsupp.map_range.linear_equiv_refl Dfinsupp.mapRange.linearEquiv_reflₓ'. -/
@[simp]
theorem mapRange.linearEquiv_refl :
    (mapRange.linearEquiv fun i => LinearEquiv.refl R (β₁ i)) = LinearEquiv.refl _ _ :=
  LinearEquiv.ext mapRange_id
#align dfinsupp.map_range.linear_equiv_refl Dfinsupp.mapRange.linearEquiv_refl

/- warning: dfinsupp.map_range.linear_equiv_trans -> Dfinsupp.mapRange.linearEquiv_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.map_range.linear_equiv_trans Dfinsupp.mapRange.linearEquiv_transₓ'. -/
theorem mapRange.linearEquiv_trans (f : ∀ i, β i ≃ₗ[R] β₁ i) (f₂ : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  LinearEquiv.ext <| mapRange_comp (fun i x => f₂ i x) (fun i x => f i x) _ _ _
#align dfinsupp.map_range.linear_equiv_trans Dfinsupp.mapRange.linearEquiv_trans

/- warning: dfinsupp.map_range.linear_equiv_symm -> Dfinsupp.mapRange.linearEquiv_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.map_range.linear_equiv_symm Dfinsupp.mapRange.linearEquiv_symmₓ'. -/
@[simp]
theorem mapRange.linearEquiv_symm (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv e).symm = mapRange.linearEquiv fun i => (e i).symm :=
  rfl
#align dfinsupp.map_range.linear_equiv_symm Dfinsupp.mapRange.linearEquiv_symm

end MapRange

section CoprodMap

variable [DecidableEq ι] [∀ x : N, Decidable (x ≠ 0)]

/- warning: dfinsupp.coprod_map -> Dfinsupp.coprodMap is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} {N : Type.{u4}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] [_inst_4 : AddCommMonoid.{u4} N] [_inst_5 : Module.{u2, u4} R N _inst_1 _inst_4] [_inst_6 : DecidableEq.{succ u1} ι] [_inst_7 : forall (x : N), Decidable (Ne.{succ u4} N x (OfNat.ofNat.{u4} N 0 (OfNat.mk.{u4} N 0 (Zero.zero.{u4} N (AddZeroClass.toHasZero.{u4} N (AddMonoid.toAddZeroClass.{u4} N (AddCommMonoid.toAddMonoid.{u4} N _inst_4)))))))], (forall (i : ι), LinearMap.{u2, u2, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) N (_inst_2 i) _inst_4 (_inst_3 i) _inst_5) -> (LinearMap.{u2, u2, max u1 u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) N (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) _inst_4 (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) _inst_5)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} {N : Type.{u4}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] [_inst_4 : AddCommMonoid.{u4} N] [_inst_5 : Module.{u2, u4} R N _inst_1 _inst_4] [_inst_6 : DecidableEq.{succ u1} ι] [_inst_7 : forall (x : N), Decidable (Ne.{succ u4} N x (OfNat.ofNat.{u4} N 0 (Zero.toOfNat0.{u4} N (AddMonoid.toZero.{u4} N (AddCommMonoid.toAddMonoid.{u4} N _inst_4)))))], (forall (i : ι), LinearMap.{u2, u2, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (M i) N (_inst_2 i) _inst_4 (_inst_3 i) _inst_5) -> (LinearMap.{u2, u2, max u3 u1, u4} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u3} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_2 i)))) N (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) _inst_4 (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) _inst_5)
Case conversion may be inaccurate. Consider using '#align dfinsupp.coprod_map Dfinsupp.coprodMapₓ'. -/
/-- Given a family of linear maps `f i : M i  →ₗ[R] N`, we can form a linear map
`(Π₀ i, M i) →ₗ[R] N` which sends `x : Π₀ i, M i` to the sum over `i` of `f i` applied to `x i`.
This is the map coming from the universal property of `Π₀ i, M i` as the coproduct of the `M i`.
See also `linear_map.coprod` for the binary product version. -/
noncomputable def coprodMap (f : ∀ i : ι, M i →ₗ[R] N) : (Π₀ i, M i) →ₗ[R] N :=
  (Finsupp.lsum ℕ fun i : ι => LinearMap.id) ∘ₗ
    (@finsuppLequivDfinsupp ι R N _ _ _ _ _).symm.toLinearMap ∘ₗ Dfinsupp.mapRange.linearMap f
#align dfinsupp.coprod_map Dfinsupp.coprodMap

/- warning: dfinsupp.coprod_map_apply -> Dfinsupp.coprodMap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dfinsupp.coprod_map_apply Dfinsupp.coprodMap_applyₓ'. -/
theorem coprodMap_apply (f : ∀ i : ι, M i →ₗ[R] N) (x : Π₀ i, M i) :
    coprodMap f x =
      Finsupp.sum (mapRange (fun i => f i) (fun i => LinearMap.map_zero _) x).toFinsupp fun i =>
        id :=
  rfl
#align dfinsupp.coprod_map_apply Dfinsupp.coprodMap_apply

end CoprodMap

section Basis

/- warning: dfinsupp.basis -> Dfinsupp.basis is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] {η : ι -> Type.{u4}}, (forall (i : ι), Basis.{u4, u2, u3} (η i) R (M i) _inst_1 (_inst_2 i) (_inst_3 i)) -> (Basis.{max u1 u4, u2, max u1 u3} (Sigma.{u1, u4} ι (fun (i : ι) => η i)) R (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_2 i))))) _inst_1 (Dfinsupp.addCommMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : ι -> Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_3 : forall (i : ι), Module.{u2, u3} R (M i) _inst_1 (_inst_2 i)] {η : ι -> Type.{u4}}, (forall (i : ι), Basis.{u4, u2, u3} (η i) R (M i) _inst_1 (_inst_2 i) (_inst_3 i)) -> (Basis.{max u4 u1, u2, max u3 u1} (Sigma.{u1, u4} ι (fun (i : ι) => η i)) R (Dfinsupp.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u3} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_2 i)))) _inst_1 (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_2 i)) (Dfinsupp.module.{u1, u3, u2} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)))
Case conversion may be inaccurate. Consider using '#align dfinsupp.basis Dfinsupp.basisₓ'. -/
/-- The direct sum of free modules is free.

Note that while this is stated for `dfinsupp` not `direct_sum`, the types are defeq. -/
noncomputable def basis {η : ι → Type _} (b : ∀ i, Basis (η i) R (M i)) :
    Basis (Σi, η i) R (Π₀ i, M i) :=
  Basis.ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDfinsupp R).symm)
#align dfinsupp.basis Dfinsupp.basis

end Basis

end Dfinsupp

include dec_ι

namespace Submodule

variable [Semiring R] [AddCommMonoid N] [Module R N]

open Dfinsupp

/- warning: submodule.dfinsupp_sum_mem -> Submodule.dfinsupp_sum_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.dfinsupp_sum_mem Submodule.dfinsupp_sum_memₓ'. -/
theorem dfinsupp_sum_mem {β : ι → Type _} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    (S : Submodule R N) (f : Π₀ i, β i) (g : ∀ i, β i → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    f.Sum g ∈ S :=
  dfinsupp_sum_mem S f g h
#align submodule.dfinsupp_sum_mem Submodule.dfinsupp_sum_mem

/- warning: submodule.dfinsupp_sum_add_hom_mem -> Submodule.dfinsupp_sumAddHom_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.dfinsupp_sum_add_hom_mem Submodule.dfinsupp_sumAddHom_memₓ'. -/
theorem dfinsupp_sumAddHom_mem {β : ι → Type _} [∀ i, AddZeroClass (β i)] (S : Submodule R N)
    (f : Π₀ i, β i) (g : ∀ i, β i →+ N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    Dfinsupp.sumAddHom g f ∈ S :=
  dfinsupp_sumAddHom_mem S f g h
#align submodule.dfinsupp_sum_add_hom_mem Submodule.dfinsupp_sumAddHom_mem

/- warning: submodule.supr_eq_range_dfinsupp_lsum -> Submodule.iSup_eq_range_dfinsupp_lsum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.supr_eq_range_dfinsupp_lsum Submodule.iSup_eq_range_dfinsupp_lsumₓ'. -/
/-- The supremum of a family of submodules is equal to the range of `dfinsupp.lsum`; that is
every element in the `supr` can be produced from taking a finite number of non-zero elements
of `p i`, coercing them to `N`, and summing them. -/
theorem iSup_eq_range_dfinsupp_lsum (p : ι → Submodule R N) :
    iSup p = (Dfinsupp.lsum ℕ fun i => (p i).Subtype).range :=
  by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    exact ⟨Dfinsupp.single i ⟨y, hy⟩, Dfinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsupp_sumAddHom_mem _ v _ fun i _ => (le_iSup p i : p i ≤ _) (v i).Prop
#align submodule.supr_eq_range_dfinsupp_lsum Submodule.iSup_eq_range_dfinsupp_lsum

/- warning: submodule.bsupr_eq_range_dfinsupp_lsum -> Submodule.biSup_eq_range_dfinsupp_lsum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.bsupr_eq_range_dfinsupp_lsum Submodule.biSup_eq_range_dfinsupp_lsumₓ'. -/
/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom` composed with `dfinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `supr` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
theorem biSup_eq_range_dfinsupp_lsum (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N) :
    (⨆ (i) (h : p i), S i) =
      ((Dfinsupp.lsum ℕ fun i => (S i).Subtype).comp (Dfinsupp.filterLinearMap R _ p)).range :=
  by
  apply le_antisymm
  · refine' iSup₂_le fun i hi y hy => ⟨Dfinsupp.single i ⟨y, hy⟩, _⟩
    rw [LinearMap.comp_apply, filter_linear_map_apply, filter_single_pos _ _ hi]
    exact Dfinsupp.sumAddHom_single _ _ _
  · rintro x ⟨v, rfl⟩
    refine' dfinsupp_sumAddHom_mem _ _ _ fun i hi => _
    refine' mem_supr_of_mem i _
    by_cases hp : p i
    · simp [hp]
    · simp [hp]
#align submodule.bsupr_eq_range_dfinsupp_lsum Submodule.biSup_eq_range_dfinsupp_lsum

/- warning: submodule.mem_supr_iff_exists_dfinsupp -> Submodule.mem_iSup_iff_exists_dfinsupp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mem_supr_iff_exists_dfinsupp Submodule.mem_iSup_iff_exists_dfinsuppₓ'. -/
theorem mem_iSup_iff_exists_dfinsupp (p : ι → Submodule R N) (x : N) :
    x ∈ iSup p ↔ ∃ f : Π₀ i, p i, Dfinsupp.lsum ℕ (fun i => (p i).Subtype) f = x :=
  SetLike.ext_iff.mp (iSup_eq_range_dfinsupp_lsum p) x
#align submodule.mem_supr_iff_exists_dfinsupp Submodule.mem_iSup_iff_exists_dfinsupp

/- warning: submodule.mem_supr_iff_exists_dfinsupp' -> Submodule.mem_iSup_iff_exists_dfinsupp' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mem_supr_iff_exists_dfinsupp' Submodule.mem_iSup_iff_exists_dfinsupp'ₓ'. -/
/-- A variant of `submodule.mem_supr_iff_exists_dfinsupp` with the RHS fully unfolded. -/
theorem mem_iSup_iff_exists_dfinsupp' (p : ι → Submodule R N) [∀ (i) (x : p i), Decidable (x ≠ 0)]
    (x : N) : x ∈ iSup p ↔ ∃ f : Π₀ i, p i, (f.Sum fun i xi => ↑xi) = x :=
  by
  rw [mem_supr_iff_exists_dfinsupp]
  simp_rw [Dfinsupp.lsum_apply_apply, Dfinsupp.sumAddHom_apply]
  congr
#align submodule.mem_supr_iff_exists_dfinsupp' Submodule.mem_iSup_iff_exists_dfinsupp'

/- warning: submodule.mem_bsupr_iff_exists_dfinsupp -> Submodule.mem_biSup_iff_exists_dfinsupp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mem_bsupr_iff_exists_dfinsupp Submodule.mem_biSup_iff_exists_dfinsuppₓ'. -/
theorem mem_biSup_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N)
    (x : N) :
    (x ∈ ⨆ (i) (h : p i), S i) ↔
      ∃ f : Π₀ i, S i, Dfinsupp.lsum ℕ (fun i => (S i).Subtype) (f.filterₓ p) = x :=
  SetLike.ext_iff.mp (biSup_eq_range_dfinsupp_lsum p S) x
#align submodule.mem_bsupr_iff_exists_dfinsupp Submodule.mem_biSup_iff_exists_dfinsupp

open BigOperators

omit dec_ι

/- warning: submodule.mem_supr_finset_iff_exists_sum -> Submodule.mem_iSup_finset_iff_exists_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mem_supr_finset_iff_exists_sum Submodule.mem_iSup_finset_iff_exists_sumₓ'. -/
theorem mem_iSup_finset_iff_exists_sum {s : Finset ι} (p : ι → Submodule R N) (a : N) :
    (a ∈ ⨆ i ∈ s, p i) ↔ ∃ μ : ∀ i, p i, (∑ i in s, (μ i : N)) = a := by
  classical
    rw [Submodule.mem_iSup_iff_exists_dfinsupp']
    constructor <;> rintro ⟨μ, hμ⟩
    · use fun i => ⟨μ i, (iSup_const_le : _ ≤ p i) (coe_mem <| μ i)⟩
      rw [← hμ]
      symm
      apply Finset.sum_subset
      · intro x
        contrapose
        intro hx
        rw [mem_support_iff, not_ne_iff]
        ext
        rw [coe_zero, ← mem_bot R]
        convert coe_mem (μ x)
        symm
        exact iSup_neg hx
      · intro x _ hx
        rw [mem_support_iff, not_ne_iff] at hx
        rw [hx]
        rfl
    · refine' ⟨Dfinsupp.mk s _, _⟩
      · rintro ⟨i, hi⟩
        refine' ⟨μ i, _⟩
        rw [iSup_pos]
        · exact coe_mem _
        · exact hi
      simp only [Dfinsupp.sum]
      rw [Finset.sum_subset support_mk_subset, ← hμ]
      exact Finset.sum_congr rfl fun x hx => congr_arg coe <| mk_of_mem hx
      · intro x _ hx
        rw [mem_support_iff, not_ne_iff] at hx
        rw [hx]
        rfl
#align submodule.mem_supr_finset_iff_exists_sum Submodule.mem_iSup_finset_iff_exists_sum

end Submodule

namespace CompleteLattice

open Dfinsupp

section Semiring

variable [Semiring R] [AddCommMonoid N] [Module R N]

/- warning: complete_lattice.independent_iff_forall_dfinsupp -> CompleteLattice.independent_iff_forall_dfinsupp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_iff_forall_dfinsupp CompleteLattice.independent_iff_forall_dfinsuppₓ'. -/
/-- Independence of a family of submodules can be expressed as a quantifier over `dfinsupp`s.

This is an intermediate result used to prove
`complete_lattice.independent_of_dfinsupp_lsum_injective` and
`complete_lattice.independent.dfinsupp_lsum_injective`. -/
theorem independent_iff_forall_dfinsupp (p : ι → Submodule R N) :
    Independent p ↔
      ∀ (i) (x : p i) (v : Π₀ i : ι, ↥(p i)),
        lsum ℕ (fun i => (p i).Subtype) (erase i v) = x → x = 0 :=
  by
  simp_rw [CompleteLattice.independent_def, Submodule.disjoint_def,
    Submodule.mem_biSup_iff_exists_dfinsupp, exists_imp, filter_ne_eq_erase]
  apply forall_congr' fun i => _
  refine' subtype.forall'.trans _
  simp_rw [Submodule.coe_eq_zero]
  rfl
#align complete_lattice.independent_iff_forall_dfinsupp CompleteLattice.independent_iff_forall_dfinsupp

/- warning: complete_lattice.independent_of_dfinsupp_lsum_injective -> CompleteLattice.independent_of_dfinsupp_lsum_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_of_dfinsupp_lsum_injective CompleteLattice.independent_of_dfinsupp_lsum_injectiveₓ'. -/
/- If `dfinsupp.lsum` applied with `submodule.subtype` is injective then the submodules are
independent. -/
theorem independent_of_dfinsupp_lsum_injective (p : ι → Submodule R N)
    (h : Function.Injective (lsum ℕ fun i => (p i).Subtype)) : Independent p :=
  by
  rw [independent_iff_forall_dfinsupp]
  intro i x v hv
  replace hv :
    lsum ℕ (fun i => (p i).Subtype) (erase i v) = lsum ℕ (fun i => (p i).Subtype) (single i x)
  · simpa only [lsum_single] using hv
  have := dfinsupp.ext_iff.mp (h hv) i
  simpa [eq_comm] using this
#align complete_lattice.independent_of_dfinsupp_lsum_injective CompleteLattice.independent_of_dfinsupp_lsum_injective

/- warning: complete_lattice.independent_of_dfinsupp_sum_add_hom_injective -> CompleteLattice.independent_of_dfinsupp_sumAddHom_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_of_dfinsupp_sum_add_hom_injective CompleteLattice.independent_of_dfinsupp_sumAddHom_injectiveₓ'. -/
/- If `dfinsupp.sum_add_hom` applied with `add_submonoid.subtype` is injective then the additive
submonoids are independent. -/
theorem independent_of_dfinsupp_sumAddHom_injective (p : ι → AddSubmonoid N)
    (h : Function.Injective (sumAddHom fun i => (p i).Subtype)) : Independent p :=
  by
  rw [← independent_map_order_iso_iff (AddSubmonoid.toNatSubmodule : AddSubmonoid N ≃o _)]
  exact independent_of_dfinsupp_lsum_injective _ h
#align complete_lattice.independent_of_dfinsupp_sum_add_hom_injective CompleteLattice.independent_of_dfinsupp_sumAddHom_injective

/- warning: complete_lattice.lsum_comp_map_range_to_span_singleton -> CompleteLattice.lsum_comp_mapRange_toSpanSingleton is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complete_lattice.lsum_comp_map_range_to_span_singleton CompleteLattice.lsum_comp_mapRange_toSpanSingletonₓ'. -/
/-- Combining `dfinsupp.lsum` with `linear_map.to_span_singleton` is the same as `finsupp.total` -/
theorem lsum_comp_mapRange_toSpanSingleton [∀ m : R, Decidable (m ≠ 0)] (p : ι → Submodule R N)
    {v : ι → N} (hv : ∀ i : ι, v i ∈ p i) :
    ((lsum ℕ) fun i => (p i).Subtype : _ →ₗ[R] _).comp
        ((mapRange.linearMap fun i => LinearMap.toSpanSingleton R (↥(p i)) ⟨v i, hv i⟩ :
              _ →ₗ[R] _).comp
          (finsuppLequivDfinsupp R : (ι →₀ R) ≃ₗ[R] _).toLinearMap) =
      Finsupp.total ι N R v :=
  by
  ext
  simp
#align complete_lattice.lsum_comp_map_range_to_span_singleton CompleteLattice.lsum_comp_mapRange_toSpanSingleton

end Semiring

section Ring

variable [Ring R] [AddCommGroup N] [Module R N]

/- warning: complete_lattice.independent_of_dfinsupp_sum_add_hom_injective' -> CompleteLattice.independent_of_dfinsupp_sumAddHom_injective' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_of_dfinsupp_sum_add_hom_injective' CompleteLattice.independent_of_dfinsupp_sumAddHom_injective'ₓ'. -/
/- If `dfinsupp.sum_add_hom` applied with `add_submonoid.subtype` is injective then the additive
subgroups are independent. -/
theorem independent_of_dfinsupp_sumAddHom_injective' (p : ι → AddSubgroup N)
    (h : Function.Injective (sumAddHom fun i => (p i).Subtype)) : Independent p :=
  by
  rw [← independent_map_order_iso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)]
  exact independent_of_dfinsupp_lsum_injective _ h
#align complete_lattice.independent_of_dfinsupp_sum_add_hom_injective' CompleteLattice.independent_of_dfinsupp_sumAddHom_injective'

/- warning: complete_lattice.independent.dfinsupp_lsum_injective -> CompleteLattice.Independent.dfinsupp_lsum_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.dfinsupp_lsum_injective CompleteLattice.Independent.dfinsupp_lsum_injectiveₓ'. -/
/-- The canonical map out of a direct sum of a family of submodules is injective when the submodules
are `complete_lattice.independent`.

Note that this is not generally true for `[semiring R]`, for instance when `A` is the
`ℕ`-submodules of the positive and negative integers.

See `counterexamples/direct_sum_is_internal.lean` for a proof of this fact. -/
theorem Independent.dfinsupp_lsum_injective {p : ι → Submodule R N} (h : Independent p) :
    Function.Injective (lsum ℕ fun i => (p i).Subtype) :=
  by
  -- simplify everything down to binders over equalities in `N`
  rw [independent_iff_forall_dfinsupp] at h
  suffices (lsum ℕ fun i => (p i).Subtype).ker = ⊥
    by
    -- Lean can't find this without our help
    letI : AddCommGroup (Π₀ i, p i) := @Dfinsupp.addCommGroup _ (fun i => p i) _
    rw [LinearMap.ker_eq_bot] at this
    exact this
  rw [LinearMap.ker_eq_bot']
  intro m hm
  ext i : 1
  -- split `m` into the piece at `i` and the pieces elsewhere, to match `h`
  rw [Dfinsupp.zero_apply, ← neg_eq_zero]
  refine' h i (-m i) m _
  rwa [← erase_add_single i m, LinearMap.map_add, lsum_single, Submodule.subtype_apply,
    add_eq_zero_iff_eq_neg, ← Submodule.coe_neg] at hm
#align complete_lattice.independent.dfinsupp_lsum_injective CompleteLattice.Independent.dfinsupp_lsum_injective

/- warning: complete_lattice.independent.dfinsupp_sum_add_hom_injective -> CompleteLattice.Independent.dfinsupp_sumAddHom_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.dfinsupp_sum_add_hom_injective CompleteLattice.Independent.dfinsupp_sumAddHom_injectiveₓ'. -/
/-- The canonical map out of a direct sum of a family of additive subgroups is injective when the
additive subgroups are `complete_lattice.independent`. -/
theorem Independent.dfinsupp_sumAddHom_injective {p : ι → AddSubgroup N} (h : Independent p) :
    Function.Injective (sumAddHom fun i => (p i).Subtype) :=
  by
  rw [← independent_map_order_iso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)] at h
  exact h.dfinsupp_lsum_injective
#align complete_lattice.independent.dfinsupp_sum_add_hom_injective CompleteLattice.Independent.dfinsupp_sumAddHom_injective

/- warning: complete_lattice.independent_iff_dfinsupp_lsum_injective -> CompleteLattice.independent_iff_dfinsupp_lsum_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_iff_dfinsupp_lsum_injective CompleteLattice.independent_iff_dfinsupp_lsum_injectiveₓ'. -/
/-- A family of submodules over an additive group are independent if and only iff `dfinsupp.lsum`
applied with `submodule.subtype` is injective.

Note that this is not generally true for `[semiring R]`; see
`complete_lattice.independent.dfinsupp_lsum_injective` for details. -/
theorem independent_iff_dfinsupp_lsum_injective (p : ι → Submodule R N) :
    Independent p ↔ Function.Injective (lsum ℕ fun i => (p i).Subtype) :=
  ⟨Independent.dfinsupp_lsum_injective, independent_of_dfinsupp_lsum_injective p⟩
#align complete_lattice.independent_iff_dfinsupp_lsum_injective CompleteLattice.independent_iff_dfinsupp_lsum_injective

/- warning: complete_lattice.independent_iff_dfinsupp_sum_add_hom_injective -> CompleteLattice.independent_iff_dfinsupp_sumAddHom_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_iff_dfinsupp_sum_add_hom_injective CompleteLattice.independent_iff_dfinsupp_sumAddHom_injectiveₓ'. -/
/-- A family of additive subgroups over an additive group are independent if and only if
`dfinsupp.sum_add_hom` applied with `add_subgroup.subtype` is injective. -/
theorem independent_iff_dfinsupp_sumAddHom_injective (p : ι → AddSubgroup N) :
    Independent p ↔ Function.Injective (sumAddHom fun i => (p i).Subtype) :=
  ⟨Independent.dfinsupp_sumAddHom_injective, independent_of_dfinsupp_sumAddHom_injective' p⟩
#align complete_lattice.independent_iff_dfinsupp_sum_add_hom_injective CompleteLattice.independent_iff_dfinsupp_sumAddHom_injective

omit dec_ι

/- warning: complete_lattice.independent.linear_independent -> CompleteLattice.Independent.linearIndependent is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {N : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u3} N] [_inst_3 : Module.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2)] [_inst_4 : NoZeroSMulDivisors.{u2, u3} R N (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (SubNegMonoid.toAddMonoid.{u3} N (AddGroup.toSubNegMonoid.{u3} N (AddCommGroup.toAddGroup.{u3} N _inst_2))))) (SMulZeroClass.toHasSmul.{u2, u3} R N (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (AddCommMonoid.toAddMonoid.{u3} N (AddCommGroup.toAddCommMonoid.{u3} N _inst_2)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R N (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (AddCommMonoid.toAddMonoid.{u3} N (AddCommGroup.toAddCommMonoid.{u3} N _inst_2)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R N (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (AddCommMonoid.toAddMonoid.{u3} N (AddCommGroup.toAddCommMonoid.{u3} N _inst_2)))) (Module.toMulActionWithZero.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3))))] (p : ι -> (Submodule.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3)), (CompleteLattice.Independent.{succ u1, u3} ι (Submodule.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3) (Submodule.completeLattice.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3) p) -> (forall {v : ι -> N}, (forall (i : ι), Membership.Mem.{u3, u3} N (Submodule.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3) (SetLike.hasMem.{u3, u3} (Submodule.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3) N (Submodule.setLike.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3)) (v i) (p i)) -> (forall (i : ι), Ne.{succ u3} N (v i) (OfNat.ofNat.{u3} N 0 (OfNat.mk.{u3} N 0 (Zero.zero.{u3} N (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (SubNegMonoid.toAddMonoid.{u3} N (AddGroup.toSubNegMonoid.{u3} N (AddCommGroup.toAddGroup.{u3} N _inst_2))))))))) -> (LinearIndependent.{u1, u2, u3} ι R N v (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {N : Type.{u2}} [_inst_1 : Ring.{u3} R] [_inst_2 : AddCommGroup.{u2} N] [_inst_3 : Module.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2)] [_inst_4 : NoZeroSMulDivisors.{u3, u2} R N (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2))))) (SMulZeroClass.toSMul.{u3, u2} R N (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2))))) (SMulWithZero.toSMulZeroClass.{u3, u2} R N (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R N (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1)) (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2))))) (Module.toMulActionWithZero.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3))))] (p : ι -> (Submodule.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3)), (CompleteLattice.Independent.{succ u1, u2} ι (Submodule.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3) (Submodule.completeLattice.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3) p) -> (forall {v : ι -> N}, (forall (i : ι), Membership.mem.{u2, u2} N (Submodule.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3) N (Submodule.setLike.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3)) (v i) (p i)) -> (forall (i : ι), Ne.{succ u2} N (v i) (OfNat.ofNat.{u2} N 0 (Zero.toOfNat0.{u2} N (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2)))))))) -> (LinearIndependent.{u1, u3, u2} ι R N v (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3))
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.linear_independent CompleteLattice.Independent.linearIndependentₓ'. -/
/-- If a family of submodules is `independent`, then a choice of nonzero vector from each submodule
forms a linearly independent family.

See also `complete_lattice.independent.linear_independent'`. -/
theorem Independent.linearIndependent [NoZeroSMulDivisors R N] (p : ι → Submodule R N)
    (hp : Independent p) {v : ι → N} (hv : ∀ i, v i ∈ p i) (hv' : ∀ i, v i ≠ 0) :
    LinearIndependent R v := by
  classical
    rw [linearIndependent_iff]
    intro l hl
    let a :=
      Dfinsupp.mapRange.linearMap (fun i => LinearMap.toSpanSingleton R (p i) ⟨v i, hv i⟩)
        l.to_dfinsupp
    have ha : a = 0 := by
      apply hp.dfinsupp_lsum_injective
      rwa [← lsum_comp_map_range_to_span_singleton _ hv] at hl
    ext i
    apply smul_left_injective R (hv' i)
    have : l i • v i = a i := rfl
    simp [this, ha]
#align complete_lattice.independent.linear_independent CompleteLattice.Independent.linearIndependent

/- warning: complete_lattice.independent_iff_linear_independent_of_ne_zero -> CompleteLattice.independent_iff_linearIndependent_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {N : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u3} N] [_inst_3 : Module.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2)] [_inst_4 : NoZeroSMulDivisors.{u2, u3} R N (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (SubNegMonoid.toAddMonoid.{u3} N (AddGroup.toSubNegMonoid.{u3} N (AddCommGroup.toAddGroup.{u3} N _inst_2))))) (SMulZeroClass.toHasSmul.{u2, u3} R N (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (AddCommMonoid.toAddMonoid.{u3} N (AddCommGroup.toAddCommMonoid.{u3} N _inst_2)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R N (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (AddCommMonoid.toAddMonoid.{u3} N (AddCommGroup.toAddCommMonoid.{u3} N _inst_2)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R N (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (AddCommMonoid.toAddMonoid.{u3} N (AddCommGroup.toAddCommMonoid.{u3} N _inst_2)))) (Module.toMulActionWithZero.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3))))] {v : ι -> N}, (forall (i : ι), Ne.{succ u3} N (v i) (OfNat.ofNat.{u3} N 0 (OfNat.mk.{u3} N 0 (Zero.zero.{u3} N (AddZeroClass.toHasZero.{u3} N (AddMonoid.toAddZeroClass.{u3} N (SubNegMonoid.toAddMonoid.{u3} N (AddGroup.toSubNegMonoid.{u3} N (AddCommGroup.toAddGroup.{u3} N _inst_2))))))))) -> (Iff (CompleteLattice.Independent.{succ u1, u3} ι (Submodule.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3) (Submodule.completeLattice.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3) (fun (i : ι) => Submodule.span.{u2, u3} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3 (Singleton.singleton.{u3, u3} N (Set.{u3} N) (Set.hasSingleton.{u3} N) (v i)))) (LinearIndependent.{u1, u2, u3} ι R N v (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} N _inst_2) _inst_3))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {N : Type.{u2}} [_inst_1 : Ring.{u3} R] [_inst_2 : AddCommGroup.{u2} N] [_inst_3 : Module.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2)] [_inst_4 : NoZeroSMulDivisors.{u3, u2} R N (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2))))) (SMulZeroClass.toSMul.{u3, u2} R N (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2))))) (SMulWithZero.toSMulZeroClass.{u3, u2} R N (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R N (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1)) (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2))))) (Module.toMulActionWithZero.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3))))] {v : ι -> N}, (forall (i : ι), Ne.{succ u2} N (v i) (OfNat.ofNat.{u2} N 0 (Zero.toOfNat0.{u2} N (NegZeroClass.toZero.{u2} N (SubNegZeroMonoid.toNegZeroClass.{u2} N (SubtractionMonoid.toSubNegZeroMonoid.{u2} N (SubtractionCommMonoid.toSubtractionMonoid.{u2} N (AddCommGroup.toDivisionAddCommMonoid.{u2} N _inst_2)))))))) -> (Iff (CompleteLattice.Independent.{succ u1, u2} ι (Submodule.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3) (Submodule.completeLattice.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3) (fun (i : ι) => Submodule.span.{u3, u2} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3 (Singleton.singleton.{u2, u2} N (Set.{u2} N) (Set.instSingletonSet.{u2} N) (v i)))) (LinearIndependent.{u1, u3, u2} ι R N v (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} N _inst_2) _inst_3))
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_iff_linear_independent_of_ne_zero CompleteLattice.independent_iff_linearIndependent_of_ne_zeroₓ'. -/
theorem independent_iff_linearIndependent_of_ne_zero [NoZeroSMulDivisors R N] {v : ι → N}
    (h_ne_zero : ∀ i, v i ≠ 0) : (Independent fun i => R ∙ v i) ↔ LinearIndependent R v :=
  ⟨fun hv => hv.LinearIndependent _ (fun i => Submodule.mem_span_singleton_self <| v i) h_ne_zero,
    fun hv => hv.independent_span_singleton⟩
#align complete_lattice.independent_iff_linear_independent_of_ne_zero CompleteLattice.independent_iff_linearIndependent_of_ne_zero

end Ring

end CompleteLattice

