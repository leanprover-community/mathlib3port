/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module linear_algebra.multilinear.finite_dimensional
! leanprover-community/mathlib commit 50251fd6309cca5ca2e747882ffecd2729f38c5d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Multilinear.Basic
import Mathbin.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Multilinear maps over finite dimensional spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main results are that multilinear maps over finitely-generated, free modules are
finitely-generated and free.

* `module.finite.multilinear_map`
* `module.free.multilinear_map`

We do not put this in `linear_algebra/multilinear_map/basic` to avoid making the imports too large
there.
-/


namespace MultilinearMap

variable {ι R M₂ : Type _} {M₁ : ι → Type _}

variable [Finite ι]

variable [CommRing R] [AddCommGroup M₂] [Module R M₂]

variable [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]

variable [Module.Finite R M₂] [Module.Free R M₂]

variable [∀ i, Module.Finite R (M₁ i)] [∀ i, Module.Free R (M₁ i)]

-- the induction requires us to show both at once
private theorem free_and_finite :
    Module.Free R (MultilinearMap R M₁ M₂) ∧ Module.Finite R (MultilinearMap R M₁ M₂) :=
  by
  -- the `fin n` case is sufficient
  suffices
    ∀ (n) (N : Fin n → Type _) [∀ i, AddCommGroup (N i)],
      ∀ [∀ i, Module R (N i)],
        ∀ [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)],
          Module.Free R (MultilinearMap R N M₂) ∧ Module.Finite R (MultilinearMap R N M₂)
    by
    cases nonempty_fintype ι
    cases this _ (M₁ ∘ (Fintype.equivFin ι).symm)
    have e := dom_dom_congr_linear_equiv' R M₁ M₂ (Fintype.equivFin ι)
    exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  intro n N _ _ _ _
  induction' n with n ih
  ·
    exact
      ⟨Module.Free.of_equiv (const_linear_equiv_of_is_empty R N M₂),
        Module.Finite.equiv (const_linear_equiv_of_is_empty R N M₂)⟩
  · suffices
      Module.Free R (N 0 →ₗ[R] MultilinearMap R (fun i : Fin n => N i.succ) M₂) ∧
        Module.Finite R (N 0 →ₗ[R] MultilinearMap R (fun i : Fin n => N i.succ) M₂)
      by
      cases this
      exact
        ⟨Module.Free.of_equiv (multilinearCurryLeftEquiv R N M₂),
          Module.Finite.equiv (multilinearCurryLeftEquiv R N M₂)⟩
    cases ih fun i => N i.succ
    exact ⟨Module.Free.linearMap _ _ _, Module.Finite.linearMap _ _⟩

/- warning: module.finite.multilinear_map -> Module.Finite.multilinearMap is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M₂ : Type.{u3}} {M₁ : ι -> Type.{u4}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : CommRing.{u2} R] [_inst_3 : AddCommGroup.{u3} M₂] [_inst_4 : Module.{u2, u3} R M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3)] [_inst_5 : forall (i : ι), AddCommGroup.{u4} (M₁ i)] [_inst_6 : forall (i : ι), Module.{u2, u4} R (M₁ i) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i))] [_inst_7 : Module.Finite.{u2, u3} R M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4] [_inst_8 : Module.Free.{u2, u3} R M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4] [_inst_9 : forall (i : ι), Module.Finite.{u2, u4} R (M₁ i) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (_inst_6 i)] [_inst_10 : forall (i : ι), Module.Free.{u2, u4} R (M₁ i) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (_inst_6 i)], Module.Finite.{u2, max u1 u4 u3} R (MultilinearMap.{u2, u4, u3, u1} R ι M₁ M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) (fun (i : ι) => _inst_6 i) _inst_4) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (MultilinearMap.addCommMonoid.{u2, u4, u3, u1} R ι M₁ M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) (fun (i : ι) => _inst_6 i) _inst_4) (MultilinearMap.module.{u4, u3, u1, u2, u2} ι M₁ M₂ (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) R R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (fun (i : ι) => _inst_6 i) _inst_4 _inst_4 (smulCommClass_self.{u2, u3} R M₂ (CommRing.toCommMonoid.{u2} R _inst_2) (MulActionWithZero.toMulAction.{u2, u3} R M₂ (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2))) (AddZeroClass.toHasZero.{u3} M₂ (AddMonoid.toAddZeroClass.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3)))) (Module.toMulActionWithZero.{u2, u3} R M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4))))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M₂ : Type.{u3}} {M₁ : ι -> Type.{u4}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : CommRing.{u2} R] [_inst_3 : AddCommGroup.{u3} M₂] [_inst_4 : Module.{u2, u3} R M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3)] [_inst_5 : Module.Finite.{u2, u3} R M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4] [_inst_6 : Module.Free.{u2, u3} R M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4] [_inst_7 : forall (i : ι), AddCommGroup.{u4} (M₁ i)] [_inst_8 : forall (i : ι), Module.{u2, u4} R (M₁ i) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i))] [_inst_9 : forall (i : ι), Module.Finite.{u2, u4} R (M₁ i) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (_inst_8 i)] [_inst_10 : forall (i : ι), Module.Free.{u2, u4} R (M₁ i) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (_inst_8 i)], Module.Finite.{u2, max (max u1 u3) u4} R (MultilinearMap.{u2, u4, u3, u1} R ι M₁ M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) (fun (i : ι) => _inst_8 i) _inst_4) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (MultilinearMap.addCommMonoid.{u2, u4, u3, u1} R ι M₁ M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) (fun (i : ι) => _inst_8 i) _inst_4) (MultilinearMap.instModuleMultilinearMapAddCommMonoid.{u4, u3, u1, u2, u2} ι M₁ M₂ (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) R R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (fun (i : ι) => _inst_8 i) _inst_4 _inst_4 (smulCommClass_self.{u2, u3} R M₂ (CommRing.toCommMonoid.{u2} R _inst_2) (MulActionWithZero.toMulAction.{u2, u3} R M₂ (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2))) (NegZeroClass.toZero.{u3} M₂ (SubNegZeroMonoid.toNegZeroClass.{u3} M₂ (SubtractionMonoid.toSubNegZeroMonoid.{u3} M₂ (SubtractionCommMonoid.toSubtractionMonoid.{u3} M₂ (AddCommGroup.toDivisionAddCommMonoid.{u3} M₂ _inst_3))))) (Module.toMulActionWithZero.{u2, u3} R M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4))))
Case conversion may be inaccurate. Consider using '#align module.finite.multilinear_map Module.Finite.multilinearMapₓ'. -/
instance Module.Finite.multilinearMap : Module.Finite R (MultilinearMap R M₁ M₂) :=
  free_and_finite.2
#align module.finite.multilinear_map Module.Finite.multilinearMap

/- warning: module.free.multilinear_map -> Module.Free.multilinearMap is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M₂ : Type.{u3}} {M₁ : ι -> Type.{u4}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : CommRing.{u2} R] [_inst_3 : AddCommGroup.{u3} M₂] [_inst_4 : Module.{u2, u3} R M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3)] [_inst_5 : forall (i : ι), AddCommGroup.{u4} (M₁ i)] [_inst_6 : forall (i : ι), Module.{u2, u4} R (M₁ i) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i))] [_inst_7 : Module.Finite.{u2, u3} R M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4] [_inst_8 : Module.Free.{u2, u3} R M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4] [_inst_9 : forall (i : ι), Module.Finite.{u2, u4} R (M₁ i) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (_inst_6 i)] [_inst_10 : forall (i : ι), Module.Free.{u2, u4} R (M₁ i) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (_inst_6 i)], Module.Free.{u2, max u1 u4 u3} R (MultilinearMap.{u2, u4, u3, u1} R ι M₁ M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) (fun (i : ι) => _inst_6 i) _inst_4) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (MultilinearMap.addCommMonoid.{u2, u4, u3, u1} R ι M₁ M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) (fun (i : ι) => _inst_6 i) _inst_4) (MultilinearMap.module.{u4, u3, u1, u2, u2} ι M₁ M₂ (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_5 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) R R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (fun (i : ι) => _inst_6 i) _inst_4 _inst_4 (smulCommClass_self.{u2, u3} R M₂ (CommRing.toCommMonoid.{u2} R _inst_2) (MulActionWithZero.toMulAction.{u2, u3} R M₂ (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2))) (AddZeroClass.toHasZero.{u3} M₂ (AddMonoid.toAddZeroClass.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3)))) (Module.toMulActionWithZero.{u2, u3} R M₂ (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4))))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M₂ : Type.{u3}} {M₁ : ι -> Type.{u4}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : CommRing.{u2} R] [_inst_3 : AddCommGroup.{u3} M₂] [_inst_4 : Module.{u2, u3} R M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3)] [_inst_5 : Module.Finite.{u2, u3} R M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4] [_inst_6 : Module.Free.{u2, u3} R M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4] [_inst_7 : forall (i : ι), AddCommGroup.{u4} (M₁ i)] [_inst_8 : forall (i : ι), Module.{u2, u4} R (M₁ i) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i))] [_inst_9 : forall (i : ι), Module.Finite.{u2, u4} R (M₁ i) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (_inst_8 i)] [_inst_10 : forall (i : ι), Module.Free.{u2, u4} R (M₁ i) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (_inst_8 i)], Module.Free.{u2, max (max u1 u3) u4} R (MultilinearMap.{u2, u4, u3, u1} R ι M₁ M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) (fun (i : ι) => _inst_8 i) _inst_4) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (MultilinearMap.addCommMonoid.{u2, u4, u3, u1} R ι M₁ M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) (fun (i : ι) => _inst_8 i) _inst_4) (MultilinearMap.instModuleMultilinearMapAddCommMonoid.{u4, u3, u1, u2, u2} ι M₁ M₂ (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u4} (M₁ i) (_inst_7 i)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) R R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (fun (i : ι) => _inst_8 i) _inst_4 _inst_4 (smulCommClass_self.{u2, u3} R M₂ (CommRing.toCommMonoid.{u2} R _inst_2) (MulActionWithZero.toMulAction.{u2, u3} R M₂ (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2))) (NegZeroClass.toZero.{u3} M₂ (SubNegZeroMonoid.toNegZeroClass.{u3} M₂ (SubtractionMonoid.toSubNegZeroMonoid.{u3} M₂ (SubtractionCommMonoid.toSubtractionMonoid.{u3} M₂ (AddCommGroup.toDivisionAddCommMonoid.{u3} M₂ _inst_3))))) (Module.toMulActionWithZero.{u2, u3} R M₂ (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_3) _inst_4))))
Case conversion may be inaccurate. Consider using '#align module.free.multilinear_map Module.Free.multilinearMapₓ'. -/
instance Module.Free.multilinearMap : Module.Free R (MultilinearMap R M₁ M₂) :=
  free_and_finite.1
#align module.free.multilinear_map Module.Free.multilinearMap

end MultilinearMap

