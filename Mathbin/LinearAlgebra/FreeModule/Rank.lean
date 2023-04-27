/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module linear_algebra.free_module.rank
! leanprover-community/mathlib commit 4f4a1c875d0baa92ab5d92f3fb1bb258ad9f3e5b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Dimension

/-!

# Extra results about `module.rank`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some extra results not in `linear_algebra.dimension`.

-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open TensorProduct DirectSum BigOperators Cardinal

open Cardinal

section Ring

variable [Ring R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

open Module.Free

/- warning: rank_finsupp -> rank_finsupp is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] (ι : Type.{u3}), Eq.{succ (succ (max u3 u2))} Cardinal.{max u3 u2} (Module.rank.{u1, max u3 u2} R (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_3)))))) (Ring.toSemiring.{u1} R _inst_1) (Finsupp.addCommMonoid.{u3, u2} ι M (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)) (Finsupp.module.{u3, u2, u1} ι M R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4)) (HMul.hMul.{succ (max u3 u2), succ (max u3 u2), succ (max u3 u2)} Cardinal.{max u3 u2} Cardinal.{max u3 u2} Cardinal.{max u3 u2} (instHMul.{succ (max u3 u2)} Cardinal.{max u3 u2} Cardinal.hasMul.{max u3 u2}) (Cardinal.lift.{u2, u3} (Cardinal.mk.{u3} ι)) (Cardinal.lift.{u3, u2} (Module.rank.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4)))
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] (ι : Type.{u3}), Eq.{max (succ (succ u2)) (succ (succ u3))} Cardinal.{max u2 u3} (Module.rank.{u1, max u2 u3} R (Finsupp.{u3, u2} ι M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_3)))))) (Ring.toSemiring.{u1} R _inst_1) (Finsupp.addCommMonoid.{u3, u2} ι M (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)) (Finsupp.module.{u3, u2, u1} ι M R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4)) (HMul.hMul.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} Cardinal.{max u3 u2} Cardinal.{max u2 u3} Cardinal.{max u3 u2} (instHMul.{max (succ u2) (succ u3)} Cardinal.{max u3 u2} Cardinal.instMulCardinal.{max u2 u3}) (Cardinal.lift.{u2, u3} (Cardinal.mk.{u3} ι)) (Cardinal.lift.{u3, u2} (Module.rank.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4)))
Case conversion may be inaccurate. Consider using '#align rank_finsupp rank_finsuppₓ'. -/
@[simp]
theorem rank_finsupp (ι : Type w) :
    Module.rank R (ι →₀ M) = Cardinal.lift.{v} (#ι) * Cardinal.lift.{w} (Module.rank R M) :=
  by
  obtain ⟨⟨_, bs⟩⟩ := Module.Free.exists_basis R M
  rw [← bs.mk_eq_rank'', ← (Finsupp.basis fun a : ι => bs).mk_eq_rank'', Cardinal.mk_sigma,
    Cardinal.sum_const]
#align rank_finsupp rank_finsupp

/- warning: rank_finsupp' -> rank_finsupp' is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] (ι : Type.{u2}), Eq.{succ (succ u2)} Cardinal.{u2} (Module.rank.{u1, u2} R (Finsupp.{u2, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_3)))))) (Ring.toSemiring.{u1} R _inst_1) (Finsupp.addCommMonoid.{u2, u2} ι M (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)) (Finsupp.module.{u2, u2, u1} ι M R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4)) (HMul.hMul.{succ u2, succ u2, succ u2} Cardinal.{u2} Cardinal.{u2} Cardinal.{u2} (instHMul.{succ u2} Cardinal.{u2} Cardinal.hasMul.{u2}) (Cardinal.mk.{u2} ι) (Module.rank.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4))
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] (ι : Type.{u2}), Eq.{succ (succ u2)} Cardinal.{u2} (Module.rank.{u1, u2} R (Finsupp.{u2, u2} ι M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_3)))))) (Ring.toSemiring.{u1} R _inst_1) (Finsupp.addCommMonoid.{u2, u2} ι M (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)) (Finsupp.module.{u2, u2, u1} ι M R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4)) (HMul.hMul.{succ u2, succ u2, succ u2} Cardinal.{u2} Cardinal.{u2} Cardinal.{u2} (instHMul.{succ u2} Cardinal.{u2} Cardinal.instMulCardinal.{u2}) (Cardinal.mk.{u2} ι) (Module.rank.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4))
Case conversion may be inaccurate. Consider using '#align rank_finsupp' rank_finsupp'ₓ'. -/
theorem rank_finsupp' (ι : Type v) : Module.rank R (ι →₀ M) = (#ι) * Module.rank R M := by
  simp [rank_finsupp]
#align rank_finsupp' rank_finsupp'

/- warning: rank_finsupp_self -> rank_finsupp_self is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] (ι : Type.{u2}), Eq.{succ (succ (max u2 u1))} Cardinal.{max u2 u1} (Module.rank.{u1, max u2 u1} R (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (Ring.toSemiring.{u1} R _inst_1) (Finsupp.addCommMonoid.{u2, u1} ι R (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Finsupp.module.{u2, u1, u1} ι R R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} ι))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] (ι : Type.{u2}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Module.rank.{u1, max u1 u2} R (Finsupp.{u2, u1} ι R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Ring.toSemiring.{u1} R _inst_1) (Finsupp.addCommMonoid.{u2, u1} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Finsupp.module.{u2, u1, u1} ι R R (Ring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} ι))
Case conversion may be inaccurate. Consider using '#align rank_finsupp_self rank_finsupp_selfₓ'. -/
/-- The rank of `(ι →₀ R)` is `(# ι).lift`. -/
@[simp]
theorem rank_finsupp_self (ι : Type w) : Module.rank R (ι →₀ R) = (#ι).lift := by
  simp [rank_finsupp]
#align rank_finsupp_self rank_finsupp_self

/- warning: rank_finsupp_self' -> rank_finsupp_self' is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] {ι : Type.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Module.rank.{u1, u1} R (Finsupp.{u1, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (Ring.toSemiring.{u1} R _inst_1) (Finsupp.addCommMonoid.{u1, u1} ι R (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Finsupp.module.{u1, u1, u1} ι R R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Cardinal.mk.{u1} ι)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] {ι : Type.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Module.rank.{u1, u1} R (Finsupp.{u1, u1} ι R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Ring.toSemiring.{u1} R _inst_1) (Finsupp.addCommMonoid.{u1, u1} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Finsupp.module.{u1, u1, u1} ι R R (Ring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Cardinal.mk.{u1} ι)
Case conversion may be inaccurate. Consider using '#align rank_finsupp_self' rank_finsupp_self'ₓ'. -/
/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
theorem rank_finsupp_self' {ι : Type u} : Module.rank R (ι →₀ R) = (#ι) := by simp
#align rank_finsupp_self' rank_finsupp_self'

/- warning: rank_direct_sum -> rank_directSum is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] {ι : Type.{u2}} (M : ι -> Type.{u3}) [_inst_9 : forall (i : ι), AddCommGroup.{u3} (M i)] [_inst_10 : forall (i : ι), Module.{u1, u3} R (M i) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_9 i))] [_inst_11 : forall (i : ι), Module.Free.{u1, u3} R (M i) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_9 i)) (_inst_10 i)], Eq.{succ (succ (max u2 u3))} Cardinal.{max u2 u3} (Module.rank.{u1, max u2 u3} R (DirectSum.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_9 i))) (Ring.toSemiring.{u1} R _inst_1) (DirectSum.addCommMonoid.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_9 i))) (DirectSum.module.{u1, u2, u3} R (Ring.toSemiring.{u1} R _inst_1) ι (fun (i : ι) => M i) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_9 i)) (fun (i : ι) => _inst_10 i))) (Cardinal.sum.{u2, u3} ι (fun (i : ι) => Module.rank.{u1, u3} R (M i) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_9 i)) (_inst_10 i)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] {ι : Type.{u2}} (M : ι -> Type.{u3}) [_inst_9 : forall (i : ι), AddCommGroup.{u3} (M i)] [_inst_10 : forall (i : ι), Module.{u1, u3} R (M i) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_9 i))] [_inst_11 : forall (i : ι), Module.Free.{u1, u3} R (M i) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_9 i)) (_inst_10 i)], Eq.{max (succ (succ u2)) (succ (succ u3))} Cardinal.{max u3 u2} (Module.rank.{u1, max u3 u2} R (DirectSum.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_9 i))) (Ring.toSemiring.{u1} R _inst_1) (instAddCommMonoidDirectSum.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_9 i))) (DirectSum.instModuleDirectSumInstAddCommMonoidDirectSum.{u1, u2, u3} R (Ring.toSemiring.{u1} R _inst_1) ι (fun (i : ι) => M i) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_9 i)) (fun (i : ι) => _inst_10 i))) (Cardinal.sum.{u2, u3} ι (fun (i : ι) => Module.rank.{u1, u3} R (M i) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} (M i) (_inst_9 i)) (_inst_10 i)))
Case conversion may be inaccurate. Consider using '#align rank_direct_sum rank_directSumₓ'. -/
/-- The rank of the direct sum is the sum of the ranks. -/
@[simp]
theorem rank_directSum {ι : Type v} (M : ι → Type w) [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] :
    Module.rank R (⨁ i, M i) = Cardinal.sum fun i => Module.rank R (M i) :=
  by
  let B i := choose_basis R (M i)
  let b : Basis _ R (⨁ i, M i) := Dfinsupp.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']
#align rank_direct_sum rank_directSum

/- warning: rank_matrix -> rank_matrix is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] (m : Type.{u2}) (n : Type.{u3}) [_inst_9 : Finite.{succ u2} m] [_inst_10 : Finite.{succ u3} n], Eq.{succ (succ (max u2 u3 u1))} Cardinal.{max u2 u3 u1} (Module.rank.{u1, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n R) (Ring.toSemiring.{u1} R _inst_1) (Matrix.addCommMonoid.{u1, u2, u3} m n R (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Matrix.module.{u1, u2, u3, u1} m n R R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (HMul.hMul.{succ (max u2 u3 u1), succ (max u2 u3 u1), succ (max u2 u3 u1)} Cardinal.{max u2 u3 u1} Cardinal.{max u2 u3 u1} Cardinal.{max u2 u3 u1} (instHMul.{succ (max u2 u3 u1)} Cardinal.{max u2 u3 u1} Cardinal.hasMul.{max u2 u3 u1}) (Cardinal.lift.{max u2 u3 u1, u2} (Cardinal.mk.{u2} m)) (Cardinal.lift.{max u2 u3 u1, u3} (Cardinal.mk.{u3} n)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] (m : Type.{u2}) (n : Type.{u3}) [_inst_9 : Finite.{succ u2} m] [_inst_10 : Finite.{succ u3} n], Eq.{max (max (succ (succ u1)) (succ (succ u2))) (succ (succ u3))} Cardinal.{max (max u1 u3) u2} (Module.rank.{u1, max (max u1 u3) u2} R (Matrix.{u2, u3, u1} m n R) (Ring.toSemiring.{u1} R _inst_1) (Matrix.addCommMonoid.{u1, u2, u3} m n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Matrix.module.{u1, u2, u3, u1} m n R R (Ring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (HMul.hMul.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} Cardinal.{max u2 u3 u1} Cardinal.{max u3 u2 u3 u1} Cardinal.{max u2 u3 u1} (instHMul.{max (max (succ u1) (succ u2)) (succ u3)} Cardinal.{max u2 u3 u1} Cardinal.instMulCardinal.{max (max u1 u2) u3}) (Cardinal.lift.{max u2 u3 u1, u2} (Cardinal.mk.{u2} m)) (Cardinal.lift.{max u2 u3 u1, u3} (Cardinal.mk.{u3} n)))
Case conversion may be inaccurate. Consider using '#align rank_matrix rank_matrixₓ'. -/
/-- If `m` and `n` are `fintype`, the rank of `m × n` matrices is `(# m).lift * (# n).lift`. -/
@[simp]
theorem rank_matrix (m : Type v) (n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = lift.{max v w u, v} (#m) * lift.{max v w u, w} (#n) :=
  by
  cases nonempty_fintype m
  cases nonempty_fintype n
  have h := (Matrix.stdBasis R m n).mk_eq_rank
  rw [← lift_lift.{max v w u, max v w}, lift_inj] at h
  simpa using h.symm
#align rank_matrix rank_matrix

/- warning: rank_matrix' -> rank_matrix' is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] (m : Type.{u2}) (n : Type.{u2}) [_inst_9 : Finite.{succ u2} m] [_inst_10 : Finite.{succ u2} n], Eq.{succ (succ (max u2 u1))} Cardinal.{max u2 u1} (Module.rank.{u1, max u2 u1} R (Matrix.{u2, u2, u1} m n R) (Ring.toSemiring.{u1} R _inst_1) (Matrix.addCommMonoid.{u1, u2, u2} m n R (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Matrix.module.{u1, u2, u2, u1} m n R R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Cardinal.lift.{u1, u2} (HMul.hMul.{succ u2, succ u2, succ u2} Cardinal.{u2} Cardinal.{u2} Cardinal.{u2} (instHMul.{succ u2} Cardinal.{u2} Cardinal.hasMul.{u2}) (Cardinal.mk.{u2} m) (Cardinal.mk.{u2} n)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] (m : Type.{u2}) (n : Type.{u2}) [_inst_9 : Finite.{succ u2} m] [_inst_10 : Finite.{succ u2} n], Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Module.rank.{u1, max u1 u2} R (Matrix.{u2, u2, u1} m n R) (Ring.toSemiring.{u1} R _inst_1) (Matrix.addCommMonoid.{u1, u2, u2} m n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Matrix.module.{u1, u2, u2, u1} m n R R (Ring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Cardinal.lift.{u1, u2} (HMul.hMul.{succ u2, succ u2, succ u2} Cardinal.{u2} Cardinal.{u2} Cardinal.{u2} (instHMul.{succ u2} Cardinal.{u2} Cardinal.instMulCardinal.{u2}) (Cardinal.mk.{u2} m) (Cardinal.mk.{u2} n)))
Case conversion may be inaccurate. Consider using '#align rank_matrix' rank_matrix'ₓ'. -/
/-- If `m` and `n` are `fintype` that lie in the same universe, the rank of `m × n` matrices is
  `(# n * # m).lift`. -/
@[simp]
theorem rank_matrix' (m n : Type v) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = ((#m) * (#n)).lift := by rw [rank_matrix, lift_mul, lift_umax]
#align rank_matrix' rank_matrix'

/- warning: rank_matrix'' -> rank_matrix'' is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] (m : Type.{u1}) (n : Type.{u1}) [_inst_9 : Finite.{succ u1} m] [_inst_10 : Finite.{succ u1} n], Eq.{succ (succ u1)} Cardinal.{u1} (Module.rank.{u1, u1} R (Matrix.{u1, u1, u1} m n R) (Ring.toSemiring.{u1} R _inst_1) (Matrix.addCommMonoid.{u1, u1, u1} m n R (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Matrix.module.{u1, u1, u1, u1} m n R R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} m) (Cardinal.mk.{u1} n))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R _inst_1)] (m : Type.{u1}) (n : Type.{u1}) [_inst_9 : Finite.{succ u1} m] [_inst_10 : Finite.{succ u1} n], Eq.{succ (succ u1)} Cardinal.{u1} (Module.rank.{u1, u1} R (Matrix.{u1, u1, u1} m n R) (Ring.toSemiring.{u1} R _inst_1) (Matrix.addCommMonoid.{u1, u1, u1} m n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Matrix.module.{u1, u1, u1, u1} m n R R (Ring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} m) (Cardinal.mk.{u1} n))
Case conversion may be inaccurate. Consider using '#align rank_matrix'' rank_matrix''ₓ'. -/
/-- If `m` and `n` are `fintype` that lie in the same universe as `R`, the rank of `m × n` matrices
  is `# m * # n`. -/
@[simp]
theorem rank_matrix'' (m n : Type u) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = (#m) * (#n) := by simp
#align rank_matrix'' rank_matrix''

end Ring

section CommRing

variable [CommRing R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

open Module.Free

/- warning: rank_tensor_product -> rank_tensorProduct is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) (N : Type.{u3}) [_inst_1 : CommRing.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] [_inst_6 : AddCommGroup.{u3} N] [_inst_7 : Module.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6)] [_inst_8 : Module.Free.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_7], Eq.{succ (succ (max u2 u3))} Cardinal.{max u2 u3} (Module.rank.{u1, max u2 u3} R (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_4 _inst_7) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (TensorProduct.addCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_4 _inst_7) (TensorProduct.module.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_4 _inst_7)) (HMul.hMul.{succ (max u2 u3), succ (max u2 u3), succ (max u2 u3)} Cardinal.{max u2 u3} Cardinal.{max u2 u3} Cardinal.{max u2 u3} (instHMul.{succ (max u2 u3)} Cardinal.{max u2 u3} Cardinal.hasMul.{max u2 u3}) (Cardinal.lift.{u3, u2} (Module.rank.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4)) (Cardinal.lift.{u2, u3} (Module.rank.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_7)))
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) (N : Type.{u3}) [_inst_1 : CommRing.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] [_inst_6 : AddCommGroup.{u3} N] [_inst_7 : Module.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6)] [_inst_8 : Module.Free.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_7], Eq.{max (succ (succ u2)) (succ (succ u3))} Cardinal.{max u3 u2} (Module.rank.{u1, max u3 u2} R (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_4 _inst_7) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (TensorProduct.addCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_4 _inst_7) (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_4 _inst_7)) (HMul.hMul.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} Cardinal.{max u2 u3} Cardinal.{max u3 u2} Cardinal.{max u2 u3} (instHMul.{max (succ u2) (succ u3)} Cardinal.{max u2 u3} Cardinal.instMulCardinal.{max u2 u3}) (Cardinal.lift.{u3, u2} (Module.rank.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4)) (Cardinal.lift.{u2, u3} (Module.rank.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_6) _inst_7)))
Case conversion may be inaccurate. Consider using '#align rank_tensor_product rank_tensorProductₓ'. -/
/-- The rank of `M ⊗[R] N` is `(module.rank R M).lift * (module.rank R N).lift`. -/
@[simp]
theorem rank_tensorProduct :
    Module.rank R (M ⊗[R] N) = lift.{w, v} (Module.rank R M) * lift.{v, w} (Module.rank R N) :=
  by
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis R M
  obtain ⟨⟨_, bN⟩⟩ := Module.Free.exists_basis R N
  rw [← bM.mk_eq_rank'', ← bN.mk_eq_rank'', ← (bM.tensor_product bN).mk_eq_rank'', Cardinal.mk_prod]
#align rank_tensor_product rank_tensorProduct

/- warning: rank_tensor_product' -> rank_tensorProduct' is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : CommRing.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] (N : Type.{u2}) [_inst_9 : AddCommGroup.{u2} N] [_inst_10 : Module.{u1, u2} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9)] [_inst_11 : Module.Free.{u1, u2} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_10], Eq.{succ (succ u2)} Cardinal.{u2} (Module.rank.{u1, u2} R (TensorProduct.{u1, u2, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_4 _inst_10) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (TensorProduct.addCommMonoid.{u1, u2, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_4 _inst_10) (TensorProduct.module.{u1, u2, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_4 _inst_10)) (HMul.hMul.{succ u2, succ u2, succ u2} Cardinal.{u2} Cardinal.{u2} Cardinal.{u2} (instHMul.{succ u2} Cardinal.{u2} Cardinal.hasMul.{u2}) (Module.rank.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4) (Module.rank.{u1, u2} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_10))
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : CommRing.{u1} R] [_inst_2 : StrongRankCondition.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] (N : Type.{u2}) [_inst_9 : AddCommGroup.{u2} N] [_inst_10 : Module.{u1, u2} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9)] [_inst_11 : Module.Free.{u1, u2} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_10], Eq.{succ (succ u2)} Cardinal.{u2} (Module.rank.{u1, u2} R (TensorProduct.{u1, u2, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_4 _inst_10) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (TensorProduct.addCommMonoid.{u1, u2, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_4 _inst_10) (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u1, u2, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_4 _inst_10)) (HMul.hMul.{succ u2, succ u2, succ u2} Cardinal.{u2} Cardinal.{u2} Cardinal.{u2} (instHMul.{succ u2} Cardinal.{u2} Cardinal.instMulCardinal.{u2}) (Module.rank.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4) (Module.rank.{u1, u2} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} N _inst_9) _inst_10))
Case conversion may be inaccurate. Consider using '#align rank_tensor_product' rank_tensorProduct'ₓ'. -/
/-- If `M` and `N` lie in the same universe, the rank of `M ⊗[R] N` is
  `(module.rank R M) * (module.rank R N)`. -/
theorem rank_tensorProduct' (N : Type v) [AddCommGroup N] [Module R N] [Module.Free R N] :
    Module.rank R (M ⊗[R] N) = Module.rank R M * Module.rank R N := by simp
#align rank_tensor_product' rank_tensorProduct'

end CommRing

