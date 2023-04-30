/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module field_theory.tower
! leanprover-community/mathlib commit c7bce2818663f456335892ddbdd1809f111a5b72
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Prime
import Mathbin.RingTheory.AlgebraTower
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Tower of field extensions

In this file we prove the tower law for arbitrary extensions and finite extensions.
Suppose `L` is a field extension of `K` and `K` is a field extension of `F`.
Then `[L:F] = [L:K] [K:F]` where `[E₁:E₂]` means the `E₂`-dimension of `E₁`.

In fact we generalize it to rings and modules, where `L` is not necessarily a field,
but just a free module over `K`.

## Implementation notes

We prove two versions, since there are two notions of dimensions: `module.rank` which gives
the dimension of an arbitrary vector space as a cardinal, and `finite_dimensional.finrank` which
gives the dimension of a finitely-dimensional vector space as a natural number.

## Tags

tower law

-/


universe u v w u₁ v₁ w₁

open Classical BigOperators

open FiniteDimensional

open Cardinal

variable (F : Type u) (K : Type v) (A : Type w)

section Ring

variable [CommRing F] [Ring K] [AddCommGroup A]

variable [Algebra F K] [Module K A] [Module F A] [IsScalarTower F K A]

variable [StrongRankCondition F] [StrongRankCondition K] [Module.Free F K] [Module.Free K A]

/- warning: lift_rank_mul_lift_rank -> lift_rank_mul_lift_rank is a dubious translation:
lean 3 declaration is
  forall (F : Type.{u1}) (K : Type.{u2}) (A : Type.{u3}) [_inst_1 : CommRing.{u1} F] [_inst_2 : Ring.{u2} K] [_inst_3 : AddCommGroup.{u3} A] [_inst_4 : Algebra.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_1) (Ring.toSemiring.{u2} K _inst_2)] [_inst_5 : Module.{u2, u3} K A (Ring.toSemiring.{u2} K _inst_2) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)] [_inst_6 : Module.{u1, u3} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)] [_inst_7 : IsScalarTower.{u1, u2, u3} F K A (SMulZeroClass.toHasSmul.{u1, u2} F K (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K _inst_2))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} F K (MulZeroClass.toHasZero.{u1} F (MulZeroOneClass.toMulZeroClass.{u1} F (MonoidWithZero.toMulZeroOneClass.{u1} F (Semiring.toMonoidWithZero.{u1} F (CommSemiring.toSemiring.{u1} F (CommRing.toCommSemiring.{u1} F _inst_1)))))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K _inst_2))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} F K (Semiring.toMonoidWithZero.{u1} F (CommSemiring.toSemiring.{u1} F (CommRing.toCommSemiring.{u1} F _inst_1))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K _inst_2))))))) (Module.toMulActionWithZero.{u1, u2} F K (CommSemiring.toSemiring.{u1} F (CommRing.toCommSemiring.{u1} F _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K _inst_2)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_1) (Ring.toSemiring.{u2} K _inst_2) _inst_4))))) (SMulZeroClass.toHasSmul.{u2, u3} K A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)))) (SMulWithZero.toSmulZeroClass.{u2, u3} K A (MulZeroClass.toHasZero.{u2} K (MulZeroOneClass.toMulZeroClass.{u2} K (MonoidWithZero.toMulZeroOneClass.{u2} K (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K _inst_2))))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)))) (MulActionWithZero.toSMulWithZero.{u2, u3} K A (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K _inst_2)) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)))) (Module.toMulActionWithZero.{u2, u3} K A (Ring.toSemiring.{u2} K _inst_2) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_5)))) (SMulZeroClass.toHasSmul.{u1, u3} F A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)))) (SMulWithZero.toSmulZeroClass.{u1, u3} F A (MulZeroClass.toHasZero.{u1} F (MulZeroOneClass.toMulZeroClass.{u1} F (MonoidWithZero.toMulZeroOneClass.{u1} F (Semiring.toMonoidWithZero.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)))))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)))) (MulActionWithZero.toSMulWithZero.{u1, u3} F A (Semiring.toMonoidWithZero.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)))) (Module.toMulActionWithZero.{u1, u3} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_6))))] [_inst_8 : StrongRankCondition.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1))] [_inst_9 : StrongRankCondition.{u2} K (Ring.toSemiring.{u2} K _inst_2)] [_inst_10 : Module.Free.{u1, u2} F K (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} K (NonUnitalNonAssocRing.toAddCommGroup.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K _inst_2)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_1) (Ring.toSemiring.{u2} K _inst_2) _inst_4)] [_inst_11 : Module.Free.{u2, u3} K A (Ring.toSemiring.{u2} K _inst_2) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_5], Eq.{succ (succ (max u2 u3))} Cardinal.{max u2 u3} (HMul.hMul.{succ (max u2 u3), succ (max u2 u3), succ (max u2 u3)} Cardinal.{max u2 u3} Cardinal.{max u2 u3} Cardinal.{max u2 u3} (instHMul.{succ (max u2 u3)} Cardinal.{max u2 u3} Cardinal.hasMul.{max u2 u3}) (Cardinal.lift.{u3, u2} (Module.rank.{u1, u2} F K (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} K (NonUnitalNonAssocRing.toAddCommGroup.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K _inst_2)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_1) (Ring.toSemiring.{u2} K _inst_2) _inst_4))) (Cardinal.lift.{u2, u3} (Module.rank.{u2, u3} K A (Ring.toSemiring.{u2} K _inst_2) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_5))) (Cardinal.lift.{u2, u3} (Module.rank.{u1, u3} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_6))
but is expected to have type
  forall (F : Type.{u1}) (K : Type.{u2}) (A : Type.{u3}) [_inst_1 : CommRing.{u1} F] [_inst_2 : Ring.{u2} K] [_inst_3 : AddCommGroup.{u3} A] [_inst_4 : Algebra.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_1) (Ring.toSemiring.{u2} K _inst_2)] [_inst_5 : Module.{u2, u3} K A (Ring.toSemiring.{u2} K _inst_2) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)] [_inst_6 : Module.{u1, u3} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3)] [_inst_7 : IsScalarTower.{u1, u2, u3} F K A (Algebra.toSMul.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_1) (Ring.toSemiring.{u2} K _inst_2) _inst_4) (SMulZeroClass.toSMul.{u2, u3} K A (NegZeroClass.toZero.{u3} A (SubNegZeroMonoid.toNegZeroClass.{u3} A (SubtractionMonoid.toSubNegZeroMonoid.{u3} A (SubtractionCommMonoid.toSubtractionMonoid.{u3} A (AddCommGroup.toDivisionAddCommMonoid.{u3} A _inst_3))))) (SMulWithZero.toSMulZeroClass.{u2, u3} K A (MonoidWithZero.toZero.{u2} K (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K _inst_2))) (NegZeroClass.toZero.{u3} A (SubNegZeroMonoid.toNegZeroClass.{u3} A (SubtractionMonoid.toSubNegZeroMonoid.{u3} A (SubtractionCommMonoid.toSubtractionMonoid.{u3} A (AddCommGroup.toDivisionAddCommMonoid.{u3} A _inst_3))))) (MulActionWithZero.toSMulWithZero.{u2, u3} K A (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K _inst_2)) (NegZeroClass.toZero.{u3} A (SubNegZeroMonoid.toNegZeroClass.{u3} A (SubtractionMonoid.toSubNegZeroMonoid.{u3} A (SubtractionCommMonoid.toSubtractionMonoid.{u3} A (AddCommGroup.toDivisionAddCommMonoid.{u3} A _inst_3))))) (Module.toMulActionWithZero.{u2, u3} K A (Ring.toSemiring.{u2} K _inst_2) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_5)))) (SMulZeroClass.toSMul.{u1, u3} F A (NegZeroClass.toZero.{u3} A (SubNegZeroMonoid.toNegZeroClass.{u3} A (SubtractionMonoid.toSubNegZeroMonoid.{u3} A (SubtractionCommMonoid.toSubtractionMonoid.{u3} A (AddCommGroup.toDivisionAddCommMonoid.{u3} A _inst_3))))) (SMulWithZero.toSMulZeroClass.{u1, u3} F A (CommMonoidWithZero.toZero.{u1} F (CommSemiring.toCommMonoidWithZero.{u1} F (CommRing.toCommSemiring.{u1} F _inst_1))) (NegZeroClass.toZero.{u3} A (SubNegZeroMonoid.toNegZeroClass.{u3} A (SubtractionMonoid.toSubNegZeroMonoid.{u3} A (SubtractionCommMonoid.toSubtractionMonoid.{u3} A (AddCommGroup.toDivisionAddCommMonoid.{u3} A _inst_3))))) (MulActionWithZero.toSMulWithZero.{u1, u3} F A (Semiring.toMonoidWithZero.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1))) (NegZeroClass.toZero.{u3} A (SubNegZeroMonoid.toNegZeroClass.{u3} A (SubtractionMonoid.toSubNegZeroMonoid.{u3} A (SubtractionCommMonoid.toSubtractionMonoid.{u3} A (AddCommGroup.toDivisionAddCommMonoid.{u3} A _inst_3))))) (Module.toMulActionWithZero.{u1, u3} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_6))))] [_inst_8 : StrongRankCondition.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1))] [_inst_9 : StrongRankCondition.{u2} K (Ring.toSemiring.{u2} K _inst_2)] [_inst_10 : Module.Free.{u1, u2} F K (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K _inst_2)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_1) (Ring.toSemiring.{u2} K _inst_2) _inst_4)] [_inst_11 : Module.Free.{u2, u3} K A (Ring.toSemiring.{u2} K _inst_2) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_5], Eq.{max (succ (succ u2)) (succ (succ u3))} Cardinal.{max u2 u3} (HMul.hMul.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} Cardinal.{max u2 u3} Cardinal.{max u3 u2} Cardinal.{max u2 u3} (instHMul.{max (succ u2) (succ u3)} Cardinal.{max u2 u3} Cardinal.instMulCardinal.{max u2 u3}) (Cardinal.lift.{u3, u2} (Module.rank.{u1, u2} F K (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K _inst_2)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_1) (Ring.toSemiring.{u2} K _inst_2) _inst_4))) (Cardinal.lift.{u2, u3} (Module.rank.{u2, u3} K A (Ring.toSemiring.{u2} K _inst_2) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_5))) (Cardinal.lift.{u2, u3} (Module.rank.{u1, u3} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A _inst_3) _inst_6))
Case conversion may be inaccurate. Consider using '#align lift_rank_mul_lift_rank lift_rank_mul_lift_rankₓ'. -/
/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$. -/
theorem lift_rank_mul_lift_rank :
    Cardinal.lift.{w} (Module.rank F K) * Cardinal.lift.{v} (Module.rank K A) =
      Cardinal.lift.{v} (Module.rank F A) :=
  by
  obtain ⟨_, b⟩ := Module.Free.exists_basis F K
  obtain ⟨_, c⟩ := Module.Free.exists_basis K A
  rw [← (Module.rank F K).lift_id, ← b.mk_eq_rank, ← (Module.rank K A).lift_id, ← c.mk_eq_rank, ←
    lift_umax.{w, v}, ← (b.smul c).mk_eq_rank, mk_prod, lift_mul, lift_lift, lift_lift, lift_lift,
    lift_lift, lift_umax]
#align lift_rank_mul_lift_rank lift_rank_mul_lift_rank

/- warning: rank_mul_rank -> rank_mul_rank is a dubious translation:
lean 3 declaration is
  forall (F : Type.{u1}) (K : Type.{u2}) (A : Type.{u2}) [_inst_12 : CommRing.{u1} F] [_inst_13 : Ring.{u2} K] [_inst_14 : AddCommGroup.{u2} A] [_inst_15 : Algebra.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_12) (Ring.toSemiring.{u2} K _inst_13)] [_inst_16 : Module.{u2, u2} K A (Ring.toSemiring.{u2} K _inst_13) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)] [_inst_17 : Module.{u1, u2} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)] [_inst_18 : IsScalarTower.{u1, u2, u2} F K A (SMulZeroClass.toHasSmul.{u1, u2} F K (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K _inst_13))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} F K (MulZeroClass.toHasZero.{u1} F (MulZeroOneClass.toMulZeroClass.{u1} F (MonoidWithZero.toMulZeroOneClass.{u1} F (Semiring.toMonoidWithZero.{u1} F (CommSemiring.toSemiring.{u1} F (CommRing.toCommSemiring.{u1} F _inst_12)))))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K _inst_13))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} F K (Semiring.toMonoidWithZero.{u1} F (CommSemiring.toSemiring.{u1} F (CommRing.toCommSemiring.{u1} F _inst_12))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K _inst_13))))))) (Module.toMulActionWithZero.{u1, u2} F K (CommSemiring.toSemiring.{u1} F (CommRing.toCommSemiring.{u1} F _inst_12)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K _inst_13)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_12) (Ring.toSemiring.{u2} K _inst_13) _inst_15))))) (SMulZeroClass.toHasSmul.{u2, u2} K A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)))) (SMulWithZero.toSmulZeroClass.{u2, u2} K A (MulZeroClass.toHasZero.{u2} K (MulZeroOneClass.toMulZeroClass.{u2} K (MonoidWithZero.toMulZeroOneClass.{u2} K (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K _inst_13))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)))) (MulActionWithZero.toSMulWithZero.{u2, u2} K A (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K _inst_13)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)))) (Module.toMulActionWithZero.{u2, u2} K A (Ring.toSemiring.{u2} K _inst_13) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_16)))) (SMulZeroClass.toHasSmul.{u1, u2} F A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)))) (SMulWithZero.toSmulZeroClass.{u1, u2} F A (MulZeroClass.toHasZero.{u1} F (MulZeroOneClass.toMulZeroClass.{u1} F (MonoidWithZero.toMulZeroOneClass.{u1} F (Semiring.toMonoidWithZero.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)))) (MulActionWithZero.toSMulWithZero.{u1, u2} F A (Semiring.toMonoidWithZero.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)))) (Module.toMulActionWithZero.{u1, u2} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_17))))] [_inst_19 : StrongRankCondition.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12))] [_inst_20 : StrongRankCondition.{u2} K (Ring.toSemiring.{u2} K _inst_13)] [_inst_21 : Module.Free.{u1, u2} F K (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (AddCommGroup.toAddCommMonoid.{u2} K (NonUnitalNonAssocRing.toAddCommGroup.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K _inst_13)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_12) (Ring.toSemiring.{u2} K _inst_13) _inst_15)] [_inst_22 : Module.Free.{u2, u2} K A (Ring.toSemiring.{u2} K _inst_13) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_16], Eq.{succ (succ u2)} Cardinal.{u2} (HMul.hMul.{succ u2, succ u2, succ u2} Cardinal.{u2} Cardinal.{u2} Cardinal.{u2} (instHMul.{succ u2} Cardinal.{u2} Cardinal.hasMul.{u2}) (Module.rank.{u1, u2} F K (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (AddCommGroup.toAddCommMonoid.{u2} K (NonUnitalNonAssocRing.toAddCommGroup.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K _inst_13)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_12) (Ring.toSemiring.{u2} K _inst_13) _inst_15)) (Module.rank.{u2, u2} K A (Ring.toSemiring.{u2} K _inst_13) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_16)) (Module.rank.{u1, u2} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_17)
but is expected to have type
  forall (F : Type.{u1}) (K : Type.{u2}) (A : Type.{u2}) [_inst_12 : CommRing.{u1} F] [_inst_13 : Ring.{u2} K] [_inst_14 : AddCommGroup.{u2} A] [_inst_15 : Algebra.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_12) (Ring.toSemiring.{u2} K _inst_13)] [_inst_16 : Module.{u2, u2} K A (Ring.toSemiring.{u2} K _inst_13) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)] [_inst_17 : Module.{u1, u2} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14)] [_inst_18 : IsScalarTower.{u1, u2, u2} F K A (Algebra.toSMul.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_12) (Ring.toSemiring.{u2} K _inst_13) _inst_15) (SMulZeroClass.toSMul.{u2, u2} K A (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (SubtractionCommMonoid.toSubtractionMonoid.{u2} A (AddCommGroup.toDivisionAddCommMonoid.{u2} A _inst_14))))) (SMulWithZero.toSMulZeroClass.{u2, u2} K A (MonoidWithZero.toZero.{u2} K (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K _inst_13))) (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (SubtractionCommMonoid.toSubtractionMonoid.{u2} A (AddCommGroup.toDivisionAddCommMonoid.{u2} A _inst_14))))) (MulActionWithZero.toSMulWithZero.{u2, u2} K A (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K _inst_13)) (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (SubtractionCommMonoid.toSubtractionMonoid.{u2} A (AddCommGroup.toDivisionAddCommMonoid.{u2} A _inst_14))))) (Module.toMulActionWithZero.{u2, u2} K A (Ring.toSemiring.{u2} K _inst_13) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_16)))) (SMulZeroClass.toSMul.{u1, u2} F A (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (SubtractionCommMonoid.toSubtractionMonoid.{u2} A (AddCommGroup.toDivisionAddCommMonoid.{u2} A _inst_14))))) (SMulWithZero.toSMulZeroClass.{u1, u2} F A (CommMonoidWithZero.toZero.{u1} F (CommSemiring.toCommMonoidWithZero.{u1} F (CommRing.toCommSemiring.{u1} F _inst_12))) (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (SubtractionCommMonoid.toSubtractionMonoid.{u2} A (AddCommGroup.toDivisionAddCommMonoid.{u2} A _inst_14))))) (MulActionWithZero.toSMulWithZero.{u1, u2} F A (Semiring.toMonoidWithZero.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12))) (NegZeroClass.toZero.{u2} A (SubNegZeroMonoid.toNegZeroClass.{u2} A (SubtractionMonoid.toSubNegZeroMonoid.{u2} A (SubtractionCommMonoid.toSubtractionMonoid.{u2} A (AddCommGroup.toDivisionAddCommMonoid.{u2} A _inst_14))))) (Module.toMulActionWithZero.{u1, u2} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_17))))] [_inst_19 : StrongRankCondition.{u1} F (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12))] [_inst_20 : StrongRankCondition.{u2} K (Ring.toSemiring.{u2} K _inst_13)] [_inst_21 : Module.Free.{u1, u2} F K (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K _inst_13)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_12) (Ring.toSemiring.{u2} K _inst_13) _inst_15)] [_inst_22 : Module.Free.{u2, u2} K A (Ring.toSemiring.{u2} K _inst_13) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_16], Eq.{succ (succ u2)} Cardinal.{u2} (HMul.hMul.{succ u2, succ u2, succ u2} Cardinal.{u2} Cardinal.{u2} Cardinal.{u2} (instHMul.{succ u2} Cardinal.{u2} Cardinal.instMulCardinal.{u2}) (Module.rank.{u1, u2} F K (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K _inst_13)))) (Algebra.toModule.{u1, u2} F K (CommRing.toCommSemiring.{u1} F _inst_12) (Ring.toSemiring.{u2} K _inst_13) _inst_15)) (Module.rank.{u2, u2} K A (Ring.toSemiring.{u2} K _inst_13) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_16)) (Module.rank.{u1, u2} F A (Ring.toSemiring.{u1} F (CommRing.toRing.{u1} F _inst_12)) (AddCommGroup.toAddCommMonoid.{u2} A _inst_14) _inst_17)
Case conversion may be inaccurate. Consider using '#align rank_mul_rank rank_mul_rankₓ'. -/
/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$.

This is a simpler version of `lift_rank_mul_lift_rank` with `K` and `A` in the same universe. -/
theorem rank_mul_rank (F : Type u) (K A : Type v) [CommRing F] [Ring K] [AddCommGroup A]
    [Algebra F K] [Module K A] [Module F A] [IsScalarTower F K A] [StrongRankCondition F]
    [StrongRankCondition K] [Module.Free F K] [Module.Free K A] :
    Module.rank F K * Module.rank K A = Module.rank F A := by
  convert lift_rank_mul_lift_rank F K A <;> rw [lift_id]
#align rank_mul_rank rank_mul_rank

#print FiniteDimensional.finrank_mul_finrank' /-
/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$. -/
theorem FiniteDimensional.finrank_mul_finrank' [Nontrivial K] [Module.Finite F K]
    [Module.Finite K A] : finrank F K * finrank K A = finrank F A :=
  by
  letI := nontrivial_of_invariantBasisNumber F
  let b := Module.Free.chooseBasis F K
  let c := Module.Free.chooseBasis K A
  rw [finrank_eq_card_basis b, finrank_eq_card_basis c, finrank_eq_card_basis (b.smul c),
    Fintype.card_prod]
#align finite_dimensional.finrank_mul_finrank' FiniteDimensional.finrank_mul_finrank'
-/

end Ring

section Field

variable [Field F] [DivisionRing K] [AddCommGroup A]

variable [Algebra F K] [Module K A] [Module F A] [IsScalarTower F K A]

namespace FiniteDimensional

open IsNoetherian

#print FiniteDimensional.trans /-
theorem trans [FiniteDimensional F K] [FiniteDimensional K A] : FiniteDimensional F A :=
  Module.Finite.trans K A
#align finite_dimensional.trans FiniteDimensional.trans
-/

/- warning: finite_dimensional.left -> FiniteDimensional.left is a dubious translation:
lean 3 declaration is
  forall (F : Type.{u1}) [_inst_1 : Field.{u1} F] (K : Type.{u2}) (L : Type.{u3}) [_inst_8 : Field.{u2} K] [_inst_9 : Algebra.{u1, u2} F K (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8)))] [_inst_10 : Ring.{u3} L] [_inst_11 : Nontrivial.{u3} L] [_inst_12 : Algebra.{u1, u3} F L (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u3} L _inst_10)] [_inst_13 : Algebra.{u2, u3} K L (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8)) (Ring.toSemiring.{u3} L _inst_10)] [_inst_14 : IsScalarTower.{u1, u2, u3} F K L (SMulZeroClass.toHasSmul.{u1, u2} F K (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8))))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} F K (MulZeroClass.toHasZero.{u1} F (MulZeroOneClass.toMulZeroClass.{u1} F (MonoidWithZero.toMulZeroOneClass.{u1} F (Semiring.toMonoidWithZero.{u1} F (CommSemiring.toSemiring.{u1} F (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))))))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8))))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} F K (Semiring.toMonoidWithZero.{u1} F (CommSemiring.toSemiring.{u1} F (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8))))))))) (Module.toMulActionWithZero.{u1, u2} F K (CommSemiring.toSemiring.{u1} F (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8)))))) (Algebra.toModule.{u1, u2} F K (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8))) _inst_9))))) (SMulZeroClass.toHasSmul.{u2, u3} K L (AddZeroClass.toHasZero.{u3} L (AddMonoid.toAddZeroClass.{u3} L (AddCommMonoid.toAddMonoid.{u3} L (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} L (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} L (Semiring.toNonAssocSemiring.{u3} L (Ring.toSemiring.{u3} L _inst_10))))))) (SMulWithZero.toSmulZeroClass.{u2, u3} K L (MulZeroClass.toHasZero.{u2} K (MulZeroOneClass.toMulZeroClass.{u2} K (MonoidWithZero.toMulZeroOneClass.{u2} K (Semiring.toMonoidWithZero.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8))))))) (AddZeroClass.toHasZero.{u3} L (AddMonoid.toAddZeroClass.{u3} L (AddCommMonoid.toAddMonoid.{u3} L (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} L (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} L (Semiring.toNonAssocSemiring.{u3} L (Ring.toSemiring.{u3} L _inst_10))))))) (MulActionWithZero.toSMulWithZero.{u2, u3} K L (Semiring.toMonoidWithZero.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8)))) (AddZeroClass.toHasZero.{u3} L (AddMonoid.toAddZeroClass.{u3} L (AddCommMonoid.toAddMonoid.{u3} L (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} L (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} L (Semiring.toNonAssocSemiring.{u3} L (Ring.toSemiring.{u3} L _inst_10))))))) (Module.toMulActionWithZero.{u2, u3} K L (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} L (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} L (Semiring.toNonAssocSemiring.{u3} L (Ring.toSemiring.{u3} L _inst_10)))) (Algebra.toModule.{u2, u3} K L (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8)) (Ring.toSemiring.{u3} L _inst_10) _inst_13))))) (SMulZeroClass.toHasSmul.{u1, u3} F L (AddZeroClass.toHasZero.{u3} L (AddMonoid.toAddZeroClass.{u3} L (AddCommMonoid.toAddMonoid.{u3} L (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} L (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} L (Semiring.toNonAssocSemiring.{u3} L (Ring.toSemiring.{u3} L _inst_10))))))) (SMulWithZero.toSmulZeroClass.{u1, u3} F L (MulZeroClass.toHasZero.{u1} F (MulZeroOneClass.toMulZeroClass.{u1} F (MonoidWithZero.toMulZeroOneClass.{u1} F (Semiring.toMonoidWithZero.{u1} F (CommSemiring.toSemiring.{u1} F (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))))))) (AddZeroClass.toHasZero.{u3} L (AddMonoid.toAddZeroClass.{u3} L (AddCommMonoid.toAddMonoid.{u3} L (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} L (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} L (Semiring.toNonAssocSemiring.{u3} L (Ring.toSemiring.{u3} L _inst_10))))))) (MulActionWithZero.toSMulWithZero.{u1, u3} F L (Semiring.toMonoidWithZero.{u1} F (CommSemiring.toSemiring.{u1} F (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)))) (AddZeroClass.toHasZero.{u3} L (AddMonoid.toAddZeroClass.{u3} L (AddCommMonoid.toAddMonoid.{u3} L (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} L (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} L (Semiring.toNonAssocSemiring.{u3} L (Ring.toSemiring.{u3} L _inst_10))))))) (Module.toMulActionWithZero.{u1, u3} F L (CommSemiring.toSemiring.{u1} F (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} L (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} L (Semiring.toNonAssocSemiring.{u3} L (Ring.toSemiring.{u3} L _inst_10)))) (Algebra.toModule.{u1, u3} F L (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u3} L _inst_10) _inst_12)))))] [_inst_15 : FiniteDimensional.{u1, u3} F L (Field.toDivisionRing.{u1} F _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u3} L (NonAssocRing.toNonUnitalNonAssocRing.{u3} L (Ring.toNonAssocRing.{u3} L _inst_10))) (Algebra.toModule.{u1, u3} F L (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u3} L _inst_10) _inst_12)], FiniteDimensional.{u1, u2} F K (Field.toDivisionRing.{u1} F _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8))))) (Algebra.toModule.{u1, u2} F K (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8))) _inst_9)
but is expected to have type
  forall (F : Type.{u3}) [_inst_1 : Field.{u3} F] (K : Type.{u2}) (L : Type.{u1}) [_inst_8 : Field.{u2} K] [_inst_9 : Algebra.{u3, u2} F K (Semifield.toCommSemiring.{u3} F (Field.toSemifield.{u3} F _inst_1)) (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8)))] [_inst_10 : Ring.{u1} L] [_inst_11 : Nontrivial.{u1} L] [_inst_12 : Algebra.{u3, u1} F L (Semifield.toCommSemiring.{u3} F (Field.toSemifield.{u3} F _inst_1)) (Ring.toSemiring.{u1} L _inst_10)] [_inst_13 : Algebra.{u2, u1} K L (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8)) (Ring.toSemiring.{u1} L _inst_10)] [_inst_14 : IsScalarTower.{u3, u2, u1} F K L (Algebra.toSMul.{u3, u2} F K (Semifield.toCommSemiring.{u3} F (Field.toSemifield.{u3} F _inst_1)) (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8))) _inst_9) (Algebra.toSMul.{u2, u1} K L (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8)) (Ring.toSemiring.{u1} L _inst_10) _inst_13) (Algebra.toSMul.{u3, u1} F L (Semifield.toCommSemiring.{u3} F (Field.toSemifield.{u3} F _inst_1)) (Ring.toSemiring.{u1} L _inst_10) _inst_12)] [_inst_15 : FiniteDimensional.{u3, u1} F L (Field.toDivisionRing.{u3} F _inst_1) (Ring.toAddCommGroup.{u1} L _inst_10) (Algebra.toModule.{u3, u1} F L (Semifield.toCommSemiring.{u3} F (Field.toSemifield.{u3} F _inst_1)) (Ring.toSemiring.{u1} L _inst_10) _inst_12)], FiniteDimensional.{u3, u2} F K (Field.toDivisionRing.{u3} F _inst_1) (Ring.toAddCommGroup.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8))) (Algebra.toModule.{u3, u2} F K (Semifield.toCommSemiring.{u3} F (Field.toSemifield.{u3} F _inst_1)) (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8))) _inst_9)
Case conversion may be inaccurate. Consider using '#align finite_dimensional.left FiniteDimensional.leftₓ'. -/
/-- In a tower of field extensions `L / K / F`, if `L / F` is finite, so is `K / F`.

(In fact, it suffices that `L` is a nontrivial ring.)

Note this cannot be an instance as Lean cannot infer `L`.
-/
theorem left (K L : Type _) [Field K] [Algebra F K] [Ring L] [Nontrivial L] [Algebra F L]
    [Algebra K L] [IsScalarTower F K L] [FiniteDimensional F L] : FiniteDimensional F K :=
  FiniteDimensional.of_injective (IsScalarTower.toAlgHom F K L).toLinearMap (RingHom.injective _)
#align finite_dimensional.left FiniteDimensional.left

#print FiniteDimensional.right /-
theorem right [hf : FiniteDimensional F A] : FiniteDimensional K A :=
  let ⟨⟨b, hb⟩⟩ := hf
  ⟨⟨b,
      Submodule.restrictScalars_injective F _ _ <|
        by
        rw [Submodule.restrictScalars_top, eq_top_iff, ← hb, Submodule.span_le]
        exact Submodule.subset_span⟩⟩
#align finite_dimensional.right FiniteDimensional.right
-/

#print FiniteDimensional.finrank_mul_finrank /-
/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`.

This is `finite_dimensional.finrank_mul_finrank'` with one fewer finiteness assumption. -/
theorem finrank_mul_finrank [FiniteDimensional F K] : finrank F K * finrank K A = finrank F A :=
  by
  by_cases hA : FiniteDimensional K A
  · skip
    rw [finrank_mul_finrank']
  · rw [finrank_of_infinite_dimensional hA, MulZeroClass.mul_zero, finrank_of_infinite_dimensional]
    exact mt (@right F K A _ _ _ _ _ _ _) hA
#align finite_dimensional.finrank_mul_finrank FiniteDimensional.finrank_mul_finrank
-/

/- warning: finite_dimensional.subalgebra.is_simple_order_of_finrank_prime -> FiniteDimensional.Subalgebra.isSimpleOrder_of_finrank_prime is a dubious translation:
lean 3 declaration is
  forall (F : Type.{u1}) [_inst_1 : Field.{u1} F] (A : Type.{u2}) [_inst_8 : Ring.{u2} A] [_inst_9 : IsDomain.{u2} A (Ring.toSemiring.{u2} A _inst_8)] [_inst_10 : Algebra.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8)], (Nat.Prime (FiniteDimensional.finrank.{u1, u2} F A (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) (NonUnitalNonAssocRing.toAddCommGroup.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A _inst_8))) (Algebra.toModule.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8) _inst_10))) -> (IsSimpleOrder.{u2} (Subalgebra.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8) _inst_10) (Preorder.toLE.{u2} (Subalgebra.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8) _inst_10) (PartialOrder.toPreorder.{u2} (Subalgebra.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8) _inst_10) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subalgebra.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8) _inst_10) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subalgebra.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8) _inst_10) (Algebra.Subalgebra.completeLattice.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8) _inst_10))))) (CompleteLattice.toBoundedOrder.{u2} (Subalgebra.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8) _inst_10) (Algebra.Subalgebra.completeLattice.{u1, u2} F A (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} A _inst_8) _inst_10)))
but is expected to have type
  forall (F : Type.{u2}) [_inst_1 : Field.{u2} F] (A : Type.{u1}) [_inst_8 : Ring.{u1} A] [_inst_9 : IsDomain.{u1} A (Ring.toSemiring.{u1} A _inst_8)] [_inst_10 : Algebra.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8)], (Nat.Prime (FiniteDimensional.finrank.{u2, u1} F A (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1))) (Ring.toAddCommGroup.{u1} A _inst_8) (Algebra.toModule.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8) _inst_10))) -> (IsSimpleOrder.{u1} (Subalgebra.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8) _inst_10) (Preorder.toLE.{u1} (Subalgebra.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8) _inst_10) (PartialOrder.toPreorder.{u1} (Subalgebra.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8) _inst_10) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subalgebra.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8) _inst_10) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subalgebra.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8) _inst_10) (Algebra.instCompleteLatticeSubalgebra.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8) _inst_10))))) (CompleteLattice.toBoundedOrder.{u1} (Subalgebra.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8) _inst_10) (Algebra.instCompleteLatticeSubalgebra.{u2, u1} F A (Semifield.toCommSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)) (Ring.toSemiring.{u1} A _inst_8) _inst_10)))
Case conversion may be inaccurate. Consider using '#align finite_dimensional.subalgebra.is_simple_order_of_finrank_prime FiniteDimensional.Subalgebra.isSimpleOrder_of_finrank_primeₓ'. -/
theorem Subalgebra.isSimpleOrder_of_finrank_prime (A) [Ring A] [IsDomain A] [Algebra F A]
    (hp : (finrank F A).Prime) : IsSimpleOrder (Subalgebra F A) :=
  { to_nontrivial :=
      ⟨⟨⊥, ⊤, fun he =>
          Nat.not_prime_one ((Subalgebra.bot_eq_top_iff_finrank_eq_one.1 he).subst hp)⟩⟩
    eq_bot_or_eq_top := fun K =>
      by
      haveI := finite_dimensional_of_finrank hp.pos
      letI := divisionRingOfFiniteDimensional F K
      refine' (hp.eq_one_or_self_of_dvd _ ⟨_, (finrank_mul_finrank F K A).symm⟩).imp _ fun h => _
      · exact Subalgebra.eq_bot_of_finrank_one
      ·
        exact
          Algebra.toSubmodule_eq_top.1 (eq_top_of_finrank_eq <| K.finrank_to_submodule.trans h) }
#align finite_dimensional.subalgebra.is_simple_order_of_finrank_prime FiniteDimensional.Subalgebra.isSimpleOrder_of_finrank_prime

#print LinearMap.finite_dimensional'' /-
-- TODO: `intermediate_field` version 
-- TODO: generalize by removing [finite_dimensional F K]
-- V = ⊕F,
-- (V →ₗ[F] K) = ((⊕F) →ₗ[F] K) = (⊕ (F →ₗ[F] K)) = ⊕K
instance LinearMap.finite_dimensional'' (F : Type u) (K : Type v) (V : Type w) [Field F] [Field K]
    [Algebra F K] [FiniteDimensional F K] [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
    FiniteDimensional K (V →ₗ[F] K) :=
  right F _ _
#align linear_map.finite_dimensional'' LinearMap.finite_dimensional''
-/

#print FiniteDimensional.finrank_linear_map' /-
theorem finrank_linear_map' (F : Type u) (K : Type v) (V : Type w) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
    finrank K (V →ₗ[F] K) = finrank F V :=
  mul_right_injective₀ finrank_pos.ne' <|
    calc
      finrank F K * finrank K (V →ₗ[F] K) = finrank F (V →ₗ[F] K) := finrank_mul_finrank _ _ _
      _ = finrank F V * finrank F K := (finrank_linearMap F V K)
      _ = finrank F K * finrank F V := mul_comm _ _
      
#align finite_dimensional.finrank_linear_map' FiniteDimensional.finrank_linear_map'
-/

end FiniteDimensional

end Field

