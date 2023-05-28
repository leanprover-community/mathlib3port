/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module linear_algebra.free_module.finite.matrix
! leanprover-community/mathlib commit f2b757fc5c341d88741b9c4630b1e8ba973c5726
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Finrank
import Mathbin.LinearAlgebra.FreeModule.Finite.Rank
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Finite and free modules using matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide some instances for finite and free modules involving matrices.

## Main results

* `module.free.linear_map` : if `M` and `N` are finite and free, then `M →ₗ[R] N` is free.
* `module.finite.of_basis` : A free module with a basis indexed by a `fintype` is finite.
* `module.finite.linear_map` : if `M` and `N` are finite and free, then `M →ₗ[R] N`
  is finite.
-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open Module.Free (chooseBasis)

open FiniteDimensional (finrank)

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

/- warning: module.free.linear_map -> Module.Free.linearMap is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u}) (M : Type.{v}) (N : Type.{w}) [_inst_1 : CommRing.{u} R] [_inst_2 : AddCommGroup.{v} M] [_inst_3 : Module.{u, v} R M (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2)] [_inst_4 : Module.Free.{u, v} R M (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2) _inst_3] [_inst_5 : AddCommGroup.{w} N] [_inst_6 : Module.{u, w} R N (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{w} N _inst_5)] [_inst_7 : Module.Free.{u, w} R N (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_6] [_inst_8 : Module.Finite.{u, v} R M (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2) _inst_3] [_inst_9 : Module.Finite.{u, w} R N (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_6], Module.Free.{u, max v w} R (LinearMap.{u, u, v, w} R R (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (RingHom.id.{u} R (Semiring.toNonAssocSemiring.{u} R (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)))) M N (AddCommGroup.toAddCommMonoid.{v} M _inst_2) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_3 _inst_6) (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (LinearMap.addCommMonoid.{u, u, v, w} R R M N (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_3 _inst_6 (RingHom.id.{u} R (Semiring.toNonAssocSemiring.{u} R (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1))))) (LinearMap.module.{u, u, u, v, w} R R R M N (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_3 _inst_6 (RingHom.id.{u} R (Semiring.toNonAssocSemiring.{u} R (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)))) (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) _inst_6 (smulCommClass_self.{u, w} R N (CommRing.toCommMonoid.{u} R _inst_1) (MulActionWithZero.toMulAction.{u, w} R N (Semiring.toMonoidWithZero.{u} R (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1))) (AddZeroClass.toHasZero.{w} N (AddMonoid.toAddZeroClass.{w} N (AddCommMonoid.toAddMonoid.{w} N (AddCommGroup.toAddCommMonoid.{w} N _inst_5)))) (Module.toMulActionWithZero.{u, w} R N (Ring.toSemiring.{u} R (CommRing.toRing.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_6))))
but is expected to have type
  forall (R : Type.{u}) (M : Type.{v}) (N : Type.{w}) [_inst_1 : CommRing.{u} R] [_inst_2 : AddCommGroup.{v} M] [_inst_3 : Module.{u, v} R M (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2)] [_inst_4 : Module.Free.{u, v} R M (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2) _inst_3] [_inst_5 : AddCommGroup.{w} N] [_inst_6 : Module.{u, w} R N (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{w} N _inst_5)] [_inst_7 : Module.Free.{u, w} R N (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_6] [_inst_8 : Module.Finite.{u, v} R M (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2) _inst_3] [_inst_9 : Module.Finite.{u, w} R N (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_6], Module.Free.{u, max w v} R (LinearMap.{u, u, v, w} R R (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (RingHom.id.{u} R (Semiring.toNonAssocSemiring.{u} R (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)))) M N (AddCommGroup.toAddCommMonoid.{v} M _inst_2) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_3 _inst_6) (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (LinearMap.addCommMonoid.{u, u, v, w} R R M N (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_3 _inst_6 (RingHom.id.{u} R (Semiring.toNonAssocSemiring.{u} R (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1))))) (LinearMap.instModuleLinearMapAddCommMonoid.{u, u, u, v, w} R R R M N (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{v} M _inst_2) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_3 _inst_6 (RingHom.id.{u} R (Semiring.toNonAssocSemiring.{u} R (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)))) (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) _inst_6 (smulCommClass_self.{u, w} R N (CommRing.toCommMonoid.{u} R _inst_1) (MulActionWithZero.toMulAction.{u, w} R N (Semiring.toMonoidWithZero.{u} R (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1))) (NegZeroClass.toZero.{w} N (SubNegZeroMonoid.toNegZeroClass.{w} N (SubtractionMonoid.toSubNegZeroMonoid.{w} N (SubtractionCommMonoid.toSubtractionMonoid.{w} N (AddCommGroup.toDivisionAddCommMonoid.{w} N _inst_5))))) (Module.toMulActionWithZero.{u, w} R N (CommSemiring.toSemiring.{u} R (CommRing.toCommSemiring.{u} R _inst_1)) (AddCommGroup.toAddCommMonoid.{w} N _inst_5) _inst_6))))
Case conversion may be inaccurate. Consider using '#align module.free.linear_map Module.Free.linearMapₓ'. -/
instance Module.Free.linearMap [Module.Finite R M] [Module.Finite R N] :
    Module.Free R (M →ₗ[R] N) :=
  by
  cases subsingleton_or_nontrivial R
  · apply Module.Free.of_subsingleton'
  classical exact
      Module.Free.of_equiv (LinearMap.toMatrix (choose_basis R M) (choose_basis R N)).symm
#align module.free.linear_map Module.Free.linearMap

variable {R}

#print Module.Finite.linearMap /-
instance Module.Finite.linearMap [Module.Finite R M] [Module.Finite R N] :
    Module.Finite R (M →ₗ[R] N) :=
  by
  cases subsingleton_or_nontrivial R
  · infer_instance
  classical
    have f := (LinearMap.toMatrix (choose_basis R M) (choose_basis R N)).symm
    exact Module.Finite.of_surjective f.to_linear_map (LinearEquiv.surjective f)
#align module.finite.linear_map Module.Finite.linearMap
-/

end CommRing

section Integer

variable [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M]

variable [AddCommGroup N] [Module.Finite ℤ N] [Module.Free ℤ N]

/- warning: module.finite.add_monoid_hom -> Module.Finite.addMonoidHom is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : AddCommGroup.{u1} M] [_inst_2 : Module.Finite.{0, u1} Int M Int.semiring (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1)] [_inst_3 : Module.Free.{0, u1} Int M Int.semiring (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1)] [_inst_4 : AddCommGroup.{u2} N] [_inst_5 : Module.Finite.{0, u2} Int N Int.semiring (AddCommGroup.toAddCommMonoid.{u2} N _inst_4) (AddCommGroup.intModule.{u2} N _inst_4)] [_inst_6 : Module.Free.{0, u2} Int N Int.semiring (AddCommGroup.toAddCommMonoid.{u2} N _inst_4) (AddCommGroup.intModule.{u2} N _inst_4)], Module.Finite.{0, max u2 u1} Int (AddMonoidHom.{u1, u2} M N (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1)))) (AddMonoid.toAddZeroClass.{u2} N (SubNegMonoid.toAddMonoid.{u2} N (AddGroup.toSubNegMonoid.{u2} N (AddCommGroup.toAddGroup.{u2} N _inst_4))))) Int.semiring (AddMonoidHom.addCommMonoid.{u1, u2} M N (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} N _inst_4)) (AddMonoidHom.module.{0, u1, u2} Int M N Int.semiring (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} N _inst_4) (AddCommGroup.intModule.{u2} N _inst_4))
but is expected to have type
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : AddCommGroup.{u1} M] [_inst_2 : Module.Finite.{0, u1} Int M Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1)] [_inst_3 : Module.Free.{0, u1} Int M Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1)] [_inst_4 : AddCommGroup.{u2} N] [_inst_5 : Module.Finite.{0, u2} Int N Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{u2} N _inst_4) (AddCommGroup.intModule.{u2} N _inst_4)] [_inst_6 : Module.Free.{0, u2} Int N Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{u2} N _inst_4) (AddCommGroup.intModule.{u2} N _inst_4)], Module.Finite.{0, max u2 u1} Int (AddMonoidHom.{u1, u2} M N (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1)))) (AddMonoid.toAddZeroClass.{u2} N (SubNegMonoid.toAddMonoid.{u2} N (AddGroup.toSubNegMonoid.{u2} N (AddCommGroup.toAddGroup.{u2} N _inst_4))))) Int.instSemiringInt (AddMonoidHom.addCommMonoid.{u1, u2} M N (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} N _inst_4)) (AddCommGroup.intModule.{max u1 u2} (AddMonoidHom.{u1, u2} M N (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1)))) (AddMonoid.toAddZeroClass.{u2} N (SubNegMonoid.toAddMonoid.{u2} N (AddGroup.toSubNegMonoid.{u2} N (AddCommGroup.toAddGroup.{u2} N _inst_4))))) (AddMonoidHom.addCommGroup.{u1, u2} M N (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1)))) _inst_4))
Case conversion may be inaccurate. Consider using '#align module.finite.add_monoid_hom Module.Finite.addMonoidHomₓ'. -/
instance Module.Finite.addMonoidHom : Module.Finite ℤ (M →+ N) :=
  Module.Finite.equiv (addMonoidHomLequivInt ℤ).symm
#align module.finite.add_monoid_hom Module.Finite.addMonoidHom

/- warning: module.free.add_monoid_hom -> Module.Free.addMonoidHom is a dubious translation:
lean 3 declaration is
  forall (M : Type.{v}) (N : Type.{w}) [_inst_1 : AddCommGroup.{v} M] [_inst_2 : Module.Finite.{0, v} Int M Int.semiring (AddCommGroup.toAddCommMonoid.{v} M _inst_1) (AddCommGroup.intModule.{v} M _inst_1)] [_inst_3 : Module.Free.{0, v} Int M Int.semiring (AddCommGroup.toAddCommMonoid.{v} M _inst_1) (AddCommGroup.intModule.{v} M _inst_1)] [_inst_4 : AddCommGroup.{w} N] [_inst_5 : Module.Finite.{0, w} Int N Int.semiring (AddCommGroup.toAddCommMonoid.{w} N _inst_4) (AddCommGroup.intModule.{w} N _inst_4)] [_inst_6 : Module.Free.{0, w} Int N Int.semiring (AddCommGroup.toAddCommMonoid.{w} N _inst_4) (AddCommGroup.intModule.{w} N _inst_4)], Module.Free.{0, max w v} Int (AddMonoidHom.{v, w} M N (AddMonoid.toAddZeroClass.{v} M (SubNegMonoid.toAddMonoid.{v} M (AddGroup.toSubNegMonoid.{v} M (AddCommGroup.toAddGroup.{v} M _inst_1)))) (AddMonoid.toAddZeroClass.{w} N (SubNegMonoid.toAddMonoid.{w} N (AddGroup.toSubNegMonoid.{w} N (AddCommGroup.toAddGroup.{w} N _inst_4))))) Int.semiring (AddMonoidHom.addCommMonoid.{v, w} M N (AddMonoid.toAddZeroClass.{v} M (SubNegMonoid.toAddMonoid.{v} M (AddGroup.toSubNegMonoid.{v} M (AddCommGroup.toAddGroup.{v} M _inst_1)))) (AddCommGroup.toAddCommMonoid.{w} N _inst_4)) (AddMonoidHom.module.{0, v, w} Int M N Int.semiring (SubNegMonoid.toAddMonoid.{v} M (AddGroup.toSubNegMonoid.{v} M (AddCommGroup.toAddGroup.{v} M _inst_1))) (AddCommGroup.toAddCommMonoid.{w} N _inst_4) (AddCommGroup.intModule.{w} N _inst_4))
but is expected to have type
  forall (M : Type.{v}) (N : Type.{w}) [_inst_1 : AddCommGroup.{v} M] [_inst_2 : Module.Finite.{0, v} Int M Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{v} M _inst_1) (AddCommGroup.intModule.{v} M _inst_1)] [_inst_3 : Module.Free.{0, v} Int M Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{v} M _inst_1) (AddCommGroup.intModule.{v} M _inst_1)] [_inst_4 : AddCommGroup.{w} N] [_inst_5 : Module.Finite.{0, w} Int N Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{w} N _inst_4) (AddCommGroup.intModule.{w} N _inst_4)] [_inst_6 : Module.Free.{0, w} Int N Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{w} N _inst_4) (AddCommGroup.intModule.{w} N _inst_4)], Module.Free.{0, max w v} Int (AddMonoidHom.{v, w} M N (AddMonoid.toAddZeroClass.{v} M (SubNegMonoid.toAddMonoid.{v} M (AddGroup.toSubNegMonoid.{v} M (AddCommGroup.toAddGroup.{v} M _inst_1)))) (AddMonoid.toAddZeroClass.{w} N (SubNegMonoid.toAddMonoid.{w} N (AddGroup.toSubNegMonoid.{w} N (AddCommGroup.toAddGroup.{w} N _inst_4))))) Int.instSemiringInt (AddMonoidHom.addCommMonoid.{v, w} M N (AddMonoid.toAddZeroClass.{v} M (SubNegMonoid.toAddMonoid.{v} M (AddGroup.toSubNegMonoid.{v} M (AddCommGroup.toAddGroup.{v} M _inst_1)))) (AddCommGroup.toAddCommMonoid.{w} N _inst_4)) (AddCommGroup.intModule.{max v w} (AddMonoidHom.{v, w} M N (AddMonoid.toAddZeroClass.{v} M (SubNegMonoid.toAddMonoid.{v} M (AddGroup.toSubNegMonoid.{v} M (AddCommGroup.toAddGroup.{v} M _inst_1)))) (AddMonoid.toAddZeroClass.{w} N (SubNegMonoid.toAddMonoid.{w} N (AddGroup.toSubNegMonoid.{w} N (AddCommGroup.toAddGroup.{w} N _inst_4))))) (AddMonoidHom.addCommGroup.{v, w} M N (AddMonoid.toAddZeroClass.{v} M (SubNegMonoid.toAddMonoid.{v} M (AddGroup.toSubNegMonoid.{v} M (AddCommGroup.toAddGroup.{v} M _inst_1)))) _inst_4))
Case conversion may be inaccurate. Consider using '#align module.free.add_monoid_hom Module.Free.addMonoidHomₓ'. -/
instance Module.Free.addMonoidHom : Module.Free ℤ (M →+ N) :=
  letI : Module.Free ℤ (M →ₗ[ℤ] N) := Module.Free.linearMap _ _ _
  Module.Free.of_equiv (addMonoidHomLequivInt ℤ).symm
#align module.free.add_monoid_hom Module.Free.addMonoidHom

end Integer

section CommRing

variable [CommRing R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

#print FiniteDimensional.finrank_linearMap /-
/-- The finrank of `M →ₗ[R] N` is `(finrank R M) * (finrank R N)`. -/
theorem FiniteDimensional.finrank_linearMap : finrank R (M →ₗ[R] N) = finrank R M * finrank R N :=
  by
  classical
    letI := nontrivial_of_invariantBasisNumber R
    have h := LinearMap.toMatrix (choose_basis R M) (choose_basis R N)
    simp_rw [h.finrank_eq, FiniteDimensional.finrank_matrix,
      FiniteDimensional.finrank_eq_card_chooseBasisIndex, mul_comm]
#align finite_dimensional.finrank_linear_map FiniteDimensional.finrank_linearMap
-/

end CommRing

/- warning: matrix.rank_vec_mul_vec -> Matrix.rank_vecMulVec is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.rank_vec_mul_vec Matrix.rank_vecMulVecₓ'. -/
theorem Matrix.rank_vecMulVec {K m n : Type u} [CommRing K] [StrongRankCondition K] [Fintype n]
    [DecidableEq n] (w : m → K) (v : n → K) : (Matrix.vecMulVec w v).toLin'.rank ≤ 1 :=
  by
  rw [Matrix.vecMulVec_eq, Matrix.toLin'_mul]
  refine' le_trans (LinearMap.rank_comp_le_left _ _) _
  refine' (LinearMap.rank_le_domain _).trans_eq _
  rw [rank_fun', Fintype.card_unit, Nat.cast_one]
#align matrix.rank_vec_mul_vec Matrix.rank_vecMulVec

