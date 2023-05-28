/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module algebra.direct_sum.finsupp
! leanprover-community/mathlib commit aa3a420527e0fbfd0f6615b95b761254a9166e12
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.DirectSum.Module
import Mathbin.Data.Finsupp.ToDfinsupp

/-!
# Results on direct sums and finitely supported functions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

1. The linear equivalence between finitely supported functions `ι →₀ M` and
the direct sum of copies of `M` indexed by `ι`.
-/


universe u v w

noncomputable section

open DirectSum

open LinearMap Submodule

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

section finsuppLEquivDirectSum

variable (R M) (ι : Type _) [DecidableEq ι]

/- warning: finsupp_lequiv_direct_sum -> finsuppLEquivDirectSum is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (ι : Type.{u3}) [_inst_4 : DecidableEq.{succ u3} ι], LinearEquiv.{u1, u1, max u3 u2, max u3 u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (finsuppLEquivDirectSum._proof_1.{u1} R _inst_1) (finsuppLEquivDirectSum._proof_2.{u1} R _inst_1) (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))) (DirectSum.{u3, u2} ι (fun (i : ι) => M) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u2} M _inst_2)) (Finsupp.addCommMonoid.{u3, u2} ι M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)) (DirectSum.addCommMonoid.{u3, u2} ι (fun (i : ι) => M) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u2} M _inst_2)) (Finsupp.module.{u3, u2, u1} ι M R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (DirectSum.module.{u1, u3, u2} R (Ring.toSemiring.{u1} R _inst_1) ι (fun (i : ι) => M) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (fun (i : ι) => _inst_3))
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (ι : Type.{u3}) [_inst_4 : DecidableEq.{succ u3} ι], LinearEquiv.{u1, u1, max u2 u3, max u2 u3} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Finsupp.{u3, u2} ι M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2)))))) (DirectSum.{u3, u2} ι (fun (i : ι) => M) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u2} ((fun (_i : ι) => M) i) _inst_2)) (Finsupp.addCommMonoid.{u3, u2} ι M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)) (instAddCommMonoidDirectSum.{u3, u2} ι (fun (i : ι) => M) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u2} ((fun (_i : ι) => M) i) _inst_2)) (Finsupp.module.{u3, u2, u1} ι M R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (DirectSum.instModuleDirectSumInstAddCommMonoidDirectSum.{u1, u3, u2} R (Ring.toSemiring.{u1} R _inst_1) ι (fun (i : ι) => M) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u2} ((fun (_i : ι) => M) i) _inst_2) (fun (i : ι) => _inst_3))
Case conversion may be inaccurate. Consider using '#align finsupp_lequiv_direct_sum finsuppLEquivDirectSumₓ'. -/
/-- The finitely supported functions `ι →₀ M` are in linear equivalence with the direct sum of
copies of M indexed by ι. -/
def finsuppLEquivDirectSum : (ι →₀ M) ≃ₗ[R] ⨁ i : ι, M :=
  haveI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  finsuppLequivDfinsupp R
#align finsupp_lequiv_direct_sum finsuppLEquivDirectSum

/- warning: finsupp_lequiv_direct_sum_single -> finsuppLEquivDirectSum_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align finsupp_lequiv_direct_sum_single finsuppLEquivDirectSum_singleₓ'. -/
@[simp]
theorem finsuppLEquivDirectSum_single (i : ι) (m : M) :
    finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i m :=
  Finsupp.toDfinsupp_single i m
#align finsupp_lequiv_direct_sum_single finsuppLEquivDirectSum_single

/- warning: finsupp_lequiv_direct_sum_symm_lof -> finsuppLEquivDirectSum_symm_lof is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align finsupp_lequiv_direct_sum_symm_lof finsuppLEquivDirectSum_symm_lofₓ'. -/
@[simp]
theorem finsuppLEquivDirectSum_symm_lof (i : ι) (m : M) :
    (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsupp.single i m :=
  letI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  Dfinsupp.toFinsupp_single i m
#align finsupp_lequiv_direct_sum_symm_lof finsuppLEquivDirectSum_symm_lof

end finsuppLEquivDirectSum

