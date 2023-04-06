/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.trace
! leanprover-community/mathlib commit d64d67d000b974f0d86a2be7918cf800be6271c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic

/-!
# Trace of a matrix

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the trace of a matrix, the map sending a matrix to the sum of its diagonal
entries.

See also `linear_algebra.trace` for the trace of an endomorphism.

## Tags

matrix, trace, diagonal

-/


open BigOperators Matrix

namespace Matrix

variable {ι m n p : Type _} {α R S : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

section AddCommMonoid

variable [AddCommMonoid R]

#print Matrix.trace /-
/-- The trace of a square matrix. For more bundled versions, see:
* `matrix.trace_add_monoid_hom`
* `matrix.trace_linear_map`
-/
def trace (A : Matrix n n R) : R :=
  ∑ i, diag A i
#align matrix.trace Matrix.trace
-/

variable (n R)

/- warning: matrix.trace_zero -> Matrix.trace_zero is a dubious translation:
lean 3 declaration is
  forall (n : Type.{u1}) (R : Type.{u2}) [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u2} R], Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 0 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 0 (Zero.zero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasZero.{u2, u1, u1} n n R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)))))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4))))))
but is expected to have type
  forall (n : Type.{u1}) (R : Type.{u2}) [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u2} R], Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 0 (Zero.toOfNat0.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.zero.{u2, u1, u1} n n R (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)))))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4))))
Case conversion may be inaccurate. Consider using '#align matrix.trace_zero Matrix.trace_zeroₓ'. -/
@[simp]
theorem trace_zero : trace (0 : Matrix n n R) = 0 :=
  (Finset.sum_const (0 : R)).trans <| smul_zero _
#align matrix.trace_zero Matrix.trace_zero

variable {n R}

/- warning: matrix.trace_add -> Matrix.trace_add is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u2} R] (A : Matrix.{u1, u1, u2} n n R) (B : Matrix.{u1, u1, u2} n n R), Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.{u1, u1, u2} n n R) (Matrix.{u1, u1, u2} n n R) (instHAdd.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasAdd.{u2, u1, u1} n n R (AddZeroClass.toHasAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4))))) A B)) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (AddZeroClass.toHasAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)))) (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 A) (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 B))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : Fintype.{u2} n] [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{u2, u2, u1} n n R) (B : Matrix.{u2, u2, u1} n n R), Eq.{succ u1} R (Matrix.trace.{u2, u1} n R _inst_2 _inst_4 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.{u2, u2, u1} n n R) (Matrix.{u2, u2, u1} n n R) (instHAdd.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.add.{u1, u2, u2} n n R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4))))) A B)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4)))) (Matrix.trace.{u2, u1} n R _inst_2 _inst_4 A) (Matrix.trace.{u2, u1} n R _inst_2 _inst_4 B))
Case conversion may be inaccurate. Consider using '#align matrix.trace_add Matrix.trace_addₓ'. -/
@[simp]
theorem trace_add (A B : Matrix n n R) : trace (A + B) = trace A + trace B :=
  Finset.sum_add_distrib
#align matrix.trace_add Matrix.trace_add

/- warning: matrix.trace_smul -> Matrix.trace_smul is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} {R : Type.{u3}} [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u3} R] [_inst_5 : Monoid.{u2} α] [_inst_6 : DistribMulAction.{u2, u3} α R _inst_5 (AddCommMonoid.toAddMonoid.{u3} R _inst_4)] (r : α) (A : Matrix.{u1, u1, u3} n n R), Eq.{succ u3} R (Matrix.trace.{u1, u3} n R _inst_2 _inst_4 (SMul.smul.{u2, max u1 u3} α (Matrix.{u1, u1, u3} n n R) (Matrix.hasSmul.{u3, u1, u1, u2} n n α R (SMulZeroClass.toHasSmul.{u2, u3} α R (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_4))) (DistribSMul.toSmulZeroClass.{u2, u3} α R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_4)) (DistribMulAction.toDistribSMul.{u2, u3} α R _inst_5 (AddCommMonoid.toAddMonoid.{u3} R _inst_4) _inst_6)))) r A)) (SMul.smul.{u2, u3} α R (SMulZeroClass.toHasSmul.{u2, u3} α R (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_4))) (DistribSMul.toSmulZeroClass.{u2, u3} α R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_4)) (DistribMulAction.toDistribSMul.{u2, u3} α R _inst_5 (AddCommMonoid.toAddMonoid.{u3} R _inst_4) _inst_6))) r (Matrix.trace.{u1, u3} n R _inst_2 _inst_4 A))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u3}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u2} R] [_inst_5 : Monoid.{u3} α] [_inst_6 : DistribMulAction.{u3, u2} α R _inst_5 (AddCommMonoid.toAddMonoid.{u2} R _inst_4)] (r : α) (A : Matrix.{u1, u1, u2} n n R), Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (Matrix.{u1, u1, u2} n n R) (Matrix.{u1, u1, u2} n n R) (instHSMul.{u3, max u1 u2} α (Matrix.{u1, u1, u2} n n R) (Matrix.smul.{u2, u1, u1, u3} n n α R (SMulZeroClass.toSMul.{u3, u2} α R (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)) (DistribSMul.toSMulZeroClass.{u3, u2} α R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)) (DistribMulAction.toDistribSMul.{u3, u2} α R _inst_5 (AddCommMonoid.toAddMonoid.{u2} R _inst_4) _inst_6))))) r A)) (HSMul.hSMul.{u3, u2, u2} α R R (instHSMul.{u3, u2} α R (SMulZeroClass.toSMul.{u3, u2} α R (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)) (DistribSMul.toSMulZeroClass.{u3, u2} α R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)) (DistribMulAction.toDistribSMul.{u3, u2} α R _inst_5 (AddCommMonoid.toAddMonoid.{u2} R _inst_4) _inst_6)))) r (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 A))
Case conversion may be inaccurate. Consider using '#align matrix.trace_smul Matrix.trace_smulₓ'. -/
@[simp]
theorem trace_smul [Monoid α] [DistribMulAction α R] (r : α) (A : Matrix n n R) :
    trace (r • A) = r • trace A :=
  Finset.smul_sum.symm
#align matrix.trace_smul Matrix.trace_smul

/- warning: matrix.trace_transpose -> Matrix.trace_transpose is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u2} R] (A : Matrix.{u1, u1, u2} n n R), Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 (Matrix.transpose.{u2, u1, u1} n n R A)) (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 A)
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : Fintype.{u2} n] [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{u2, u2, u1} n n R), Eq.{succ u1} R (Matrix.trace.{u2, u1} n R _inst_2 _inst_4 (Matrix.transpose.{u1, u2, u2} n n R A)) (Matrix.trace.{u2, u1} n R _inst_2 _inst_4 A)
Case conversion may be inaccurate. Consider using '#align matrix.trace_transpose Matrix.trace_transposeₓ'. -/
@[simp]
theorem trace_transpose (A : Matrix n n R) : trace Aᵀ = trace A :=
  rfl
#align matrix.trace_transpose Matrix.trace_transpose

#print Matrix.trace_conjTranspose /-
@[simp]
theorem trace_conjTranspose [StarAddMonoid R] (A : Matrix n n R) : trace Aᴴ = star (trace A) :=
  (star_sum _ _).symm
#align matrix.trace_conj_transpose Matrix.trace_conjTranspose
-/

variable (n α R)

#print Matrix.traceAddMonoidHom /-
/-- `matrix.trace` as an `add_monoid_hom` -/
@[simps]
def traceAddMonoidHom : Matrix n n R →+ R
    where
  toFun := trace
  map_zero' := trace_zero n R
  map_add' := trace_add
#align matrix.trace_add_monoid_hom Matrix.traceAddMonoidHom
-/

#print Matrix.traceLinearMap /-
/-- `matrix.trace` as a `linear_map` -/
@[simps]
def traceLinearMap [Semiring α] [Module α R] : Matrix n n R →ₗ[α] R
    where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul
#align matrix.trace_linear_map Matrix.traceLinearMap
-/

variable {n α R}

/- warning: matrix.trace_list_sum -> Matrix.trace_list_sum is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u2} R] (l : List.{max u1 u2} (Matrix.{u1, u1, u2} n n R)), Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 (List.sum.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasAdd.{u2, u1, u1} n n R (AddZeroClass.toHasAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)))) (Matrix.hasZero.{u2, u1, u1} n n R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)))) l)) (List.sum.{u2} R (AddZeroClass.toHasAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4))) (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4))) (List.map.{max u1 u2, u2} (Matrix.{u1, u1, u2} n n R) R (Matrix.trace.{u1, u2} n R _inst_2 _inst_4) l))
but is expected to have type
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u2} R] (l : List.{max u2 u1} (Matrix.{u1, u1, u2} n n R)), Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 _inst_4 (List.sum.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.add.{u2, u1, u1} n n R (AddZeroClass.toAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)))) (Matrix.zero.{u2, u1, u1} n n R (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4))) l)) (List.sum.{u2} R (AddZeroClass.toAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4))) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)) (List.map.{max u2 u1, u2} (Matrix.{u1, u1, u2} n n R) R (Matrix.trace.{u1, u2} n R _inst_2 _inst_4) l))
Case conversion may be inaccurate. Consider using '#align matrix.trace_list_sum Matrix.trace_list_sumₓ'. -/
@[simp]
theorem trace_list_sum (l : List (Matrix n n R)) : trace l.Sum = (l.map trace).Sum :=
  map_list_sum (traceAddMonoidHom n R) l
#align matrix.trace_list_sum Matrix.trace_list_sum

#print Matrix.trace_multiset_sum /-
@[simp]
theorem trace_multiset_sum (s : Multiset (Matrix n n R)) : trace s.Sum = (s.map trace).Sum :=
  map_multiset_sum (traceAddMonoidHom n R) s
#align matrix.trace_multiset_sum Matrix.trace_multiset_sum
-/

/- warning: matrix.trace_sum -> Matrix.trace_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : Fintype.{u2} n] [_inst_4 : AddCommMonoid.{u3} R] (s : Finset.{u1} ι) (f : ι -> (Matrix.{u2, u2, u3} n n R)), Eq.{succ u3} R (Matrix.trace.{u2, u3} n R _inst_2 _inst_4 (Finset.sum.{max u2 u3, u1} (Matrix.{u2, u2, u3} n n R) ι (Matrix.addCommMonoid.{u3, u2, u2} n n R _inst_4) s (fun (i : ι) => f i))) (Finset.sum.{u3, u1} R ι _inst_4 s (fun (i : ι) => Matrix.trace.{u2, u3} n R _inst_2 _inst_4 (f i)))
but is expected to have type
  forall {ι : Type.{u3}} {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : Fintype.{u2} n] [_inst_4 : AddCommMonoid.{u1} R] (s : Finset.{u3} ι) (f : ι -> (Matrix.{u2, u2, u1} n n R)), Eq.{succ u1} R (Matrix.trace.{u2, u1} n R _inst_2 _inst_4 (Finset.sum.{max u1 u2, u3} (Matrix.{u2, u2, u1} n n R) ι (Matrix.addCommMonoid.{u1, u2, u2} n n R _inst_4) s (fun (i : ι) => f i))) (Finset.sum.{u1, u3} R ι _inst_4 s (fun (i : ι) => Matrix.trace.{u2, u1} n R _inst_2 _inst_4 (f i)))
Case conversion may be inaccurate. Consider using '#align matrix.trace_sum Matrix.trace_sumₓ'. -/
@[simp]
theorem trace_sum (s : Finset ι) (f : ι → Matrix n n R) :
    trace (∑ i in s, f i) = ∑ i in s, trace (f i) :=
  map_sum (traceAddMonoidHom n R) f s
#align matrix.trace_sum Matrix.trace_sum

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R]

/- warning: matrix.trace_sub -> Matrix.trace_sub is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommGroup.{u2} R] (A : Matrix.{u1, u1, u2} n n R) (B : Matrix.{u1, u1, u2} n n R), Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u2} R _inst_4) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.{u1, u1, u2} n n R) (Matrix.{u1, u1, u2} n n R) (instHSub.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasSub.{u2, u1, u1} n n R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R _inst_4))))) A B)) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R _inst_4)))) (Matrix.trace.{u1, u2} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u2} R _inst_4) A) (Matrix.trace.{u1, u2} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u2} R _inst_4) B))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : Fintype.{u2} n] [_inst_4 : AddCommGroup.{u1} R] (A : Matrix.{u2, u2, u1} n n R) (B : Matrix.{u2, u2, u1} n n R), Eq.{succ u1} R (Matrix.trace.{u2, u1} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u1} R _inst_4) (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.{u2, u2, u1} n n R) (Matrix.{u2, u2, u1} n n R) (instHSub.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.sub.{u1, u2, u2} n n R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_4))))) A B)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_4)))) (Matrix.trace.{u2, u1} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u1} R _inst_4) A) (Matrix.trace.{u2, u1} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u1} R _inst_4) B))
Case conversion may be inaccurate. Consider using '#align matrix.trace_sub Matrix.trace_subₓ'. -/
@[simp]
theorem trace_sub (A B : Matrix n n R) : trace (A - B) = trace A - trace B :=
  Finset.sum_sub_distrib
#align matrix.trace_sub Matrix.trace_sub

/- warning: matrix.trace_neg -> Matrix.trace_neg is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommGroup.{u2} R] (A : Matrix.{u1, u1, u2} n n R), Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u2} R _inst_4) (Neg.neg.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasNeg.{u2, u1, u1} n n R (SubNegMonoid.toHasNeg.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R _inst_4)))) A)) (Neg.neg.{u2} R (SubNegMonoid.toHasNeg.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R _inst_4))) (Matrix.trace.{u1, u2} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u2} R _inst_4) A))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : Fintype.{u2} n] [_inst_4 : AddCommGroup.{u1} R] (A : Matrix.{u2, u2, u1} n n R), Eq.{succ u1} R (Matrix.trace.{u2, u1} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u1} R _inst_4) (Neg.neg.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.neg.{u1, u2, u2} n n R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (SubtractionCommMonoid.toSubtractionMonoid.{u1} R (AddCommGroup.toDivisionAddCommMonoid.{u1} R _inst_4)))))) A)) (Neg.neg.{u1} R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (SubtractionCommMonoid.toSubtractionMonoid.{u1} R (AddCommGroup.toDivisionAddCommMonoid.{u1} R _inst_4))))) (Matrix.trace.{u2, u1} n R _inst_2 (AddCommGroup.toAddCommMonoid.{u1} R _inst_4) A))
Case conversion may be inaccurate. Consider using '#align matrix.trace_neg Matrix.trace_negₓ'. -/
@[simp]
theorem trace_neg (A : Matrix n n R) : trace (-A) = -trace A :=
  Finset.sum_neg_distrib
#align matrix.trace_neg Matrix.trace_neg

end AddCommGroup

section One

variable [DecidableEq n] [AddCommMonoidWithOne R]

/- warning: matrix.trace_one -> Matrix.trace_one is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : DecidableEq.{succ u1} n] [_inst_5 : AddCommMonoidWithOne.{u2} R], Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 (AddCommMonoidWithOne.toAddCommMonoid.{u2} R _inst_5) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (One.one.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasOne.{u2, u1} n R (fun (a : n) (b : n) => _inst_4 a b) (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R _inst_5)))) (AddMonoidWithOne.toOne.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R _inst_5))))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u2} Nat R (CoeTCₓ.coe.{1, succ u2} Nat R (Nat.castCoe.{u2} R (AddMonoidWithOne.toNatCast.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R _inst_5))))) (Fintype.card.{u1} n _inst_2))
but is expected to have type
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : DecidableEq.{succ u1} n] [_inst_5 : AddCommMonoidWithOne.{u2} R], Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 (AddCommMonoidWithOne.toAddCommMonoid.{u2} R _inst_5) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (One.toOfNat1.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.one.{u2, u1} n R (fun (a : n) (b : n) => _inst_4 a b) (AddMonoid.toZero.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R _inst_5))) (AddMonoidWithOne.toOne.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R _inst_5)))))) (Nat.cast.{u2} R (AddMonoidWithOne.toNatCast.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R _inst_5)) (Fintype.card.{u1} n _inst_2))
Case conversion may be inaccurate. Consider using '#align matrix.trace_one Matrix.trace_oneₓ'. -/
@[simp]
theorem trace_one : trace (1 : Matrix n n R) = Fintype.card n := by
  simp_rw [trace, diag_one, Pi.one_def, Finset.sum_const, nsmul_one, Finset.card_univ]
#align matrix.trace_one Matrix.trace_one

end One

section Mul

/- warning: matrix.trace_transpose_mul -> Matrix.trace_transpose_mul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : Fintype.{u1} m] [_inst_2 : Fintype.{u2} n] [_inst_4 : AddCommMonoid.{u3} R] [_inst_5 : Mul.{u3} R] (A : Matrix.{u1, u2, u3} m n R) (B : Matrix.{u2, u1, u3} n m R), Eq.{succ u3} R (Matrix.trace.{u2, u3} n R _inst_2 _inst_4 (Matrix.mul.{u3, u2, u1, u2} n m n R _inst_1 _inst_5 _inst_4 (Matrix.transpose.{u3, u1, u2} m n R A) (Matrix.transpose.{u3, u2, u1} n m R B))) (Matrix.trace.{u1, u3} m R _inst_1 _inst_4 (Matrix.mul.{u3, u1, u2, u1} m n m R _inst_2 _inst_5 _inst_4 A B))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u3} R] [_inst_5 : Mul.{u3} R] (A : Matrix.{u2, u1, u3} m n R) (B : Matrix.{u1, u2, u3} n m R), Eq.{succ u3} R (Matrix.trace.{u1, u3} n R _inst_2 _inst_4 (Matrix.mul.{u3, u1, u2, u1} n m n R _inst_1 _inst_5 _inst_4 (Matrix.transpose.{u3, u2, u1} m n R A) (Matrix.transpose.{u3, u1, u2} n m R B))) (Matrix.trace.{u2, u3} m R _inst_1 _inst_4 (Matrix.mul.{u3, u2, u1, u2} m n m R _inst_2 _inst_5 _inst_4 A B))
Case conversion may be inaccurate. Consider using '#align matrix.trace_transpose_mul Matrix.trace_transpose_mulₓ'. -/
@[simp]
theorem trace_transpose_mul [AddCommMonoid R] [Mul R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (Aᵀ ⬝ Bᵀ) = trace (A ⬝ B) :=
  Finset.sum_comm
#align matrix.trace_transpose_mul Matrix.trace_transpose_mul

/- warning: matrix.trace_mul_comm -> Matrix.trace_mul_comm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : Fintype.{u1} m] [_inst_2 : Fintype.{u2} n] [_inst_4 : AddCommMonoid.{u3} R] [_inst_5 : CommSemigroup.{u3} R] (A : Matrix.{u1, u2, u3} m n R) (B : Matrix.{u2, u1, u3} n m R), Eq.{succ u3} R (Matrix.trace.{u1, u3} m R _inst_1 _inst_4 (Matrix.mul.{u3, u1, u2, u1} m n m R _inst_2 (Semigroup.toHasMul.{u3} R (CommSemigroup.toSemigroup.{u3} R _inst_5)) _inst_4 A B)) (Matrix.trace.{u2, u3} n R _inst_2 _inst_4 (Matrix.mul.{u3, u2, u1, u2} n m n R _inst_1 (Semigroup.toHasMul.{u3} R (CommSemigroup.toSemigroup.{u3} R _inst_5)) _inst_4 B A))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u1} n] [_inst_4 : AddCommMonoid.{u3} R] [_inst_5 : CommSemigroup.{u3} R] (A : Matrix.{u2, u1, u3} m n R) (B : Matrix.{u1, u2, u3} n m R), Eq.{succ u3} R (Matrix.trace.{u2, u3} m R _inst_1 _inst_4 (Matrix.mul.{u3, u2, u1, u2} m n m R _inst_2 (Semigroup.toMul.{u3} R (CommSemigroup.toSemigroup.{u3} R _inst_5)) _inst_4 A B)) (Matrix.trace.{u1, u3} n R _inst_2 _inst_4 (Matrix.mul.{u3, u1, u2, u1} n m n R _inst_1 (Semigroup.toMul.{u3} R (CommSemigroup.toSemigroup.{u3} R _inst_5)) _inst_4 B A))
Case conversion may be inaccurate. Consider using '#align matrix.trace_mul_comm Matrix.trace_mul_commₓ'. -/
theorem trace_mul_comm [AddCommMonoid R] [CommSemigroup R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (A ⬝ B) = trace (B ⬝ A) := by rw [← trace_transpose, ← trace_transpose_mul, transpose_mul]
#align matrix.trace_mul_comm Matrix.trace_mul_comm

/- warning: matrix.trace_mul_cycle -> Matrix.trace_mul_cycle is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {p : Type.{u3}} {R : Type.{u4}} [_inst_1 : Fintype.{u1} m] [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u3} p] [_inst_4 : NonUnitalCommSemiring.{u4} R] (A : Matrix.{u1, u2, u4} m n R) (B : Matrix.{u2, u3, u4} n p R) (C : Matrix.{u3, u1, u4} p m R), Eq.{succ u4} R (Matrix.trace.{u1, u4} m R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u1, u3, u1} m p m R _inst_3 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u1, u2, u3} m n p R _inst_2 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) A B) C)) (Matrix.trace.{u3, u4} p R _inst_3 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u3, u2, u3} p n p R _inst_2 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u3, u1, u2} p m n R _inst_1 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) C A) B))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {p : Type.{u1}} {R : Type.{u4}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u1} p] [_inst_4 : NonUnitalCommSemiring.{u4} R] (A : Matrix.{u3, u2, u4} m n R) (B : Matrix.{u2, u1, u4} n p R) (C : Matrix.{u1, u3, u4} p m R), Eq.{succ u4} R (Matrix.trace.{u3, u4} m R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u3, u1, u3} m p m R _inst_3 (NonUnitalNonAssocSemiring.toMul.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u3, u2, u1} m n p R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) A B) C)) (Matrix.trace.{u1, u4} p R _inst_3 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u1, u2, u1} p n p R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u1, u3, u2} p m n R _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) C A) B))
Case conversion may be inaccurate. Consider using '#align matrix.trace_mul_cycle Matrix.trace_mul_cycleₓ'. -/
theorem trace_mul_cycle [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) : trace (A ⬝ B ⬝ C) = trace (C ⬝ A ⬝ B) := by
  rw [trace_mul_comm, Matrix.mul_assoc]
#align matrix.trace_mul_cycle Matrix.trace_mul_cycle

/- warning: matrix.trace_mul_cycle' -> Matrix.trace_mul_cycle' is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {p : Type.{u3}} {R : Type.{u4}} [_inst_1 : Fintype.{u1} m] [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u3} p] [_inst_4 : NonUnitalCommSemiring.{u4} R] (A : Matrix.{u1, u2, u4} m n R) (B : Matrix.{u2, u3, u4} n p R) (C : Matrix.{u3, u1, u4} p m R), Eq.{succ u4} R (Matrix.trace.{u1, u4} m R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u1, u2, u1} m n m R _inst_2 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) A (Matrix.mul.{u4, u2, u3, u1} n p m R _inst_3 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) B C))) (Matrix.trace.{u3, u4} p R _inst_3 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u3, u1, u3} p m p R _inst_1 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) C (Matrix.mul.{u4, u1, u2, u3} m n p R _inst_2 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) A B)))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {p : Type.{u1}} {R : Type.{u4}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u1} p] [_inst_4 : NonUnitalCommSemiring.{u4} R] (A : Matrix.{u3, u2, u4} m n R) (B : Matrix.{u2, u1, u4} n p R) (C : Matrix.{u1, u3, u4} p m R), Eq.{succ u4} R (Matrix.trace.{u3, u4} m R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u3, u2, u3} m n m R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) A (Matrix.mul.{u4, u2, u1, u3} n p m R _inst_3 (NonUnitalNonAssocSemiring.toMul.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) B C))) (Matrix.trace.{u1, u4} p R _inst_3 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (Matrix.mul.{u4, u1, u3, u1} p m p R _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) C (Matrix.mul.{u4, u3, u2, u1} m n p R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R _inst_4))) A B)))
Case conversion may be inaccurate. Consider using '#align matrix.trace_mul_cycle' Matrix.trace_mul_cycle'ₓ'. -/
theorem trace_mul_cycle' [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) : trace (A ⬝ (B ⬝ C)) = trace (C ⬝ (A ⬝ B)) := by
  rw [← Matrix.mul_assoc, trace_mul_comm]
#align matrix.trace_mul_cycle' Matrix.trace_mul_cycle'

/- warning: matrix.trace_col_mul_row -> Matrix.trace_col_mul_row is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : NonUnitalNonAssocSemiring.{u2} R] (a : n -> R) (b : n -> R), Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_4) (Matrix.mul.{u2, u1, 0, u1} n Unit n R PUnit.fintype.{0} (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_4) (Matrix.col.{u2, u1} n R a) (Matrix.row.{u2, u1} n R b))) (Matrix.dotProduct.{u2, u1} n R _inst_2 (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_4) a b)
but is expected to have type
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_4 : NonUnitalNonAssocSemiring.{u2} R] (a : n -> R) (b : n -> R), Eq.{succ u2} R (Matrix.trace.{u1, u2} n R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_4) (Matrix.mul.{u2, u1, 0, u1} n Unit n R PUnit.fintype.{0} (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_4) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_4) (Matrix.col.{u2, u1} n R a) (Matrix.row.{u2, u1} n R b))) (Matrix.dotProduct.{u2, u1} n R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_4) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_4) a b)
Case conversion may be inaccurate. Consider using '#align matrix.trace_col_mul_row Matrix.trace_col_mul_rowₓ'. -/
@[simp]
theorem trace_col_mul_row [NonUnitalNonAssocSemiring R] (a b : n → R) :
    trace (col a ⬝ row b) = dotProduct a b := by simp [dot_product, trace]
#align matrix.trace_col_mul_row Matrix.trace_col_mul_row

end Mul

section Fin

variable [AddCommMonoid R]

/-! ### Special cases for `fin n`

While `simp [fin.sum_univ_succ]` can prove these, we include them for convenience and consistency
with `matrix.det_fin_two` etc.
-/


/- warning: matrix.trace_fin_zero -> Matrix.trace_fin_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) R), Eq.{succ u1} R (Matrix.trace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) R (Fin.fintype (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) _inst_4 A) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) R), Eq.{succ u1} R (Matrix.trace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) R (Fin.fintype (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) _inst_4 A) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4))))
Case conversion may be inaccurate. Consider using '#align matrix.trace_fin_zero Matrix.trace_fin_zeroₓ'. -/
@[simp]
theorem trace_fin_zero (A : Matrix (Fin 0) (Fin 0) R) : trace A = 0 :=
  rfl
#align matrix.trace_fin_zero Matrix.trace_fin_zero

/- warning: matrix.trace_fin_one -> Matrix.trace_fin_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Fin (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) R), Eq.{succ u1} R (Matrix.trace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) R (Fin.fintype (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) _inst_4 A) (A (OfNat.ofNat.{0} (Fin (One.one.{0} Nat Nat.hasOne)) 0 (OfNat.mk.{0} (Fin (One.one.{0} Nat Nat.hasOne)) 0 (Zero.zero.{0} (Fin (One.one.{0} Nat Nat.hasOne)) (Fin.hasZeroOfNeZero (One.one.{0} Nat Nat.hasOne) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial))))) (OfNat.ofNat.{0} (Fin (One.one.{0} Nat Nat.hasOne)) 0 (OfNat.mk.{0} (Fin (One.one.{0} Nat Nat.hasOne)) 0 (Zero.zero.{0} (Fin (One.one.{0} Nat Nat.hasOne)) (Fin.hasZeroOfNeZero (One.one.{0} Nat Nat.hasOne) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) R), Eq.{succ u1} R (Matrix.trace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) R (Fin.fintype (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) _inst_4 A) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align matrix.trace_fin_one Matrix.trace_fin_oneₓ'. -/
theorem trace_fin_one (A : Matrix (Fin 1) (Fin 1) R) : trace A = A 0 0 :=
  add_zero _
#align matrix.trace_fin_one Matrix.trace_fin_one

/- warning: matrix.trace_fin_two -> Matrix.trace_fin_two is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R), Eq.{succ u1} R (Matrix.trace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_4 A) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4)))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R), Eq.{succ u1} R (Matrix.trace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_4 A) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4)))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align matrix.trace_fin_two Matrix.trace_fin_twoₓ'. -/
theorem trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : trace A = A 0 0 + A 1 1 :=
  congr_arg ((· + ·) _) (add_zero (A 1 1))
#align matrix.trace_fin_two Matrix.trace_fin_two

/- warning: matrix.trace_fin_three -> Matrix.trace_fin_three is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R), Eq.{succ u1} R (Matrix.trace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Fin.fintype (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_4 A) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4)))) (A (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))) (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))) (A (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))) (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))))) (A (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (bit0.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))) (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (bit0.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) R), Eq.{succ u1} R (Matrix.trace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) R (Fin.fintype (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) _inst_4 A) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_4)))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 2 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 2 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 2 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 2 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))
Case conversion may be inaccurate. Consider using '#align matrix.trace_fin_three Matrix.trace_fin_threeₓ'. -/
theorem trace_fin_three (A : Matrix (Fin 3) (Fin 3) R) : trace A = A 0 0 + A 1 1 + A 2 2 :=
  by
  rw [← add_zero (A 2 2), add_assoc]
  rfl
#align matrix.trace_fin_three Matrix.trace_fin_three

end Fin

end Matrix

