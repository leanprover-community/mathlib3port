/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov

! This file was ported from Lean 3 source module linear_algebra.quotient
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.LinearAlgebra.Span

/-!
# Quotients by submodules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

-/


-- For most of this file we work over a noncommutative ring
section Ring

namespace Submodule

variable {R M : Type _} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]

variable (p p' : Submodule R M)

open LinearMap quotientAddGroup

#print Submodule.quotientRel /-
/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `-x + y ∈ p`.

Note this is equivalent to `y - x ∈ p`, but defined this way to be be defeq to the `add_subgroup`
version, where commutativity can't be assumed. -/
def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup
#align submodule.quotient_rel Submodule.quotientRel
-/

/- warning: submodule.quotient_rel_r_def -> Submodule.quotientRel_r_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) {x : M} {y : M}, Iff (Setoid.r.{succ u2} M (Submodule.quotientRel.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) x y) (Membership.Mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) x y) p)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) {x : M} {y : M}, Iff (Setoid.r.{succ u2} M (Submodule.quotientRel.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) x y) (Membership.mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) x y) p)
Case conversion may be inaccurate. Consider using '#align submodule.quotient_rel_r_def Submodule.quotientRel_r_defₓ'. -/
theorem quotientRel_r_def {x y : M} : @Setoid.r _ p.quotientRel x y ↔ x - y ∈ p :=
  Iff.trans
    (by
      rw [left_rel_apply, sub_eq_add_neg, neg_add, neg_neg]
      rfl)
    neg_mem_iff
#align submodule.quotient_rel_r_def Submodule.quotientRel_r_def

#print Submodule.hasQuotient /-
/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩
#align submodule.has_quotient Submodule.hasQuotient
-/

namespace Quotient

#print Submodule.Quotient.mk /-
/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''
#align submodule.quotient.mk Submodule.Quotient.mk
-/

/- warning: submodule.quotient.mk_eq_mk -> Submodule.Quotient.mk'_eq_mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} (x : M), Eq.{succ u2} (Quotient.{succ u2} M (Submodule.quotientRel.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Quotient.mk'.{succ u2} M (Submodule.quotientRel.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {p : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} (x : M), Eq.{succ u1} (Quotient.{succ u1} M (Submodule.quotientRel.{u2, u1} R M _inst_1 _inst_2 _inst_3 p)) (Quotient.mk'.{succ u1} M (Submodule.quotientRel.{u2, u1} R M _inst_1 _inst_2 _inst_3 p) x) (Submodule.Quotient.mk.{u2, u1} R M _inst_1 _inst_2 _inst_3 p x)
Case conversion may be inaccurate. Consider using '#align submodule.quotient.mk_eq_mk Submodule.Quotient.mk'_eq_mk'ₓ'. -/
@[simp]
theorem mk'_eq_mk' {p : Submodule R M} (x : M) : @Quotient.mk' _ (quotientRel p) x = mk x :=
  rfl
#align submodule.quotient.mk_eq_mk Submodule.Quotient.mk'_eq_mk'

/- warning: submodule.quotient.mk'_eq_mk -> Submodule.Quotient.mk''_eq_mk is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} (x : M), Eq.{succ u2} (Quotient.{succ u2} M (Submodule.quotientRel.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Quotient.mk''.{succ u2} M (Submodule.quotientRel.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {p : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} (x : M), Eq.{succ u1} (Quotient.{succ u1} M (Submodule.quotientRel.{u2, u1} R M _inst_1 _inst_2 _inst_3 p)) (Quotient.mk''.{succ u1} M (Submodule.quotientRel.{u2, u1} R M _inst_1 _inst_2 _inst_3 p) x) (Submodule.Quotient.mk.{u2, u1} R M _inst_1 _inst_2 _inst_3 p x)
Case conversion may be inaccurate. Consider using '#align submodule.quotient.mk'_eq_mk Submodule.Quotient.mk''_eq_mkₓ'. -/
@[simp]
theorem mk''_eq_mk {p : Submodule R M} (x : M) : (Quotient.mk'' x : M ⧸ p) = mk x :=
  rfl
#align submodule.quotient.mk'_eq_mk Submodule.Quotient.mk''_eq_mk

/- warning: submodule.quotient.quot_mk_eq_mk -> Submodule.Quotient.quot_mk_eq_mk is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} (x : M), Eq.{succ u2} (Quot.{succ u2} M (Setoid.r.{succ u2} M (Submodule.quotientRel.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))) (Quot.mk.{succ u2} M (Setoid.r.{succ u2} M (Submodule.quotientRel.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {p : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} (x : M), Eq.{succ u1} (Quot.{succ u1} M (Setoid.r.{succ u1} M (Submodule.quotientRel.{u2, u1} R M _inst_1 _inst_2 _inst_3 p))) (Quot.mk.{succ u1} M (Setoid.r.{succ u1} M (Submodule.quotientRel.{u2, u1} R M _inst_1 _inst_2 _inst_3 p)) x) (Submodule.Quotient.mk.{u2, u1} R M _inst_1 _inst_2 _inst_3 p x)
Case conversion may be inaccurate. Consider using '#align submodule.quotient.quot_mk_eq_mk Submodule.Quotient.quot_mk_eq_mkₓ'. -/
@[simp]
theorem quot_mk_eq_mk {p : Submodule R M} (x : M) : (Quot.mk _ x : M ⧸ p) = mk x :=
  rfl
#align submodule.quotient.quot_mk_eq_mk Submodule.Quotient.quot_mk_eq_mk

/- warning: submodule.quotient.eq' -> Submodule.Quotient.eq' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) {x : M} {y : M}, Iff (Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p y)) (Membership.Mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))) (Neg.neg.{u2} M (SubNegMonoid.toHasNeg.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))) x) y) p)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) {x : M} {y : M}, Iff (Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p y)) (Membership.mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))) (Neg.neg.{u2} M (NegZeroClass.toNeg.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) x) y) p)
Case conversion may be inaccurate. Consider using '#align submodule.quotient.eq' Submodule.Quotient.eq'ₓ'. -/
protected theorem eq' {x y : M} : (mk x : M ⧸ p) = mk y ↔ -x + y ∈ p :=
  QuotientAddGroup.eq
#align submodule.quotient.eq' Submodule.Quotient.eq'

/- warning: submodule.quotient.eq -> Submodule.Quotient.eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) {x : M} {y : M}, Iff (Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p y)) (Membership.Mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) x y) p)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) {x : M} {y : M}, Iff (Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p y)) (Membership.mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) x y) p)
Case conversion may be inaccurate. Consider using '#align submodule.quotient.eq Submodule.Quotient.eqₓ'. -/
protected theorem eq {x y : M} : (mk x : M ⧸ p) = mk y ↔ x - y ∈ p :=
  p.Quotient.eq''.trans (leftRel_apply.symm.trans p.quotientRel_r_def)
#align submodule.quotient.eq Submodule.Quotient.eq

instance : Zero (M ⧸ p) :=
  ⟨mk 0⟩

instance : Inhabited (M ⧸ p) :=
  ⟨0⟩

/- warning: submodule.quotient.mk_zero -> Submodule.Quotient.mk_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))))))))) (OfNat.ofNat.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) 0 (OfNat.mk.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) 0 (Zero.zero.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.HasQuotient.Quotient.hasZero.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2)))))))) (OfNat.ofNat.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) 0 (Zero.toOfNat0.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.instZeroQuotientSubmoduleToSemiringToAddCommMonoidHasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.mk_zero Submodule.Quotient.mk_zeroₓ'. -/
@[simp]
theorem mk_zero : mk 0 = (0 : M ⧸ p) :=
  rfl
#align submodule.quotient.mk_zero Submodule.Quotient.mk_zero

/- warning: submodule.quotient.mk_eq_zero -> Submodule.Quotient.mk_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {x : M} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Iff (Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (OfNat.ofNat.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) 0 (OfNat.mk.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) 0 (Zero.zero.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.HasQuotient.Quotient.hasZero.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))))) (Membership.Mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) x p)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {x : M} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Iff (Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (OfNat.ofNat.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) 0 (Zero.toOfNat0.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.instZeroQuotientSubmoduleToSemiringToAddCommMonoidHasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)))) (Membership.mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) x p)
Case conversion may be inaccurate. Consider using '#align submodule.quotient.mk_eq_zero Submodule.Quotient.mk_eq_zeroₓ'. -/
@[simp]
theorem mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x ∈ p := by simpa using (Quotient.eq' p : mk x = 0 ↔ _)
#align submodule.quotient.mk_eq_zero Submodule.Quotient.mk_eq_zero

#print Submodule.Quotient.addCommGroup /-
instance addCommGroup : AddCommGroup (M ⧸ p) :=
  QuotientAddGroup.Quotient.addCommGroup p.toAddSubgroup
#align submodule.quotient.add_comm_group Submodule.Quotient.addCommGroup
-/

/- warning: submodule.quotient.mk_add -> Submodule.Quotient.mk_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {x : M} {y : M} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))) x y)) (HAdd.hAdd.{u2, u2, u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (instHAdd.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddZeroClass.toHasAdd.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddMonoid.toAddZeroClass.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (SubNegMonoid.toAddMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))))))) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p y))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {x : M} {y : M} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))) x y)) (HAdd.hAdd.{u2, u2, u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (instHAdd.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddZeroClass.toAdd.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddMonoid.toAddZeroClass.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (SubNegMonoid.toAddMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))))))) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p y))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.mk_add Submodule.Quotient.mk_addₓ'. -/
@[simp]
theorem mk_add : (mk (x + y) : M ⧸ p) = mk x + mk y :=
  rfl
#align submodule.quotient.mk_add Submodule.Quotient.mk_add

/- warning: submodule.quotient.mk_neg -> Submodule.Quotient.mk_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {x : M} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p (Neg.neg.{u2} M (SubNegMonoid.toHasNeg.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))) x)) (Neg.neg.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (SubNegMonoid.toHasNeg.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)))) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {x : M} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p (Neg.neg.{u2} M (NegZeroClass.toNeg.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) x)) (Neg.neg.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (NegZeroClass.toNeg.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (SubNegZeroMonoid.toNegZeroClass.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (SubtractionMonoid.toSubNegZeroMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (SubtractionCommMonoid.toSubtractionMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toDivisionAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)))))) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.mk_neg Submodule.Quotient.mk_negₓ'. -/
@[simp]
theorem mk_neg : (mk (-x) : M ⧸ p) = -mk x :=
  rfl
#align submodule.quotient.mk_neg Submodule.Quotient.mk_neg

/- warning: submodule.quotient.mk_sub -> Submodule.Quotient.mk_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {x : M} {y : M} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) x y)) (HSub.hSub.{u2, u2, u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (instHSub.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (SubNegMonoid.toHasSub.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))))) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p y))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {x : M} {y : M} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) x y)) (HSub.hSub.{u2, u2, u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (instHSub.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (SubNegMonoid.toSub.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))))) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p y))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.mk_sub Submodule.Quotient.mk_subₓ'. -/
@[simp]
theorem mk_sub : (mk (x - y) : M ⧸ p) = mk x - mk y :=
  rfl
#align submodule.quotient.mk_sub Submodule.Quotient.mk_sub

section SMul

variable {S : Type _} [SMul S R] [SMul S M] [IsScalarTower S R M] (P : Submodule R M)

#print Submodule.Quotient.hasSmul' /-
instance hasSmul' : SMul S (M ⧸ P) :=
  ⟨fun a =>
    Quotient.map' ((· • ·) a) fun x y h =>
      leftRel_apply.mpr <| by simpa [smul_sub] using P.smul_mem (a • 1 : R) (left_rel_apply.mp h)⟩
#align submodule.quotient.has_smul' Submodule.Quotient.hasSmul'
-/

#print Submodule.Quotient.hasSmul /-
/-- Shortcut to help the elaborator in the common case. -/
instance hasSmul : SMul R (M ⧸ P) :=
  Quotient.hasSmul' P
#align submodule.quotient.has_smul Submodule.Quotient.hasSmul
-/

/- warning: submodule.quotient.mk_smul -> Submodule.Quotient.mk_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) {S : Type.{u3}} [_inst_4 : SMul.{u3, u1} S R] [_inst_5 : SMul.{u3, u2} S M] [_inst_6 : IsScalarTower.{u3, u1, u2} S R M _inst_4 (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) _inst_5] (r : S) (x : M), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p (SMul.smul.{u3, u2} S M _inst_5 r x)) (SMul.smul.{u3, u2} S (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.hasSmul'.{u1, u2, u3} R M _inst_1 _inst_2 _inst_3 S _inst_4 _inst_5 _inst_6 p) r (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u3} M] [_inst_3 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2)] (p : Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) _inst_3) {S : Type.{u1}} [_inst_4 : SMul.{u1, u2} S R] [_inst_5 : SMul.{u1, u3} S M] [_inst_6 : IsScalarTower.{u1, u2, u3} S R M _inst_4 (SMulZeroClass.toSMul.{u2, u3} R M (NegZeroClass.toZero.{u3} M (SubNegZeroMonoid.toNegZeroClass.{u3} M (SubtractionMonoid.toSubNegZeroMonoid.{u3} M (SubtractionCommMonoid.toSubtractionMonoid.{u3} M (AddCommGroup.toDivisionAddCommMonoid.{u3} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u3} R M (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u3} M (SubNegZeroMonoid.toNegZeroClass.{u3} M (SubtractionMonoid.toSubNegZeroMonoid.{u3} M (SubtractionCommMonoid.toSubtractionMonoid.{u3} M (AddCommGroup.toDivisionAddCommMonoid.{u3} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u3} M (SubNegZeroMonoid.toNegZeroClass.{u3} M (SubtractionMonoid.toSubNegZeroMonoid.{u3} M (SubtractionCommMonoid.toSubtractionMonoid.{u3} M (AddCommGroup.toDivisionAddCommMonoid.{u3} M _inst_2))))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) _inst_3)))) _inst_5] (r : S) (x : M), Eq.{succ u3} (HasQuotient.Quotient.{u3, u3} M (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u3} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.mk.{u2, u3} R M _inst_1 _inst_2 _inst_3 p (HSMul.hSMul.{u1, u3, u3} S M M (instHSMul.{u1, u3} S M _inst_5) r x)) (HSMul.hSMul.{u1, u3, u3} S (HasQuotient.Quotient.{u3, u3} M (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u3} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u3, u3} M (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u3} R M _inst_1 _inst_2 _inst_3) p) (instHSMul.{u1, u3} S (HasQuotient.Quotient.{u3, u3} M (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u3} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.hasSmul'.{u2, u3, u1} R M _inst_1 _inst_2 _inst_3 S _inst_4 _inst_5 _inst_6 p)) r (Submodule.Quotient.mk.{u2, u3} R M _inst_1 _inst_2 _inst_3 p x))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.mk_smul Submodule.Quotient.mk_smulₓ'. -/
@[simp]
theorem mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ p) = r • mk x :=
  rfl
#align submodule.quotient.mk_smul Submodule.Quotient.mk_smul

#print Submodule.Quotient.smulCommClass /-
instance smulCommClass (T : Type _) [SMul T R] [SMul T M] [IsScalarTower T R M]
    [SMulCommClass S T M] : SMulCommClass S T (M ⧸ P)
    where smul_comm x y := Quotient.ind' fun z => congr_arg mk (smul_comm _ _ _)
#align submodule.quotient.smul_comm_class Submodule.Quotient.smulCommClass
-/

#print Submodule.Quotient.isScalarTower /-
instance isScalarTower (T : Type _) [SMul T R] [SMul T M] [IsScalarTower T R M] [SMul S T]
    [IsScalarTower S T M] : IsScalarTower S T (M ⧸ P)
    where smul_assoc x y := Quotient.ind' fun z => congr_arg mk (smul_assoc _ _ _)
#align submodule.quotient.is_scalar_tower Submodule.Quotient.isScalarTower
-/

#print Submodule.Quotient.isCentralScalar /-
instance isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
    [IsCentralScalar S M] : IsCentralScalar S (M ⧸ P)
    where op_smul_eq_smul x := Quotient.ind' fun z => congr_arg mk <| op_smul_eq_smul _ _
#align submodule.quotient.is_central_scalar Submodule.Quotient.isCentralScalar
-/

end SMul

section Module

variable {S : Type _}

#print Submodule.Quotient.mulAction' /-
instance mulAction' [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : MulAction S (M ⧸ P) :=
  Function.Surjective.mulAction mk (surjective_quot_mk _) P.Quotient.mk_smul
#align submodule.quotient.mul_action' Submodule.Quotient.mulAction'
-/

/- warning: submodule.quotient.mul_action -> Submodule.Quotient.mulAction is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), MulAction.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Ring.toMonoid.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), MulAction.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.mul_action Submodule.Quotient.mulActionₓ'. -/
instance mulAction (P : Submodule R M) : MulAction R (M ⧸ P) :=
  Quotient.mulAction' P
#align submodule.quotient.mul_action Submodule.Quotient.mulAction

/- warning: submodule.quotient.smul_zero_class' -> Submodule.Quotient.smulZeroClass' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {S : Type.{u3}} [_inst_4 : SMul.{u3, u1} S R] [_inst_5 : SMulZeroClass.{u3, u2} S M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))] [_inst_6 : IsScalarTower.{u3, u1, u2} S R M _inst_4 (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (SMulZeroClass.toHasSmul.{u3, u2} S M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))))) _inst_5)] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), SMulZeroClass.{u3, u2} S (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.HasQuotient.Quotient.hasZero.{u1, u2} R M _inst_1 _inst_2 _inst_3 P)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {S : Type.{u3}} [_inst_4 : SMul.{u3, u1} S R] [_inst_5 : SMulZeroClass.{u3, u2} S M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2)))))] [_inst_6 : IsScalarTower.{u3, u1, u2} S R M _inst_4 (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (SMulZeroClass.toSMul.{u3, u2} S M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) _inst_5)] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), SMulZeroClass.{u3, u2} S (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.instZeroQuotientSubmoduleToSemiringToAddCommMonoidHasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3 P)
Case conversion may be inaccurate. Consider using '#align submodule.quotient.smul_zero_class' Submodule.Quotient.smulZeroClass'ₓ'. -/
instance smulZeroClass' [SMul S R] [SMulZeroClass S M] [IsScalarTower S R M] (P : Submodule R M) :
    SMulZeroClass S (M ⧸ P) :=
  ZeroHom.smulZeroClass ⟨mk, mk_zero _⟩ P.Quotient.mk_smul
#align submodule.quotient.smul_zero_class' Submodule.Quotient.smulZeroClass'

/- warning: submodule.quotient.smul_zero_class -> Submodule.Quotient.smulZeroClass is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), SMulZeroClass.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.HasQuotient.Quotient.hasZero.{u1, u2} R M _inst_1 _inst_2 _inst_3 P)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), SMulZeroClass.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.instZeroQuotientSubmoduleToSemiringToAddCommMonoidHasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3 P)
Case conversion may be inaccurate. Consider using '#align submodule.quotient.smul_zero_class Submodule.Quotient.smulZeroClassₓ'. -/
instance smulZeroClass (P : Submodule R M) : SMulZeroClass R (M ⧸ P) :=
  Quotient.smulZeroClass' P
#align submodule.quotient.smul_zero_class Submodule.Quotient.smulZeroClass

/- warning: submodule.quotient.distrib_smul' -> Submodule.Quotient.distribSmul' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {S : Type.{u3}} [_inst_4 : SMul.{u3, u1} S R] [_inst_5 : DistribSMul.{u3, u2} S M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))))] [_inst_6 : IsScalarTower.{u3, u1, u2} S R M _inst_4 (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (SMulZeroClass.toHasSmul.{u3, u2} S M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))))) (DistribSMul.toSmulZeroClass.{u3, u2} S M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) _inst_5))] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), DistribSMul.{u3, u2} S (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddMonoid.toAddZeroClass.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (SubNegMonoid.toAddMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 P)))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {S : Type.{u3}} [_inst_4 : SMul.{u3, u1} S R] [_inst_5 : DistribSMul.{u3, u2} S M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))))] [_inst_6 : IsScalarTower.{u3, u1, u2} S R M _inst_4 (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (SMulZeroClass.toSMul.{u3, u2} S M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (DistribSMul.toSMulZeroClass.{u3, u2} S M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) _inst_5))] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), DistribSMul.{u3, u2} S (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddMonoid.toAddZeroClass.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (SubNegMonoid.toAddMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 P)))))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.distrib_smul' Submodule.Quotient.distribSmul'ₓ'. -/
instance distribSmul' [SMul S R] [DistribSMul S M] [IsScalarTower S R M] (P : Submodule R M) :
    DistribSMul S (M ⧸ P) :=
  Function.Surjective.distribSMul ⟨mk, rfl, fun _ _ => rfl⟩ (surjective_quot_mk _)
    P.Quotient.mk_smul
#align submodule.quotient.distrib_smul' Submodule.Quotient.distribSmul'

#print Submodule.Quotient.distribSmul /-
instance distribSmul (P : Submodule R M) : DistribSMul R (M ⧸ P) :=
  Quotient.distribSmul' P
#align submodule.quotient.distrib_smul Submodule.Quotient.distribSmul
-/

/- warning: submodule.quotient.distrib_mul_action' -> Submodule.Quotient.distribMulAction' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {S : Type.{u3}} [_inst_4 : Monoid.{u3} S] [_inst_5 : SMul.{u3, u1} S R] [_inst_6 : DistribMulAction.{u3, u2} S M _inst_4 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))] [_inst_7 : IsScalarTower.{u3, u1, u2} S R M _inst_5 (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (SMulZeroClass.toHasSmul.{u3, u2} S M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))))) (DistribSMul.toSmulZeroClass.{u3, u2} S M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) (DistribMulAction.toDistribSMul.{u3, u2} S M _inst_4 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))) _inst_6)))] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), DistribMulAction.{u3, u2} S (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) _inst_4 (SubNegMonoid.toAddMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 P))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {S : Type.{u3}} [_inst_4 : Monoid.{u3} S] [_inst_5 : SMul.{u3, u1} S R] [_inst_6 : DistribMulAction.{u3, u2} S M _inst_4 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))] [_inst_7 : IsScalarTower.{u3, u1, u2} S R M _inst_5 (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (SMulZeroClass.toSMul.{u3, u2} S M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (DistribSMul.toSMulZeroClass.{u3, u2} S M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) (DistribMulAction.toDistribSMul.{u3, u2} S M _inst_4 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))) _inst_6)))] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), DistribMulAction.{u3, u2} S (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) _inst_4 (SubNegMonoid.toAddMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 P))))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.distrib_mul_action' Submodule.Quotient.distribMulAction'ₓ'. -/
instance distribMulAction' [Monoid S] [SMul S R] [DistribMulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : DistribMulAction S (M ⧸ P) :=
  Function.Surjective.distribMulAction ⟨mk, rfl, fun _ _ => rfl⟩ (surjective_quot_mk _)
    P.Quotient.mk_smul
#align submodule.quotient.distrib_mul_action' Submodule.Quotient.distribMulAction'

/- warning: submodule.quotient.distrib_mul_action -> Submodule.Quotient.distribMulAction is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), DistribMulAction.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Ring.toMonoid.{u1} R _inst_1) (SubNegMonoid.toAddMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 P))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), DistribMulAction.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (SubNegMonoid.toAddMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddGroup.toSubNegMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (AddCommGroup.toAddGroup.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) P) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 P))))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.distrib_mul_action Submodule.Quotient.distribMulActionₓ'. -/
instance distribMulAction (P : Submodule R M) : DistribMulAction R (M ⧸ P) :=
  Quotient.distribMulAction' P
#align submodule.quotient.distrib_mul_action Submodule.Quotient.distribMulAction

#print Submodule.Quotient.module' /-
instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M) :
    Module S (M ⧸ P) :=
  Function.Surjective.module _ ⟨mk, rfl, fun _ _ => rfl⟩ (surjective_quot_mk _) P.Quotient.mk_smul
#align submodule.quotient.module' Submodule.Quotient.module'
-/

#print Submodule.Quotient.module /-
instance module (P : Submodule R M) : Module R (M ⧸ P) :=
  Quotient.module' P
#align submodule.quotient.module Submodule.Quotient.module
-/

variable (S)

#print Submodule.Quotient.restrictScalarsEquiv /-
/-- The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an `R`-submodule,
where `P : submodule R M`.
-/
def restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=
  {
    Quotient.congrRight fun _ _ =>
      Iff.rfl with
    map_add' := fun x y => Quotient.inductionOn₂' x y fun x' y' => rfl
    map_smul' := fun c x => Quotient.inductionOn' x fun x' => rfl }
#align submodule.quotient.restrict_scalars_equiv Submodule.Quotient.restrictScalarsEquiv
-/

/- warning: submodule.quotient.restrict_scalars_equiv_mk -> Submodule.Quotient.restrictScalarsEquiv_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quotient.restrict_scalars_equiv_mk Submodule.Quotient.restrictScalarsEquiv_mkₓ'. -/
@[simp]
theorem restrictScalarsEquiv_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) : restrictScalarsEquiv S P (mk x) = mk x :=
  rfl
#align submodule.quotient.restrict_scalars_equiv_mk Submodule.Quotient.restrictScalarsEquiv_mk

/- warning: submodule.quotient.restrict_scalars_equiv_symm_mk -> Submodule.Quotient.restrictScalarsEquiv_symm_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quotient.restrict_scalars_equiv_symm_mk Submodule.Quotient.restrictScalarsEquiv_symm_mkₓ'. -/
@[simp]
theorem restrictScalarsEquiv_symm_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) : (restrictScalarsEquiv S P).symm (mk x) = mk x :=
  rfl
#align submodule.quotient.restrict_scalars_equiv_symm_mk Submodule.Quotient.restrictScalarsEquiv_symm_mk

end Module

#print Submodule.Quotient.mk_surjective /-
theorem mk_surjective : Function.Surjective (@mk _ _ _ _ _ p) :=
  by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩
#align submodule.quotient.mk_surjective Submodule.Quotient.mk_surjective
-/

/- warning: submodule.quotient.nontrivial_of_lt_top -> Submodule.Quotient.nontrivial_of_lt_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), (LT.lt.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toHasLt.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.partialOrder.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) p (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasTop.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))) -> (Nontrivial.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), (LT.lt.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toLT.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) p (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.instTopSubmodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))) -> (Nontrivial.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p))
Case conversion may be inaccurate. Consider using '#align submodule.quotient.nontrivial_of_lt_top Submodule.Quotient.nontrivial_of_lt_topₓ'. -/
theorem nontrivial_of_lt_top (h : p < ⊤) : Nontrivial (M ⧸ p) :=
  by
  obtain ⟨x, _, not_mem_s⟩ := SetLike.exists_of_lt h
  refine' ⟨⟨mk x, 0, _⟩⟩
  simpa using not_mem_s
#align submodule.quotient.nontrivial_of_lt_top Submodule.Quotient.nontrivial_of_lt_top

end Quotient

/- warning: submodule.quotient_bot.infinite -> Submodule.QuotientBot.infinite is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_4 : Infinite.{succ u2} M], Infinite.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Bot.bot.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasBot.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_4 : Infinite.{succ u2} M], Infinite.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Bot.bot.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.instBotSubmodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
Case conversion may be inaccurate. Consider using '#align submodule.quotient_bot.infinite Submodule.QuotientBot.infiniteₓ'. -/
instance QuotientBot.infinite [Infinite M] : Infinite (M ⧸ (⊥ : Submodule R M)) :=
  Infinite.of_injective Submodule.Quotient.mk fun x y h =>
    sub_eq_zero.mp <| (Submodule.Quotient.eq ⊥).mp h
#align submodule.quotient_bot.infinite Submodule.QuotientBot.infinite

/- warning: submodule.quotient_top.unique -> Submodule.QuotientTop.unique is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)], Unique.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasTop.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)], Unique.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.instTopSubmodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
Case conversion may be inaccurate. Consider using '#align submodule.quotient_top.unique Submodule.QuotientTop.uniqueₓ'. -/
instance QuotientTop.unique : Unique (M ⧸ (⊤ : Submodule R M))
    where
  default := 0
  uniq x := Quotient.inductionOn' x fun x => (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top
#align submodule.quotient_top.unique Submodule.QuotientTop.unique

/- warning: submodule.quotient_top.fintype -> Submodule.QuotientTop.fintype is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)], Fintype.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasTop.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)], Fintype.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.instTopSubmodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
Case conversion may be inaccurate. Consider using '#align submodule.quotient_top.fintype Submodule.QuotientTop.fintypeₓ'. -/
instance QuotientTop.fintype : Fintype (M ⧸ (⊤ : Submodule R M)) :=
  Fintype.ofSubsingleton 0
#align submodule.quotient_top.fintype Submodule.QuotientTop.fintype

variable {p}

/- warning: submodule.subsingleton_quotient_iff_eq_top -> Submodule.subsingleton_quotient_iff_eq_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3}, Iff (Subsingleton.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p)) (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) p (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasTop.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3}, Iff (Subsingleton.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p)) (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) p (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.instTopSubmodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
Case conversion may be inaccurate. Consider using '#align submodule.subsingleton_quotient_iff_eq_top Submodule.subsingleton_quotient_iff_eq_topₓ'. -/
theorem subsingleton_quotient_iff_eq_top : Subsingleton (M ⧸ p) ↔ p = ⊤ :=
  by
  constructor
  · rintro h
    refine' eq_top_iff.mpr fun x _ => _
    have : x - 0 ∈ p := (Submodule.Quotient.eq p).mp (Subsingleton.elim _ _)
    rwa [sub_zero] at this
  · rintro rfl
    infer_instance
#align submodule.subsingleton_quotient_iff_eq_top Submodule.subsingleton_quotient_iff_eq_top

/- warning: submodule.unique_quotient_iff_eq_top -> Submodule.unique_quotient_iff_eq_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3}, Iff (Nonempty.{succ u2} (Unique.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p))) (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) p (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasTop.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3}, Iff (Nonempty.{succ u2} (Unique.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p))) (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) p (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.instTopSubmodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))
Case conversion may be inaccurate. Consider using '#align submodule.unique_quotient_iff_eq_top Submodule.unique_quotient_iff_eq_topₓ'. -/
theorem unique_quotient_iff_eq_top : Nonempty (Unique (M ⧸ p)) ↔ p = ⊤ :=
  ⟨fun ⟨h⟩ => subsingleton_quotient_iff_eq_top.mp (@Unique.subsingleton h),
    by
    rintro rfl
    exact ⟨quotient_top.unique⟩⟩
#align submodule.unique_quotient_iff_eq_top Submodule.unique_quotient_iff_eq_top

variable (p)

#print Submodule.Quotient.fintype /-
noncomputable instance Quotient.fintype [Fintype M] (S : Submodule R M) : Fintype (M ⧸ S) :=
  @Quotient.fintype _ _ fun _ _ => Classical.dec _
#align submodule.quotient.fintype Submodule.Quotient.fintype
-/

#print Submodule.card_eq_card_quotient_mul_card /-
theorem card_eq_card_quotient_mul_card [Fintype M] (S : Submodule R M) [DecidablePred (· ∈ S)] :
    Fintype.card M = Fintype.card S * Fintype.card (M ⧸ S) :=
  by
  rw [mul_comm, ← Fintype.card_prod]
  exact Fintype.card_congr AddSubgroup.addGroupEquivQuotientProdAddSubgroup
#align submodule.card_eq_card_quotient_mul_card Submodule.card_eq_card_quotient_mul_card
-/

section

variable {M₂ : Type _} [AddCommGroup M₂] [Module R M₂]

/- warning: submodule.quot_hom_ext -> Submodule.quot_hom_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quot_hom_ext Submodule.quot_hom_extₓ'. -/
theorem quot_hom_ext ⦃f g : M ⧸ p →ₗ[R] M₂⦄ (h : ∀ x, f (Quotient.mk x) = g (Quotient.mk x)) :
    f = g :=
  LinearMap.ext fun x => Quotient.inductionOn' x h
#align submodule.quot_hom_ext Submodule.quot_hom_ext

#print Submodule.mkQ /-
/-- The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map. -/
def mkQ : M →ₗ[R] M ⧸ p where
  toFun := Quotient.mk
  map_add' := by simp
  map_smul' := by simp
#align submodule.mkq Submodule.mkQ
-/

/- warning: submodule.mkq_apply -> Submodule.mkQ_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (x : M), Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (coeFn.{succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (fun (_x : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) => M -> (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p)) (LinearMap.hasCoeToFun.{u1, u1, u2, u2} R R M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Submodule.mkQ.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (x : M), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) x) (FunLike.coe.{succ u2, succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u2, u2} R R M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Submodule.mkQ.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 p x)
Case conversion may be inaccurate. Consider using '#align submodule.mkq_apply Submodule.mkQ_applyₓ'. -/
@[simp]
theorem mkQ_apply (x : M) : p.mkQ x = Quotient.mk x :=
  rfl
#align submodule.mkq_apply Submodule.mkQ_apply

/- warning: submodule.mkq_surjective -> Submodule.mkQ_surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (A : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), Function.Surjective.{succ u2, succ u2} M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) A) (coeFn.{succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) A) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) A) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 A)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 A)) (fun (_x : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) A) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) A) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 A)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 A)) => M -> (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) A)) (LinearMap.hasCoeToFun.{u1, u1, u2, u2} R R M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) A) (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) A) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 A)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 A) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Submodule.mkQ.{u1, u2} R M _inst_1 _inst_2 _inst_3 A))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] (A : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3), Function.Surjective.{succ u1, succ u1} M (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) A) (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) A) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) A) (Submodule.Quotient.addCommGroup.{u2, u1} R M _inst_1 _inst_2 _inst_3 A)) _inst_3 (Submodule.Quotient.module.{u2, u1} R M _inst_1 _inst_2 _inst_3 A)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) A) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u1} R R M (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) A) (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) A) (Submodule.Quotient.addCommGroup.{u2, u1} R M _inst_1 _inst_2 _inst_3 A)) _inst_3 (Submodule.Quotient.module.{u2, u1} R M _inst_1 _inst_2 _inst_3 A) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (Submodule.mkQ.{u2, u1} R M _inst_1 _inst_2 _inst_3 A))
Case conversion may be inaccurate. Consider using '#align submodule.mkq_surjective Submodule.mkQ_surjectiveₓ'. -/
theorem mkQ_surjective (A : Submodule R M) : Function.Surjective A.mkQ := by
  rintro ⟨x⟩ <;> exact ⟨x, rfl⟩
#align submodule.mkq_surjective Submodule.mkQ_surjective

end

variable {R₂ M₂ : Type _} [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R →+* R₂}

/- warning: submodule.linear_map_qext -> Submodule.linearMap_qext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.linear_map_qext Submodule.linearMap_qextₓ'. -/
/-- Two `linear_map`s from a quotient module are equal if their compositions with
`submodule.mkq` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem linearMap_qext ⦃f g : M ⧸ p →ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkQ = g.comp p.mkQ) : f = g :=
  LinearMap.ext fun x => Quotient.inductionOn' x <| (LinearMap.congr_fun h : _)
#align submodule.linear_map_qext Submodule.linearMap_qext

/- warning: submodule.liftq -> Submodule.liftQ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) {R₂ : Type.{u3}} {M₂ : Type.{u4}} [_inst_4 : Ring.{u3} R₂] [_inst_5 : AddCommGroup.{u4} M₂] [_inst_6 : Module.{u3, u4} R₂ M₂ (Ring.toSemiring.{u3} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5)] {τ₁₂ : RingHom.{u1, u3} R R₂ (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u3} R₂ (Ring.toNonAssocRing.{u3} R₂ _inst_4))} (f : LinearMap.{u1, u3, u2, u4} R R₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) τ₁₂ M M₂ (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) _inst_3 _inst_6), (LE.le.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toHasLe.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.partialOrder.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) p (LinearMap.ker.{u1, u3, u2, u4, max u2 u4} R R₂ M M₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) _inst_3 _inst_6 τ₁₂ (LinearMap.{u1, u3, u2, u4} R R₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) τ₁₂ M M₂ (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) _inst_3 _inst_6) (LinearMap.semilinearMapClass.{u1, u3, u2, u4} R R₂ M M₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) _inst_3 _inst_6 τ₁₂) f)) -> (LinearMap.{u1, u3, u2, u4} R R₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) τ₁₂ (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) M₂ (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) _inst_6)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) {R₂ : Type.{u3}} {M₂ : Type.{u4}} [_inst_4 : Ring.{u3} R₂] [_inst_5 : AddCommGroup.{u4} M₂] [_inst_6 : Module.{u3, u4} R₂ M₂ (Ring.toSemiring.{u3} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5)] {τ₁₂ : RingHom.{u1, u3} R R₂ (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} R₂ (Ring.toSemiring.{u3} R₂ _inst_4))} (f : LinearMap.{u1, u3, u2, u4} R R₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) τ₁₂ M M₂ (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) _inst_3 _inst_6), (LE.le.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toLE.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) p (LinearMap.ker.{u1, u3, u2, u4, max u2 u4} R R₂ M M₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) _inst_3 _inst_6 τ₁₂ (LinearMap.{u1, u3, u2, u4} R R₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) τ₁₂ M M₂ (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) _inst_3 _inst_6) (LinearMap.semilinearMapClass.{u1, u3, u2, u4} R R₂ M M₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) _inst_3 _inst_6 τ₁₂) f)) -> (LinearMap.{u1, u3, u2, u4} R R₂ (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R₂ _inst_4) τ₁₂ (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) M₂ (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u4} M₂ _inst_5) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) _inst_6)
Case conversion may be inaccurate. Consider using '#align submodule.liftq Submodule.liftQₓ'. -/
/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
def liftQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ f.ker) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩ <;> exact f.map_smulₛₗ a x }
#align submodule.liftq Submodule.liftQ

/- warning: submodule.liftq_apply -> Submodule.liftQ_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.liftq_apply Submodule.liftQ_applyₓ'. -/
@[simp]
theorem liftQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) : p.liftQ f h (Quotient.mk x) = f x :=
  rfl
#align submodule.liftq_apply Submodule.liftQ_apply

/- warning: submodule.liftq_mkq -> Submodule.liftQ_mkQ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.liftq_mkq Submodule.liftQ_mkQₓ'. -/
@[simp]
theorem liftQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).comp p.mkQ = f := by ext <;> rfl
#align submodule.liftq_mkq Submodule.liftQ_mkQ

/- warning: submodule.liftq_span_singleton -> Submodule.liftQSpanSingleton is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.liftq_span_singleton Submodule.liftQSpanSingletonₓ'. -/
/-- Special case of `liftq` when `p` is the span of `x`. In this case, the condition on `f` simply
becomes vanishing at `x`.-/
def liftQSpanSingleton (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R ∙ x) →ₛₗ[τ₁₂] M₂ :=
  (R ∙ x).liftQ f <| by rw [span_singleton_le_iff_mem, LinearMap.mem_ker, h]
#align submodule.liftq_span_singleton Submodule.liftQSpanSingleton

/- warning: submodule.liftq_span_singleton_apply -> Submodule.liftQSpanSingleton_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.liftq_span_singleton_apply Submodule.liftQSpanSingleton_applyₓ'. -/
@[simp]
theorem liftQSpanSingleton_apply (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M) :
    liftQSpanSingleton x f h (Quotient.mk y) = f y :=
  rfl
#align submodule.liftq_span_singleton_apply Submodule.liftQSpanSingleton_apply

/- warning: submodule.range_mkq -> Submodule.range_mkQ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.range_mkq Submodule.range_mkQₓ'. -/
@[simp]
theorem range_mkQ : p.mkQ.range = ⊤ :=
  eq_top_iff'.2 <| by rintro ⟨x⟩ <;> exact ⟨x, rfl⟩
#align submodule.range_mkq Submodule.range_mkQ

#print Submodule.ker_mkQ /-
@[simp]
theorem ker_mkQ : p.mkQ.ker = p := by ext <;> simp
#align submodule.ker_mkq Submodule.ker_mkQ
-/

/- warning: submodule.le_comap_mkq -> Submodule.le_comap_mkQ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (p' : Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)), LE.le.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toHasLe.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.partialOrder.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) p (Submodule.comap.{u1, u1, u2, u2, u2} R R M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (LinearMap.semilinearMapClass.{u1, u1, u2, u2} R R M (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Submodule.mkQ.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) p')
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] (p : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (p' : Submodule.{u2, u1} R (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u2, u1} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u2, u1} R M _inst_1 _inst_2 _inst_3 p)), LE.le.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Preorder.toLE.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.completeLattice.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3))))) p (Submodule.comap.{u2, u2, u1, u1, u1} R R M (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u2, u1} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u2, u1} R M _inst_1 _inst_2 _inst_3 p) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u2, u1} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u2, u1} R M _inst_1 _inst_2 _inst_3 p)) (LinearMap.semilinearMapClass.{u2, u2, u1, u1} R R M (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u2, u1} R M _inst_1 _inst_2 _inst_3 p)) _inst_3 (Submodule.Quotient.module.{u2, u1} R M _inst_1 _inst_2 _inst_3 p) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (Submodule.mkQ.{u2, u1} R M _inst_1 _inst_2 _inst_3 p) p')
Case conversion may be inaccurate. Consider using '#align submodule.le_comap_mkq Submodule.le_comap_mkQₓ'. -/
theorem le_comap_mkQ (p' : Submodule R (M ⧸ p)) : p ≤ comap p.mkQ p' := by
  simpa using (comap_mono bot_le : p.mkq.ker ≤ comap p.mkq p')
#align submodule.le_comap_mkq Submodule.le_comap_mkQ

/- warning: submodule.mkq_map_self -> Submodule.mkQ_map_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mkq_map_self Submodule.mkQ_map_selfₓ'. -/
@[simp]
theorem mkQ_map_self : map p.mkQ p = ⊥ := by
  rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkq] <;> exact le_rfl
#align submodule.mkq_map_self Submodule.mkQ_map_self

/- warning: submodule.comap_map_mkq -> Submodule.comap_map_mkQ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.comap_map_mkq Submodule.comap_map_mkQₓ'. -/
@[simp]
theorem comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p ⊔ p' := by simp [comap_map_eq, sup_comm]
#align submodule.comap_map_mkq Submodule.comap_map_mkQ

/- warning: submodule.map_mkq_eq_top -> Submodule.map_mkQ_eq_top is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map_mkq_eq_top Submodule.map_mkQ_eq_topₓ'. -/
@[simp]
theorem map_mkQ_eq_top : map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤ := by
  simp only [map_eq_top_iff p.range_mkq, sup_comm, ker_mkq]
#align submodule.map_mkq_eq_top Submodule.map_mkQ_eq_top

variable (q : Submodule R₂ M₂)

/- warning: submodule.mapq -> Submodule.mapQ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mapq Submodule.mapQₓ'. -/
/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
def mapQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) : M ⧸ p →ₛₗ[τ₁₂] M₂ ⧸ q :=
  p.liftQ (q.mkQ.comp f) <| by simpa [ker_comp] using h
#align submodule.mapq Submodule.mapQ

/- warning: submodule.mapq_apply -> Submodule.mapQ_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mapq_apply Submodule.mapQ_applyₓ'. -/
@[simp]
theorem mapQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) :
    mapQ p q f h (Quotient.mk x) = Quotient.mk (f x) :=
  rfl
#align submodule.mapq_apply Submodule.mapQ_apply

/- warning: submodule.mapq_mkq -> Submodule.mapQ_mkQ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mapq_mkq Submodule.mapQ_mkQₓ'. -/
theorem mapQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) {h} : (mapQ p q f h).comp p.mkQ = q.mkQ.comp f := by
  ext x <;> rfl
#align submodule.mapq_mkq Submodule.mapQ_mkQ

/- warning: submodule.mapq_zero -> Submodule.mapQ_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mapq_zero Submodule.mapQ_zeroₓ'. -/
@[simp]
theorem mapQ_zero (h : p ≤ q.comap (0 : M →ₛₗ[τ₁₂] M₂) := (by simp)) :
    p.mapQ q (0 : M →ₛₗ[τ₁₂] M₂) h = 0 := by
  ext
  simp
#align submodule.mapq_zero Submodule.mapQ_zero

/- warning: submodule.mapq_comp -> Submodule.mapQ_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mapq_comp Submodule.mapQ_compₓ'. -/
/-- Given submodules `p ⊆ M`, `p₂ ⊆ M₂`, `p₃ ⊆ M₃` and maps `f : M → M₂`, `g : M₂ → M₃` inducing
`mapq f : M ⧸ p → M₂ ⧸ p₂` and `mapq g : M₂ ⧸ p₂ → M₃ ⧸ p₃` then
`mapq (g ∘ f) = (mapq g) ∘ (mapq f)`. -/
theorem mapQ_comp {R₃ M₃ : Type _} [Ring R₃] [AddCommGroup M₃] [Module R₃ M₃] (p₂ : Submodule R₂ M₂)
    (p₃ : Submodule R₃ M₃) {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃} [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]
    (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : p ≤ p₂.comap f) (hg : p₂ ≤ p₃.comap g)
    (h := hf.trans (comap_mono hg)) :
    p.mapQ p₃ (g.comp f) h = (p₂.mapQ p₃ g hg).comp (p.mapQ p₂ f hf) :=
  by
  ext
  simp
#align submodule.mapq_comp Submodule.mapQ_comp

/- warning: submodule.mapq_id -> Submodule.mapQ_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mapq_id Submodule.mapQ_idₓ'. -/
@[simp]
theorem mapQ_id
    (h : p ≤ p.comap LinearMap.id :=
      (by
        rw [comap_id]
        exact le_refl _)) :
    p.mapQ p LinearMap.id h = LinearMap.id := by
  ext
  simp
#align submodule.mapq_id Submodule.mapQ_id

/- warning: submodule.mapq_pow -> Submodule.mapQ_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.mapq_pow Submodule.mapQ_powₓ'. -/
theorem mapQ_pow {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ)
    (h' : p ≤ p.comap (f ^ k) := p.le_comap_pow_of_le_comap h k) :
    p.mapQ p (f ^ k) h' = p.mapQ p f h ^ k :=
  by
  induction' k with k ih
  · simp [LinearMap.one_eq_id]
  · simp only [LinearMap.iterate_succ, ← ih]
    apply p.mapq_comp
#align submodule.mapq_pow Submodule.mapQ_pow

/- warning: submodule.comap_liftq -> Submodule.comap_liftQ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.comap_liftq Submodule.comap_liftQₓ'. -/
theorem comap_liftQ (f : M →ₛₗ[τ₁₂] M₂) (h) : q.comap (p.liftQ f h) = (q.comap f).map (mkQ p) :=
  le_antisymm (by rintro ⟨x⟩ hx <;> exact ⟨_, hx, rfl⟩)
    (by rw [map_le_iff_le_comap, ← comap_comp, liftq_mkq] <;> exact le_rfl)
#align submodule.comap_liftq Submodule.comap_liftQ

/- warning: submodule.map_liftq -> Submodule.map_liftQ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map_liftq Submodule.map_liftQₓ'. -/
theorem map_liftQ [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) (q : Submodule R (M ⧸ p)) :
    q.map (p.liftQ f h) = (q.comap p.mkQ).map f :=
  le_antisymm (by rintro _ ⟨⟨x⟩, hxq, rfl⟩ <;> exact ⟨x, hxq, rfl⟩)
    (by rintro _ ⟨x, hxq, rfl⟩ <;> exact ⟨Quotient.mk' x, hxq, rfl⟩)
#align submodule.map_liftq Submodule.map_liftQ

/- warning: submodule.ker_liftq -> Submodule.ker_liftQ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.ker_liftq Submodule.ker_liftQₓ'. -/
theorem ker_liftQ (f : M →ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f h) = (ker f).map (mkQ p) :=
  comap_liftQ _ _ _ _
#align submodule.ker_liftq Submodule.ker_liftQ

/- warning: submodule.range_liftq -> Submodule.range_liftQ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.range_liftq Submodule.range_liftQₓ'. -/
theorem range_liftQ [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) :
    range (p.liftQ f h) = range f := by simpa only [range_eq_map] using map_liftq _ _ _ _
#align submodule.range_liftq Submodule.range_liftQ

/- warning: submodule.ker_liftq_eq_bot -> Submodule.ker_liftQ_eq_bot is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.ker_liftq_eq_bot Submodule.ker_liftQ_eq_botₓ'. -/
theorem ker_liftQ_eq_bot (f : M →ₛₗ[τ₁₂] M₂) (h) (h' : ker f ≤ p) : ker (p.liftQ f h) = ⊥ := by
  rw [ker_liftq, le_antisymm h h', mkq_map_self]
#align submodule.ker_liftq_eq_bot Submodule.ker_liftQ_eq_bot

/- warning: submodule.comap_mkq.rel_iso -> Submodule.comapMkQRelIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.comap_mkq.rel_iso Submodule.comapMkQRelIsoₓ'. -/
/-- The correspondence theorem for modules: there is an order isomorphism between submodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`. -/
def Submodule.comapMkQRelIso : Submodule R (M ⧸ p) ≃o { p' : Submodule R M // p ≤ p' }
    where
  toFun p' := ⟨comap p.mkQ p', le_comap_mkQ p _⟩
  invFun q := map p.mkQ q
  left_inv p' := map_comap_eq_self <| by simp
  right_inv := fun ⟨q, hq⟩ => Subtype.ext_val <| by simpa [comap_map_mkq p]
  map_rel_iff' p₁ p₂ := comap_le_comap_iff <| range_mkQ _
#align submodule.comap_mkq.rel_iso Submodule.comapMkQRelIso

/- warning: submodule.comap_mkq.order_embedding -> Submodule.comapMkQOrderEmbedding is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), OrderEmbedding.{u2, u2} (Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toHasLe.{u2} (Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (SetLike.partialOrder.{u2, u2} (Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.setLike.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))))) (Preorder.toHasLe.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.partialOrder.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), OrderEmbedding.{u2, u2} (Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toLE.{u2} (Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.completeLattice.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)))))) (Preorder.toLE.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))))
Case conversion may be inaccurate. Consider using '#align submodule.comap_mkq.order_embedding Submodule.comapMkQOrderEmbeddingₓ'. -/
/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def Submodule.comapMkQOrderEmbedding : Submodule R (M ⧸ p) ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| Submodule.comapMkQRelIso p).trans (Subtype.relEmbedding _ _)
#align submodule.comap_mkq.order_embedding Submodule.comapMkQOrderEmbedding

/- warning: submodule.comap_mkq_embedding_eq -> Submodule.comapMkQOrderEmbedding_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.comap_mkq_embedding_eq Submodule.comapMkQOrderEmbedding_eqₓ'. -/
@[simp]
theorem comapMkQOrderEmbedding_eq (p' : Submodule R (M ⧸ p)) :
    Submodule.comapMkQOrderEmbedding p p' = comap p.mkQ p' :=
  rfl
#align submodule.comap_mkq_embedding_eq Submodule.comapMkQOrderEmbedding_eq

/- warning: submodule.span_preimage_eq -> Submodule.span_preimage_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.span_preimage_eq Submodule.span_preimage_eqₓ'. -/
theorem span_preimage_eq [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {s : Set M₂} (h₀ : s.Nonempty)
    (h₁ : s ⊆ range f) : span R (f ⁻¹' s) = (span R₂ s).comap f :=
  by
  suffices (span R₂ s).comap f ≤ span R (f ⁻¹' s) by exact le_antisymm (span_preimage_le f s) this
  have hk : ker f ≤ span R (f ⁻¹' s) :=
    by
    let y := Classical.choose h₀
    have hy : y ∈ s := Classical.choose_spec h₀
    rw [ker_le_iff]
    use y, h₁ hy
    rw [← Set.singleton_subset_iff] at hy
    exact Set.Subset.trans subset_span (span_mono (Set.preimage_mono hy))
  rw [← left_eq_sup] at hk
  rw [f.range_coe] at h₁
  rw [hk, ← LinearMap.map_le_map_iff, map_span, map_comap_eq, Set.image_preimage_eq_of_subset h₁]
  exact inf_le_right
#align submodule.span_preimage_eq Submodule.span_preimage_eq

/- warning: submodule.quotient.equiv -> Submodule.Quotient.equiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quotient.equiv Submodule.Quotient.equivₓ'. -/
/-- If `P` is a submodule of `M` and `Q` a submodule of `N`,
and `f : M ≃ₗ N` maps `P` to `Q`, then `M ⧸ P` is equivalent to `N ⧸ Q`. -/
@[simps]
def Quotient.equiv {N : Type _} [AddCommGroup N] [Module R N] (P : Submodule R M)
    (Q : Submodule R N) (f : M ≃ₗ[R] N) (hf : P.map f = Q) : (M ⧸ P) ≃ₗ[R] N ⧸ Q :=
  {
    P.mapQ Q (f : M →ₗ[R] N) fun x hx =>
      hf ▸
        Submodule.mem_map_of_mem
          hx with
    toFun := P.mapQ Q (f : M →ₗ[R] N) fun x hx => hf ▸ Submodule.mem_map_of_mem hx
    invFun :=
      Q.mapQ P (f.symm : N →ₗ[R] M) fun x hx =>
        by
        rw [← hf, Submodule.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simpa
    left_inv := fun x => Quotient.inductionOn' x (by simp)
    right_inv := fun x => Quotient.inductionOn' x (by simp) }
#align submodule.quotient.equiv Submodule.Quotient.equiv

/- warning: submodule.quotient.equiv_symm -> Submodule.Quotient.equiv_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quotient.equiv_symm Submodule.Quotient.equiv_symmₓ'. -/
@[simp]
theorem Quotient.equiv_symm {R M N : Type _} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (P : Submodule R M) (Q : Submodule R N) (f : M ≃ₗ[R] N)
    (hf : P.map f = Q) :
    (Quotient.equiv P Q f hf).symm =
      Quotient.equiv Q P f.symm ((Submodule.map_symm_eq_iff f).mpr hf) :=
  rfl
#align submodule.quotient.equiv_symm Submodule.Quotient.equiv_symm

/- warning: submodule.quotient.equiv_trans -> Submodule.Quotient.equiv_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quotient.equiv_trans Submodule.Quotient.equiv_transₓ'. -/
@[simp]
theorem Quotient.equiv_trans {N O : Type _} [AddCommGroup N] [Module R N] [AddCommGroup O]
    [Module R O] (P : Submodule R M) (Q : Submodule R N) (S : Submodule R O) (e : M ≃ₗ[R] N)
    (f : N ≃ₗ[R] O) (he : P.map e = Q) (hf : Q.map f = S) (hef : P.map (e.trans f) = S) :
    Quotient.equiv P S (e.trans f) hef =
      (Quotient.equiv P Q e he).trans (Quotient.equiv Q S f hf) :=
  by
  ext
  -- `simp` can deal with `hef` depending on `e` and `f`
  simp only [quotient.equiv_apply, LinearEquiv.trans_apply, LinearEquiv.coe_trans]
  -- `rw` can deal with `mapq_comp` needing extra hypotheses coming from the RHS
  rw [mapq_comp, LinearMap.comp_apply]
#align submodule.quotient.equiv_trans Submodule.Quotient.equiv_trans

end Submodule

open Submodule

namespace LinearMap

section Ring

variable {R M R₂ M₂ R₃ M₃ : Type _}

variable [Ring R] [Ring R₂] [Ring R₃]

variable [AddCommMonoid M] [AddCommGroup M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] [RingHomSurjective τ₁₂]

/- warning: linear_map.range_mkq_comp -> LinearMap.range_mkQ_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.range_mkq_comp LinearMap.range_mkQ_compₓ'. -/
theorem range_mkQ_comp (f : M →ₛₗ[τ₁₂] M₂) : f.range.mkQ.comp f = 0 :=
  LinearMap.ext fun x => by simp
#align linear_map.range_mkq_comp LinearMap.range_mkQ_comp

/- warning: linear_map.ker_le_range_iff -> LinearMap.ker_le_range_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.ker_le_range_iff LinearMap.ker_le_range_iffₓ'. -/
theorem ker_le_range_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    g.ker ≤ f.range ↔ f.range.mkQ.comp g.ker.Subtype = 0 := by
  rw [← range_le_ker_iff, Submodule.ker_mkQ, Submodule.range_subtype]
#align linear_map.ker_le_range_iff LinearMap.ker_le_range_iff

/- warning: linear_map.range_eq_top_of_cancel -> LinearMap.range_eq_top_of_cancel is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.range_eq_top_of_cancel LinearMap.range_eq_top_of_cancelₓ'. -/
/-- An epimorphism is surjective. -/
theorem range_eq_top_of_cancel {f : M →ₛₗ[τ₁₂] M₂}
    (h : ∀ u v : M₂ →ₗ[R₂] M₂ ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ :=
  by
  have h₁ : (0 : M₂ →ₗ[R₂] M₂ ⧸ f.range).comp f = 0 := zero_comp _
  rw [← Submodule.ker_mkQ f.range, ← h 0 f.range.mkq (Eq.trans h₁ (range_mkq_comp _).symm)]
  exact ker_zero
#align linear_map.range_eq_top_of_cancel LinearMap.range_eq_top_of_cancel

end Ring

end LinearMap

open LinearMap

namespace Submodule

variable {R M : Type _} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]

variable (p p' : Submodule R M)

/- warning: submodule.quot_equiv_of_eq_bot -> Submodule.quotEquivOfEqBot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) p (Bot.bot.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasBot.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))) -> (LinearEquiv.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Submodule.quotEquivOfEqBot._proof_1.{u1} R _inst_1) (Submodule.quotEquivOfEqBot._proof_2.{u1} R _inst_1) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) M (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) _inst_3)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3), (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) p (Bot.bot.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.instBotSubmodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))) -> (LinearEquiv.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) M (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) _inst_3)
Case conversion may be inaccurate. Consider using '#align submodule.quot_equiv_of_eq_bot Submodule.quotEquivOfEqBotₓ'. -/
/-- If `p = ⊥`, then `M / p ≃ₗ[R] M`. -/
def quotEquivOfEqBot (hp : p = ⊥) : (M ⧸ p) ≃ₗ[R] M :=
  LinearEquiv.ofLinear (p.liftQ id <| hp.symm ▸ bot_le) p.mkQ (liftQ_mkQ _ _ _) <|
    p.quot_hom_ext fun x => rfl
#align submodule.quot_equiv_of_eq_bot Submodule.quotEquivOfEqBot

/- warning: submodule.quot_equiv_of_eq_bot_apply_mk -> Submodule.quotEquivOfEqBot_apply_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quot_equiv_of_eq_bot_apply_mk Submodule.quotEquivOfEqBot_apply_mkₓ'. -/
@[simp]
theorem quotEquivOfEqBot_apply_mk (hp : p = ⊥) (x : M) :
    p.quotEquivOfEqBot hp (Quotient.mk x) = x :=
  rfl
#align submodule.quot_equiv_of_eq_bot_apply_mk Submodule.quotEquivOfEqBot_apply_mk

/- warning: submodule.quot_equiv_of_eq_bot_symm_apply -> Submodule.quotEquivOfEqBot_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quot_equiv_of_eq_bot_symm_apply Submodule.quotEquivOfEqBot_symm_applyₓ'. -/
@[simp]
theorem quotEquivOfEqBot_symm_apply (hp : p = ⊥) (x : M) :
    (p.quotEquivOfEqBot hp).symm x = Quotient.mk x :=
  rfl
#align submodule.quot_equiv_of_eq_bot_symm_apply Submodule.quotEquivOfEqBot_symm_apply

/- warning: submodule.coe_quot_equiv_of_eq_bot_symm -> Submodule.coe_quotEquivOfEqBot_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.coe_quot_equiv_of_eq_bot_symm Submodule.coe_quotEquivOfEqBot_symmₓ'. -/
@[simp]
theorem coe_quotEquivOfEqBot_symm (hp : p = ⊥) :
    ((p.quotEquivOfEqBot hp).symm : M →ₗ[R] M ⧸ p) = p.mkQ :=
  rfl
#align submodule.coe_quot_equiv_of_eq_bot_symm Submodule.coe_quotEquivOfEqBot_symm

#print Submodule.quotEquivOfEq /-
/-- Quotienting by equal submodules gives linearly equivalent quotients. -/
def quotEquivOfEq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p' :=
  {
    @Quotient.congr _ _ (quotientRel p) (quotientRel p') (Equiv.refl _) fun a b =>
      by
      subst h
      rfl with
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl
    map_smul' := by
      rintro x ⟨y⟩
      rfl }
#align submodule.quot_equiv_of_eq Submodule.quotEquivOfEq
-/

/- warning: submodule.quot_equiv_of_eq_mk -> Submodule.quotEquivOfEq_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quot_equiv_of_eq_mk Submodule.quotEquivOfEq_mkₓ'. -/
@[simp]
theorem quotEquivOfEq_mk (h : p = p') (x : M) :
    Submodule.quotEquivOfEq p p' h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  rfl
#align submodule.quot_equiv_of_eq_mk Submodule.quotEquivOfEq_mk

/- warning: submodule.quotient.equiv_refl -> Submodule.Quotient.equiv_refl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.quotient.equiv_refl Submodule.Quotient.equiv_reflₓ'. -/
@[simp]
theorem Quotient.equiv_refl (P : Submodule R M) (Q : Submodule R M)
    (hf : P.map (LinearEquiv.refl R M : M →ₗ[R] M) = Q) :
    Quotient.equiv P Q (LinearEquiv.refl R M) hf = quotEquivOfEq _ _ (by simpa using hf) :=
  rfl
#align submodule.quotient.equiv_refl Submodule.Quotient.equiv_refl

end Submodule

end Ring

section CommRing

variable {R M M₂ : Type _} {r : R} {x y : M} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M₂] [Module R M₂] (p : Submodule R M) (q : Submodule R M₂)

namespace Submodule

#print Submodule.mapQLinear /-
/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the natural map $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \} \to Hom(M/p, M₂/q)$ is linear. -/
def mapQLinear : compatibleMaps p q →ₗ[R] M ⧸ p →ₗ[R] M₂ ⧸ q
    where
  toFun f := mapQ _ _ f.val f.property
  map_add' x y := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl
#align submodule.mapq_linear Submodule.mapQLinear
-/

end Submodule

end CommRing

