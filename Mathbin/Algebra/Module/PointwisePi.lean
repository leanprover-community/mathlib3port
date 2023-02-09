/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best

! This file was ported from Lean 3 source module algebra.module.pointwise_pi
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Smul
import Mathbin.GroupTheory.GroupAction.Pi

/-!
# Pointwise actions on sets in Pi types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains lemmas about pointwise actions on sets in Pi types.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication, pi

-/


open Pointwise

open Set

variable {K ι : Type _} {R : ι → Type _}

/- warning: smul_pi_subset -> smul_pi_subset is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {ι : Type.{u2}} {R : ι -> Type.{u3}} [_inst_1 : forall (i : ι), SMul.{u1, u3} K (R i)] (r : K) (s : Set.{u2} ι) (t : forall (i : ι), Set.{u3} (R i)), HasSubset.Subset.{max u2 u3} (Set.{max u2 u3} (forall (i : ι), R i)) (Set.hasSubset.{max u2 u3} (forall (i : ι), R i)) (SMul.smul.{u1, max u2 u3} K (Set.{max u2 u3} (forall (i : ι), R i)) (Set.smulSet.{u1, max u2 u3} K (forall (i : ι), R i) (Pi.instSMul.{u2, u3, u1} ι K (fun (i : ι) => R i) (fun (i : ι) => _inst_1 i))) r (Set.pi.{u2, u3} ι (fun (i : ι) => R i) s t)) (Set.pi.{u2, u3} ι (fun (i : ι) => R i) s (SMul.smul.{u1, max u2 u3} K (forall (i : ι), Set.{u3} (R i)) (Pi.instSMul.{u2, u3, u1} ι K (fun (i : ι) => Set.{u3} (R i)) (fun (i : ι) => Set.smulSet.{u1, u3} K (R i) (_inst_1 i))) r t))
but is expected to have type
  forall {K : Type.{u3}} {ι : Type.{u1}} {R : ι -> Type.{u2}} [_inst_1 : forall (i : ι), SMul.{u3, u2} K (R i)] (r : K) (s : Set.{u1} ι) (t : forall (i : ι), Set.{u2} (R i)), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), R i)) (Set.instHasSubsetSet.{max u1 u2} (forall (i : ι), R i)) (HSMul.hSMul.{u3, max u2 u1, max u1 u2} K (Set.{max u1 u2} (forall (i : ι), R i)) (Set.{max u1 u2} (forall (i : ι), R i)) (instHSMul.{u3, max u1 u2} K (Set.{max u1 u2} (forall (i : ι), R i)) (Set.smulSet.{u3, max u1 u2} K (forall (i : ι), R i) (Pi.instSMul.{u1, u2, u3} ι K (fun (i : ι) => R i) (fun (i : ι) => _inst_1 i)))) r (Set.pi.{u1, u2} ι (fun (i : ι) => R i) s t)) (Set.pi.{u1, u2} ι (fun (i : ι) => R i) s (HSMul.hSMul.{u3, max u1 u2, max u1 u2} K (forall (i : ι), Set.{u2} (R i)) (forall (i : ι), Set.{u2} (R i)) (instHSMul.{u3, max u1 u2} K (forall (i : ι), Set.{u2} (R i)) (Pi.instSMul.{u1, u2, u3} ι K (fun (i : ι) => Set.{u2} (R i)) (fun (i : ι) => Set.smulSet.{u3, u2} K (R i) (_inst_1 i)))) r t))
Case conversion may be inaccurate. Consider using '#align smul_pi_subset smul_pi_subsetₓ'. -/
@[to_additive]
theorem smul_pi_subset [∀ i, SMul K (R i)] (r : K) (s : Set ι) (t : ∀ i, Set (R i)) :
    r • pi s t ⊆ pi s (r • t) := by
  rintro x ⟨y, h, rfl⟩ i hi
  exact smul_mem_smul_set (h i hi)
#align smul_pi_subset smul_pi_subset
#align vadd_pi_subset vadd_pi_subset

/- warning: smul_univ_pi -> smul_univ_pi is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {ι : Type.{u2}} {R : ι -> Type.{u3}} [_inst_1 : forall (i : ι), SMul.{u1, u3} K (R i)] (r : K) (t : forall (i : ι), Set.{u3} (R i)), Eq.{succ (max u2 u3)} (Set.{max u2 u3} (forall (i : ι), R i)) (SMul.smul.{u1, max u2 u3} K (Set.{max u2 u3} (forall (i : ι), R i)) (Set.smulSet.{u1, max u2 u3} K (forall (i : ι), R i) (Pi.instSMul.{u2, u3, u1} ι K (fun (i : ι) => R i) (fun (i : ι) => _inst_1 i))) r (Set.pi.{u2, u3} ι (fun (i : ι) => R i) (Set.univ.{u2} ι) t)) (Set.pi.{u2, u3} ι (fun (i : ι) => R i) (Set.univ.{u2} ι) (SMul.smul.{u1, max u2 u3} K (forall (i : ι), Set.{u3} (R i)) (Pi.instSMul.{u2, u3, u1} ι K (fun (i : ι) => Set.{u3} (R i)) (fun (i : ι) => Set.smulSet.{u1, u3} K (R i) (_inst_1 i))) r t))
but is expected to have type
  forall {K : Type.{u3}} {ι : Type.{u1}} {R : ι -> Type.{u2}} [_inst_1 : forall (i : ι), SMul.{u3, u2} K (R i)] (r : K) (t : forall (i : ι), Set.{u2} (R i)), Eq.{max (succ u1) (succ u2)} (Set.{max u1 u2} (forall (i : ι), R i)) (HSMul.hSMul.{u3, max u2 u1, max u1 u2} K (Set.{max u1 u2} (forall (i : ι), R i)) (Set.{max u1 u2} (forall (i : ι), R i)) (instHSMul.{u3, max u1 u2} K (Set.{max u1 u2} (forall (i : ι), R i)) (Set.smulSet.{u3, max u1 u2} K (forall (i : ι), R i) (Pi.instSMul.{u1, u2, u3} ι K (fun (i : ι) => R i) (fun (i : ι) => _inst_1 i)))) r (Set.pi.{u1, u2} ι (fun (i : ι) => R i) (Set.univ.{u1} ι) t)) (Set.pi.{u1, u2} ι (fun (i : ι) => R i) (Set.univ.{u1} ι) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} K (forall (i : ι), Set.{u2} (R i)) (forall (i : ι), Set.{u2} (R i)) (instHSMul.{u3, max u1 u2} K (forall (i : ι), Set.{u2} (R i)) (Pi.instSMul.{u1, u2, u3} ι K (fun (i : ι) => Set.{u2} (R i)) (fun (i : ι) => Set.smulSet.{u3, u2} K (R i) (_inst_1 i)))) r t))
Case conversion may be inaccurate. Consider using '#align smul_univ_pi smul_univ_piₓ'. -/
@[to_additive]
theorem smul_univ_pi [∀ i, SMul K (R i)] (r : K) (t : ∀ i, Set (R i)) :
    r • pi (univ : Set ι) t = pi (univ : Set ι) (r • t) :=
  Subset.antisymm (smul_pi_subset _ _ _) fun x h =>
    by
    refine' ⟨fun i => Classical.choose (h i <| Set.mem_univ _), fun i hi => _, funext fun i => _⟩
    · exact (Classical.choose_spec (h i _)).left
    · exact (Classical.choose_spec (h i _)).right
#align smul_univ_pi smul_univ_pi
#align vadd_univ_pi vadd_univ_pi

/- warning: smul_pi -> smul_pi is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {ι : Type.{u2}} {R : ι -> Type.{u3}} [_inst_1 : Group.{u1} K] [_inst_2 : forall (i : ι), MulAction.{u1, u3} K (R i) (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_1))] (r : K) (S : Set.{u2} ι) (t : forall (i : ι), Set.{u3} (R i)), Eq.{succ (max u2 u3)} (Set.{max u2 u3} (forall (i : ι), R i)) (SMul.smul.{u1, max u2 u3} K (Set.{max u2 u3} (forall (i : ι), R i)) (Set.smulSet.{u1, max u2 u3} K (forall (i : ι), R i) (Pi.instSMul.{u2, u3, u1} ι K (fun (i : ι) => R i) (fun (i : ι) => MulAction.toHasSmul.{u1, u3} K (R i) (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_1)) (_inst_2 i)))) r (Set.pi.{u2, u3} ι (fun (i : ι) => R i) S t)) (Set.pi.{u2, u3} ι (fun (i : ι) => R i) S (SMul.smul.{u1, max u2 u3} K (forall (i : ι), Set.{u3} (R i)) (Pi.instSMul.{u2, u3, u1} ι K (fun (i : ι) => Set.{u3} (R i)) (fun (i : ι) => Set.smulSet.{u1, u3} K (R i) (MulAction.toHasSmul.{u1, u3} K (R i) (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_1)) (_inst_2 i)))) r t))
but is expected to have type
  forall {K : Type.{u3}} {ι : Type.{u1}} {R : ι -> Type.{u2}} [_inst_1 : Group.{u3} K] [_inst_2 : forall (i : ι), MulAction.{u3, u2} K (R i) (DivInvMonoid.toMonoid.{u3} K (Group.toDivInvMonoid.{u3} K _inst_1))] (r : K) (S : Set.{u1} ι) (t : forall (i : ι), Set.{u2} (R i)), Eq.{max (succ u1) (succ u2)} (Set.{max u1 u2} (forall (i : ι), R i)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} K (Set.{max u1 u2} (forall (i : ι), R i)) (Set.{max u1 u2} (forall (i : ι), R i)) (instHSMul.{u3, max u1 u2} K (Set.{max u1 u2} (forall (i : ι), R i)) (Set.smulSet.{u3, max u1 u2} K (forall (i : ι), R i) (Pi.instSMul.{u1, u2, u3} ι K (fun (i : ι) => R i) (fun (i : ι) => MulAction.toSMul.{u3, u2} K (R i) (DivInvMonoid.toMonoid.{u3} K (Group.toDivInvMonoid.{u3} K _inst_1)) (_inst_2 i))))) r (Set.pi.{u1, u2} ι (fun (i : ι) => R i) S t)) (Set.pi.{u1, u2} ι (fun (i : ι) => R i) S (HSMul.hSMul.{u3, max u1 u2, max u1 u2} K (forall (i : ι), Set.{u2} (R i)) (forall (i : ι), Set.{u2} (R i)) (instHSMul.{u3, max u1 u2} K (forall (i : ι), Set.{u2} (R i)) (Pi.instSMul.{u1, u2, u3} ι K (fun (i : ι) => Set.{u2} (R i)) (fun (i : ι) => Set.smulSet.{u3, u2} K (R i) (MulAction.toSMul.{u3, u2} K (R i) (DivInvMonoid.toMonoid.{u3} K (Group.toDivInvMonoid.{u3} K _inst_1)) (_inst_2 i))))) r t))
Case conversion may be inaccurate. Consider using '#align smul_pi smul_piₓ'. -/
@[to_additive]
theorem smul_pi [Group K] [∀ i, MulAction K (R i)] (r : K) (S : Set ι) (t : ∀ i, Set (R i)) :
    r • S.pi t = S.pi (r • t) :=
  Subset.antisymm (smul_pi_subset _ _ _) fun x h =>
    ⟨r⁻¹ • x, fun i hiS => mem_smul_set_iff_inv_smul_mem.mp (h i hiS), smul_inv_smul _ _⟩
#align smul_pi smul_pi
#align vadd_pi vadd_pi

/- warning: smul_pi₀ -> smul_pi₀ is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {ι : Type.{u2}} {R : ι -> Type.{u3}} [_inst_1 : GroupWithZero.{u1} K] [_inst_2 : forall (i : ι), MulAction.{u1, u3} K (R i) (MonoidWithZero.toMonoid.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K _inst_1))] {r : K} (S : Set.{u2} ι) (t : forall (i : ι), Set.{u3} (R i)), (Ne.{succ u1} K r (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K _inst_1)))))))) -> (Eq.{succ (max u2 u3)} (Set.{max u2 u3} (forall (i : ι), R i)) (SMul.smul.{u1, max u2 u3} K (Set.{max u2 u3} (forall (i : ι), R i)) (Set.smulSet.{u1, max u2 u3} K (forall (i : ι), R i) (Pi.instSMul.{u2, u3, u1} ι K (fun (i : ι) => R i) (fun (i : ι) => MulAction.toHasSmul.{u1, u3} K (R i) (MonoidWithZero.toMonoid.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K _inst_1)) (_inst_2 i)))) r (Set.pi.{u2, u3} ι (fun (i : ι) => R i) S t)) (Set.pi.{u2, u3} ι (fun (i : ι) => R i) S (SMul.smul.{u1, max u2 u3} K (forall (i : ι), Set.{u3} (R i)) (Pi.instSMul.{u2, u3, u1} ι K (fun (i : ι) => Set.{u3} (R i)) (fun (i : ι) => Set.smulSet.{u1, u3} K (R i) (MulAction.toHasSmul.{u1, u3} K (R i) (MonoidWithZero.toMonoid.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K _inst_1)) (_inst_2 i)))) r t)))
but is expected to have type
  forall {K : Type.{u3}} {ι : Type.{u1}} {R : ι -> Type.{u2}} [_inst_1 : GroupWithZero.{u3} K] [_inst_2 : forall (i : ι), MulAction.{u3, u2} K (R i) (MonoidWithZero.toMonoid.{u3} K (GroupWithZero.toMonoidWithZero.{u3} K _inst_1))] {r : K} (S : Set.{u1} ι) (t : forall (i : ι), Set.{u2} (R i)), (Ne.{succ u3} K r (OfNat.ofNat.{u3} K 0 (Zero.toOfNat0.{u3} K (MonoidWithZero.toZero.{u3} K (GroupWithZero.toMonoidWithZero.{u3} K _inst_1))))) -> (Eq.{max (succ u1) (succ u2)} (Set.{max u1 u2} (forall (i : ι), R i)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} K (Set.{max u1 u2} (forall (i : ι), R i)) (Set.{max u1 u2} (forall (i : ι), R i)) (instHSMul.{u3, max u1 u2} K (Set.{max u1 u2} (forall (i : ι), R i)) (Set.smulSet.{u3, max u1 u2} K (forall (i : ι), R i) (Pi.instSMul.{u1, u2, u3} ι K (fun (i : ι) => R i) (fun (i : ι) => MulAction.toSMul.{u3, u2} K (R i) (MonoidWithZero.toMonoid.{u3} K (GroupWithZero.toMonoidWithZero.{u3} K _inst_1)) (_inst_2 i))))) r (Set.pi.{u1, u2} ι (fun (i : ι) => R i) S t)) (Set.pi.{u1, u2} ι (fun (i : ι) => R i) S (HSMul.hSMul.{u3, max u1 u2, max u1 u2} K (forall (i : ι), Set.{u2} (R i)) (forall (i : ι), Set.{u2} (R i)) (instHSMul.{u3, max u1 u2} K (forall (i : ι), Set.{u2} (R i)) (Pi.instSMul.{u1, u2, u3} ι K (fun (i : ι) => Set.{u2} (R i)) (fun (i : ι) => Set.smulSet.{u3, u2} K (R i) (MulAction.toSMul.{u3, u2} K (R i) (MonoidWithZero.toMonoid.{u3} K (GroupWithZero.toMonoidWithZero.{u3} K _inst_1)) (_inst_2 i))))) r t)))
Case conversion may be inaccurate. Consider using '#align smul_pi₀ smul_pi₀ₓ'. -/
theorem smul_pi₀ [GroupWithZero K] [∀ i, MulAction K (R i)] {r : K} (S : Set ι) (t : ∀ i, Set (R i))
    (hr : r ≠ 0) : r • S.pi t = S.pi (r • t) :=
  smul_pi (Units.mk0 r hr) S t
#align smul_pi₀ smul_pi₀

