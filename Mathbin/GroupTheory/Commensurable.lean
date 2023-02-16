/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module group_theory.commensurable
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Index
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.GroupTheory.GroupAction.ConjAct

/-!
# Commensurability for subgroups

This file defines commensurability for subgroups of a group `G`. It then goes on to prove that
commensurability defines an equivalence relation and finally defines the commensurator of a subgroup
of `G`.

## Main definitions

* `commensurable`: defines commensurability for two subgroups `H`, `K` of  `G`
* `commensurator`: defines the commensurator of a subgroup `H` of `G`.

## Implementation details

We define the commensurator of a subgroup `H` of `G` by first defining it as a subgroup of
`(conj_act G)`, which we call commensurator' and then taking the pre-image under
the map `G → (conj_act G)` to obtain our commensurator as a subgroup of `G`.
-/


variable {G : Type _} [Group G]

#print Commensurable /-
/-- Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both `H` and `K` -/
def Commensurable (H K : Subgroup G) : Prop :=
  H.relindex K ≠ 0 ∧ K.relindex H ≠ 0
#align commensurable Commensurable
-/

namespace Commensurable

open Pointwise

#print Commensurable.refl /-
@[refl]
protected theorem refl (H : Subgroup G) : Commensurable H H := by simp [Commensurable]
#align commensurable.refl Commensurable.refl
-/

#print Commensurable.comm /-
theorem comm {H K : Subgroup G} : Commensurable H K ↔ Commensurable K H :=
  and_comm
#align commensurable.comm Commensurable.comm
-/

#print Commensurable.symm /-
@[symm]
theorem symm {H K : Subgroup G} : Commensurable H K → Commensurable K H :=
  And.symm
#align commensurable.symm Commensurable.symm
-/

#print Commensurable.trans /-
@[trans]
theorem trans {H K L : Subgroup G} (hhk : Commensurable H K) (hkl : Commensurable K L) :
    Commensurable H L :=
  ⟨Subgroup.relindex_ne_zero_trans hhk.1 hkl.1, Subgroup.relindex_ne_zero_trans hkl.2 hhk.2⟩
#align commensurable.trans Commensurable.trans
-/

#print Commensurable.equivalence /-
theorem equivalence : Equivalence (@Commensurable G _) :=
  ⟨Commensurable.refl, fun _ _ => Commensurable.symm, fun _ _ _ => Commensurable.trans⟩
#align commensurable.equivalence Commensurable.equivalence
-/

/- warning: commensurable.quot_conj_equiv -> Commensurable.quotConjEquiv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) (g : ConjAct.{u1} G), Equiv.{succ u1, succ u1} (HasQuotient.Quotient.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) (QuotientGroup.Subgroup.hasQuotient.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) (Subgroup.subgroupOf.{u1} G _inst_1 H K)) (HasQuotient.Quotient.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} G) Type.{u1} (Set.hasCoeToSort.{u1} G) (Subgroup.carrier.{u1} G _inst_1 (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g K))) (Subgroup.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g K)) (Subgroup.toGroup.{u1} G _inst_1 (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g K))) (QuotientGroup.Subgroup.hasQuotient.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g K)) (Subgroup.toGroup.{u1} G _inst_1 (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g K))) (Subgroup.subgroupOf.{u1} G _inst_1 (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g H) (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g K)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) (g : ConjAct.{u1} G), Equiv.{succ u1, succ u1} (HasQuotient.Quotient.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) (QuotientGroup.instHasQuotientSubgroup.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) (Subgroup.subgroupOf.{u1} G _inst_1 H K)) (HasQuotient.Quotient.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) G (Submonoid.instSetLikeSubmonoid.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x (Subgroup.toSubmonoid.{u1} G _inst_1 (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g K)))) (Subgroup.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g K))) (Subgroup.toGroup.{u1} G _inst_1 (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g K))) (QuotientGroup.instHasQuotientSubgroup.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g K))) (Subgroup.toGroup.{u1} G _inst_1 (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g K))) (Subgroup.subgroupOf.{u1} G _inst_1 (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g H) (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g K)))
Case conversion may be inaccurate. Consider using '#align commensurable.quot_conj_equiv Commensurable.quotConjEquivₓ'. -/
/-- Equivalence of `K/H ⊓ K` with `gKg⁻¹/gHg⁻¹ ⊓ gKg⁻¹`-/
def quotConjEquiv (H K : Subgroup G) (g : ConjAct G) :
    K ⧸ H.subgroupOf K ≃ (g • K).1 ⧸ (g • H).subgroupOf (g • K) :=
  Quotient.congr (K.equivSmul g).toEquiv fun a b =>
    by
    dsimp
    rw [← Quotient.eq'', ← Quotient.eq'', QuotientGroup.eq', QuotientGroup.eq',
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← MulEquiv.map_inv, ← MulEquiv.map_mul,
      Subgroup.equivSmul_apply_coe]
    exact subgroup.smul_mem_pointwise_smul_iff.symm
#align commensurable.quot_conj_equiv Commensurable.quotConjEquiv

/- warning: commensurable.commensurable_conj -> Commensurable.commensurable_conj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} (g : ConjAct.{u1} G), Iff (Commensurable.{u1} G _inst_1 H K) (Commensurable.{u1} G _inst_1 (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g H) (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g K))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} (g : ConjAct.{u1} G), Iff (Commensurable.{u1} G _inst_1 H K) (Commensurable.{u1} G _inst_1 (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g H) (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g K))
Case conversion may be inaccurate. Consider using '#align commensurable.commensurable_conj Commensurable.commensurable_conjₓ'. -/
theorem commensurable_conj {H K : Subgroup G} (g : ConjAct G) :
    Commensurable H K ↔ Commensurable (g • H) (g • K) :=
  and_congr (not_iff_not.mpr (Eq.congr_left (Cardinal.toNat_congr (quotConjEquiv H K g))))
    (not_iff_not.mpr (Eq.congr_left (Cardinal.toNat_congr (quotConjEquiv K H g))))
#align commensurable.commensurable_conj Commensurable.commensurable_conj

/- warning: commensurable.commensurable_inv -> Commensurable.commensurable_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (g : ConjAct.{u1} G), Iff (Commensurable.{u1} G _inst_1 (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g H) H) (Commensurable.{u1} G _inst_1 H (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) (Inv.inv.{u1} (ConjAct.{u1} G) (DivInvMonoid.toHasInv.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) g) H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (g : ConjAct.{u1} G), Iff (Commensurable.{u1} G _inst_1 (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g H) H) (Commensurable.{u1} G _inst_1 H (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) (Inv.inv.{u1} (ConjAct.{u1} G) (InvOneClass.toInv.{u1} (ConjAct.{u1} G) (DivInvOneMonoid.toInvOneClass.{u1} (ConjAct.{u1} G) (DivisionMonoid.toDivInvOneMonoid.{u1} (ConjAct.{u1} G) (Group.toDivisionMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instGroupConjAct.{u1} G _inst_1))))) g) H))
Case conversion may be inaccurate. Consider using '#align commensurable.commensurable_inv Commensurable.commensurable_invₓ'. -/
theorem commensurable_inv (H : Subgroup G) (g : ConjAct G) :
    Commensurable (g • H) H ↔ Commensurable H (g⁻¹ • H) := by rw [commensurable_conj, inv_smul_smul]
#align commensurable.commensurable_inv Commensurable.commensurable_inv

#print Commensurable.commensurator' /-
/-- For `H` a subgroup of `G`, this is the subgroup of all elements `g : conj_aut G`
such that `commensurable (g • H) H` -/
def commensurator' (H : Subgroup G) : Subgroup (ConjAct G)
    where
  carrier := { g : ConjAct G | Commensurable (g • H) H }
  one_mem' := by rw [Set.mem_setOf_eq, one_smul]
  mul_mem' a b ha hb := by
    rw [Set.mem_setOf_eq, mul_smul]
    exact trans ((commensurable_conj a).mp hb) ha
  inv_mem' a ha := by rwa [Set.mem_setOf_eq, comm, ← commensurable_inv]
#align commensurable.commensurator' Commensurable.commensurator'
-/

#print Commensurable.commensurator /-
/-- For `H` a subgroup of `G`, this is the subgroup of all elements `g : G`
such that `commensurable (g H g⁻¹) H` -/
def commensurator (H : Subgroup G) : Subgroup G :=
  (commensurator' H).comap ConjAct.toConjAct.toMonoidHom
#align commensurable.commensurator Commensurable.commensurator
-/

/- warning: commensurable.commensurator'_mem_iff -> Commensurable.commensurator'_mem_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (g : ConjAct.{u1} G), Iff (Membership.Mem.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} (ConjAct.{u1} G) (ConjAct.group.{u1} G _inst_1)) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} (ConjAct.{u1} G) (ConjAct.group.{u1} G _inst_1)) (ConjAct.{u1} G) (Subgroup.setLike.{u1} (ConjAct.{u1} G) (ConjAct.group.{u1} G _inst_1))) g (Commensurable.commensurator'.{u1} G _inst_1 H)) (Commensurable.{u1} G _inst_1 (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) g H) H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (g : ConjAct.{u1} G), Iff (Membership.mem.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} (ConjAct.{u1} G) (ConjAct.instGroupConjAct.{u1} G _inst_1)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} (ConjAct.{u1} G) (ConjAct.instGroupConjAct.{u1} G _inst_1)) (ConjAct.{u1} G) (Subgroup.instSetLikeSubgroup.{u1} (ConjAct.{u1} G) (ConjAct.instGroupConjAct.{u1} G _inst_1))) g (Commensurable.commensurator'.{u1} G _inst_1 H)) (Commensurable.{u1} G _inst_1 (HSMul.hSMul.{u1, u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) g H) H)
Case conversion may be inaccurate. Consider using '#align commensurable.commensurator'_mem_iff Commensurable.commensurator'_mem_iffₓ'. -/
@[simp]
theorem commensurator'_mem_iff (H : Subgroup G) (g : ConjAct G) :
    g ∈ commensurator' H ↔ Commensurable (g • H) H :=
  Iff.rfl
#align commensurable.commensurator'_mem_iff Commensurable.commensurator'_mem_iff

/- warning: commensurable.commensurator_mem_iff -> Commensurable.commensurator_mem_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (g : G), Iff (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) g (Commensurable.commensurator.{u1} G _inst_1 H)) (Commensurable.{u1} G _inst_1 (SMul.smul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (MulAction.toHasSmul.{u1, u1} (ConjAct.{u1} G) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} (ConjAct.{u1} G) G _inst_1 (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.mulDistribMulAction.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (MulEquiv.{u1, u1} G (ConjAct.{u1} G) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasMul.{u1} (ConjAct.{u1} G) (Monoid.toMulOneClass.{u1} (ConjAct.{u1} G) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (fun (_x : MulEquiv.{u1, u1} G (ConjAct.{u1} G) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasMul.{u1} (ConjAct.{u1} G) (Monoid.toMulOneClass.{u1} (ConjAct.{u1} G) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) => G -> (ConjAct.{u1} G)) (MulEquiv.hasCoeToFun.{u1, u1} G (ConjAct.{u1} G) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasMul.{u1} (ConjAct.{u1} G) (Monoid.toMulOneClass.{u1} (ConjAct.{u1} G) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.divInvMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (ConjAct.toConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) g) H) H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (g : G), Iff (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) g (Commensurable.commensurator.{u1} G _inst_1 H)) (Commensurable.{u1} G _inst_1 (HSMul.hSMul.{u1, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => ConjAct.{u1} G) g) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} G _inst_1) (instHSMul.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => ConjAct.{u1} G) g) (Subgroup.{u1} G _inst_1) (MulAction.toSMul.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => ConjAct.{u1} G) g) (Subgroup.{u1} G _inst_1) (DivInvMonoid.toMonoid.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => ConjAct.{u1} G) g) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.pointwiseMulAction.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => ConjAct.{u1} G) g) G _inst_1 (DivInvMonoid.toMonoid.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => ConjAct.{u1} G) g) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (ConjAct.instMulDistribMulActionConjActToMonoidInstDivInvMonoidConjActToDivInvMonoid.{u1} G _inst_1)))) (FunLike.coe.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} G (ConjAct.{u1} G) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (ConjAct.{u1} G) (Monoid.toMulOneClass.{u1} (ConjAct.{u1} G) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => ConjAct.{u1} G) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} G (ConjAct.{u1} G) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (ConjAct.{u1} G) (Monoid.toMulOneClass.{u1} (ConjAct.{u1} G) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) G (ConjAct.{u1} G) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} G (ConjAct.{u1} G) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (ConjAct.{u1} G) (Monoid.toMulOneClass.{u1} (ConjAct.{u1} G) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) G (ConjAct.{u1} G) (MulEquivClass.toEquivLike.{u1, u1, u1} (MulEquiv.{u1, u1} G (ConjAct.{u1} G) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (ConjAct.{u1} G) (Monoid.toMulOneClass.{u1} (ConjAct.{u1} G) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) G (ConjAct.{u1} G) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (ConjAct.{u1} G) (Monoid.toMulOneClass.{u1} (ConjAct.{u1} G) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} G (ConjAct.{u1} G) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (ConjAct.{u1} G) (Monoid.toMulOneClass.{u1} (ConjAct.{u1} G) (DivInvMonoid.toMonoid.{u1} (ConjAct.{u1} G) (ConjAct.instDivInvMonoidConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))) (ConjAct.toConjAct.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) g) H) H)
Case conversion may be inaccurate. Consider using '#align commensurable.commensurator_mem_iff Commensurable.commensurator_mem_iffₓ'. -/
@[simp]
theorem commensurator_mem_iff (H : Subgroup G) (g : G) :
    g ∈ commensurator H ↔ Commensurable (ConjAct.toConjAct g • H) H :=
  Iff.rfl
#align commensurable.commensurator_mem_iff Commensurable.commensurator_mem_iff

#print Commensurable.eq /-
theorem eq {H K : Subgroup G} (hk : Commensurable H K) : commensurator H = commensurator K :=
  Subgroup.ext fun x =>
    let hx := (commensurable_conj x).1 hk
    ⟨fun h => hx.symm.trans (h.trans hk), fun h => hx.trans (h.trans hk.symm)⟩
#align commensurable.eq Commensurable.eq
-/

end Commensurable

