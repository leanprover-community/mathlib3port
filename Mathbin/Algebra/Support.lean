/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module algebra.support
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Data.Set.Finite
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Module.Basic
import Mathbin.GroupTheory.GroupAction.Pi

/-!
# Support of a function

In this file we define `function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `function.mul_support f = {x | f x ≠ 1}`.
-/


open Set

open BigOperators

namespace Function

variable {α β A B M N P R S G M₀ G₀ : Type _} {ι : Sort _}

section One

variable [One M] [One N] [One P]

#print Function.support /-
/-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/
def support [Zero A] (f : α → A) : Set α :=
  { x | f x ≠ 0 }
#align function.support Function.support
-/

#print Function.mulSupport /-
/-- `mul_support` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive]
def mulSupport (f : α → M) : Set α :=
  { x | f x ≠ 1 }
#align function.mul_support Function.mulSupport
#align function.support Function.support
-/

/- warning: function.mul_support_eq_preimage -> Function.mulSupport_eq_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (f : α -> M), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Set.preimage.{u1, u2} α M f (HasCompl.compl.{u2} (Set.{u2} M) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} M) (Set.booleanAlgebra.{u2} M)) (Singleton.singleton.{u2, u2} M (Set.{u2} M) (Set.hasSingleton.{u2} M) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (f : α -> M), Eq.{succ u2} (Set.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 f) (Set.preimage.{u2, u1} α M f (HasCompl.compl.{u1} (Set.{u1} M) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} M) (Set.instBooleanAlgebraSet.{u1} M)) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align function.mul_support_eq_preimage Function.mulSupport_eq_preimageₓ'. -/
@[to_additive]
theorem mulSupport_eq_preimage (f : α → M) : mulSupport f = f ⁻¹' {1}ᶜ :=
  rfl
#align function.mul_support_eq_preimage Function.mulSupport_eq_preimage
#align function.support_eq_preimage Function.support_eq_preimage

/- warning: function.nmem_mul_support -> Function.nmem_mulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M} {x : α}, Iff (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Function.mulSupport.{u1, u2} α M _inst_1 f))) (Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M} {x : α}, Iff (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Function.mulSupport.{u2, u1} α M _inst_1 f))) (Eq.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align function.nmem_mul_support Function.nmem_mulSupportₓ'. -/
@[to_additive]
theorem nmem_mulSupport {f : α → M} {x : α} : x ∉ mulSupport f ↔ f x = 1 :=
  not_not
#align function.nmem_mul_support Function.nmem_mulSupport
#align function.nmem_support Function.nmem_support

/- warning: function.compl_mul_support -> Function.compl_mulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M}, Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Function.mulSupport.{u1, u2} α M _inst_1 f)) (setOf.{u1} α (fun (x : α) => Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M}, Eq.{succ u2} (Set.{u2} α) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) (Function.mulSupport.{u2, u1} α M _inst_1 f)) (setOf.{u2} α (fun (x : α) => Eq.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align function.compl_mul_support Function.compl_mulSupportₓ'. -/
@[to_additive]
theorem compl_mulSupport {f : α → M} : mulSupport fᶜ = { x | f x = 1 } :=
  ext fun x => nmem_mulSupport
#align function.compl_mul_support Function.compl_mulSupport
#align function.compl_support Function.compl_support

/- warning: function.mem_mul_support -> Function.mem_mulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M} {x : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Function.mulSupport.{u1, u2} α M _inst_1 f)) (Ne.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M} {x : α}, Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Function.mulSupport.{u2, u1} α M _inst_1 f)) (Ne.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align function.mem_mul_support Function.mem_mulSupportₓ'. -/
@[simp, to_additive]
theorem mem_mulSupport {f : α → M} {x : α} : x ∈ mulSupport f ↔ f x ≠ 1 :=
  Iff.rfl
#align function.mem_mul_support Function.mem_mulSupport
#align function.mem_support Function.mem_support

/- warning: function.mul_support_subset_iff -> Function.mulSupport_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M} {s : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) s) (forall (x : α), (Ne.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M} {s : Set.{u2} α}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 f) s) (forall (x : α), (Ne.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s))
Case conversion may be inaccurate. Consider using '#align function.mul_support_subset_iff Function.mulSupport_subset_iffₓ'. -/
@[simp, to_additive]
theorem mulSupport_subset_iff {f : α → M} {s : Set α} : mulSupport f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s :=
  Iff.rfl
#align function.mul_support_subset_iff Function.mulSupport_subset_iff
#align function.support_subset_iff Function.support_subset_iff

/- warning: function.mul_support_subset_iff' -> Function.mulSupport_subset_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M} {s : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) s) (forall (x : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) -> (Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M} {s : Set.{u2} α}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 f) s) (forall (x : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) -> (Eq.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align function.mul_support_subset_iff' Function.mulSupport_subset_iff'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ∉ » s) -/
@[to_additive]
theorem mulSupport_subset_iff' {f : α → M} {s : Set α} :
    mulSupport f ⊆ s ↔ ∀ (x) (_ : x ∉ s), f x = 1 :=
  forall_congr' fun x => not_imp_comm
#align function.mul_support_subset_iff' Function.mulSupport_subset_iff'
#align function.support_subset_iff' Function.support_subset_iff'

/- warning: function.mul_support_eq_iff -> Function.mulSupport_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) s) (And (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Ne.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))) (forall (x : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) -> (Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M} {s : Set.{u2} α}, Iff (Eq.{succ u2} (Set.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 f) s) (And (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Ne.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))) (forall (x : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) -> (Eq.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align function.mul_support_eq_iff Function.mulSupport_eq_iffₓ'. -/
@[to_additive]
theorem mulSupport_eq_iff {f : α → M} {s : Set α} :
    mulSupport f = s ↔ (∀ x, x ∈ s → f x ≠ 1) ∧ ∀ x, x ∉ s → f x = 1 := by
  simp only [Set.ext_iff, mem_mul_support, Ne.def, imp_not_comm, ← forall_and, ← iff_def, ←
    xor'_iff_not_iff', ← xor'_iff_iff_not]
#align function.mul_support_eq_iff Function.mulSupport_eq_iff
#align function.support_eq_iff Function.support_eq_iff

/- warning: function.mul_support_disjoint_iff -> Function.mulSupport_disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Function.mulSupport.{u1, u2} α M _inst_1 f) s) (Set.EqOn.{u1, u2} α M f (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1))))) s)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M} {s : Set.{u2} α}, Iff (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Function.mulSupport.{u2, u1} α M _inst_1 f) s) (Set.EqOn.{u2, u1} α M f (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Data.Set.Function._hyg.1366 : α) => M) (fun (i : α) => _inst_1)))) s)
Case conversion may be inaccurate. Consider using '#align function.mul_support_disjoint_iff Function.mulSupport_disjoint_iffₓ'. -/
@[to_additive]
theorem mulSupport_disjoint_iff {f : α → M} {s : Set α} : Disjoint (mulSupport f) s ↔ EqOn f 1 s :=
  by
  simp_rw [← subset_compl_iff_disjoint_right, mul_support_subset_iff', not_mem_compl_iff, eq_on,
    Pi.one_apply]
#align function.mul_support_disjoint_iff Function.mulSupport_disjoint_iff
#align function.support_disjoint_iff Function.support_disjoint_iff

/- warning: function.disjoint_mul_support_iff -> Function.disjoint_mulSupport_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (Function.mulSupport.{u1, u2} α M _inst_1 f)) (Set.EqOn.{u1, u2} α M f (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1))))) s)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M} {s : Set.{u2} α}, Iff (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s (Function.mulSupport.{u2, u1} α M _inst_1 f)) (Set.EqOn.{u2, u1} α M f (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Data.Set.Function._hyg.1366 : α) => M) (fun (i : α) => _inst_1)))) s)
Case conversion may be inaccurate. Consider using '#align function.disjoint_mul_support_iff Function.disjoint_mulSupport_iffₓ'. -/
@[to_additive]
theorem disjoint_mulSupport_iff {f : α → M} {s : Set α} : Disjoint s (mulSupport f) ↔ EqOn f 1 s :=
  by rw [disjoint_comm, mul_support_disjoint_iff]
#align function.disjoint_mul_support_iff Function.disjoint_mulSupport_iff
#align function.disjoint_support_iff Function.disjoint_support_iff

/- warning: function.mul_support_eq_empty_iff -> Function.mulSupport_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M}, Iff (Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{max (succ u1) (succ u2)} (α -> M) f (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M}, Iff (Eq.{succ u2} (Set.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 f) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (Eq.{max (succ u2) (succ u1)} (α -> M) f (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.Support._hyg.721 : α) => M) (fun (i : α) => _inst_1)))))
Case conversion may be inaccurate. Consider using '#align function.mul_support_eq_empty_iff Function.mulSupport_eq_empty_iffₓ'. -/
@[simp, to_additive]
theorem mulSupport_eq_empty_iff {f : α → M} : mulSupport f = ∅ ↔ f = 1 :=
  by
  simp_rw [← subset_empty_iff, mul_support_subset_iff', funext_iff]
  simp
#align function.mul_support_eq_empty_iff Function.mulSupport_eq_empty_iff
#align function.support_eq_empty_iff Function.support_eq_empty_iff

/- warning: function.mul_support_nonempty_iff -> Function.mulSupport_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M}, Iff (Set.Nonempty.{u1} α (Function.mulSupport.{u1, u2} α M _inst_1 f)) (Ne.{max (succ u1) (succ u2)} (α -> M) f (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M}, Iff (Set.Nonempty.{u2} α (Function.mulSupport.{u2, u1} α M _inst_1 f)) (Ne.{max (succ u2) (succ u1)} (α -> M) f (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.Support._hyg.777 : α) => M) (fun (i : α) => _inst_1)))))
Case conversion may be inaccurate. Consider using '#align function.mul_support_nonempty_iff Function.mulSupport_nonempty_iffₓ'. -/
@[simp, to_additive]
theorem mulSupport_nonempty_iff {f : α → M} : (mulSupport f).Nonempty ↔ f ≠ 1 := by
  rw [nonempty_iff_ne_empty, Ne.def, mul_support_eq_empty_iff]
#align function.mul_support_nonempty_iff Function.mulSupport_nonempty_iff
#align function.support_nonempty_iff Function.support_nonempty_iff

#print Function.range_subset_insert_image_mulSupport /-
@[to_additive]
theorem range_subset_insert_image_mulSupport (f : α → M) : range f ⊆ insert 1 (f '' mulSupport f) :=
  by
  simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left] using
    fun x (hx : x ∈ mul_support f) => mem_image_of_mem f hx
#align function.range_subset_insert_image_mul_support Function.range_subset_insert_image_mulSupport
#align function.range_subset_insert_image_support Function.range_subset_insert_image_support
-/

/- warning: function.mul_support_one' -> Function.mulSupport_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M], Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)))))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M], Eq.{succ u2} (Set.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.Support._hyg.916 : α) => M) (fun (i : α) => _inst_1))))) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))
Case conversion may be inaccurate. Consider using '#align function.mul_support_one' Function.mulSupport_one'ₓ'. -/
@[simp, to_additive]
theorem mulSupport_one' : mulSupport (1 : α → M) = ∅ :=
  mulSupport_eq_empty_iff.2 rfl
#align function.mul_support_one' Function.mulSupport_one'
#align function.support_zero' Function.support_zero'

/- warning: function.mul_support_one -> Function.mulSupport_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M], Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M], Eq.{succ u2} (Set.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 (fun (x : α) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))
Case conversion may be inaccurate. Consider using '#align function.mul_support_one Function.mulSupport_oneₓ'. -/
@[simp, to_additive]
theorem mulSupport_one : (mulSupport fun x : α => (1 : M)) = ∅ :=
  mul_support_one'
#align function.mul_support_one Function.mulSupport_one
#align function.support_zero Function.support_zero

#print Function.mulSupport_const /-
@[to_additive]
theorem mulSupport_const {c : M} (hc : c ≠ 1) : (mulSupport fun x : α => c) = Set.univ :=
  by
  ext x
  simp [hc]
#align function.mul_support_const Function.mulSupport_const
#align function.support_const Function.support_const
-/

/- warning: function.mul_support_binop_subset -> Function.mulSupport_binop_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} {P : Type.{u4}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u3} N] [_inst_3 : One.{u4} P] (op : M -> N -> P), (Eq.{succ u4} P (op (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) (OfNat.ofNat.{u3} N 1 (OfNat.mk.{u3} N 1 (One.one.{u3} N _inst_2)))) (OfNat.ofNat.{u4} P 1 (OfNat.mk.{u4} P 1 (One.one.{u4} P _inst_3)))) -> (forall (f : α -> M) (g : α -> N), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u4} α P _inst_3 (fun (x : α) => op (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u3} α N _inst_2 g)))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u4}} [_inst_1 : One.{u3} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u4} P] (op : M -> N -> P), (Eq.{succ u4} P (op (OfNat.ofNat.{u3} M 1 (One.toOfNat1.{u3} M _inst_1)) (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N _inst_2))) (OfNat.ofNat.{u4} P 1 (One.toOfNat1.{u4} P _inst_3))) -> (forall (f : α -> M) (g : α -> N), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.mulSupport.{u1, u4} α P _inst_3 (fun (x : α) => op (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Function.mulSupport.{u1, u3} α M _inst_1 f) (Function.mulSupport.{u1, u2} α N _inst_2 g)))
Case conversion may be inaccurate. Consider using '#align function.mul_support_binop_subset Function.mulSupport_binop_subsetₓ'. -/
@[to_additive]
theorem mulSupport_binop_subset (op : M → N → P) (op1 : op 1 1 = 1) (f : α → M) (g : α → N) :
    (mulSupport fun x => op (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := fun x hx =>
  not_or_of_imp fun hf hg => hx <| by simp only [hf, hg, op1]
#align function.mul_support_binop_subset Function.mulSupport_binop_subset
#align function.support_binop_subset Function.support_binop_subset

/- warning: function.mul_support_sup -> Function.mulSupport_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_4 : SemilatticeSup.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => HasSup.sup.{u2} M (SemilatticeSup.toHasSup.{u2} M _inst_4) (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u2} α M _inst_1 g))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_4 : SemilatticeSup.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => HasSup.sup.{u2} M (SemilatticeSup.toHasSup.{u2} M _inst_4) (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u2} α M _inst_1 g))
Case conversion may be inaccurate. Consider using '#align function.mul_support_sup Function.mulSupport_supₓ'. -/
@[to_additive]
theorem mulSupport_sup [SemilatticeSup M] (f g : α → M) :
    (mulSupport fun x => f x ⊔ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊔ ·) sup_idem f g
#align function.mul_support_sup Function.mulSupport_sup
#align function.support_sup Function.support_sup

/- warning: function.mul_support_inf -> Function.mulSupport_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_4 : SemilatticeInf.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => HasInf.inf.{u2} M (SemilatticeInf.toHasInf.{u2} M _inst_4) (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u2} α M _inst_1 g))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_4 : SemilatticeInf.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => HasInf.inf.{u2} M (SemilatticeInf.toHasInf.{u2} M _inst_4) (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u2} α M _inst_1 g))
Case conversion may be inaccurate. Consider using '#align function.mul_support_inf Function.mulSupport_infₓ'. -/
@[to_additive]
theorem mulSupport_inf [SemilatticeInf M] (f g : α → M) :
    (mulSupport fun x => f x ⊓ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊓ ·) inf_idem f g
#align function.mul_support_inf Function.mulSupport_inf
#align function.support_inf Function.support_inf

/- warning: function.mul_support_max -> Function.mulSupport_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_4 : LinearOrder.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => LinearOrder.max.{u2} M _inst_4 (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u2} α M _inst_1 g))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_4 : LinearOrder.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => Max.max.{u2} M (LinearOrder.toMax.{u2} M _inst_4) (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u2} α M _inst_1 g))
Case conversion may be inaccurate. Consider using '#align function.mul_support_max Function.mulSupport_maxₓ'. -/
@[to_additive]
theorem mulSupport_max [LinearOrder M] (f g : α → M) :
    (mulSupport fun x => max (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_sup f g
#align function.mul_support_max Function.mulSupport_max
#align function.support_max Function.support_max

/- warning: function.mul_support_min -> Function.mulSupport_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_4 : LinearOrder.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => LinearOrder.min.{u2} M _inst_4 (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u2} α M _inst_1 g))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_4 : LinearOrder.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => Min.min.{u2} M (LinearOrder.toMin.{u2} M _inst_4) (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u2} α M _inst_1 g))
Case conversion may be inaccurate. Consider using '#align function.mul_support_min Function.mulSupport_minₓ'. -/
@[to_additive]
theorem mulSupport_min [LinearOrder M] (f g : α → M) :
    (mulSupport fun x => min (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_inf f g
#align function.mul_support_min Function.mulSupport_min
#align function.support_min Function.support_min

/- warning: function.mul_support_supr -> Function.mulSupport_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : One.{u2} M] [_inst_4 : ConditionallyCompleteLattice.{u2} M] [_inst_5 : Nonempty.{u3} ι] (f : ι -> α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => supᵢ.{u2, u3} M (ConditionallyCompleteLattice.toHasSup.{u2} M _inst_4) ι (fun (i : ι) => f i x))) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Function.mulSupport.{u1, u2} α M _inst_1 (f i)))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {ι : Sort.{u2}} [_inst_1 : One.{u3} M] [_inst_4 : ConditionallyCompleteLattice.{u3} M] [_inst_5 : Nonempty.{u2} ι] (f : ι -> α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.mulSupport.{u1, u3} α M _inst_1 (fun (x : α) => supᵢ.{u3, u2} M (ConditionallyCompleteLattice.toSupSet.{u3} M _inst_4) ι (fun (i : ι) => f i x))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Function.mulSupport.{u1, u3} α M _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align function.mul_support_supr Function.mulSupport_supᵢₓ'. -/
@[to_additive]
theorem mulSupport_supᵢ [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (mulSupport fun x => ⨆ i, f i x) ⊆ ⋃ i, mulSupport (f i) :=
  by
  rw [mul_support_subset_iff']
  simp only [mem_Union, not_exists, nmem_mul_support]
  intro x hx
  simp only [hx, csupᵢ_const]
#align function.mul_support_supr Function.mulSupport_supᵢ
#align function.support_supr Function.support_supᵢ

/- warning: function.mul_support_infi -> Function.mulSupport_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : One.{u2} M] [_inst_4 : ConditionallyCompleteLattice.{u2} M] [_inst_5 : Nonempty.{u3} ι] (f : ι -> α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => infᵢ.{u2, u3} M (ConditionallyCompleteLattice.toHasInf.{u2} M _inst_4) ι (fun (i : ι) => f i x))) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Function.mulSupport.{u1, u2} α M _inst_1 (f i)))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {ι : Sort.{u2}} [_inst_1 : One.{u3} M] [_inst_4 : ConditionallyCompleteLattice.{u3} M] [_inst_5 : Nonempty.{u2} ι] (f : ι -> α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.mulSupport.{u1, u3} α M _inst_1 (fun (x : α) => infᵢ.{u3, u2} M (ConditionallyCompleteLattice.toInfSet.{u3} M _inst_4) ι (fun (i : ι) => f i x))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Function.mulSupport.{u1, u3} α M _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align function.mul_support_infi Function.mulSupport_infᵢₓ'. -/
@[to_additive]
theorem mulSupport_infᵢ [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (mulSupport fun x => ⨅ i, f i x) ⊆ ⋃ i, mulSupport (f i) :=
  @mulSupport_supᵢ _ Mᵒᵈ ι ⟨(1 : M)⟩ _ _ f
#align function.mul_support_infi Function.mulSupport_infᵢ
#align function.support_infi Function.support_infᵢ

#print Function.mulSupport_comp_subset /-
@[to_additive]
theorem mulSupport_comp_subset {g : M → N} (hg : g 1 = 1) (f : α → M) :
    mulSupport (g ∘ f) ⊆ mulSupport f := fun x => mt fun h => by simp only [(· ∘ ·), *]
#align function.mul_support_comp_subset Function.mulSupport_comp_subset
#align function.support_comp_subset Function.support_comp_subset
-/

#print Function.mulSupport_subset_comp /-
@[to_additive]
theorem mulSupport_subset_comp {g : M → N} (hg : ∀ {x}, g x = 1 → x = 1) (f : α → M) :
    mulSupport f ⊆ mulSupport (g ∘ f) := fun x => mt hg
#align function.mul_support_subset_comp Function.mulSupport_subset_comp
#align function.support_subset_comp Function.support_subset_comp
-/

#print Function.mulSupport_comp_eq /-
@[to_additive]
theorem mulSupport_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : α → M) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun x => not_congr hg
#align function.mul_support_comp_eq Function.mulSupport_comp_eq
#align function.support_comp_eq Function.support_comp_eq
-/

/- warning: function.mul_support_comp_eq_preimage -> Function.mulSupport_comp_eq_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : One.{u3} M] (g : β -> M) (f : α -> β), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u3} α M _inst_1 (Function.comp.{succ u1, succ u2, succ u3} α β M g f)) (Set.preimage.{u1, u2} α β f (Function.mulSupport.{u2, u3} β M _inst_1 g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (g : β -> M) (f : α -> β), Eq.{succ u3} (Set.{u3} α) (Function.mulSupport.{u3, u2} α M _inst_1 (Function.comp.{succ u3, succ u1, succ u2} α β M g f)) (Set.preimage.{u3, u1} α β f (Function.mulSupport.{u1, u2} β M _inst_1 g))
Case conversion may be inaccurate. Consider using '#align function.mul_support_comp_eq_preimage Function.mulSupport_comp_eq_preimageₓ'. -/
@[to_additive]
theorem mulSupport_comp_eq_preimage (g : β → M) (f : α → β) :
    mulSupport (g ∘ f) = f ⁻¹' mulSupport g :=
  rfl
#align function.mul_support_comp_eq_preimage Function.mulSupport_comp_eq_preimage
#align function.support_comp_eq_preimage Function.support_comp_eq_preimage

/- warning: function.mul_support_prod_mk -> Function.mulSupport_prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u3} N] (f : α -> M) (g : α -> N), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, max u2 u3} α (Prod.{u2, u3} M N) (Prod.hasOne.{u2, u3} M N _inst_1 _inst_2) (fun (x : α) => Prod.mk.{u2, u3} M N (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) (Function.mulSupport.{u1, u3} α N _inst_2 g))
but is expected to have type
  forall {α : Type.{u3}} {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] (f : α -> M) (g : α -> N), Eq.{succ u3} (Set.{u3} α) (Function.mulSupport.{u3, max u2 u1} α (Prod.{u1, u2} M N) (Prod.instOneProd.{u1, u2} M N _inst_1 _inst_2) (fun (x : α) => Prod.mk.{u1, u2} M N (f x) (g x))) (Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) (Function.mulSupport.{u3, u1} α M _inst_1 f) (Function.mulSupport.{u3, u2} α N _inst_2 g))
Case conversion may be inaccurate. Consider using '#align function.mul_support_prod_mk Function.mulSupport_prod_mkₓ'. -/
@[to_additive support_prod_mk]
theorem mulSupport_prod_mk (f : α → M) (g : α → N) :
    (mulSupport fun x => (f x, g x)) = mulSupport f ∪ mulSupport g :=
  Set.ext fun x => by
    simp only [mul_support, not_and_or, mem_union, mem_set_of_eq, Prod.mk_eq_one, Ne.def]
#align function.mul_support_prod_mk Function.mulSupport_prod_mk
#align function.support_prod_mk Function.support_prod_mk

/- warning: function.mul_support_prod_mk' -> Function.mulSupport_prod_mk' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u3} N] (f : α -> (Prod.{u2, u3} M N)), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, max u2 u3} α (Prod.{u2, u3} M N) (Prod.hasOne.{u2, u3} M N _inst_1 _inst_2) f) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (fun (x : α) => Prod.fst.{u2, u3} M N (f x))) (Function.mulSupport.{u1, u3} α N _inst_2 (fun (x : α) => Prod.snd.{u2, u3} M N (f x))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : One.{u3} M] [_inst_2 : One.{u2} N] (f : α -> (Prod.{u3, u2} M N)), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, max u3 u2} α (Prod.{u3, u2} M N) (Prod.instOneProd.{u3, u2} M N _inst_1 _inst_2) f) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Function.mulSupport.{u1, u3} α M _inst_1 (fun (x : α) => Prod.fst.{u3, u2} M N (f x))) (Function.mulSupport.{u1, u2} α N _inst_2 (fun (x : α) => Prod.snd.{u3, u2} M N (f x))))
Case conversion may be inaccurate. Consider using '#align function.mul_support_prod_mk' Function.mulSupport_prod_mk'ₓ'. -/
@[to_additive support_prod_mk']
theorem mulSupport_prod_mk' (f : α → M × N) :
    mulSupport f = (mulSupport fun x => (f x).1) ∪ mulSupport fun x => (f x).2 := by
  simp only [← mul_support_prod_mk, Prod.mk.eta]
#align function.mul_support_prod_mk' Function.mulSupport_prod_mk'
#align function.support_prod_mk' Function.support_prod_mk'

/- warning: function.mul_support_along_fiber_subset -> Function.mulSupport_along_fiber_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : One.{u3} M] (f : (Prod.{u1, u2} α β) -> M) (a : α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Function.mulSupport.{u2, u3} β M _inst_1 (fun (b : β) => f (Prod.mk.{u1, u2} α β a b))) (Set.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (Function.mulSupport.{max u1 u2, u3} (Prod.{u1, u2} α β) M _inst_1 f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (f : (Prod.{u3, u2} α β) -> M) (a : α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Function.mulSupport.{u2, u1} β M _inst_1 (fun (b : β) => f (Prod.mk.{u3, u2} α β a b))) (Set.image.{max u2 u3, u2} (Prod.{u3, u2} α β) β (Prod.snd.{u3, u2} α β) (Function.mulSupport.{max u3 u2, u1} (Prod.{u3, u2} α β) M _inst_1 f))
Case conversion may be inaccurate. Consider using '#align function.mul_support_along_fiber_subset Function.mulSupport_along_fiber_subsetₓ'. -/
@[to_additive]
theorem mulSupport_along_fiber_subset (f : α × β → M) (a : α) :
    (mulSupport fun b => f (a, b)) ⊆ (mulSupport f).image Prod.snd := by tidy
#align function.mul_support_along_fiber_subset Function.mulSupport_along_fiber_subset
#align function.support_along_fiber_subset Function.support_along_fiber_subset

/- warning: function.mul_support_along_fiber_finite_of_finite -> Function.mulSupport_along_fiber_finite_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : One.{u3} M] (f : (Prod.{u1, u2} α β) -> M) (a : α), (Set.Finite.{max u1 u2} (Prod.{u1, u2} α β) (Function.mulSupport.{max u1 u2, u3} (Prod.{u1, u2} α β) M _inst_1 f)) -> (Set.Finite.{u2} β (Function.mulSupport.{u2, u3} β M _inst_1 (fun (b : β) => f (Prod.mk.{u1, u2} α β a b))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (f : (Prod.{u3, u2} α β) -> M) (a : α), (Set.Finite.{max u3 u2} (Prod.{u3, u2} α β) (Function.mulSupport.{max u3 u2, u1} (Prod.{u3, u2} α β) M _inst_1 f)) -> (Set.Finite.{u2} β (Function.mulSupport.{u2, u1} β M _inst_1 (fun (b : β) => f (Prod.mk.{u3, u2} α β a b))))
Case conversion may be inaccurate. Consider using '#align function.mul_support_along_fiber_finite_of_finite Function.mulSupport_along_fiber_finite_of_finiteₓ'. -/
@[simp, to_additive]
theorem mulSupport_along_fiber_finite_of_finite (f : α × β → M) (a : α)
    (h : (mulSupport f).Finite) : (mulSupport fun b => f (a, b)).Finite :=
  (h.image Prod.snd).Subset (mulSupport_along_fiber_subset f a)
#align function.mul_support_along_fiber_finite_of_finite Function.mulSupport_along_fiber_finite_of_finite
#align function.support_along_fiber_finite_of_finite Function.support_along_fiber_finite_of_finite

end One

/- warning: function.mul_support_mul -> Function.mulSupport_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (fun (x : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) f) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) g))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (f : α -> M) (g : α -> M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.mulSupport.{u1, u2} α M (MulOneClass.toOne.{u2} M _inst_1) (fun (x : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Function.mulSupport.{u1, u2} α M (MulOneClass.toOne.{u2} M _inst_1) f) (Function.mulSupport.{u1, u2} α M (MulOneClass.toOne.{u2} M _inst_1) g))
Case conversion may be inaccurate. Consider using '#align function.mul_support_mul Function.mulSupport_mulₓ'. -/
@[to_additive]
theorem mulSupport_mul [MulOneClass M] (f g : α → M) :
    (mulSupport fun x => f x * g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· * ·) (one_mul _) f g
#align function.mul_support_mul Function.mulSupport_mul
#align function.support_add Function.support_add

/- warning: function.mul_support_pow -> Function.mulSupport_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] (f : α -> M) (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (fun (x : α) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_1)) (f x) n)) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) f)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] (f : α -> M) (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.mulSupport.{u1, u2} α M (Monoid.toOne.{u2} M _inst_1) (fun (x : α) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_1)) (f x) n)) (Function.mulSupport.{u1, u2} α M (Monoid.toOne.{u2} M _inst_1) f)
Case conversion may be inaccurate. Consider using '#align function.mul_support_pow Function.mulSupport_powₓ'. -/
@[to_additive]
theorem mulSupport_pow [Monoid M] (f : α → M) (n : ℕ) :
    (mulSupport fun x => f x ^ n) ⊆ mulSupport f :=
  by
  induction' n with n hfn
  · simpa only [pow_zero, mul_support_one] using empty_subset _
  · simpa only [pow_succ] using (mul_support_mul f _).trans (union_subset subset.rfl hfn)
#align function.mul_support_pow Function.mulSupport_pow
#align function.support_nsmul Function.support_nsmul

section DivisionMonoid

variable [DivisionMonoid G] (f g : α → G)

/- warning: function.mul_support_inv -> Function.mulSupport_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : DivisionMonoid.{u2} G] (f : α -> G), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) (fun (x : α) => Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)) (f x))) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) f)
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] (f : α -> G), Eq.{succ u2} (Set.{u2} α) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) (fun (x : α) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) (f x))) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) f)
Case conversion may be inaccurate. Consider using '#align function.mul_support_inv Function.mulSupport_invₓ'. -/
@[simp, to_additive]
theorem mulSupport_inv : (mulSupport fun x => (f x)⁻¹) = mulSupport f :=
  ext fun _ => inv_ne_one
#align function.mul_support_inv Function.mulSupport_inv
#align function.support_neg Function.support_neg

/- warning: function.mul_support_inv' -> Function.mulSupport_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : DivisionMonoid.{u2} G] (f : α -> G), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) (Inv.inv.{max u1 u2} (α -> G) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => DivInvMonoid.toHasInv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1))) f)) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) f)
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] (f : α -> G), Eq.{succ u2} (Set.{u2} α) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) (Inv.inv.{max u1 u2} (α -> G) (Pi.instInv.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1)))) f)) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) f)
Case conversion may be inaccurate. Consider using '#align function.mul_support_inv' Function.mulSupport_inv'ₓ'. -/
@[simp, to_additive]
theorem mulSupport_inv' : mulSupport f⁻¹ = mulSupport f :=
  mulSupport_inv f
#align function.mul_support_inv' Function.mulSupport_inv'
#align function.support_neg' Function.support_neg'

/- warning: function.mul_support_mul_inv -> Function.mulSupport_mul_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : DivisionMonoid.{u2} G] (f : α -> G) (g : α -> G), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) (fun (x : α) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1))))) (f x) (Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)) (g x)))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) f) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) g))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] (f : α -> G) (g : α -> G), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) (fun (x : α) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1))))) (f x) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) (g x)))) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) f) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) g))
Case conversion may be inaccurate. Consider using '#align function.mul_support_mul_inv Function.mulSupport_mul_invₓ'. -/
@[to_additive]
theorem mulSupport_mul_inv : (mulSupport fun x => f x * (g x)⁻¹) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g
#align function.mul_support_mul_inv Function.mulSupport_mul_inv
#align function.support_add_neg Function.support_add_neg

/- warning: function.mul_support_div -> Function.mulSupport_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : DivisionMonoid.{u2} G] (f : α -> G) (g : α -> G), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1))) (f x) (g x))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) f) (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G _inst_1)))) g))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] (f : α -> G) (g : α -> G), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) (fun (x : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1))) (f x) (g x))) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) f) (Function.mulSupport.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) g))
Case conversion may be inaccurate. Consider using '#align function.mul_support_div Function.mulSupport_divₓ'. -/
@[to_additive]
theorem mulSupport_div : (mulSupport fun x => f x / g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· / ·) one_div_one f g
#align function.mul_support_div Function.mulSupport_div
#align function.support_sub Function.support_sub

end DivisionMonoid

/- warning: function.support_smul -> Function.support_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {R : Type.{u3}} [_inst_1 : Zero.{u3} R] [_inst_2 : Zero.{u2} M] [_inst_3 : SMulWithZero.{u3, u2} R M _inst_1 _inst_2] [_inst_4 : NoZeroSMulDivisors.{u3, u2} R M _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u3, u2} R M _inst_2 (SMulWithZero.toSmulZeroClass.{u3, u2} R M _inst_1 _inst_2 _inst_3))] (f : α -> R) (g : α -> M), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α M _inst_2 (SMul.smul.{max u1 u3, max u1 u2} (α -> R) (α -> M) (Pi.smul'.{u1, u3, u2} α (fun (ᾰ : α) => R) (fun (ᾰ : α) => M) (fun (i : α) => SMulZeroClass.toHasSmul.{u3, u2} R M _inst_2 (SMulWithZero.toSmulZeroClass.{u3, u2} R M _inst_1 _inst_2 _inst_3))) f g)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Function.support.{u1, u3} α R _inst_1 f) (Function.support.{u1, u2} α M _inst_2 g))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} {R : Type.{u3}} [_inst_1 : Zero.{u3} R] [_inst_2 : Zero.{u2} M] [_inst_3 : SMulWithZero.{u3, u2} R M _inst_1 _inst_2] [_inst_4 : NoZeroSMulDivisors.{u3, u2} R M _inst_1 _inst_2 (SMulZeroClass.toSMul.{u3, u2} R M _inst_2 (SMulWithZero.toSMulZeroClass.{u3, u2} R M _inst_1 _inst_2 _inst_3))] (f : α -> R) (g : α -> M), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α M _inst_2 (HSMul.hSMul.{max u1 u3, max u1 u2, max u1 u2} (α -> R) (α -> M) (α -> M) (instHSMul.{max u1 u3, max u1 u2} (α -> R) (α -> M) (Pi.smul'.{u1, u3, u2} α (fun (a._@.Mathlib.Algebra.Support._hyg.2534 : α) => R) (fun (a._@.Mathlib.Algebra.Support._hyg.2537 : α) => M) (fun (i : α) => SMulZeroClass.toSMul.{u3, u2} R M _inst_2 (SMulWithZero.toSMulZeroClass.{u3, u2} R M _inst_1 _inst_2 _inst_3)))) f g)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Function.support.{u1, u3} α R _inst_1 f) (Function.support.{u1, u2} α M _inst_2 g))
Case conversion may be inaccurate. Consider using '#align function.support_smul Function.support_smulₓ'. -/
theorem support_smul [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] (f : α → R)
    (g : α → M) : support (f • g) = support f ∩ support g :=
  ext fun x => smul_ne_zero_iff
#align function.support_smul Function.support_smul

/- warning: function.support_mul -> Function.support_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : MulZeroClass.{u2} R] [_inst_2 : NoZeroDivisors.{u2} R (MulZeroClass.toHasMul.{u2} R _inst_1) (MulZeroClass.toHasZero.{u2} R _inst_1)] (f : α -> R) (g : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R _inst_1) (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulZeroClass.toHasMul.{u2} R _inst_1)) (f x) (g x))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Function.support.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R _inst_1) f) (Function.support.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R _inst_1) g))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : MulZeroClass.{u2} R] [_inst_2 : NoZeroDivisors.{u2} R (MulZeroClass.toMul.{u2} R _inst_1) (MulZeroClass.toZero.{u2} R _inst_1)] (f : α -> R) (g : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α R (MulZeroClass.toZero.{u2} R _inst_1) (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulZeroClass.toMul.{u2} R _inst_1)) (f x) (g x))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Function.support.{u1, u2} α R (MulZeroClass.toZero.{u2} R _inst_1) f) (Function.support.{u1, u2} α R (MulZeroClass.toZero.{u2} R _inst_1) g))
Case conversion may be inaccurate. Consider using '#align function.support_mul Function.support_mulₓ'. -/
@[simp]
theorem support_mul [MulZeroClass R] [NoZeroDivisors R] (f g : α → R) :
    (support fun x => f x * g x) = support f ∩ support g :=
  support_smul f g
#align function.support_mul Function.support_mul

/- warning: function.support_mul_subset_left -> Function.support_mul_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : MulZeroClass.{u2} R] (f : α -> R) (g : α -> R), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.support.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R _inst_1) (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulZeroClass.toHasMul.{u2} R _inst_1)) (f x) (g x))) (Function.support.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R _inst_1) f)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : MulZeroClass.{u2} R] (f : α -> R) (g : α -> R), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.support.{u1, u2} α R (MulZeroClass.toZero.{u2} R _inst_1) (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulZeroClass.toMul.{u2} R _inst_1)) (f x) (g x))) (Function.support.{u1, u2} α R (MulZeroClass.toZero.{u2} R _inst_1) f)
Case conversion may be inaccurate. Consider using '#align function.support_mul_subset_left Function.support_mul_subset_leftₓ'. -/
@[simp]
theorem support_mul_subset_left [MulZeroClass R] (f g : α → R) :
    (support fun x => f x * g x) ⊆ support f := fun x hfg hf => hfg <| by simp only [hf, zero_mul]
#align function.support_mul_subset_left Function.support_mul_subset_left

/- warning: function.support_mul_subset_right -> Function.support_mul_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : MulZeroClass.{u2} R] (f : α -> R) (g : α -> R), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.support.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R _inst_1) (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulZeroClass.toHasMul.{u2} R _inst_1)) (f x) (g x))) (Function.support.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R _inst_1) g)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : MulZeroClass.{u2} R] (f : α -> R) (g : α -> R), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.support.{u1, u2} α R (MulZeroClass.toZero.{u2} R _inst_1) (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulZeroClass.toMul.{u2} R _inst_1)) (f x) (g x))) (Function.support.{u1, u2} α R (MulZeroClass.toZero.{u2} R _inst_1) g)
Case conversion may be inaccurate. Consider using '#align function.support_mul_subset_right Function.support_mul_subset_rightₓ'. -/
@[simp]
theorem support_mul_subset_right [MulZeroClass R] (f g : α → R) :
    (support fun x => f x * g x) ⊆ support g := fun x hfg hg => hfg <| by simp only [hg, mul_zero]
#align function.support_mul_subset_right Function.support_mul_subset_right

/- warning: function.support_smul_subset_right -> Function.support_smul_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : AddMonoid.{u2} A] [_inst_2 : Monoid.{u3} B] [_inst_3 : DistribMulAction.{u3, u2} B A _inst_2 _inst_1] (b : B) (f : α -> A), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.support.{u1, u2} α A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_1)) (SMul.smul.{u3, max u1 u2} B (α -> A) (Function.hasSMul.{u1, u3, u2} α B A (SMulZeroClass.toHasSmul.{u3, u2} B A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_1)) (DistribSMul.toSmulZeroClass.{u3, u2} B A (AddMonoid.toAddZeroClass.{u2} A _inst_1) (DistribMulAction.toDistribSMul.{u3, u2} B A _inst_2 _inst_1 _inst_3)))) b f)) (Function.support.{u1, u2} α A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_1)) f)
but is expected to have type
  forall {α : Type.{u1}} {A : Type.{u3}} {B : Type.{u2}} [_inst_1 : AddMonoid.{u3} A] [_inst_2 : Monoid.{u2} B] [_inst_3 : DistribMulAction.{u2, u3} B A _inst_2 _inst_1] (b : B) (f : α -> A), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Function.support.{u1, u3} α A (AddMonoid.toZero.{u3} A _inst_1) (HSMul.hSMul.{u2, max u1 u3, max u1 u3} B (α -> A) (α -> A) (instHSMul.{u2, max u1 u3} B (α -> A) (Pi.instSMul.{u1, u3, u2} α B (fun (a._@.Mathlib.Algebra.Support._hyg.2751 : α) => A) (fun (i : α) => SMulZeroClass.toSMul.{u2, u3} B A (AddMonoid.toZero.{u3} A _inst_1) (DistribSMul.toSMulZeroClass.{u2, u3} B A (AddMonoid.toAddZeroClass.{u3} A _inst_1) (DistribMulAction.toDistribSMul.{u2, u3} B A _inst_2 _inst_1 _inst_3))))) b f)) (Function.support.{u1, u3} α A (AddMonoid.toZero.{u3} A _inst_1) f)
Case conversion may be inaccurate. Consider using '#align function.support_smul_subset_right Function.support_smul_subset_rightₓ'. -/
theorem support_smul_subset_right [AddMonoid A] [Monoid B] [DistribMulAction B A] (b : B)
    (f : α → A) : support (b • f) ⊆ support f := fun x hbf hf =>
  hbf <| by rw [Pi.smul_apply, hf, smul_zero]
#align function.support_smul_subset_right Function.support_smul_subset_right

#print Function.support_smul_subset_left /-
theorem support_smul_subset_left [Zero M] [Zero β] [SMulWithZero M β] (f : α → M) (g : α → β) :
    support (f • g) ⊆ support f := fun x hfg hf => hfg <| by rw [Pi.smul_apply', hf, zero_smul]
#align function.support_smul_subset_left Function.support_smul_subset_left
-/

/- warning: function.support_const_smul_of_ne_zero -> Function.support_const_smul_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {R : Type.{u3}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M _inst_1 _inst_2] [_inst_4 : NoZeroSMulDivisors.{u3, u2} R M (MulZeroClass.toHasZero.{u3} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (SMulZeroClass.toHasSmul.{u3, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u3, u2} R M (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Module.toMulActionWithZero.{u3, u2} R M _inst_1 _inst_2 _inst_3))))] (c : R) (g : α -> M), (Ne.{succ u3} R c (OfNat.ofNat.{u3} R 0 (OfNat.mk.{u3} R 0 (Zero.zero.{u3} R (MulZeroClass.toHasZero.{u3} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))))))) -> (Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (SMul.smul.{u3, max u1 u2} R (α -> M) (Function.hasSMul.{u1, u3, u2} α R M (SMulZeroClass.toHasSmul.{u3, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u3, u2} R M (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Module.toMulActionWithZero.{u3, u2} R M _inst_1 _inst_2 _inst_3))))) c g)) (Function.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) g))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} {R : Type.{u3}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M _inst_1 _inst_2] [_inst_4 : NoZeroSMulDivisors.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (SMulZeroClass.toSMul.{u3, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (Module.toMulActionWithZero.{u3, u2} R M _inst_1 _inst_2 _inst_3))))] (c : R) (g : α -> M), (Ne.{succ u3} R c (OfNat.ofNat.{u3} R 0 (Zero.toOfNat0.{u3} R (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1))))) -> (Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} R (α -> M) (α -> M) (instHSMul.{u3, max u1 u2} R (α -> M) (Pi.instSMul.{u1, u2, u3} α R (fun (a._@.Mathlib.Algebra.Support._hyg.2919 : α) => M) (fun (i : α) => SMulZeroClass.toSMul.{u3, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (Module.toMulActionWithZero.{u3, u2} R M _inst_1 _inst_2 _inst_3)))))) c g)) (Function.support.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align function.support_const_smul_of_ne_zero Function.support_const_smul_of_ne_zeroₓ'. -/
theorem support_const_smul_of_ne_zero [Semiring R] [AddCommMonoid M] [Module R M]
    [NoZeroSMulDivisors R M] (c : R) (g : α → M) (hc : c ≠ 0) : support (c • g) = support g :=
  ext fun x => by simp only [hc, mem_support, Pi.smul_apply, Ne.def, smul_eq_zero, false_or_iff]
#align function.support_const_smul_of_ne_zero Function.support_const_smul_of_ne_zero

/- warning: function.support_inv -> Function.support_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] (f : α -> G₀), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (fun (x : α) => Inv.inv.{u2} G₀ (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)) (f x))) (Function.support.{u1, u2} α G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) f)
but is expected to have type
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] (f : α -> G₀), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (fun (x : α) => Inv.inv.{u2} G₀ (GroupWithZero.toInv.{u2} G₀ _inst_1) (f x))) (Function.support.{u1, u2} α G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) f)
Case conversion may be inaccurate. Consider using '#align function.support_inv Function.support_invₓ'. -/
@[simp]
theorem support_inv [GroupWithZero G₀] (f : α → G₀) : (support fun x => (f x)⁻¹) = support f :=
  Set.ext fun x => not_congr inv_eq_zero
#align function.support_inv Function.support_inv

/- warning: function.support_div -> Function.support_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] (f : α -> G₀) (g : α -> G₀), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) (f x) (g x))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Function.support.{u1, u2} α G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) f) (Function.support.{u1, u2} α G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) g))
but is expected to have type
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] (f : α -> G₀) (g : α -> G₀), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (GroupWithZero.toDiv.{u2} G₀ _inst_1)) (f x) (g x))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Function.support.{u1, u2} α G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) f) (Function.support.{u1, u2} α G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) g))
Case conversion may be inaccurate. Consider using '#align function.support_div Function.support_divₓ'. -/
@[simp]
theorem support_div [GroupWithZero G₀] (f g : α → G₀) :
    (support fun x => f x / g x) = support f ∩ support g := by simp [div_eq_mul_inv]
#align function.support_div Function.support_div

/- warning: function.mul_support_prod -> Function.mulSupport_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (s : Finset.{u1} α) (f : α -> β -> M), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Function.mulSupport.{u2, u3} β M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (fun (x : β) => Finset.prod.{u3, u1} M α _inst_1 s (fun (i : α) => f i x))) (Set.unionᵢ.{u2, succ u1} β α (fun (i : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) => Function.mulSupport.{u2, u3} β M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (s : Finset.{u2} α) (f : α -> β -> M), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Function.mulSupport.{u1, u3} β M (Monoid.toOne.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (fun (x : β) => Finset.prod.{u3, u2} M α _inst_1 s (fun (i : α) => f i x))) (Set.unionᵢ.{u1, succ u2} β α (fun (i : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) => Function.mulSupport.{u1, u3} β M (Monoid.toOne.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (f i))))
Case conversion may be inaccurate. Consider using '#align function.mul_support_prod Function.mulSupport_prodₓ'. -/
@[to_additive]
theorem mulSupport_prod [CommMonoid M] (s : Finset α) (f : α → β → M) :
    (mulSupport fun x => ∏ i in s, f i x) ⊆ ⋃ i ∈ s, mulSupport (f i) :=
  by
  rw [mul_support_subset_iff']
  simp only [mem_Union, not_exists, nmem_mul_support]
  exact fun x => Finset.prod_eq_one
#align function.mul_support_prod Function.mulSupport_prod
#align function.support_sum Function.support_sum

/- warning: function.support_prod_subset -> Function.support_prod_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommMonoidWithZero.{u3} A] (s : Finset.{u1} α) (f : α -> β -> A), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Function.support.{u2, u3} β A (MulZeroClass.toHasZero.{u3} A (MulZeroOneClass.toMulZeroClass.{u3} A (MonoidWithZero.toMulZeroOneClass.{u3} A (CommMonoidWithZero.toMonoidWithZero.{u3} A _inst_1)))) (fun (x : β) => Finset.prod.{u3, u1} A α (CommMonoidWithZero.toCommMonoid.{u3} A _inst_1) s (fun (i : α) => f i x))) (Set.interᵢ.{u2, succ u1} β α (fun (i : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) => Function.support.{u2, u3} β A (MulZeroClass.toHasZero.{u3} A (MulZeroOneClass.toMulZeroClass.{u3} A (MonoidWithZero.toMulZeroOneClass.{u3} A (CommMonoidWithZero.toMonoidWithZero.{u3} A _inst_1)))) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {A : Type.{u3}} [_inst_1 : CommMonoidWithZero.{u3} A] (s : Finset.{u2} α) (f : α -> β -> A), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Function.support.{u1, u3} β A (CommMonoidWithZero.toZero.{u3} A _inst_1) (fun (x : β) => Finset.prod.{u3, u2} A α (CommMonoidWithZero.toCommMonoid.{u3} A _inst_1) s (fun (i : α) => f i x))) (Set.interᵢ.{u1, succ u2} β α (fun (i : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) => Function.support.{u1, u3} β A (CommMonoidWithZero.toZero.{u3} A _inst_1) (f i))))
Case conversion may be inaccurate. Consider using '#align function.support_prod_subset Function.support_prod_subsetₓ'. -/
theorem support_prod_subset [CommMonoidWithZero A] (s : Finset α) (f : α → β → A) :
    (support fun x => ∏ i in s, f i x) ⊆ ⋂ i ∈ s, support (f i) := fun x hx =>
  mem_interᵢ₂.2 fun i hi H => hx <| Finset.prod_eq_zero hi H
#align function.support_prod_subset Function.support_prod_subset

/- warning: function.support_prod -> Function.support_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommMonoidWithZero.{u3} A] [_inst_2 : NoZeroDivisors.{u3} A (MulZeroClass.toHasMul.{u3} A (MulZeroOneClass.toMulZeroClass.{u3} A (MonoidWithZero.toMulZeroOneClass.{u3} A (CommMonoidWithZero.toMonoidWithZero.{u3} A _inst_1)))) (MulZeroClass.toHasZero.{u3} A (MulZeroOneClass.toMulZeroClass.{u3} A (MonoidWithZero.toMulZeroOneClass.{u3} A (CommMonoidWithZero.toMonoidWithZero.{u3} A _inst_1))))] [_inst_3 : Nontrivial.{u3} A] (s : Finset.{u1} α) (f : α -> β -> A), Eq.{succ u2} (Set.{u2} β) (Function.support.{u2, u3} β A (MulZeroClass.toHasZero.{u3} A (MulZeroOneClass.toMulZeroClass.{u3} A (MonoidWithZero.toMulZeroOneClass.{u3} A (CommMonoidWithZero.toMonoidWithZero.{u3} A _inst_1)))) (fun (x : β) => Finset.prod.{u3, u1} A α (CommMonoidWithZero.toCommMonoid.{u3} A _inst_1) s (fun (i : α) => f i x))) (Set.interᵢ.{u2, succ u1} β α (fun (i : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) => Function.support.{u2, u3} β A (MulZeroClass.toHasZero.{u3} A (MulZeroOneClass.toMulZeroClass.{u3} A (MonoidWithZero.toMulZeroOneClass.{u3} A (CommMonoidWithZero.toMonoidWithZero.{u3} A _inst_1)))) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {A : Type.{u3}} [_inst_1 : CommMonoidWithZero.{u3} A] [_inst_2 : NoZeroDivisors.{u3} A (MulZeroClass.toMul.{u3} A (MulZeroOneClass.toMulZeroClass.{u3} A (MonoidWithZero.toMulZeroOneClass.{u3} A (CommMonoidWithZero.toMonoidWithZero.{u3} A _inst_1)))) (CommMonoidWithZero.toZero.{u3} A _inst_1)] [_inst_3 : Nontrivial.{u3} A] (s : Finset.{u2} α) (f : α -> β -> A), Eq.{succ u1} (Set.{u1} β) (Function.support.{u1, u3} β A (CommMonoidWithZero.toZero.{u3} A _inst_1) (fun (x : β) => Finset.prod.{u3, u2} A α (CommMonoidWithZero.toCommMonoid.{u3} A _inst_1) s (fun (i : α) => f i x))) (Set.interᵢ.{u1, succ u2} β α (fun (i : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) => Function.support.{u1, u3} β A (CommMonoidWithZero.toZero.{u3} A _inst_1) (f i))))
Case conversion may be inaccurate. Consider using '#align function.support_prod Function.support_prodₓ'. -/
theorem support_prod [CommMonoidWithZero A] [NoZeroDivisors A] [Nontrivial A] (s : Finset α)
    (f : α → β → A) : (support fun x => ∏ i in s, f i x) = ⋂ i ∈ s, support (f i) :=
  Set.ext fun x => by
    simp only [support, Ne.def, Finset.prod_eq_zero_iff, mem_set_of_eq, Set.mem_interᵢ, not_exists]
#align function.support_prod Function.support_prod

/- warning: function.mul_support_one_add -> Function.mulSupport_one_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddLeftCancelMonoid.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (fun (x : α) => HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (AddZeroClass.toHasAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddLeftCancelMonoid.toAddMonoid.{u2} R _inst_2)))) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R _inst_1))) (f x))) (Function.support.{u1, u2} α R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddLeftCancelMonoid.toAddMonoid.{u2} R _inst_2))) f)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddLeftCancelMonoid.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (fun (x : α) => HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (AddZeroClass.toAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddLeftCancelMonoid.toAddMonoid.{u2} R _inst_2)))) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R _inst_1)) (f x))) (Function.support.{u1, u2} α R (AddLeftCancelMonoid.toZero.{u2} R _inst_2) f)
Case conversion may be inaccurate. Consider using '#align function.mul_support_one_add Function.mulSupport_one_addₓ'. -/
theorem mulSupport_one_add [One R] [AddLeftCancelMonoid R] (f : α → R) :
    (mulSupport fun x => 1 + f x) = support f :=
  Set.ext fun x => not_congr add_right_eq_self
#align function.mul_support_one_add Function.mulSupport_one_add

/- warning: function.mul_support_one_add' -> Function.mulSupport_one_add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddLeftCancelMonoid.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> R) (α -> R) (α -> R) (instHAdd.{max u1 u2} (α -> R) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => AddZeroClass.toHasAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddLeftCancelMonoid.toAddMonoid.{u2} R _inst_2))))) (OfNat.ofNat.{max u1 u2} (α -> R) 1 (OfNat.mk.{max u1 u2} (α -> R) 1 (One.one.{max u1 u2} (α -> R) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => _inst_1))))) f)) (Function.support.{u1, u2} α R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddLeftCancelMonoid.toAddMonoid.{u2} R _inst_2))) f)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddLeftCancelMonoid.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (HAdd.hAdd.{max u1 u2, max u1 u2, max u2 u1} (α -> R) (α -> R) (α -> R) (instHAdd.{max u1 u2} (α -> R) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => AddZeroClass.toAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddLeftCancelMonoid.toAddMonoid.{u2} R _inst_2))))) (OfNat.ofNat.{max u1 u2} (α -> R) 1 (One.toOfNat1.{max u1 u2} (α -> R) (Pi.instOne.{u1, u2} α (fun (a._@.Mathlib.Algebra.Support._hyg.3416 : α) => R) (fun (i : α) => _inst_1)))) f)) (Function.support.{u1, u2} α R (AddLeftCancelMonoid.toZero.{u2} R _inst_2) f)
Case conversion may be inaccurate. Consider using '#align function.mul_support_one_add' Function.mulSupport_one_add'ₓ'. -/
theorem mulSupport_one_add' [One R] [AddLeftCancelMonoid R] (f : α → R) :
    mulSupport (1 + f) = support f :=
  mulSupport_one_add f
#align function.mul_support_one_add' Function.mulSupport_one_add'

/- warning: function.mul_support_add_one -> Function.mulSupport_add_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddRightCancelMonoid.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (fun (x : α) => HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (AddZeroClass.toHasAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddRightCancelMonoid.toAddMonoid.{u2} R _inst_2)))) (f x) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R _inst_1))))) (Function.support.{u1, u2} α R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddRightCancelMonoid.toAddMonoid.{u2} R _inst_2))) f)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddRightCancelMonoid.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (fun (x : α) => HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (AddZeroClass.toAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddRightCancelMonoid.toAddMonoid.{u2} R _inst_2)))) (f x) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R _inst_1)))) (Function.support.{u1, u2} α R (AddRightCancelMonoid.toZero.{u2} R _inst_2) f)
Case conversion may be inaccurate. Consider using '#align function.mul_support_add_one Function.mulSupport_add_oneₓ'. -/
theorem mulSupport_add_one [One R] [AddRightCancelMonoid R] (f : α → R) :
    (mulSupport fun x => f x + 1) = support f :=
  Set.ext fun x => not_congr add_left_eq_self
#align function.mul_support_add_one Function.mulSupport_add_one

/- warning: function.mul_support_add_one' -> Function.mulSupport_add_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddRightCancelMonoid.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> R) (α -> R) (α -> R) (instHAdd.{max u1 u2} (α -> R) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => AddZeroClass.toHasAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddRightCancelMonoid.toAddMonoid.{u2} R _inst_2))))) f (OfNat.ofNat.{max u1 u2} (α -> R) 1 (OfNat.mk.{max u1 u2} (α -> R) 1 (One.one.{max u1 u2} (α -> R) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => _inst_1))))))) (Function.support.{u1, u2} α R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddRightCancelMonoid.toAddMonoid.{u2} R _inst_2))) f)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddRightCancelMonoid.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (HAdd.hAdd.{max u1 u2, max u1 u2, max u2 u1} (α -> R) (α -> R) (α -> R) (instHAdd.{max u1 u2} (α -> R) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => AddZeroClass.toAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddRightCancelMonoid.toAddMonoid.{u2} R _inst_2))))) f (OfNat.ofNat.{max u1 u2} (α -> R) 1 (One.toOfNat1.{max u1 u2} (α -> R) (Pi.instOne.{u1, u2} α (fun (a._@.Mathlib.Algebra.Support._hyg.3501 : α) => R) (fun (i : α) => _inst_1)))))) (Function.support.{u1, u2} α R (AddRightCancelMonoid.toZero.{u2} R _inst_2) f)
Case conversion may be inaccurate. Consider using '#align function.mul_support_add_one' Function.mulSupport_add_one'ₓ'. -/
theorem mulSupport_add_one' [One R] [AddRightCancelMonoid R] (f : α → R) :
    mulSupport (f + 1) = support f :=
  mulSupport_add_one f
#align function.mul_support_add_one' Function.mulSupport_add_one'

/- warning: function.mul_support_one_sub' -> Function.mulSupport_one_sub' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddGroup.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> R) (α -> R) (α -> R) (instHSub.{max u1 u2} (α -> R) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R _inst_2)))) (OfNat.ofNat.{max u1 u2} (α -> R) 1 (OfNat.mk.{max u1 u2} (α -> R) 1 (One.one.{max u1 u2} (α -> R) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => _inst_1))))) f)) (Function.support.{u1, u2} α R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R _inst_2)))) f)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddGroup.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (HSub.hSub.{max u1 u2, max u1 u2, max u2 u1} (α -> R) (α -> R) (α -> R) (instHSub.{max u1 u2} (α -> R) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => SubNegMonoid.toSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R _inst_2)))) (OfNat.ofNat.{max u1 u2} (α -> R) 1 (One.toOfNat1.{max u1 u2} (α -> R) (Pi.instOne.{u1, u2} α (fun (a._@.Mathlib.Algebra.Support._hyg.3540 : α) => R) (fun (i : α) => _inst_1)))) f)) (Function.support.{u1, u2} α R (NegZeroClass.toZero.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (AddGroup.toSubtractionMonoid.{u2} R _inst_2)))) f)
Case conversion may be inaccurate. Consider using '#align function.mul_support_one_sub' Function.mulSupport_one_sub'ₓ'. -/
theorem mulSupport_one_sub' [One R] [AddGroup R] (f : α → R) : mulSupport (1 - f) = support f := by
  rw [sub_eq_add_neg, mul_support_one_add', support_neg']
#align function.mul_support_one_sub' Function.mulSupport_one_sub'

/- warning: function.mul_support_one_sub -> Function.mulSupport_one_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddGroup.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (fun (x : α) => HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R _inst_2))) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R _inst_1))) (f x))) (Function.support.{u1, u2} α R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R _inst_2)))) f)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : One.{u2} R] [_inst_2 : AddGroup.{u2} R] (f : α -> R), Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α R _inst_1 (fun (x : α) => HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R _inst_2))) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R _inst_1)) (f x))) (Function.support.{u1, u2} α R (NegZeroClass.toZero.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (AddGroup.toSubtractionMonoid.{u2} R _inst_2)))) f)
Case conversion may be inaccurate. Consider using '#align function.mul_support_one_sub Function.mulSupport_one_subₓ'. -/
theorem mulSupport_one_sub [One R] [AddGroup R] (f : α → R) :
    (mulSupport fun x => 1 - f x) = support f :=
  mulSupport_one_sub' f
#align function.mul_support_one_sub Function.mulSupport_one_sub

end Function

namespace Set

open Function

variable {α β M : Type _} [One M] {f : α → M}

/- warning: set.image_inter_mul_support_eq -> Set.image_inter_mulSupport_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : One.{u3} M] {f : α -> M} {s : Set.{u2} β} {g : β -> α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.image.{u2, u1} β α g s) (Function.mulSupport.{u1, u3} α M _inst_1 f)) (Set.image.{u2, u1} β α g (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s (Function.mulSupport.{u2, u3} β M _inst_1 (Function.comp.{succ u2, succ u1, succ u3} β α M f g))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M} {s : Set.{u3} β} {g : β -> α}, Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Set.image.{u3, u2} β α g s) (Function.mulSupport.{u2, u1} α M _inst_1 f)) (Set.image.{u3, u2} β α g (Inter.inter.{u3} (Set.{u3} β) (Set.instInterSet.{u3} β) s (Function.mulSupport.{u3, u1} β M _inst_1 (Function.comp.{succ u3, succ u2, succ u1} β α M f g))))
Case conversion may be inaccurate. Consider using '#align set.image_inter_mul_support_eq Set.image_inter_mulSupport_eqₓ'. -/
@[to_additive]
theorem image_inter_mulSupport_eq {s : Set β} {g : β → α} :
    g '' s ∩ mulSupport f = g '' (s ∩ mulSupport (f ∘ g)) := by
  rw [mul_support_comp_eq_preimage f g, image_inter_preimage]
#align set.image_inter_mul_support_eq Set.image_inter_mulSupport_eq
#align set.image_inter_support_eq Set.image_inter_support_eq

end Set

namespace Pi

variable {A : Type _} {B : Type _} [DecidableEq A] [One B] {a : A} {b : B}

open Function

/- warning: pi.mul_support_mul_single_subset -> Pi.mulSupport_mulSingle_subset is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} A] [_inst_2 : One.{u2} B] {a : A} {b : B}, HasSubset.Subset.{u1} (Set.{u1} A) (Set.hasSubset.{u1} A) (Function.mulSupport.{u1, u2} A B _inst_2 (Pi.mulSingle.{u1, u2} A (fun {a : A} => B) (fun (a : A) (b : A) => _inst_1 a b) (fun (i : A) => _inst_2) a b)) (Singleton.singleton.{u1, u1} A (Set.{u1} A) (Set.hasSingleton.{u1} A) a)
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} A] [_inst_2 : One.{u1} B] {a : A} {b : B}, HasSubset.Subset.{u2} (Set.{u2} A) (Set.instHasSubsetSet.{u2} A) (Function.mulSupport.{u2, u1} A B _inst_2 (Pi.mulSingle.{u2, u1} A (fun (a : A) => B) (fun (a : A) (b : A) => _inst_1 a b) (fun (i : A) => _inst_2) a b)) (Singleton.singleton.{u2, u2} A (Set.{u2} A) (Set.instSingletonSet.{u2} A) a)
Case conversion may be inaccurate. Consider using '#align pi.mul_support_mul_single_subset Pi.mulSupport_mulSingle_subsetₓ'. -/
@[to_additive]
theorem mulSupport_mulSingle_subset : mulSupport (mulSingle a b) ⊆ {a} := fun x hx =>
  by_contra fun hx' => hx <| mulSingle_eq_of_ne hx' _
#align pi.mul_support_mul_single_subset Pi.mulSupport_mulSingle_subset
#align pi.support_single_subset Pi.support_single_subset

/- warning: pi.mul_support_mul_single_one -> Pi.mulSupport_mulSingle_one is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} A] [_inst_2 : One.{u2} B] {a : A}, Eq.{succ u1} (Set.{u1} A) (Function.mulSupport.{u1, u2} A B _inst_2 (Pi.mulSingle.{u1, u2} A (fun {a : A} => B) (fun (a : A) (b : A) => _inst_1 a b) (fun (i : A) => _inst_2) a (OfNat.ofNat.{u2} B 1 (OfNat.mk.{u2} B 1 (One.one.{u2} B _inst_2))))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} A) (Set.hasEmptyc.{u1} A))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} A] [_inst_2 : One.{u1} B] {a : A}, Eq.{succ u2} (Set.{u2} A) (Function.mulSupport.{u2, u1} A B _inst_2 (Pi.mulSingle.{u2, u1} A (fun (a : A) => B) (fun (a : A) (b : A) => _inst_1 a b) (fun (i : A) => _inst_2) a (OfNat.ofNat.{u1} B 1 (One.toOfNat1.{u1} B _inst_2)))) (EmptyCollection.emptyCollection.{u2} (Set.{u2} A) (Set.instEmptyCollectionSet.{u2} A))
Case conversion may be inaccurate. Consider using '#align pi.mul_support_mul_single_one Pi.mulSupport_mulSingle_oneₓ'. -/
@[to_additive]
theorem mulSupport_mulSingle_one : mulSupport (mulSingle a (1 : B)) = ∅ := by simp
#align pi.mul_support_mul_single_one Pi.mulSupport_mulSingle_one
#align pi.support_single_zero Pi.support_single_zero

#print Pi.mulSupport_mulSingle_of_ne /-
@[simp, to_additive]
theorem mulSupport_mulSingle_of_ne (h : b ≠ 1) : mulSupport (mulSingle a b) = {a} :=
  mulSupport_mulSingle_subset.antisymm fun x (hx : x = a) => by
    rwa [mem_mul_support, hx, mul_single_eq_same]
#align pi.mul_support_mul_single_of_ne Pi.mulSupport_mulSingle_of_ne
#align pi.support_single_of_ne Pi.support_single_of_ne
-/

#print Pi.mulSupport_mulSingle /-
@[to_additive]
theorem mulSupport_mulSingle [DecidableEq B] :
    mulSupport (mulSingle a b) = if b = 1 then ∅ else {a} := by split_ifs with h <;> simp [h]
#align pi.mul_support_mul_single Pi.mulSupport_mulSingle
#align pi.support_single Pi.support_single
-/

/- warning: pi.mul_support_mul_single_disjoint -> Pi.mulSupport_mulSingle_disjoint is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} A] [_inst_2 : One.{u2} B] {b : B} {b' : B}, (Ne.{succ u2} B b (OfNat.ofNat.{u2} B 1 (OfNat.mk.{u2} B 1 (One.one.{u2} B _inst_2)))) -> (Ne.{succ u2} B b' (OfNat.ofNat.{u2} B 1 (OfNat.mk.{u2} B 1 (One.one.{u2} B _inst_2)))) -> (forall {i : A} {j : A}, Iff (Disjoint.{u1} (Set.{u1} A) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} A) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} A) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} A) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} A) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} A) (Set.completeBooleanAlgebra.{u1} A)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} A) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} A) (Set.booleanAlgebra.{u1} A))) (Function.mulSupport.{u1, u2} A B _inst_2 (Pi.mulSingle.{u1, u2} A (fun {i : A} => B) (fun (a : A) (b : A) => _inst_1 a b) (fun (i : A) => _inst_2) i b)) (Function.mulSupport.{u1, u2} A B _inst_2 (Pi.mulSingle.{u1, u2} A (fun {j : A} => B) (fun (a : A) (b : A) => _inst_1 a b) (fun (i : A) => _inst_2) j b'))) (Ne.{succ u1} A i j))
but is expected to have type
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} A] [_inst_2 : One.{u2} B] {b : B} {b' : B}, (Ne.{succ u2} B b (OfNat.ofNat.{u2} B 1 (One.toOfNat1.{u2} B _inst_2))) -> (Ne.{succ u2} B b' (OfNat.ofNat.{u2} B 1 (One.toOfNat1.{u2} B _inst_2))) -> (forall {i : A} {j : A}, Iff (Disjoint.{u1} (Set.{u1} A) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} A) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} A) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} A) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} A) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} A) (Set.instCompleteBooleanAlgebraSet.{u1} A)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} A) (Preorder.toLE.{u1} (Set.{u1} A) (PartialOrder.toPreorder.{u1} (Set.{u1} A) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} A) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} A) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} A) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} A) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} A) (Set.instCompleteBooleanAlgebraSet.{u1} A)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} A) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} A) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} A) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} A) (Set.instCompleteBooleanAlgebraSet.{u1} A)))))) (Function.mulSupport.{u1, u2} A B _inst_2 (Pi.mulSingle.{u1, u2} A (fun (i : A) => B) (fun (a : A) (b : A) => _inst_1 a b) (fun (i : A) => _inst_2) i b)) (Function.mulSupport.{u1, u2} A B _inst_2 (Pi.mulSingle.{u1, u2} A (fun (j : A) => B) (fun (a : A) (b : A) => _inst_1 a b) (fun (i : A) => _inst_2) j b'))) (Ne.{succ u1} A i j))
Case conversion may be inaccurate. Consider using '#align pi.mul_support_mul_single_disjoint Pi.mulSupport_mulSingle_disjointₓ'. -/
@[to_additive]
theorem mulSupport_mulSingle_disjoint {b' : B} (hb : b ≠ 1) (hb' : b' ≠ 1) {i j : A} :
    Disjoint (mulSupport (mulSingle i b)) (mulSupport (mulSingle j b')) ↔ i ≠ j := by
  rw [mul_support_mul_single_of_ne hb, mul_support_mul_single_of_ne hb', disjoint_singleton]
#align pi.mul_support_mul_single_disjoint Pi.mulSupport_mulSingle_disjoint
#align pi.support_single_disjoint Pi.support_single_disjoint

end Pi

