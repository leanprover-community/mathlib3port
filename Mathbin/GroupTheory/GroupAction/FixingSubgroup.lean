/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module group_theory.group_action.fixing_subgroup
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subgroup.Actions
import Mathbin.GroupTheory.GroupAction.Basic

/-!

# Fixing submonoid, fixing subgroup of an action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In the presence of of an action of a monoid or a group,
this file defines the fixing submonoid or the fixing subgroup,
and relates it to the set of fixed points via a Galois connection.

## Main definitions

* `fixing_submonoid M s` : in the presence of `mul_action M α` (with `monoid M`)
  it is the `submonoid M` consisting of elements which fix `s : set α` pointwise.

* `fixing_submonoid_fixed_points_gc M α` is the `galois_connection`
  that relates `fixing_submonoid` with `fixed_points`.

* `fixing_subgroup M s` : in the presence of `mul_action M α` (with `group M`)
  it is the `subgroup M` consisting of elements which fix `s : set α` pointwise.

* `fixing_subgroup_fixed_points_gc M α` is the `galois_connection`
  that relates `fixing_subgroup` with `fixed_points`.

TODO :

* Maybe other lemmas are useful

* Treat semigroups ?

-/


section Monoid

open MulAction

variable (M : Type _) {α : Type _} [Monoid M] [MulAction M α]

#print fixingSubmonoid /-
/-- The submonoid fixing a set under a `mul_action`. -/
@[to_additive " The additive submonoid fixing a set under an `add_action`. "]
def fixingSubmonoid (s : Set α) : Submonoid M
    where
  carrier := { ϕ : M | ∀ x : s, ϕ • (x : α) = x }
  one_mem' _ := one_smul _ _
  mul_mem' x y hx hy z := by rw [mul_smul, hy z, hx z]
#align fixing_submonoid fixingSubmonoid
#align fixing_add_submonoid fixingAddSubmonoid
-/

/- warning: mem_fixing_submonoid_iff -> mem_fixingSubmonoid_iff is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] {s : Set.{u2} α} {m : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) m (fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 s)) (forall (y : α), (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) y s) -> (Eq.{succ u2} α (SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_2) m y) y))
but is expected to have type
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] {s : Set.{u2} α} {m : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) m (fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 s)) (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Eq.{succ u2} α (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_2)) m y) y))
Case conversion may be inaccurate. Consider using '#align mem_fixing_submonoid_iff mem_fixingSubmonoid_iffₓ'. -/
theorem mem_fixingSubmonoid_iff {s : Set α} {m : M} :
    m ∈ fixingSubmonoid M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩
#align mem_fixing_submonoid_iff mem_fixingSubmonoid_iff

variable (α)

#print fixingSubmonoid_fixedPoints_gc /-
/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
theorem fixingSubmonoid_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubmonoid M)
      ((fun P : Submonoid M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun s P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩
#align fixing_submonoid_fixed_points_gc fixingSubmonoid_fixedPoints_gc
-/

/- warning: fixing_submonoid_antitone -> fixingSubmonoid_antitone is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1], Antitone.{u2, u1} (Set.{u2} α) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (fun (s : Set.{u2} α) => fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 s)
but is expected to have type
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1], Antitone.{u2, u1} (Set.{u2} α) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (fun (s : Set.{u2} α) => fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 s)
Case conversion may be inaccurate. Consider using '#align fixing_submonoid_antitone fixingSubmonoid_antitoneₓ'. -/
theorem fixingSubmonoid_antitone : Antitone fun s : Set α => fixingSubmonoid M s :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_l
#align fixing_submonoid_antitone fixingSubmonoid_antitone

/- warning: fixed_points_antitone -> fixedPoints_antitone is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1], Antitone.{u1, u2} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u2} α) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (fun (P : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) => MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) P) α (Submonoid.toMonoid.{u1} M _inst_1 P) (Submonoid.mulAction.{u1, u2} M α _inst_1 _inst_2 P))
but is expected to have type
  forall (M : Type.{u2}) (α : Type.{u1}) [_inst_1 : Monoid.{u2} M] [_inst_2 : MulAction.{u2, u1} M α _inst_1], Antitone.{u2, u1} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (fun (P : Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) => MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x P)) α (Submonoid.toMonoid.{u2} M _inst_1 P) (Submonoid.mulAction.{u2, u1} M α _inst_1 _inst_2 P))
Case conversion may be inaccurate. Consider using '#align fixed_points_antitone fixedPoints_antitoneₓ'. -/
theorem fixedPoints_antitone : Antitone fun P : Submonoid M => fixedPoints P α :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_u.dual_left
#align fixed_points_antitone fixedPoints_antitone

/- warning: fixing_submonoid_union -> fixingSubmonoid_union is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] {s : Set.{u2} α} {t : Set.{u2} α}, Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 (Union.union.{u2} (Set.{u2} α) (Set.hasUnion.{u2} α) s t)) (HasInf.inf.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasInf.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 s) (fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 t))
but is expected to have type
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] {s : Set.{u2} α} {t : Set.{u2} α}, Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) (HasInf.inf.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instHasInfSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 s) (fixingSubmonoid.{u1, u2} M α _inst_1 _inst_2 t))
Case conversion may be inaccurate. Consider using '#align fixing_submonoid_union fixingSubmonoid_unionₓ'. -/
/-- Fixing submonoid of union is intersection -/
theorem fixingSubmonoid_union {s t : Set α} :
    fixingSubmonoid M (s ∪ t) = fixingSubmonoid M s ⊓ fixingSubmonoid M t :=
  (fixingSubmonoid_fixedPoints_gc M α).l_sup
#align fixing_submonoid_union fixingSubmonoid_union

#print fixingSubmonoid_unionᵢ /-
/-- Fixing submonoid of Union is intersection -/
theorem fixingSubmonoid_unionᵢ {ι : Sort _} {s : ι → Set α} :
    fixingSubmonoid M (⋃ i, s i) = ⨅ i, fixingSubmonoid M (s i) :=
  (fixingSubmonoid_fixedPoints_gc M α).l_supᵢ
#align fixing_submonoid_Union fixingSubmonoid_unionᵢ
-/

/- warning: fixed_points_submonoid_sup -> fixedPoints_submonoid_sup is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] {P : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)} {Q : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)}, Eq.{succ u2} (Set.{u2} α) (MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (HasSup.sup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.completeLattice.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) P Q)) α (Submonoid.toMonoid.{u1} M _inst_1 (HasSup.sup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.completeLattice.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) P Q)) (Submonoid.mulAction.{u1, u2} M α _inst_1 _inst_2 (HasSup.sup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.completeLattice.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) P Q))) (Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) P) α (Submonoid.toMonoid.{u1} M _inst_1 P) (Submonoid.mulAction.{u1, u2} M α _inst_1 _inst_2 P)) (MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) Q) α (Submonoid.toMonoid.{u1} M _inst_1 Q) (Submonoid.mulAction.{u1, u2} M α _inst_1 _inst_2 Q)))
but is expected to have type
  forall (M : Type.{u2}) (α : Type.{u1}) [_inst_1 : Monoid.{u2} M] [_inst_2 : MulAction.{u2, u1} M α _inst_1] {P : Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)} {Q : Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)}, Eq.{succ u1} (Set.{u1} α) (MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x (HasSup.sup.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SemilatticeSup.toHasSup.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Lattice.toSemilatticeSup.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (CompleteLattice.toLattice.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) P Q))) α (Submonoid.toMonoid.{u2} M _inst_1 (HasSup.sup.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SemilatticeSup.toHasSup.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Lattice.toSemilatticeSup.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (CompleteLattice.toLattice.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) P Q)) (Submonoid.mulAction.{u2, u1} M α _inst_1 _inst_2 (HasSup.sup.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SemilatticeSup.toHasSup.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Lattice.toSemilatticeSup.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (CompleteLattice.toLattice.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) P Q))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x P)) α (Submonoid.toMonoid.{u2} M _inst_1 P) (Submonoid.mulAction.{u2, u1} M α _inst_1 _inst_2 P)) (MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x Q)) α (Submonoid.toMonoid.{u2} M _inst_1 Q) (Submonoid.mulAction.{u2, u1} M α _inst_1 _inst_2 Q)))
Case conversion may be inaccurate. Consider using '#align fixed_points_submonoid_sup fixedPoints_submonoid_supₓ'. -/
/-- Fixed points of sup of submonoids is intersection -/
theorem fixedPoints_submonoid_sup {P Q : Submonoid M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_inf
#align fixed_points_submonoid_sup fixedPoints_submonoid_sup

/- warning: fixed_points_submonoid_supr -> fixedPoints_submonoid_supᵢ is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M α _inst_1] {ι : Sort.{u3}} {P : ι -> (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))}, Eq.{succ u2} (Set.{u2} α) (MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (supᵢ.{u1, u3} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.completeLattice.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) ι P)) α (Submonoid.toMonoid.{u1} M _inst_1 (supᵢ.{u1, u3} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.completeLattice.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) ι P)) (Submonoid.mulAction.{u1, u2} M α _inst_1 _inst_2 (supᵢ.{u1, u3} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.completeLattice.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) ι P))) (Set.interᵢ.{u2, u3} α ι (fun (i : ι) => MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (P i)) α (Submonoid.toMonoid.{u1} M _inst_1 (P i)) (Submonoid.mulAction.{u1, u2} M α _inst_1 _inst_2 (P i))))
but is expected to have type
  forall (M : Type.{u2}) (α : Type.{u1}) [_inst_1 : Monoid.{u2} M] [_inst_2 : MulAction.{u2, u1} M α _inst_1] {ι : Sort.{u3}} {P : ι -> (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))}, Eq.{succ u1} (Set.{u1} α) (MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x (supᵢ.{u2, u3} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (CompleteLattice.toSupSet.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) ι P))) α (Submonoid.toMonoid.{u2} M _inst_1 (supᵢ.{u2, u3} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (CompleteLattice.toSupSet.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) ι P)) (Submonoid.mulAction.{u2, u1} M α _inst_1 _inst_2 (supᵢ.{u2, u3} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (CompleteLattice.toSupSet.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) ι P))) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x (P i))) α (Submonoid.toMonoid.{u2} M _inst_1 (P i)) (Submonoid.mulAction.{u2, u1} M α _inst_1 _inst_2 (P i))))
Case conversion may be inaccurate. Consider using '#align fixed_points_submonoid_supr fixedPoints_submonoid_supᵢₓ'. -/
/-- Fixed points of supr of submonoids is intersection -/
theorem fixedPoints_submonoid_supᵢ {ι : Sort _} {P : ι → Submonoid M} :
    fixedPoints (↥(supᵢ P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_infᵢ
#align fixed_points_submonoid_supr fixedPoints_submonoid_supᵢ

end Monoid

section Group

open MulAction

variable (M : Type _) {α : Type _} [Group M] [MulAction M α]

#print fixingSubgroup /-
/-- The subgroup fixing a set under a `mul_action`. -/
@[to_additive " The additive subgroup fixing a set under an `add_action`. "]
def fixingSubgroup (s : Set α) : Subgroup M :=
  { fixingSubmonoid M s with inv_mem' := fun _ hx z => by rw [inv_smul_eq_iff, hx z] }
#align fixing_subgroup fixingSubgroup
#align fixing_add_subgroup fixingAddSubgroup
-/

/- warning: mem_fixing_subgroup_iff -> mem_fixingSubgroup_iff is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Group.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))] {s : Set.{u2} α} {m : M}, Iff (Membership.Mem.{u1, u1} M (Subgroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) m (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2 s)) (forall (y : α), (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) y s) -> (Eq.{succ u2} α (SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)) _inst_2) m y) y))
but is expected to have type
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Group.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))] {s : Set.{u2} α} {m : M}, Iff (Membership.mem.{u1, u1} M (Subgroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.instSetLikeSubgroup.{u1} M _inst_1)) m (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2 s)) (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Eq.{succ u2} α (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)) _inst_2)) m y) y))
Case conversion may be inaccurate. Consider using '#align mem_fixing_subgroup_iff mem_fixingSubgroup_iffₓ'. -/
theorem mem_fixingSubgroup_iff {s : Set α} {m : M} : m ∈ fixingSubgroup M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩
#align mem_fixing_subgroup_iff mem_fixingSubgroup_iff

variable (α)

#print fixingSubgroup_fixedPoints_gc /-
/-- The Galois connection between fixing subgroups and fixed points of a group action -/
theorem fixingSubgroup_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubgroup M)
      ((fun P : Subgroup M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun s P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩
#align fixing_subgroup_fixed_points_gc fixingSubgroup_fixedPoints_gc
-/

/- warning: fixing_subgroup_antitone -> fixingSubgroup_antitone is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Group.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))], Antitone.{u2, u1} (Set.{u2} α) (Subgroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1))) (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2)
but is expected to have type
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Group.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))], Antitone.{u2, u1} (Set.{u2} α) (Subgroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} M _inst_1)))) (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align fixing_subgroup_antitone fixingSubgroup_antitoneₓ'. -/
theorem fixingSubgroup_antitone : Antitone (fixingSubgroup M : Set α → Subgroup M) :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_l
#align fixing_subgroup_antitone fixingSubgroup_antitone

/- warning: fixed_points_subgroup_antitone -> fixedPoints_subgroup_antitone is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Group.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))], Antitone.{u1, u2} (Subgroup.{u1} M _inst_1) (Set.{u2} α) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (fun (P : Subgroup.{u1} M _inst_1) => MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) P) α (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) P) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) P) (Subgroup.toGroup.{u1} M _inst_1 P))) (Subgroup.mulAction.{u1, u2} M _inst_1 α _inst_2 P))
but is expected to have type
  forall (M : Type.{u2}) (α : Type.{u1}) [_inst_1 : Group.{u2} M] [_inst_2 : MulAction.{u2, u1} M α (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_1))], Antitone.{u2, u1} (Subgroup.{u2} M _inst_1) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Subgroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subgroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subgroup.{u2} M _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u2} M _inst_1)))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (fun (P : Subgroup.{u2} M _inst_1) => MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subgroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} M _inst_1) M (Subgroup.instSetLikeSubgroup.{u2} M _inst_1)) x P)) α (Submonoid.toMonoid.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_1)) (Subgroup.toSubmonoid.{u2} M _inst_1 P)) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u2, u1} M _inst_1 α _inst_2 P))
Case conversion may be inaccurate. Consider using '#align fixed_points_subgroup_antitone fixedPoints_subgroup_antitoneₓ'. -/
theorem fixedPoints_subgroup_antitone : Antitone fun P : Subgroup M => fixedPoints P α :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_u.dual_left
#align fixed_points_subgroup_antitone fixedPoints_subgroup_antitone

/- warning: fixing_subgroup_union -> fixingSubgroup_union is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Group.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))] {s : Set.{u2} α} {t : Set.{u2} α}, Eq.{succ u1} (Subgroup.{u1} M _inst_1) (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2 (Union.union.{u2} (Set.{u2} α) (Set.hasUnion.{u2} α) s t)) (HasInf.inf.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.hasInf.{u1} M _inst_1) (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2 s) (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2 t))
but is expected to have type
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Group.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))] {s : Set.{u2} α} {t : Set.{u2} α}, Eq.{succ u1} (Subgroup.{u1} M _inst_1) (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2 (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) (HasInf.inf.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.instHasInfSubgroup.{u1} M _inst_1) (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2 s) (fixingSubgroup.{u1, u2} M α _inst_1 _inst_2 t))
Case conversion may be inaccurate. Consider using '#align fixing_subgroup_union fixingSubgroup_unionₓ'. -/
/-- Fixing subgroup of union is intersection -/
theorem fixingSubgroup_union {s t : Set α} :
    fixingSubgroup M (s ∪ t) = fixingSubgroup M s ⊓ fixingSubgroup M t :=
  (fixingSubgroup_fixedPoints_gc M α).l_sup
#align fixing_subgroup_union fixingSubgroup_union

#print fixingSubgroup_unionᵢ /-
/-- Fixing subgroup of Union is intersection -/
theorem fixingSubgroup_unionᵢ {ι : Sort _} {s : ι → Set α} :
    fixingSubgroup M (⋃ i, s i) = ⨅ i, fixingSubgroup M (s i) :=
  (fixingSubgroup_fixedPoints_gc M α).l_supᵢ
#align fixing_subgroup_Union fixingSubgroup_unionᵢ
-/

/- warning: fixed_points_subgroup_sup -> fixedPoints_subgroup_sup is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Group.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))] {P : Subgroup.{u1} M _inst_1} {Q : Subgroup.{u1} M _inst_1}, Eq.{succ u2} (Set.{u2} α) (MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) (HasSup.sup.{u1} (Subgroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1)))) P Q)) α (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) (HasSup.sup.{u1} (Subgroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1)))) P Q)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) (HasSup.sup.{u1} (Subgroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1)))) P Q)) (Subgroup.toGroup.{u1} M _inst_1 (HasSup.sup.{u1} (Subgroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1)))) P Q)))) (Subgroup.mulAction.{u1, u2} M _inst_1 α _inst_2 (HasSup.sup.{u1} (Subgroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1)))) P Q))) (Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) P) α (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) P) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) P) (Subgroup.toGroup.{u1} M _inst_1 P))) (Subgroup.mulAction.{u1, u2} M _inst_1 α _inst_2 P)) (MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) Q) α (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) Q) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) Q) (Subgroup.toGroup.{u1} M _inst_1 Q))) (Subgroup.mulAction.{u1, u2} M _inst_1 α _inst_2 Q)))
but is expected to have type
  forall (M : Type.{u2}) (α : Type.{u1}) [_inst_1 : Group.{u2} M] [_inst_2 : MulAction.{u2, u1} M α (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_1))] {P : Subgroup.{u2} M _inst_1} {Q : Subgroup.{u2} M _inst_1}, Eq.{succ u1} (Set.{u1} α) (MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subgroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} M _inst_1) M (Subgroup.instSetLikeSubgroup.{u2} M _inst_1)) x (HasSup.sup.{u2} (Subgroup.{u2} M _inst_1) (SemilatticeSup.toHasSup.{u2} (Subgroup.{u2} M _inst_1) (Lattice.toSemilatticeSup.{u2} (Subgroup.{u2} M _inst_1) (CompleteLattice.toLattice.{u2} (Subgroup.{u2} M _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u2} M _inst_1)))) P Q))) α (Submonoid.toMonoid.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_1)) (Subgroup.toSubmonoid.{u2} M _inst_1 (HasSup.sup.{u2} (Subgroup.{u2} M _inst_1) (SemilatticeSup.toHasSup.{u2} (Subgroup.{u2} M _inst_1) (Lattice.toSemilatticeSup.{u2} (Subgroup.{u2} M _inst_1) (CompleteLattice.toLattice.{u2} (Subgroup.{u2} M _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u2} M _inst_1)))) P Q))) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u2, u1} M _inst_1 α _inst_2 (HasSup.sup.{u2} (Subgroup.{u2} M _inst_1) (SemilatticeSup.toHasSup.{u2} (Subgroup.{u2} M _inst_1) (Lattice.toSemilatticeSup.{u2} (Subgroup.{u2} M _inst_1) (CompleteLattice.toLattice.{u2} (Subgroup.{u2} M _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u2} M _inst_1)))) P Q))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subgroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} M _inst_1) M (Subgroup.instSetLikeSubgroup.{u2} M _inst_1)) x P)) α (Submonoid.toMonoid.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_1)) (Subgroup.toSubmonoid.{u2} M _inst_1 P)) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u2, u1} M _inst_1 α _inst_2 P)) (MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subgroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} M _inst_1) M (Subgroup.instSetLikeSubgroup.{u2} M _inst_1)) x Q)) α (Submonoid.toMonoid.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_1)) (Subgroup.toSubmonoid.{u2} M _inst_1 Q)) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u2, u1} M _inst_1 α _inst_2 Q)))
Case conversion may be inaccurate. Consider using '#align fixed_points_subgroup_sup fixedPoints_subgroup_supₓ'. -/
/-- Fixed points of sup of subgroups is intersection -/
theorem fixedPoints_subgroup_sup {P Q : Subgroup M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubgroup_fixedPoints_gc M α).u_inf
#align fixed_points_subgroup_sup fixedPoints_subgroup_sup

/- warning: fixed_points_subgroup_supr -> fixedPoints_subgroup_supᵢ is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (α : Type.{u2}) [_inst_1 : Group.{u1} M] [_inst_2 : MulAction.{u1, u2} M α (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))] {ι : Sort.{u3}} {P : ι -> (Subgroup.{u1} M _inst_1)}, Eq.{succ u2} (Set.{u2} α) (MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) (supᵢ.{u1, u3} (Subgroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1))) ι P)) α (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) (supᵢ.{u1, u3} (Subgroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1))) ι P)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) (supᵢ.{u1, u3} (Subgroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1))) ι P)) (Subgroup.toGroup.{u1} M _inst_1 (supᵢ.{u1, u3} (Subgroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1))) ι P)))) (Subgroup.mulAction.{u1, u2} M _inst_1 α _inst_2 (supᵢ.{u1, u3} (Subgroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subgroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subgroup.{u1} M _inst_1) (Subgroup.completeLattice.{u1} M _inst_1))) ι P))) (Set.interᵢ.{u2, u3} α ι (fun (i : ι) => MulAction.fixedPoints.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) (P i)) α (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) (P i)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} M _inst_1) M (Subgroup.setLike.{u1} M _inst_1)) (P i)) (Subgroup.toGroup.{u1} M _inst_1 (P i)))) (Subgroup.mulAction.{u1, u2} M _inst_1 α _inst_2 (P i))))
but is expected to have type
  forall (M : Type.{u2}) (α : Type.{u1}) [_inst_1 : Group.{u2} M] [_inst_2 : MulAction.{u2, u1} M α (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_1))] {ι : Sort.{u3}} {P : ι -> (Subgroup.{u2} M _inst_1)}, Eq.{succ u1} (Set.{u1} α) (MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subgroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} M _inst_1) M (Subgroup.instSetLikeSubgroup.{u2} M _inst_1)) x (supᵢ.{u2, u3} (Subgroup.{u2} M _inst_1) (CompleteLattice.toSupSet.{u2} (Subgroup.{u2} M _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u2} M _inst_1)) ι P))) α (Submonoid.toMonoid.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_1)) (Subgroup.toSubmonoid.{u2} M _inst_1 (supᵢ.{u2, u3} (Subgroup.{u2} M _inst_1) (CompleteLattice.toSupSet.{u2} (Subgroup.{u2} M _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u2} M _inst_1)) ι P))) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u2, u1} M _inst_1 α _inst_2 (supᵢ.{u2, u3} (Subgroup.{u2} M _inst_1) (CompleteLattice.toSupSet.{u2} (Subgroup.{u2} M _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u2} M _inst_1)) ι P))) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => MulAction.fixedPoints.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subgroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} M _inst_1) M (Subgroup.instSetLikeSubgroup.{u2} M _inst_1)) x (P i))) α (Submonoid.toMonoid.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_1)) (Subgroup.toSubmonoid.{u2} M _inst_1 (P i))) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u2, u1} M _inst_1 α _inst_2 (P i))))
Case conversion may be inaccurate. Consider using '#align fixed_points_subgroup_supr fixedPoints_subgroup_supᵢₓ'. -/
/-- Fixed points of supr of subgroups is intersection -/
theorem fixedPoints_subgroup_supᵢ {ι : Sort _} {P : ι → Subgroup M} :
    fixedPoints (↥(supᵢ P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubgroup_fixedPoints_gc M α).u_infᵢ
#align fixed_points_subgroup_supr fixedPoints_subgroup_supᵢ

end Group

