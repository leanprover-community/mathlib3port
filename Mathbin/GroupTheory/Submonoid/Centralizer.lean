/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module group_theory.submonoid.centralizer
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subsemigroup.Centralizer
import Mathbin.GroupTheory.Submonoid.Center

/-!
# Centralizers of magmas and monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `submonoid.centralizer`: the centralizer of a subset of a monoid
* `add_submonoid.centralizer`: the centralizer of a subset of an additive monoid

We provide `subgroup.centralizer`, `add_subgroup.centralizer` in other files.
-/


variable {M : Type _} {S T : Set M}

namespace Submonoid

section

variable [Monoid M] (S)

#print Submonoid.centralizer /-
/-- The centralizer of a subset of a monoid `M`. -/
@[to_additive "The centralizer of a subset of an additive monoid."]
def centralizer : Submonoid M where
  carrier := S.centralizer
  one_mem' := S.one_mem_centralizer
  mul_mem' a b := Set.mul_mem_centralizer
#align submonoid.centralizer Submonoid.centralizer
#align add_submonoid.centralizer AddSubmonoid.centralizer
-/

/- warning: submonoid.coe_centralizer -> Submonoid.coe_centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (Submonoid.centralizer.{u1} M S _inst_1)) (Set.centralizer.{u1} M S (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.centralizer.{u1} M S _inst_1)) (Set.centralizer.{u1} M S (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_centralizer Submonoid.coe_centralizerₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl
#align submonoid.coe_centralizer Submonoid.coe_centralizer
#align add_submonoid.coe_centralizer AddSubmonoid.coe_centralizer

/- warning: submonoid.centralizer_to_subsemigroup -> Submonoid.centralizer_toSubsemigroup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Subsemigroup.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.toSubsemigroup.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Submonoid.centralizer.{u1} M S _inst_1)) (Subsemigroup.centralizer.{u1} M S (Monoid.toSemigroup.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Subsemigroup.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.toSubsemigroup.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Submonoid.centralizer.{u1} M S _inst_1)) (Subsemigroup.centralizer.{u1} M S (Monoid.toSemigroup.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.centralizer_to_subsemigroup Submonoid.centralizer_toSubsemigroupₓ'. -/
theorem centralizer_toSubsemigroup : (centralizer S).toSubsemigroup = Subsemigroup.centralizer S :=
  rfl
#align submonoid.centralizer_to_subsemigroup Submonoid.centralizer_toSubsemigroup

/- warning: add_submonoid.centralizer_to_add_subsemigroup -> AddSubmonoid.centralizer_toAddSubsemigroup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : AddMonoid.{u1} M] (S : Set.{u1} M), Eq.{succ u1} (AddSubsemigroup.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_2))) (AddSubmonoid.toAddSubsemigroup.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_2) (AddSubmonoid.centralizer.{u1} M S _inst_2)) (AddSubsemigroup.centralizer.{u1} M S (AddMonoid.toAddSemigroup.{u1} M _inst_2))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : AddMonoid.{u1} M] (S : Set.{u1} M), Eq.{succ u1} (AddSubsemigroup.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_2))) (AddSubmonoid.toAddSubsemigroup.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_2) (AddSubmonoid.centralizer.{u1} M S _inst_2)) (AddSubsemigroup.centralizer.{u1} M S (AddMonoid.toAddSemigroup.{u1} M _inst_2))
Case conversion may be inaccurate. Consider using '#align add_submonoid.centralizer_to_add_subsemigroup AddSubmonoid.centralizer_toAddSubsemigroupₓ'. -/
theorem AddSubmonoid.centralizer_toAddSubsemigroup {M} [AddMonoid M] (S : Set M) :
    (AddSubmonoid.centralizer S).toAddSubsemigroup = AddSubsemigroup.centralizer S :=
  rfl
#align add_submonoid.centralizer_to_add_subsemigroup AddSubmonoid.centralizer_toAddSubsemigroup

attribute [to_additive AddSubmonoid.centralizer_toAddSubsemigroup]
  Submonoid.centralizer_toSubsemigroup

variable {S}

/- warning: submonoid.mem_centralizer_iff -> Submonoid.mem_centralizer_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} [_inst_1 : Monoid.{u1} M] {z : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) z (Submonoid.centralizer.{u1} M S _inst_1)) (forall (g : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) g S) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) g z) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) z g)))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} [_inst_1 : Monoid.{u1} M] {z : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) z (Submonoid.centralizer.{u1} M S _inst_1)) (forall (g : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) g S) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) g z) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) z g)))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_centralizer_iff Submonoid.mem_centralizer_iffₓ'. -/
@[to_additive]
theorem mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
  Iff.rfl
#align submonoid.mem_centralizer_iff Submonoid.mem_centralizer_iff
#align add_submonoid.mem_centralizer_iff AddSubmonoid.mem_centralizer_iff

/- warning: submonoid.decidable_mem_centralizer -> Submonoid.decidableMemCentralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} [_inst_1 : Monoid.{u1} M] (a : M) [_inst_2 : Decidable (forall (b : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b S) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) b a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b)))], Decidable (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a (Submonoid.centralizer.{u1} M S _inst_1))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} [_inst_1 : Monoid.{u1} M] (a : M) [_inst_2 : Decidable (forall (b : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b S) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) b a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b)))], Decidable (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a (Submonoid.centralizer.{u1} M S _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.decidable_mem_centralizer Submonoid.decidableMemCentralizerₓ'. -/
@[to_additive]
instance decidableMemCentralizer (a) [Decidable <| ∀ b ∈ S, b * a = a * b] :
    Decidable (a ∈ centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff
#align submonoid.decidable_mem_centralizer Submonoid.decidableMemCentralizer
#align add_submonoid.decidable_mem_centralizer AddSubmonoid.decidableMemCentralizer

/- warning: submonoid.centralizer_le -> Submonoid.centralizer_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} {T : Set.{u1} M} [_inst_1 : Monoid.{u1} M], (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) S T) -> (LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (Submonoid.centralizer.{u1} M T _inst_1) (Submonoid.centralizer.{u1} M S _inst_1))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} {T : Set.{u1} M} [_inst_1 : Monoid.{u1} M], (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) S T) -> (LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (Submonoid.centralizer.{u1} M T _inst_1) (Submonoid.centralizer.{u1} M S _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.centralizer_le Submonoid.centralizer_leₓ'. -/
@[to_additive]
theorem centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
  Set.centralizer_subset h
#align submonoid.centralizer_le Submonoid.centralizer_le
#align add_submonoid.centralizer_le AddSubmonoid.centralizer_le

variable (M)

#print Submonoid.centralizer_univ /-
@[simp, to_additive]
theorem centralizer_univ : centralizer Set.univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)
#align submonoid.centralizer_univ Submonoid.centralizer_univ
#align add_submonoid.centralizer_univ AddSubmonoid.centralizer_univ
-/

end

end Submonoid

-- Guard against import creep
assert_not_exists Finset

