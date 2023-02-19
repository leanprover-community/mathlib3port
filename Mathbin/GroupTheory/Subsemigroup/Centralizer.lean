/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux

! This file was ported from Lean 3 source module group_theory.subsemigroup.centralizer
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subsemigroup.Center
import Mathbin.Algebra.GroupWithZero.Units.Lemmas

/-!
# Centralizers of magmas and semigroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `set.centralizer`: the centralizer of a subset of a magma
* `subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `set.add_centralizer`: the centralizer of a subset of an additive magma
* `add_subsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `monoid.centralizer`, `add_monoid.centralizer`, `subgroup.centralizer`, and
`add_subgroup.centralizer` in other files.
-/


variable {M : Type _} {S T : Set M}

namespace Set

variable (S)

#print Set.centralizer /-
/-- The centralizer of a subset of a magma. -/
@[to_additive add_centralizer " The centralizer of a subset of an additive magma. "]
def centralizer [Mul M] : Set M :=
  { c | ∀ m ∈ S, m * c = c * m }
#align set.centralizer Set.centralizer
#align set.add_centralizer Set.addCentralizer
-/

variable {S}

#print Set.mem_centralizer_iff /-
@[to_additive mem_add_centralizer]
theorem mem_centralizer_iff [Mul M] {c : M} : c ∈ centralizer S ↔ ∀ m ∈ S, m * c = c * m :=
  Iff.rfl
#align set.mem_centralizer_iff Set.mem_centralizer_iff
#align set.mem_add_centralizer Set.mem_add_centralizer
-/

#print Set.decidableMemCentralizer /-
@[to_additive decidable_mem_add_centralizer]
instance decidableMemCentralizer [Mul M] [∀ a : M, Decidable <| ∀ b ∈ S, b * a = a * b] :
    DecidablePred (· ∈ centralizer S) := fun _ => decidable_of_iff' _ mem_centralizer_iff
#align set.decidable_mem_centralizer Set.decidableMemCentralizer
#align set.decidable_mem_add_centralizer Set.decidableMemAddCentralizer
-/

variable (S)

/- warning: set.one_mem_centralizer -> Set.one_mem_centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : MulOneClass.{u1} M], Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) (Set.centralizer.{u1} M S (MulOneClass.toHasMul.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : MulOneClass.{u1} M], Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) (Set.centralizer.{u1} M S (MulOneClass.toMul.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align set.one_mem_centralizer Set.one_mem_centralizerₓ'. -/
@[simp, to_additive zero_mem_add_centralizer]
theorem one_mem_centralizer [MulOneClass M] : (1 : M) ∈ centralizer S := by
  simp [mem_centralizer_iff]
#align set.one_mem_centralizer Set.one_mem_centralizer
#align set.zero_mem_add_centralizer Set.zero_mem_add_centralizer

/- warning: set.zero_mem_centralizer -> Set.zero_mem_centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : MulZeroClass.{u1} M], Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (MulZeroClass.toHasZero.{u1} M _inst_1)))) (Set.centralizer.{u1} M S (MulZeroClass.toHasMul.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : MulZeroClass.{u1} M], Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (MulZeroClass.toZero.{u1} M _inst_1))) (Set.centralizer.{u1} M S (MulZeroClass.toMul.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align set.zero_mem_centralizer Set.zero_mem_centralizerₓ'. -/
@[simp]
theorem zero_mem_centralizer [MulZeroClass M] : (0 : M) ∈ centralizer S := by
  simp [mem_centralizer_iff]
#align set.zero_mem_centralizer Set.zero_mem_centralizer

variable {S} {a b : M}

/- warning: set.mul_mem_centralizer -> Set.mul_mem_centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} {b : M} [_inst_1 : Semigroup.{u1} M], (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.centralizer.{u1} M S (Semigroup.toHasMul.{u1} M _inst_1))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b (Set.centralizer.{u1} M S (Semigroup.toHasMul.{u1} M _inst_1))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) a b) (Set.centralizer.{u1} M S (Semigroup.toHasMul.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} {b : M} [_inst_1 : Semigroup.{u1} M], (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.centralizer.{u1} M S (Semigroup.toMul.{u1} M _inst_1))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b (Set.centralizer.{u1} M S (Semigroup.toMul.{u1} M _inst_1))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) a b) (Set.centralizer.{u1} M S (Semigroup.toMul.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.mul_mem_centralizer Set.mul_mem_centralizerₓ'. -/
@[simp, to_additive add_mem_add_centralizer]
theorem mul_mem_centralizer [Semigroup M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a * b ∈ centralizer S := fun g hg => by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]
#align set.mul_mem_centralizer Set.mul_mem_centralizer
#align set.add_mem_add_centralizer Set.add_mem_add_centralizer

/- warning: set.inv_mem_centralizer -> Set.inv_mem_centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} [_inst_1 : Group.{u1} M], (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.centralizer.{u1} M S (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (Inv.inv.{u1} M (DivInvMonoid.toHasInv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)) a) (Set.centralizer.{u1} M S (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} [_inst_1 : Group.{u1} M], (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.centralizer.{u1} M S (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (Inv.inv.{u1} M (InvOneClass.toInv.{u1} M (DivInvOneMonoid.toInvOneClass.{u1} M (DivisionMonoid.toDivInvOneMonoid.{u1} M (Group.toDivisionMonoid.{u1} M _inst_1)))) a) (Set.centralizer.{u1} M S (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.inv_mem_centralizer Set.inv_mem_centralizerₓ'. -/
@[simp, to_additive neg_mem_add_centralizer]
theorem inv_mem_centralizer [Group M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S := fun g hg =>
  by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]
#align set.inv_mem_centralizer Set.inv_mem_centralizer
#align set.neg_mem_add_centralizer Set.neg_mem_add_centralizer

/- warning: set.add_mem_centralizer -> Set.add_mem_centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} {b : M} [_inst_1 : Distrib.{u1} M], (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.centralizer.{u1} M S (Distrib.toHasMul.{u1} M _inst_1))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b (Set.centralizer.{u1} M S (Distrib.toHasMul.{u1} M _inst_1))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (Distrib.toHasAdd.{u1} M _inst_1)) a b) (Set.centralizer.{u1} M S (Distrib.toHasMul.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} {b : M} [_inst_1 : Distrib.{u1} M], (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.centralizer.{u1} M S (Distrib.toMul.{u1} M _inst_1))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b (Set.centralizer.{u1} M S (Distrib.toMul.{u1} M _inst_1))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (Distrib.toAdd.{u1} M _inst_1)) a b) (Set.centralizer.{u1} M S (Distrib.toMul.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.add_mem_centralizer Set.add_mem_centralizerₓ'. -/
@[simp]
theorem add_mem_centralizer [Distrib M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a + b ∈ centralizer S := fun c hc => by rw [add_mul, mul_add, ha c hc, hb c hc]
#align set.add_mem_centralizer Set.add_mem_centralizer

/- warning: set.neg_mem_centralizer -> Set.neg_mem_centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} [_inst_1 : Mul.{u1} M] [_inst_2 : HasDistribNeg.{u1} M _inst_1], (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.centralizer.{u1} M S _inst_1)) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (Neg.neg.{u1} M (InvolutiveNeg.toHasNeg.{u1} M (HasDistribNeg.toHasInvolutiveNeg.{u1} M _inst_1 _inst_2)) a) (Set.centralizer.{u1} M S _inst_1))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} [_inst_1 : Mul.{u1} M] [_inst_2 : HasDistribNeg.{u1} M _inst_1], (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.centralizer.{u1} M S _inst_1)) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (Neg.neg.{u1} M (InvolutiveNeg.toNeg.{u1} M (HasDistribNeg.toInvolutiveNeg.{u1} M _inst_1 _inst_2)) a) (Set.centralizer.{u1} M S _inst_1))
Case conversion may be inaccurate. Consider using '#align set.neg_mem_centralizer Set.neg_mem_centralizerₓ'. -/
@[simp]
theorem neg_mem_centralizer [Mul M] [HasDistribNeg M] (ha : a ∈ centralizer S) :
    -a ∈ centralizer S := fun c hc => by rw [mul_neg, ha c hc, neg_mul]
#align set.neg_mem_centralizer Set.neg_mem_centralizer

/- warning: set.inv_mem_centralizer₀ -> Set.inv_mem_centralizer₀ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} [_inst_1 : GroupWithZero.{u1} M], (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.centralizer.{u1} M S (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (Inv.inv.{u1} M (DivInvMonoid.toHasInv.{u1} M (GroupWithZero.toDivInvMonoid.{u1} M _inst_1)) a) (Set.centralizer.{u1} M S (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} [_inst_1 : GroupWithZero.{u1} M], (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.centralizer.{u1} M S (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (Inv.inv.{u1} M (GroupWithZero.toInv.{u1} M _inst_1) a) (Set.centralizer.{u1} M S (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.inv_mem_centralizer₀ Set.inv_mem_centralizer₀ₓ'. -/
@[simp]
theorem inv_mem_centralizer₀ [GroupWithZero M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
  (eq_or_ne a 0).elim
    (fun h => by
      rw [h, inv_zero]
      exact zero_mem_centralizer S)
    fun ha0 c hc => by
    rw [mul_inv_eq_iff_eq_mul₀ ha0, mul_assoc, eq_inv_mul_iff_mul_eq₀ ha0, ha c hc]
#align set.inv_mem_centralizer₀ Set.inv_mem_centralizer₀

/- warning: set.div_mem_centralizer -> Set.div_mem_centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} {b : M} [_inst_1 : Group.{u1} M], (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.centralizer.{u1} M S (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b (Set.centralizer.{u1} M S (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) a b) (Set.centralizer.{u1} M S (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} {b : M} [_inst_1 : Group.{u1} M], (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.centralizer.{u1} M S (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b (Set.centralizer.{u1} M S (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) a b) (Set.centralizer.{u1} M S (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.div_mem_centralizer Set.div_mem_centralizerₓ'. -/
@[simp, to_additive sub_mem_add_centralizer]
theorem div_mem_centralizer [Group M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer hb)
#align set.div_mem_centralizer Set.div_mem_centralizer
#align set.sub_mem_add_centralizer Set.sub_mem_add_centralizer

/- warning: set.div_mem_centralizer₀ -> Set.div_mem_centralizer₀ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} {b : M} [_inst_1 : GroupWithZero.{u1} M], (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.centralizer.{u1} M S (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b (Set.centralizer.{u1} M S (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (GroupWithZero.toDivInvMonoid.{u1} M _inst_1))) a b) (Set.centralizer.{u1} M S (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} {a : M} {b : M} [_inst_1 : GroupWithZero.{u1} M], (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.centralizer.{u1} M S (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b (Set.centralizer.{u1} M S (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (GroupWithZero.toDiv.{u1} M _inst_1)) a b) (Set.centralizer.{u1} M S (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.div_mem_centralizer₀ Set.div_mem_centralizer₀ₓ'. -/
@[simp]
theorem div_mem_centralizer₀ [GroupWithZero M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer₀ hb)
#align set.div_mem_centralizer₀ Set.div_mem_centralizer₀

#print Set.centralizer_subset /-
@[to_additive add_centralizer_subset]
theorem centralizer_subset [Mul M] (h : S ⊆ T) : centralizer T ⊆ centralizer S := fun t ht s hs =>
  ht s (h hs)
#align set.centralizer_subset Set.centralizer_subset
#align set.add_centralizer_subset Set.add_centralizer_subset
-/

variable (M)

#print Set.centralizer_univ /-
@[simp, to_additive add_centralizer_univ]
theorem centralizer_univ [Mul M] : centralizer univ = center M :=
  Subset.antisymm (fun a ha b => ha b (Set.mem_univ b)) fun a ha b hb => ha b
#align set.centralizer_univ Set.centralizer_univ
#align set.add_centralizer_univ Set.add_centralizer_univ
-/

variable {M} (S)

/- warning: set.centralizer_eq_univ -> Set.centralizer_eq_univ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : CommSemigroup.{u1} M], Eq.{succ u1} (Set.{u1} M) (Set.centralizer.{u1} M S (Semigroup.toHasMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))) (Set.univ.{u1} M)
but is expected to have type
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : CommSemigroup.{u1} M], Eq.{succ u1} (Set.{u1} M) (Set.centralizer.{u1} M S (Semigroup.toMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))) (Set.univ.{u1} M)
Case conversion may be inaccurate. Consider using '#align set.centralizer_eq_univ Set.centralizer_eq_univₓ'. -/
@[simp, to_additive add_centralizer_eq_univ]
theorem centralizer_eq_univ [CommSemigroup M] : centralizer S = univ :=
  Subset.antisymm (subset_univ _) fun x hx y hy => mul_comm y x
#align set.centralizer_eq_univ Set.centralizer_eq_univ
#align set.add_centralizer_eq_univ Set.add_centralizer_eq_univ

end Set

namespace Subsemigroup

section

variable {M} [Semigroup M] (S)

/- warning: subsemigroup.centralizer -> Subsemigroup.centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}}, (Set.{u1} M) -> (forall [_inst_1 : Semigroup.{u1} M], Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}}, (Set.{u1} M) -> (forall [_inst_1 : Semigroup.{u1} M], Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align subsemigroup.centralizer Subsemigroup.centralizerₓ'. -/
/-- The centralizer of a subset of a semigroup `M`. -/
@[to_additive "The centralizer of a subset of an additive semigroup."]
def centralizer : Subsemigroup M where
  carrier := S.centralizer
  mul_mem' a b := Set.mul_mem_centralizer
#align subsemigroup.centralizer Subsemigroup.centralizer
#align add_subsemigroup.centralizer AddSubsemigroup.centralizer

/- warning: subsemigroup.coe_centralizer -> Subsemigroup.coe_centralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : Semigroup.{u1} M], Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) M (Subsemigroup.setLike.{u1} M (Semigroup.toHasMul.{u1} M _inst_1))))) (Subsemigroup.centralizer.{u1} M S _inst_1)) (Set.centralizer.{u1} M S (Semigroup.toHasMul.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} (S : Set.{u1} M) [_inst_1 : Semigroup.{u1} M], Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (Subsemigroup.centralizer.{u1} M S _inst_1)) (Set.centralizer.{u1} M S (Semigroup.toMul.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align subsemigroup.coe_centralizer Subsemigroup.coe_centralizerₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl
#align subsemigroup.coe_centralizer Subsemigroup.coe_centralizer
#align add_subsemigroup.coe_centralizer AddSubsemigroup.coe_centralizer

variable {S}

/- warning: subsemigroup.mem_centralizer_iff -> Subsemigroup.mem_centralizer_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} [_inst_1 : Semigroup.{u1} M] {z : M}, Iff (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) M (Subsemigroup.setLike.{u1} M (Semigroup.toHasMul.{u1} M _inst_1))) z (Subsemigroup.centralizer.{u1} M S _inst_1)) (forall (g : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) g S) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) g z) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) z g)))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} [_inst_1 : Semigroup.{u1} M] {z : M}, Iff (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1))) z (Subsemigroup.centralizer.{u1} M S _inst_1)) (forall (g : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) g S) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) g z) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) z g)))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_centralizer_iff Subsemigroup.mem_centralizer_iffₓ'. -/
@[to_additive]
theorem mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
  Iff.rfl
#align subsemigroup.mem_centralizer_iff Subsemigroup.mem_centralizer_iff
#align add_subsemigroup.mem_centralizer_iff AddSubsemigroup.mem_centralizer_iff

/- warning: subsemigroup.decidable_mem_centralizer -> Subsemigroup.decidableMemCentralizer is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} [_inst_1 : Semigroup.{u1} M] (a : M) [_inst_2 : Decidable (forall (b : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b S) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) b a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) a b)))], Decidable (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) M (Subsemigroup.setLike.{u1} M (Semigroup.toHasMul.{u1} M _inst_1))) a (Subsemigroup.centralizer.{u1} M S _inst_1))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} [_inst_1 : Semigroup.{u1} M] (a : M) [_inst_2 : Decidable (forall (b : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b S) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) b a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) a b)))], Decidable (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1))) a (Subsemigroup.centralizer.{u1} M S _inst_1))
Case conversion may be inaccurate. Consider using '#align subsemigroup.decidable_mem_centralizer Subsemigroup.decidableMemCentralizerₓ'. -/
@[to_additive]
instance decidableMemCentralizer (a) [Decidable <| ∀ b ∈ S, b * a = a * b] :
    Decidable (a ∈ centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff
#align subsemigroup.decidable_mem_centralizer Subsemigroup.decidableMemCentralizer
#align add_subsemigroup.decidable_mem_centralizer AddSubsemigroup.decidableMemCentralizer

/- warning: subsemigroup.centralizer_le -> Subsemigroup.centralizer_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {S : Set.{u1} M} {T : Set.{u1} M} [_inst_1 : Semigroup.{u1} M], (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) S T) -> (LE.le.{u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) M (Subsemigroup.setLike.{u1} M (Semigroup.toHasMul.{u1} M _inst_1))))) (Subsemigroup.centralizer.{u1} M T _inst_1) (Subsemigroup.centralizer.{u1} M S _inst_1))
but is expected to have type
  forall {M : Type.{u1}} {S : Set.{u1} M} {T : Set.{u1} M} [_inst_1 : Semigroup.{u1} M], (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) S T) -> (LE.le.{u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)))))) (Subsemigroup.centralizer.{u1} M T _inst_1) (Subsemigroup.centralizer.{u1} M S _inst_1))
Case conversion may be inaccurate. Consider using '#align subsemigroup.centralizer_le Subsemigroup.centralizer_leₓ'. -/
@[to_additive]
theorem centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
  Set.centralizer_subset h
#align subsemigroup.centralizer_le Subsemigroup.centralizer_le
#align add_subsemigroup.centralizer_le AddSubsemigroup.centralizer_le

variable (M)

/- warning: subsemigroup.centralizer_univ -> Subsemigroup.centralizer_univ is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : Semigroup.{u1} M], Eq.{succ u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (Subsemigroup.centralizer.{u1} M (Set.univ.{u1} M) _inst_1) (Subsemigroup.center.{u1} M _inst_1)
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Semigroup.{u1} M], Eq.{succ u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (Subsemigroup.centralizer.{u1} M (Set.univ.{u1} M) _inst_1) (Subsemigroup.center.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align subsemigroup.centralizer_univ Subsemigroup.centralizer_univₓ'. -/
@[simp, to_additive]
theorem centralizer_univ : centralizer Set.univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)
#align subsemigroup.centralizer_univ Subsemigroup.centralizer_univ
#align add_subsemigroup.centralizer_univ AddSubsemigroup.centralizer_univ

end

end Subsemigroup

-- Guard against import creep
assert_not_exists Finset

