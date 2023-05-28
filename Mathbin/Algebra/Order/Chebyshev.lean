/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.chebyshev
! leanprover-community/mathlib commit 814d76e2247d5ba8bc024843552da1278bfe9e5c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Algebra.Order.Rearrangement
import Mathbin.GroupTheory.Perm.Cycle.Basic

/-!
# Chebyshev's sum inequality

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the Chebyshev sum inequality.

Chebyshev's inequality states `(∑ i in s, f i) * (∑ i in s, g i) ≤ s.card * ∑ i in s, f i * g i`
when `f g : ι → α` monovary, and the reverse inequality when `f` and `g` antivary.


## Main declarations

* `monovary_on.sum_mul_sum_le_card_mul_sum`: Chebyshev's inequality.
* `antivary_on.card_mul_sum_le_sum_mul_sum`: Chebyshev's inequality, dual version.
* `sq_sum_le_card_mul_sum_sq`: Special case of Chebyshev's inequality when `f = g`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `monotone`/`antitone` pairs of functions over a `linear_order` is not deduced in this
file because it is easily deducible from the `monovary` API.
-/


open Equiv Equiv.Perm Finset Function OrderDual

open BigOperators

variable {ι α β : Type _}

/-! ### Scalar multiplication versions -/


section Smul

variable [LinearOrderedRing α] [LinearOrderedAddCommGroup β] [Module α β] [OrderedSMul α β]
  {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

/- warning: monovary_on.sum_smul_sum_le_card_smul_sum -> MonovaryOn.sum_smul_sum_le_card_smul_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align monovary_on.sum_smul_sum_le_card_smul_sum MonovaryOn.sum_smul_sum_le_card_smul_sumₓ'. -/
/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem MonovaryOn.sum_smul_sum_le_card_smul_sum (hfg : MonovaryOn f g s) :
    ((∑ i in s, f i) • ∑ i in s, g i) ≤ s.card • ∑ i in s, f i • g i := by
  classical
    obtain ⟨σ, hσ, hs⟩ := s.countable_to_set.exists_cycle_on
    rw [← card_range s.card, sum_smul_sum_eq_sum_perm hσ]
    exact
      sum_le_card_nsmul _ _ _ fun n _ =>
        hfg.sum_smul_comp_perm_le_sum_smul fun x hx => hs fun h => hx <| is_fixed_pt.perm_pow h _
#align monovary_on.sum_smul_sum_le_card_smul_sum MonovaryOn.sum_smul_sum_le_card_smul_sum

/- warning: antivary_on.card_smul_sum_le_sum_smul_sum -> AntivaryOn.card_smul_sum_le_sum_smul_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align antivary_on.card_smul_sum_le_sum_smul_sum AntivaryOn.card_smul_sum_le_sum_smul_sumₓ'. -/
/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem AntivaryOn.card_smul_sum_le_sum_smul_sum (hfg : AntivaryOn f g s) :
    (s.card • ∑ i in s, f i • g i) ≤ (∑ i in s, f i) • ∑ i in s, g i := by
  convert hfg.dual_right.sum_smul_sum_le_card_smul_sum
#align antivary_on.card_smul_sum_le_sum_smul_sum AntivaryOn.card_smul_sum_le_sum_smul_sum

variable [Fintype ι]

/- warning: monovary.sum_smul_sum_le_card_smul_sum -> Monovary.sum_smul_sum_le_card_smul_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align monovary.sum_smul_sum_le_card_smul_sum Monovary.sum_smul_sum_le_card_smul_sumₓ'. -/
/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem Monovary.sum_smul_sum_le_card_smul_sum (hfg : Monovary f g) :
    ((∑ i, f i) • ∑ i, g i) ≤ Fintype.card ι • ∑ i, f i • g i :=
  (hfg.MonovaryOn _).sum_smul_sum_le_card_smul_sum
#align monovary.sum_smul_sum_le_card_smul_sum Monovary.sum_smul_sum_le_card_smul_sum

/- warning: antivary.card_smul_sum_le_sum_smul_sum -> Antivary.card_smul_sum_le_sum_smul_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align antivary.card_smul_sum_le_sum_smul_sum Antivary.card_smul_sum_le_sum_smul_sumₓ'. -/
/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem Antivary.card_smul_sum_le_sum_smul_sum (hfg : Antivary f g) :
    (Fintype.card ι • ∑ i, f i • g i) ≤ (∑ i, f i) • ∑ i, g i := by
  convert(hfg.dual_right.monovary_on _).sum_smul_sum_le_card_smul_sum
#align antivary.card_smul_sum_le_sum_smul_sum Antivary.card_smul_sum_le_sum_smul_sum

end Smul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/


section Mul

variable [LinearOrderedRing α] {s : Finset ι} {σ : Perm ι} {f g : ι → α}

/- warning: monovary_on.sum_mul_sum_le_card_mul_sum -> MonovaryOn.sum_mul_sum_le_card_mul_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedRing.{u2} α] {s : Finset.{u1} ι} {f : ι -> α} {g : ι -> α}, (MonovaryOn.{u1, u2, u2} ι α α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) f g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) s)) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) s (fun (i : ι) => f i)) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) s (fun (i : ι) => g i))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (AddCommGroupWithOne.toAddGroupWithOne.{u2} α (Ring.toAddCommGroupWithOne.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))))))) (Finset.card.{u1} ι s)) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) s (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (f i) (g i)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {s : Finset.{u2} ι} {f : ι -> α} {g : ι -> α}, (MonovaryOn.{u2, u1, u1} ι α α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) f g (Finset.toSet.{u2} ι s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) s (fun (i : ι) => f i)) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) s (fun (i : ι) => g i))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Finset.card.{u2} ι s)) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) s (fun (i : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (f i) (g i)))))
Case conversion may be inaccurate. Consider using '#align monovary_on.sum_mul_sum_le_card_mul_sum MonovaryOn.sum_mul_sum_le_card_mul_sumₓ'. -/
/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
theorem MonovaryOn.sum_mul_sum_le_card_mul_sum (hfg : MonovaryOn f g s) :
    ((∑ i in s, f i) * ∑ i in s, g i) ≤ s.card * ∑ i in s, f i * g i := by rw [← nsmul_eq_mul];
  exact hfg.sum_smul_sum_le_card_smul_sum
#align monovary_on.sum_mul_sum_le_card_mul_sum MonovaryOn.sum_mul_sum_le_card_mul_sum

/- warning: antivary_on.card_mul_sum_le_sum_mul_sum -> AntivaryOn.card_mul_sum_le_sum_mul_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedRing.{u2} α] {s : Finset.{u1} ι} {f : ι -> α} {g : ι -> α}, (AntivaryOn.{u1, u2, u2} ι α α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) f g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) s)) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (AddCommGroupWithOne.toAddGroupWithOne.{u2} α (Ring.toAddCommGroupWithOne.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))))))) (Finset.card.{u1} ι s)) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) s (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (f i) (g i)))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) s (fun (i : ι) => f i)) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) s (fun (i : ι) => g i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {s : Finset.{u2} ι} {f : ι -> α} {g : ι -> α}, (AntivaryOn.{u2, u1, u1} ι α α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) f g (Finset.toSet.{u2} ι s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Finset.card.{u2} ι s)) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) s (fun (i : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (f i) (g i)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) s (fun (i : ι) => f i)) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) s (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align antivary_on.card_mul_sum_le_sum_mul_sum AntivaryOn.card_mul_sum_le_sum_mul_sumₓ'. -/
/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the product of their sum is greater than the size of the set times their scalar
product. -/
theorem AntivaryOn.card_mul_sum_le_sum_mul_sum (hfg : AntivaryOn f g s) :
    ((s.card : α) * ∑ i in s, f i * g i) ≤ (∑ i in s, f i) * ∑ i in s, g i := by
  rw [← nsmul_eq_mul]; exact hfg.card_smul_sum_le_sum_smul_sum
#align antivary_on.card_mul_sum_le_sum_mul_sum AntivaryOn.card_mul_sum_le_sum_mul_sum

/- warning: sq_sum_le_card_mul_sum_sq -> sq_sum_le_card_mul_sum_sq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedRing.{u2} α] {s : Finset.{u1} ι} {f : ι -> α}, LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (Ring.toMonoid.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) s (fun (i : ι) => f i)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (AddCommGroupWithOne.toAddGroupWithOne.{u2} α (Ring.toAddCommGroupWithOne.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))))))) (Finset.card.{u1} ι s)) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) s (fun (i : ι) => HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (Ring.toMonoid.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (f i) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedRing.{u2} α] {s : Finset.{u1} ι} {f : ι -> α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedRing.toPartialOrder.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (MonoidWithZero.toMonoid.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedRing.toLinearOrderedSemiring.{u2} α _inst_1))))))) (Finset.sum.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedRing.toLinearOrderedSemiring.{u2} α _inst_1)))) s (fun (i : ι) => f i)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocRing.toMul.{u2} α (NonAssocRing.toNonUnitalNonAssocRing.{u2} α (Ring.toNonAssocRing.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))))) (Nat.cast.{u2} α (Semiring.toNatCast.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedRing.toLinearOrderedSemiring.{u2} α _inst_1)))) (Finset.card.{u1} ι s)) (Finset.sum.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedRing.toLinearOrderedSemiring.{u2} α _inst_1)))) s (fun (i : ι) => HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (MonoidWithZero.toMonoid.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedRing.toLinearOrderedSemiring.{u2} α _inst_1))))))) (f i) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align sq_sum_le_card_mul_sum_sq sq_sum_le_card_mul_sum_sqₓ'. -/
/-- Special case of **Chebyshev's Sum Inequality** or the **Cauchy-Schwarz Inequality**: The square
of the sum is less than the size of the set times the sum of the squares. -/
theorem sq_sum_le_card_mul_sum_sq : (∑ i in s, f i) ^ 2 ≤ s.card * ∑ i in s, f i ^ 2 := by
  simp_rw [sq]; exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum
#align sq_sum_le_card_mul_sum_sq sq_sum_le_card_mul_sum_sq

variable [Fintype ι]

/- warning: monovary.sum_mul_sum_le_card_mul_sum -> Monovary.sum_mul_sum_le_card_mul_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedRing.{u2} α] {f : ι -> α} {g : ι -> α} [_inst_2 : Fintype.{u1} ι], (Monovary.{u1, u2, u2} ι α α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) f g) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => f i)) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => g i))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (AddCommGroupWithOne.toAddGroupWithOne.{u2} α (Ring.toAddCommGroupWithOne.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))))))) (Fintype.card.{u1} ι _inst_2)) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (f i) (g i)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {f : ι -> α} {g : ι -> α} [_inst_2 : Fintype.{u2} ι], (Monovary.{u2, u1, u1} ι α α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) f g) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => f i)) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => g i))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Fintype.card.{u2} ι _inst_2)) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (f i) (g i)))))
Case conversion may be inaccurate. Consider using '#align monovary.sum_mul_sum_le_card_mul_sum Monovary.sum_mul_sum_le_card_mul_sumₓ'. -/
/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
theorem Monovary.sum_mul_sum_le_card_mul_sum (hfg : Monovary f g) :
    ((∑ i, f i) * ∑ i, g i) ≤ Fintype.card ι * ∑ i, f i * g i :=
  (hfg.MonovaryOn _).sum_mul_sum_le_card_mul_sum
#align monovary.sum_mul_sum_le_card_mul_sum Monovary.sum_mul_sum_le_card_mul_sum

/- warning: antivary.card_mul_sum_le_sum_mul_sum -> Antivary.card_mul_sum_le_sum_mul_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedRing.{u2} α] {f : ι -> α} {g : ι -> α} [_inst_2 : Fintype.{u1} ι], (Antivary.{u1, u2, u2} ι α α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) f g) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (AddCommGroupWithOne.toAddGroupWithOne.{u2} α (Ring.toAddCommGroupWithOne.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))))))) (Fintype.card.{u1} ι _inst_2)) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (f i) (g i)))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (Ring.toDistrib.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1))))) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => f i)) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α _inst_1)))) (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => g i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {f : ι -> α} {g : ι -> α} [_inst_2 : Fintype.{u2} ι], (Antivary.{u2, u1, u1} ι α α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) f g) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Fintype.card.{u2} ι _inst_2)) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (f i) (g i)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => f i)) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1)))) (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align antivary.card_mul_sum_le_sum_mul_sum Antivary.card_mul_sum_le_sum_mul_sumₓ'. -/
/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the product of their sum is less than the size of the set times their scalar
product. -/
theorem Antivary.card_mul_sum_le_sum_mul_sum (hfg : Antivary f g) :
    ((Fintype.card ι : α) * ∑ i, f i * g i) ≤ (∑ i, f i) * ∑ i, g i :=
  (hfg.AntivaryOn _).card_mul_sum_le_sum_mul_sum
#align antivary.card_mul_sum_le_sum_mul_sum Antivary.card_mul_sum_le_sum_mul_sum

end Mul

variable [LinearOrderedField α] {s : Finset ι} {f : ι → α}

/- warning: sum_div_card_sq_le_sum_sq_div_card -> sum_div_card_sq_le_sum_sq_div_card is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} α] {s : Finset.{u1} ι} {f : ι -> α}, LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1))))))) (HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (Ring.toMonoid.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1))))))) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (DivisionRing.toDivInvMonoid.{u2} α (Field.toDivisionRing.{u2} α (LinearOrderedField.toField.{u2} α _inst_1))))) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))) s (fun (i : ι) => f i)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (AddCommGroupWithOne.toAddGroupWithOne.{u2} α (Ring.toAddCommGroupWithOne.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1))))))))))) (Finset.card.{u1} ι s))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (DivisionRing.toDivInvMonoid.{u2} α (Field.toDivisionRing.{u2} α (LinearOrderedField.toField.{u2} α _inst_1))))) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (StrictOrderedRing.toOrderedAddCommGroup.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))) s (fun (i : ι) => HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (Ring.toMonoid.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1))))))) (f i) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (AddCommGroupWithOne.toAddGroupWithOne.{u2} α (Ring.toAddCommGroupWithOne.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1))))))))))) (Finset.card.{u1} ι s)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} α] {s : Finset.{u1} ι} {f : ι -> α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedRing.toPartialOrder.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))) (HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (MonoidWithZero.toMonoid.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1))))))))) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (LinearOrderedField.toDiv.{u2} α _inst_1)) (Finset.sum.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1)))))) s (fun (i : ι) => f i)) (Nat.cast.{u2} α (Semiring.toNatCast.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1)))))) (Finset.card.{u1} ι s))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (LinearOrderedField.toDiv.{u2} α _inst_1)) (Finset.sum.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1)))))) s (fun (i : ι) => HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (MonoidWithZero.toMonoid.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1))))))))) (f i) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Nat.cast.{u2} α (Semiring.toNatCast.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1)))))) (Finset.card.{u1} ι s)))
Case conversion may be inaccurate. Consider using '#align sum_div_card_sq_le_sum_sq_div_card sum_div_card_sq_le_sum_sq_div_cardₓ'. -/
theorem sum_div_card_sq_le_sum_sq_div_card :
    ((∑ i in s, f i) / s.card) ^ 2 ≤ (∑ i in s, f i ^ 2) / s.card :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← card_pos, ← @Nat.cast_pos α] at hs
  rw [div_pow, div_le_div_iff (sq_pos_of_ne_zero _ hs.ne') hs, sq (s.card : α), mul_left_comm, ←
    mul_assoc]
  exact mul_le_mul_of_nonneg_right sq_sum_le_card_mul_sum_sq hs.le
#align sum_div_card_sq_le_sum_sq_div_card sum_div_card_sq_le_sum_sq_div_card

