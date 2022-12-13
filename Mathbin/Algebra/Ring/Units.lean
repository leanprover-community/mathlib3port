/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathbin.Algebra.Ring.InjSurj
import Mathbin.Algebra.Group.Units

/-!
# Units in semirings and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/746
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

namespace Units

section HasDistribNeg

variable [Monoid α] [HasDistribNeg α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : Neg αˣ :=
  ⟨fun u => ⟨-↑u, -↑u⁻¹, by simp, by simp⟩⟩

/- warning: units.coe_neg -> Units.val_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] (u : Units.{u1} α _inst_1), Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.val.{u1} α _inst_1)))) (Neg.neg.{u1} (Units.{u1} α _inst_1) (Units.hasNeg.{u1} α _inst_1 _inst_2) u)) (Neg.neg.{u1} α (HasInvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.val.{u1} α _inst_1)))) u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] (u : Units.{u1} α _inst_1), Eq.{succ u1} α (Units.val.{u1} α _inst_1 (Neg.neg.{u1} (Units.{u1} α _inst_1) (Units.instNegUnits.{u1} α _inst_1 _inst_2) u)) (Neg.neg.{u1} α (HasInvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (Units.val.{u1} α _inst_1 u))
Case conversion may be inaccurate. Consider using '#align units.coe_neg Units.val_negₓ'. -/
/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast]
protected theorem val_neg (u : αˣ) : (↑(-u) : α) = -u :=
  rfl
#align units.coe_neg Units.val_neg

/- warning: units.coe_neg_one -> Units.coe_neg_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))], Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.val.{u1} α _inst_1)))) (Neg.neg.{u1} (Units.{u1} α _inst_1) (Units.hasNeg.{u1} α _inst_1 _inst_2) (OfNat.ofNat.{u1} (Units.{u1} α _inst_1) 1 (OfNat.mk.{u1} (Units.{u1} α _inst_1) 1 (One.one.{u1} (Units.{u1} α _inst_1) (MulOneClass.toHasOne.{u1} (Units.{u1} α _inst_1) (Units.mulOneClass.{u1} α _inst_1))))))) (Neg.neg.{u1} α (HasInvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))], Eq.{succ u1} α (Units.val.{u1} α _inst_1 (Neg.neg.{u1} (Units.{u1} α _inst_1) (Units.instNegUnits.{u1} α _inst_1 _inst_2) (OfNat.ofNat.{u1} (Units.{u1} α _inst_1) 1 (One.toOfNat1.{u1} (Units.{u1} α _inst_1) (InvOneClass.toOne.{u1} (Units.{u1} α _inst_1) (DivInvOneMonoid.toInvOneClass.{u1} (Units.{u1} α _inst_1) (DivisionMonoid.toDivInvOneMonoid.{u1} (Units.{u1} α _inst_1) (Group.toDivisionMonoid.{u1} (Units.{u1} α _inst_1) (Units.instGroupUnits.{u1} α _inst_1))))))))) (Neg.neg.{u1} α (HasInvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align units.coe_neg_one Units.coe_neg_oneₓ'. -/
@[simp, norm_cast]
protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 :=
  rfl
#align units.coe_neg_one Units.coe_neg_one

instance : HasDistribNeg αˣ :=
  Units.ext.HasDistribNeg _ Units.val_neg Units.val_mul

/- warning: units.neg_divp -> Units.neg_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] (a : α) (u : Units.{u1} α _inst_1), Eq.{succ u1} α (Neg.neg.{u1} α (HasInvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (divp.{u1} α _inst_1 a u)) (divp.{u1} α _inst_1 (Neg.neg.{u1} α (HasInvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] (a : α) (u : Units.{u1} α _inst_1), Eq.{succ u1} α (Neg.neg.{u1} α (HasInvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (divp.{u1} α _inst_1 a u)) (divp.{u1} α _inst_1 (Neg.neg.{u1} α (HasInvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a) u)
Case conversion may be inaccurate. Consider using '#align units.neg_divp Units.neg_divpₓ'. -/
@[field_simps]
theorem neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = -a /ₚ u := by simp only [divp, neg_mul]
#align units.neg_divp Units.neg_divp

end HasDistribNeg

section Ring

variable [Ring α] {a b : α}

/- warning: units.divp_add_divp_same -> Units.divp_add_divp_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) a u) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) b u)) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a b) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) a u) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) b u)) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b) u)
Case conversion may be inaccurate. Consider using '#align units.divp_add_divp_same Units.divp_add_divp_sameₓ'. -/
@[field_simps]
theorem divp_add_divp_same (a b : α) (u : αˣ) : a /ₚ u + b /ₚ u = (a + b) /ₚ u := by
  simp only [divp, add_mul]
#align units.divp_add_divp_same Units.divp_add_divp_same

/- warning: units.divp_sub_divp_same -> Units.divp_sub_divp_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) a u) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) b u)) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) a u) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) b u)) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) a b) u)
Case conversion may be inaccurate. Consider using '#align units.divp_sub_divp_same Units.divp_sub_divp_sameₓ'. -/
@[field_simps]
theorem divp_sub_divp_same (a b : α) (u : αˣ) : a /ₚ u - b /ₚ u = (a - b) /ₚ u := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_divp, divp_add_divp_same]
#align units.divp_sub_divp_same Units.divp_sub_divp_same

/- warning: units.add_divp -> Units.add_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) b u)) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (Units.val.{u1} α (Ring.toMonoid.{u1} α _inst_1))))) u)) b) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) b u)) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))) a (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) u)) b) u)
Case conversion may be inaccurate. Consider using '#align units.add_divp Units.add_divpₓ'. -/
@[field_simps]
theorem add_divp (a b : α) (u : αˣ) : a + b /ₚ u = (a * u + b) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]
#align units.add_divp Units.add_divp

/- warning: units.sub_divp -> Units.sub_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) b u)) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (Units.val.{u1} α (Ring.toMonoid.{u1} α _inst_1))))) u)) b) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) a (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) b u)) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))) a (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) u)) b) u)
Case conversion may be inaccurate. Consider using '#align units.sub_divp Units.sub_divpₓ'. -/
@[field_simps]
theorem sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u := by
  simp only [divp, sub_mul, Units.mul_inv_cancel_right]
#align units.sub_divp Units.sub_divp

/- warning: units.divp_add -> Units.divp_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) a u) b) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1))) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (Units.val.{u1} α (Ring.toMonoid.{u1} α _inst_1))))) u))) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) a u) b) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))) b (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) u))) u)
Case conversion may be inaccurate. Consider using '#align units.divp_add Units.divp_addₓ'. -/
@[field_simps]
theorem divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]
#align units.divp_add Units.divp_add

/- warning: units.divp_sub -> Units.divp_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) a u) b) (divp.{u1} α (Ring.toMonoid.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1))) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α _inst_1)) α (Units.val.{u1} α (Ring.toMonoid.{u1} α _inst_1))))) u))) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (a : α) (b : α) (u : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) a u) b) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))) b (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) u))) u)
Case conversion may be inaccurate. Consider using '#align units.divp_sub Units.divp_subₓ'. -/
@[field_simps]
theorem divp_sub (a b : α) (u : αˣ) : a /ₚ u - b = (a - b * u) /ₚ u := by
  simp only [divp, sub_mul, sub_right_inj]
  assoc_rw [Units.mul_inv, mul_one]
#align units.divp_sub Units.divp_sub

end Ring

end Units

/- warning: is_unit.neg -> IsUnit.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] {a : α}, (IsUnit.{u1} α _inst_1 a) -> (IsUnit.{u1} α _inst_1 (Neg.neg.{u1} α (HasInvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] {a : α}, (IsUnit.{u1} α _inst_1 a) -> (IsUnit.{u1} α _inst_1 (Neg.neg.{u1} α (HasInvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a))
Case conversion may be inaccurate. Consider using '#align is_unit.neg IsUnit.negₓ'. -/
theorem IsUnit.neg [Monoid α] [HasDistribNeg α] {a : α} : IsUnit a → IsUnit (-a)
  | ⟨x, hx⟩ => hx ▸ (-x).IsUnit
#align is_unit.neg IsUnit.neg

/- warning: is_unit.neg_iff -> IsUnit.neg_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] (a : α), Iff (IsUnit.{u1} α _inst_1 (Neg.neg.{u1} α (HasInvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a)) (IsUnit.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] (a : α), Iff (IsUnit.{u1} α _inst_1 (Neg.neg.{u1} α (HasInvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a)) (IsUnit.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align is_unit.neg_iff IsUnit.neg_iffₓ'. -/
@[simp]
theorem IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : IsUnit (-a) ↔ IsUnit a :=
  ⟨fun h => neg_neg a ▸ h.neg, IsUnit.neg⟩
#align is_unit.neg_iff IsUnit.neg_iff

/- warning: is_unit.sub_iff -> IsUnit.sub_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {x : α} {y : α}, Iff (IsUnit.{u1} α (Ring.toMonoid.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) x y)) (IsUnit.{u1} α (Ring.toMonoid.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) y x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {x : α} {y : α}, Iff (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) x y)) (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) y x))
Case conversion may be inaccurate. Consider using '#align is_unit.sub_iff IsUnit.sub_iffₓ'. -/
theorem IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsUnit (y - x) :=
  (IsUnit.neg_iff _).symm.trans <| neg_sub x y ▸ Iff.rfl
#align is_unit.sub_iff IsUnit.sub_iff

namespace Units

/- warning: units.divp_add_divp -> Units.divp_add_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] (a : α) (b : α) (u₁ : Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (u₂ : Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (CommRing.toRing.{u1} α _inst_1)))) (divp.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)) a u₁) (divp.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)) b u₂)) (divp.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (CommRing.toRing.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (CommRing.toRing.{u1} α _inst_1)))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (Units.val.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)))))) u₂)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (CommRing.toRing.{u1} α _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (Units.val.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)))))) u₁) b)) (HMul.hMul.{u1, u1, u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (instHMul.{u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (MulOneClass.toHasMul.{u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (Units.mulOneClass.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))))) u₁ u₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] (a : α) (b : α) (u₁ : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (u₂ : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))))) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) a u₁) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) b u₂)) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))) a (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) u₂)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) u₁) b)) (HMul.hMul.{u1, u1, u1} (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (instHMul.{u1} (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (Units.instMulOneClassUnits.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))))) u₁ u₂))
Case conversion may be inaccurate. Consider using '#align units.divp_add_divp Units.divp_add_divpₓ'. -/
@[field_simps]
theorem divp_add_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) :
    a /ₚ u₁ + b /ₚ u₂ = (a * u₂ + u₁ * b) /ₚ (u₁ * u₂) := by
  simp only [divp, add_mul, mul_inv_rev, coe_mul]
  rw [mul_comm (↑u₁ * b), mul_comm b]
  assoc_rw [mul_inv, mul_inv, mul_one, mul_one]
#align units.divp_add_divp Units.divp_add_divp

/- warning: units.divp_sub_divp -> Units.divp_sub_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] (a : α) (b : α) (u₁ : Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (u₂ : Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))))) (divp.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)) a u₁) (divp.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)) b u₂)) (divp.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (CommRing.toRing.{u1} α _inst_1)))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (Units.val.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)))))) u₂)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (CommRing.toRing.{u1} α _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) α (Units.val.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1)))))) u₁) b)) (HMul.hMul.{u1, u1, u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (instHMul.{u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (MulOneClass.toHasMul.{u1} (Units.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))) (Units.mulOneClass.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_1))))) u₁ u₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] (a : α) (b : α) (u₁ : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (u₂ : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α (CommRing.toRing.{u1} α _inst_1))) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) a u₁) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) b u₂)) (divp.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α (CommRing.toRing.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))) a (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) u₂)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1)))) u₁) b)) (HMul.hMul.{u1, u1, u1} (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (instHMul.{u1} (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))) (Units.instMulOneClassUnits.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))))))) u₁ u₂))
Case conversion may be inaccurate. Consider using '#align units.divp_sub_divp Units.divp_sub_divpₓ'. -/
@[field_simps]
theorem divp_sub_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) :
    a /ₚ u₁ - b /ₚ u₂ = (a * u₂ - u₁ * b) /ₚ (u₁ * u₂) := by
  simp_rw [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]
#align units.divp_sub_divp Units.divp_sub_divp

theorem add_eq_mul_one_add_div [Semiring R] {a : Rˣ} {b : R} : ↑a + b = a * (1 + ↑a⁻¹ * b) := by
  rwa [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
#align units.add_eq_mul_one_add_div Units.add_eq_mul_one_add_div

end Units

