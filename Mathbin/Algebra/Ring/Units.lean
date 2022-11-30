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
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] [_inst_2 : HasDistribNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))] (u : Units.{u} α _inst_1), Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Neg.neg.{u} (Units.{u} α _inst_1) (Units.hasNeg.{u} α _inst_1 _inst_2) u)) (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1)) _inst_2)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.102 : Monoid.{u} α] [inst._@.Mathlib.Algebra.Ring.Units._hyg.105 : HasDistribNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.102))] (u : Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.102), Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.102 (Neg.neg.{u} (Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.102) (Units.instNegUnits.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.102 inst._@.Mathlib.Algebra.Ring.Units._hyg.105) u)) (Neg.neg.{u} α (HasInvolutiveNeg.toNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.102)) inst._@.Mathlib.Algebra.Ring.Units._hyg.105)) (Units.val.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.102 u))
Case conversion may be inaccurate. Consider using '#align units.coe_neg Units.val_negₓ'. -/
/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast]
protected theorem val_neg (u : αˣ) : (↑(-u) : α) = -u :=
  rfl
#align units.coe_neg Units.val_neg

/- warning: units.coe_neg_one -> Units.coe_neg_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] [_inst_2 : HasDistribNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))], Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Neg.neg.{u} (Units.{u} α _inst_1) (Units.hasNeg.{u} α _inst_1 _inst_2) (OfNat.ofNat.{u} (Units.{u} α _inst_1) 1 (OfNat.mk.{u} (Units.{u} α _inst_1) 1 (One.one.{u} (Units.{u} α _inst_1) (MulOneClass.toHasOne.{u} (Units.{u} α _inst_1) (Units.mulOneClass.{u} α _inst_1))))))) (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1)) _inst_2)) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.137 : Monoid.{u} α] [inst._@.Mathlib.Algebra.Ring.Units._hyg.140 : HasDistribNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137))], Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137 (Neg.neg.{u} (Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137) (Units.instNegUnits.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137 inst._@.Mathlib.Algebra.Ring.Units._hyg.140) (OfNat.ofNat.{u} (Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137) 1 (One.toOfNat1.{u} (Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137) (InvOneClass.toOne.{u} (Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137) (DivInvOneMonoid.toInvOneClass.{u} (Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137) (DivisionMonoid.toDivInvOneMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137) (Group.toDivisionMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137) (Units.instGroupUnits.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137))))))))) (Neg.neg.{u} α (HasInvolutiveNeg.toNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137)) inst._@.Mathlib.Algebra.Ring.Units._hyg.140)) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.137))))
Case conversion may be inaccurate. Consider using '#align units.coe_neg_one Units.coe_neg_oneₓ'. -/
@[simp, norm_cast]
protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 :=
  rfl
#align units.coe_neg_one Units.coe_neg_one

instance : HasDistribNeg αˣ :=
  Units.ext.HasDistribNeg _ Units.val_neg Units.val_mul

/- warning: units.neg_divp -> Units.neg_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] [_inst_2 : HasDistribNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))] (a : α) (u : Units.{u} α _inst_1), Eq.{succ u} α (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1)) _inst_2)) (divp.{u} α _inst_1 a u)) (divp.{u} α _inst_1 (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1)) _inst_2)) a) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.193 : Monoid.{u} α] [inst._@.Mathlib.Algebra.Ring.Units._hyg.196 : HasDistribNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.193))] (a : α) (u : Units.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.193), Eq.{succ u} α (Neg.neg.{u} α (HasInvolutiveNeg.toNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.193)) inst._@.Mathlib.Algebra.Ring.Units._hyg.196)) (divp.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.193 a u)) (divp.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.193 (Neg.neg.{u} α (HasInvolutiveNeg.toNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.193)) inst._@.Mathlib.Algebra.Ring.Units._hyg.196)) a) u)
Case conversion may be inaccurate. Consider using '#align units.neg_divp Units.neg_divpₓ'. -/
@[field_simps]
theorem neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = -a /ₚ u := by simp only [divp, neg_mul]
#align units.neg_divp Units.neg_divp

end HasDistribNeg

section Ring

variable [Ring α] {a b : α}

/- warning: units.divp_add_divp_same -> Units.divp_add_divp_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (Ring.toMonoid.{u} α _inst_1)), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toHasAdd.{u} α (Ring.toDistrib.{u} α _inst_1))) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) a u) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) b u)) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toHasAdd.{u} α (Ring.toDistrib.{u} α _inst_1))) a b) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.250 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.250)))), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toAdd.{u} α (NonUnitalNonAssocSemiring.toDistrib.{u} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.250)))))) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.250))) a u) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.250))) b u)) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.250))) (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toAdd.{u} α (NonUnitalNonAssocSemiring.toDistrib.{u} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.250)))))) a b) u)
Case conversion may be inaccurate. Consider using '#align units.divp_add_divp_same Units.divp_add_divp_sameₓ'. -/
@[field_simps]
theorem divp_add_divp_same (a b : α) (u : αˣ) : a /ₚ u + b /ₚ u = (a + b) /ₚ u := by
  simp only [divp, add_mul]
#align units.divp_add_divp_same Units.divp_add_divp_same

/- warning: units.divp_sub_divp_same -> Units.divp_sub_divp_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (Ring.toMonoid.{u} α _inst_1)), Eq.{succ u} α (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α _inst_1)))))) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) a u) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) b u)) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α _inst_1)))))) a b) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.299 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.299)))), Eq.{succ u} α (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.299)) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.299))) a u) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.299))) b u)) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.299))) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.299)) a b) u)
Case conversion may be inaccurate. Consider using '#align units.divp_sub_divp_same Units.divp_sub_divp_sameₓ'. -/
@[field_simps]
theorem divp_sub_divp_same (a b : α) (u : αˣ) : a /ₚ u - b /ₚ u = (a - b) /ₚ u := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_divp, divp_add_divp_same]
#align units.divp_sub_divp_same Units.divp_sub_divp_same

/- warning: units.add_divp -> Units.add_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (Ring.toMonoid.{u} α _inst_1)), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toHasAdd.{u} α (Ring.toDistrib.{u} α _inst_1))) a (divp.{u} α (Ring.toMonoid.{u} α _inst_1) b u)) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toHasAdd.{u} α (Ring.toDistrib.{u} α _inst_1))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (Distrib.toHasMul.{u} α (Ring.toDistrib.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (Units.val.{u} α (Ring.toMonoid.{u} α _inst_1))))) u)) b) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.376 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.376)))), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toAdd.{u} α (NonUnitalNonAssocSemiring.toDistrib.{u} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.376)))))) a (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.376))) b u)) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.376))) (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toAdd.{u} α (NonUnitalNonAssocSemiring.toDistrib.{u} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.376)))))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (NonUnitalNonAssocRing.toMul.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.376)))) a (Units.val.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.376))) u)) b) u)
Case conversion may be inaccurate. Consider using '#align units.add_divp Units.add_divpₓ'. -/
@[field_simps]
theorem add_divp (a b : α) (u : αˣ) : a + b /ₚ u = (a * u + b) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]
#align units.add_divp Units.add_divp

/- warning: units.sub_divp -> Units.sub_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (Ring.toMonoid.{u} α _inst_1)), Eq.{succ u} α (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α _inst_1)))))) a (divp.{u} α (Ring.toMonoid.{u} α _inst_1) b u)) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α _inst_1)))))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (Distrib.toHasMul.{u} α (Ring.toDistrib.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (Units.val.{u} α (Ring.toMonoid.{u} α _inst_1))))) u)) b) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.422 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.422)))), Eq.{succ u} α (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.422)) a (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.422))) b u)) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.422))) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.422)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (NonUnitalNonAssocRing.toMul.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.422)))) a (Units.val.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.422))) u)) b) u)
Case conversion may be inaccurate. Consider using '#align units.sub_divp Units.sub_divpₓ'. -/
@[field_simps]
theorem sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u := by
  simp only [divp, sub_mul, Units.mul_inv_cancel_right]
#align units.sub_divp Units.sub_divp

/- warning: units.divp_add -> Units.divp_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (Ring.toMonoid.{u} α _inst_1)), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toHasAdd.{u} α (Ring.toDistrib.{u} α _inst_1))) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) a u) b) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toHasAdd.{u} α (Ring.toDistrib.{u} α _inst_1))) a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (Distrib.toHasMul.{u} α (Ring.toDistrib.{u} α _inst_1))) b ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (Units.val.{u} α (Ring.toMonoid.{u} α _inst_1))))) u))) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.468 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.468)))), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toAdd.{u} α (NonUnitalNonAssocSemiring.toDistrib.{u} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.468)))))) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.468))) a u) b) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.468))) (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toAdd.{u} α (NonUnitalNonAssocSemiring.toDistrib.{u} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.468)))))) a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (NonUnitalNonAssocRing.toMul.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.468)))) b (Units.val.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.468))) u))) u)
Case conversion may be inaccurate. Consider using '#align units.divp_add Units.divp_addₓ'. -/
@[field_simps]
theorem divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]
#align units.divp_add Units.divp_add

/- warning: units.divp_sub -> Units.divp_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (Ring.toMonoid.{u} α _inst_1)), Eq.{succ u} α (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α _inst_1)))))) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) a u) b) (divp.{u} α (Ring.toMonoid.{u} α _inst_1) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α _inst_1)))))) a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (Distrib.toHasMul.{u} α (Ring.toDistrib.{u} α _inst_1))) b ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α _inst_1)) α (Units.val.{u} α (Ring.toMonoid.{u} α _inst_1))))) u))) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.514 : Ring.{u} α] (a : α) (b : α) (u : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.514)))), Eq.{succ u} α (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.514)) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.514))) a u) b) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.514))) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.514)) a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (NonUnitalNonAssocRing.toMul.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.514)))) b (Units.val.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.514))) u))) u)
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
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] [_inst_2 : HasDistribNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))] {a : α}, (IsUnit.{u} α _inst_1 a) -> (IsUnit.{u} α _inst_1 (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1)) _inst_2)) a))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.593 : Monoid.{u} α] [inst._@.Mathlib.Algebra.Ring.Units._hyg.596 : HasDistribNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.593))] {a : α}, (IsUnit.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.593 a) -> (IsUnit.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.593 (Neg.neg.{u} α (HasInvolutiveNeg.toNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.593)) inst._@.Mathlib.Algebra.Ring.Units._hyg.596)) a))
Case conversion may be inaccurate. Consider using '#align is_unit.neg IsUnit.negₓ'. -/
theorem IsUnit.neg [Monoid α] [HasDistribNeg α] {a : α} : IsUnit a → IsUnit (-a)
  | ⟨x, hx⟩ => hx ▸ (-x).IsUnit
#align is_unit.neg IsUnit.neg

/- warning: is_unit.neg_iff -> IsUnit.neg_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] [_inst_2 : HasDistribNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))] (a : α), Iff (IsUnit.{u} α _inst_1 (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1)) _inst_2)) a)) (IsUnit.{u} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.653 : Monoid.{u} α] [inst._@.Mathlib.Algebra.Ring.Units._hyg.656 : HasDistribNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.653))] (a : α), Iff (IsUnit.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.653 (Neg.neg.{u} α (HasInvolutiveNeg.toNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.653)) inst._@.Mathlib.Algebra.Ring.Units._hyg.656)) a)) (IsUnit.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.653 a)
Case conversion may be inaccurate. Consider using '#align is_unit.neg_iff IsUnit.neg_iffₓ'. -/
@[simp]
theorem IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : IsUnit (-a) ↔ IsUnit a :=
  ⟨fun h => neg_neg a ▸ h.neg, IsUnit.neg⟩
#align is_unit.neg_iff IsUnit.neg_iff

/- warning: is_unit.sub_iff -> IsUnit.sub_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Ring.{u} α] {x : α} {y : α}, Iff (IsUnit.{u} α (Ring.toMonoid.{u} α _inst_1) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α _inst_1)))))) x y)) (IsUnit.{u} α (Ring.toMonoid.{u} α _inst_1) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α _inst_1)))))) y x))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.694 : Ring.{u} α] {x : α} {y : α}, Iff (IsUnit.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.694))) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.694)) x y)) (IsUnit.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.694))) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.694)) y x))
Case conversion may be inaccurate. Consider using '#align is_unit.sub_iff IsUnit.sub_iffₓ'. -/
theorem IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsUnit (y - x) :=
  (IsUnit.neg_iff _).symm.trans <| neg_sub x y ▸ Iff.rfl
#align is_unit.sub_iff IsUnit.sub_iff

namespace Units

/- warning: units.divp_add_divp -> Units.divp_add_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : CommRing.{u} α] (a : α) (b : α) (u₁ : Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (u₂ : Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toHasAdd.{u} α (Ring.toDistrib.{u} α (CommRing.toRing.{u} α _inst_1)))) (divp.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)) a u₁) (divp.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)) b u₂)) (divp.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)) (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toHasAdd.{u} α (Ring.toDistrib.{u} α (CommRing.toRing.{u} α _inst_1)))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (Distrib.toHasMul.{u} α (Ring.toDistrib.{u} α (CommRing.toRing.{u} α _inst_1)))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (Units.val.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)))))) u₂)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (Distrib.toHasMul.{u} α (Ring.toDistrib.{u} α (CommRing.toRing.{u} α _inst_1)))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (Units.val.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)))))) u₁) b)) (HMul.hMul.{u, u, u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (instHMul.{u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (MulOneClass.toHasMul.{u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (Units.mulOneClass.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))))) u₁ u₂))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.741 : CommRing.{u} α] (a : α) (b : α) (u₁ : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))) (u₂ : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toAdd.{u} α (NonUnitalNonAssocSemiring.toDistrib.{u} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))))) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741)))) a u₁) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741)))) b u₂)) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741)))) (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (Distrib.toAdd.{u} α (NonUnitalNonAssocSemiring.toDistrib.{u} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (NonUnitalNonAssocRing.toMul.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))) a (Units.val.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741)))) u₂)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (NonUnitalNonAssocRing.toMul.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))) (Units.val.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741)))) u₁) b)) (HMul.hMul.{u, u, u} (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))) (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))) (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))) (instHMul.{u} (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))) (MulOneClass.toMul.{u} (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))) (Units.instMulOneClassUnits.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.741))))))) u₁ u₂))
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
  forall {α : Type.{u}} [_inst_1 : CommRing.{u} α] (a : α) (b : α) (u₁ : Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (u₂ : Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))), Eq.{succ u} α (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α (CommRing.toRing.{u} α _inst_1))))))) (divp.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)) a u₁) (divp.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)) b u₂)) (divp.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (SubNegMonoid.toHasSub.{u} α (AddGroup.toSubNegMonoid.{u} α (AddGroupWithOne.toAddGroup.{u} α (NonAssocRing.toAddGroupWithOne.{u} α (Ring.toNonAssocRing.{u} α (CommRing.toRing.{u} α _inst_1))))))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (Distrib.toHasMul.{u} α (Ring.toDistrib.{u} α (CommRing.toRing.{u} α _inst_1)))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (Units.val.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)))))) u₂)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (Distrib.toHasMul.{u} α (Ring.toDistrib.{u} α (CommRing.toRing.{u} α _inst_1)))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) α (Units.val.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1)))))) u₁) b)) (HMul.hMul.{u, u, u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (instHMul.{u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (MulOneClass.toHasMul.{u} (Units.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))) (Units.mulOneClass.{u} α (Ring.toMonoid.{u} α (CommRing.toRing.{u} α _inst_1))))) u₁ u₂))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Ring.Units._hyg.885 : CommRing.{u} α] (a : α) (b : α) (u₁ : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))) (u₂ : Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))), Eq.{succ u} α (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885)))) a u₁) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885)))) b u₂)) (divp.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885)))) (HSub.hSub.{u, u, u} α α α (instHSub.{u} α (Ring.toSub.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (NonUnitalNonAssocRing.toMul.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))) a (Units.val.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885)))) u₂)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (NonUnitalNonAssocRing.toMul.{u} α (NonAssocRing.toNonUnitalNonAssocRing.{u} α (Ring.toNonAssocRing.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))) (Units.val.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885)))) u₁) b)) (HMul.hMul.{u, u, u} (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))) (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))) (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))) (instHMul.{u} (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))) (MulOneClass.toMul.{u} (Units.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))) (Units.instMulOneClassUnits.{u} α (MonoidWithZero.toMonoid.{u} α (Semiring.toMonoidWithZero.{u} α (Ring.toSemiring.{u} α (CommRing.toRing.{u} α inst._@.Mathlib.Algebra.Ring.Units._hyg.885))))))) u₁ u₂))
Case conversion may be inaccurate. Consider using '#align units.divp_sub_divp Units.divp_sub_divpₓ'. -/
@[field_simps]
theorem divp_sub_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) :
    a /ₚ u₁ - b /ₚ u₂ = (a * u₂ - u₁ * b) /ₚ (u₁ * u₂) := by
  simp_rw [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]
#align units.divp_sub_divp Units.divp_sub_divp

end Units

