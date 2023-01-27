/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module ring_theory.congruence
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.Algebra.Hom.Ring
import Mathbin.Algebra.Ring.InjSurj
import Mathbin.GroupTheory.Congruence

/-!
# Congruence relations on rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines congruence relations on rings, which extend `con` and `add_con` on monoids and
additive monoids.

Most of the time you likely want to use the `ideal.quotient` API that is built on top of this.

## Main Definitions

* `ring_con R`: the type of congruence relations respecting `+` and `*`.
* `ring_con_gen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Use this for `ring_quot` too.
* Copy across more API from `con` and `add_con` in `group_theory/congruence.lean`, such as:
  * The `complete_lattice` structure.
  * The `con_gen_eq` lemma, stating that
    `ring_con_gen r = Inf {s : ring_con M | ∀ x y, r x y → s x y}`.
-/


#print RingCon /-
/- Note: we can't extend both `add_con R` and `mul_con R` in Lean 3 due to interactions between old-
and new-style structures. We can revisit this in Lean 4. (After and not during the port!) -/
/-- A congruence relation on a type with an addition and multiplication is an equivalence relation
which preserves both. -/
structure RingCon (R : Type _) [Add R] [Mul R] extends Setoid R where
  add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z)
  mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z)
#align ring_con RingCon
-/

variable {α R : Type _}

#print RingConGen.Rel /-
/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
inductive RingConGen.Rel [Add R] [Mul R] (r : R → R → Prop) : R → R → Prop
  | of : ∀ x y, r x y → RingConGen.Rel x y
  | refl : ∀ x, RingConGen.Rel x x
  | symm : ∀ {x y}, RingConGen.Rel x y → RingConGen.Rel y x
  | trans : ∀ {x y z}, RingConGen.Rel x y → RingConGen.Rel y z → RingConGen.Rel x z
  | add : ∀ {w x y z}, RingConGen.Rel w x → RingConGen.Rel y z → RingConGen.Rel (w + y) (x + z)
  | mul : ∀ {w x y z}, RingConGen.Rel w x → RingConGen.Rel y z → RingConGen.Rel (w * y) (x * z)
#align ring_con_gen.rel RingConGen.Rel
-/

#print ringConGen /-
/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
def ringConGen [Add R] [Mul R] (r : R → R → Prop) : RingCon R
    where
  R := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' _ _ _ _ := RingConGen.Rel.add
  mul' _ _ _ _ := RingConGen.Rel.mul
#align ring_con_gen ringConGen
-/

namespace RingCon

section Basic

variable [Add R] [Mul R] (c : RingCon R)

#print RingCon.toAddCon /-
/-- Every `ring_con` is also an `add_con` -/
def toAddCon : AddCon R :=
  { c with }
#align ring_con.to_add_con RingCon.toAddCon
-/

#print RingCon.toCon /-
/-- Every `ring_con` is also a `con` -/
def toCon : Con R :=
  { c with }
#align ring_con.to_con RingCon.toCon
-/

/-- A coercion from a congruence relation to its underlying binary relation. -/
instance : CoeFun (RingCon R) fun _ => R → R → Prop :=
  ⟨fun c => c.R⟩

#print RingCon.rel_eq_coe /-
@[simp]
theorem rel_eq_coe : c.R = c :=
  rfl
#align ring_con.rel_eq_coe RingCon.rel_eq_coe
-/

#print RingCon.refl /-
protected theorem refl (x) : c x x :=
  c.refl' x
#align ring_con.refl RingCon.refl
-/

#print RingCon.symm /-
protected theorem symm {x y} : c x y → c y x :=
  c.symm'
#align ring_con.symm RingCon.symm
-/

#print RingCon.trans /-
protected theorem trans {x y z} : c x y → c y z → c x z :=
  c.trans'
#align ring_con.trans RingCon.trans
-/

#print RingCon.add /-
protected theorem add {w x y z} : c w x → c y z → c (w + y) (x + z) :=
  c.add'
#align ring_con.add RingCon.add
-/

#print RingCon.mul /-
protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) :=
  c.mul'
#align ring_con.mul RingCon.mul
-/

#print RingCon.rel_mk /-
@[simp]
theorem rel_mk {s : Setoid R} {ha hm a b} : RingCon.mk s ha hm a b ↔ Setoid.r a b :=
  Iff.rfl
#align ring_con.rel_mk RingCon.rel_mk
-/

instance : Inhabited (RingCon R) :=
  ⟨ringConGen EmptyRelation⟩

end Basic

section Quotient

section Basic

variable [Add R] [Mul R] (c : RingCon R)

#print RingCon.Quotient /-
/-- Defining the quotient by a congruence relation of a type with addition and multiplication. -/
protected def Quotient :=
  Quotient c.toSetoid
#align ring_con.quotient RingCon.Quotient
-/

/-- Coercion from a type with addition and multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
instance : CoeTC R c.Quotient :=
  ⟨@Quotient.mk' _ c.toSetoid⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
instance (priority := 500) [d : ∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  @Quotient.decidableEq R c.toSetoid d

#print RingCon.quot_mk_eq_coe /-
@[simp]
theorem quot_mk_eq_coe (x : R) : Quot.mk c x = (x : c.Quotient) :=
  rfl
#align ring_con.quot_mk_eq_coe RingCon.quot_mk_eq_coe
-/

#print RingCon.eq /-
/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[simp]
protected theorem eq {a b : R} : (a : c.Quotient) = b ↔ c a b :=
  Quotient.eq''
#align ring_con.eq RingCon.eq
-/

end Basic

/-! ### Basic notation

The basic algebraic notation, `0`, `1`, `+`, `*`, `-`, `^`, descend naturally under the quotient
-/


section Data

section add_mul

variable [Add R] [Mul R] (c : RingCon R)

instance : Add c.Quotient :=
  c.toAddCon.HasAdd

#print RingCon.coe_add /-
@[simp, norm_cast]
theorem coe_add (x y : R) : (↑(x + y) : c.Quotient) = ↑x + ↑y :=
  rfl
#align ring_con.coe_add RingCon.coe_add
-/

instance : Mul c.Quotient :=
  c.toCon.HasMul

#print RingCon.coe_mul /-
@[simp, norm_cast]
theorem coe_mul (x y : R) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl
#align ring_con.coe_mul RingCon.coe_mul
-/

end add_mul

section Zero

variable [AddZeroClass R] [Mul R] (c : RingCon R)

instance : Zero c.Quotient :=
  c.toAddCon

/- warning: ring_con.coe_zero -> RingCon.coe_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddZeroClass.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2 c))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R _inst_1))))) (OfNat.ofNat.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2 c) 0 (OfNat.mk.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2 c) 0 (Zero.zero.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R _inst_1) _inst_2 c) (RingCon.Quotient.hasZero.{u1} R _inst_1 _inst_2 c))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddZeroClass.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toAdd.{u1} R _inst_1) _inst_2), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R _inst_1) _inst_2 c) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R _inst_1) _inst_2 c (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddZeroClass.toZero.{u1} R _inst_1)))) (OfNat.ofNat.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R _inst_1) _inst_2 c) 0 (Zero.toOfNat0.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R _inst_1) _inst_2 c) (RingCon.instZeroQuotientToAdd.{u1} R _inst_1 _inst_2 c)))
Case conversion may be inaccurate. Consider using '#align ring_con.coe_zero RingCon.coe_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_zero : (↑(0 : R) : c.Quotient) = 0 :=
  rfl
#align ring_con.coe_zero RingCon.coe_zero

end Zero

section One

variable [Add R] [MulOneClass R] (c : RingCon R)

instance : One c.Quotient :=
  c.toCon

/- warning: ring_con.coe_one -> RingCon.coe_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Add.{u1} R] [_inst_2 : MulOneClass.{u1} R] (c : RingCon.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R _inst_2)), Eq.{succ u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R _inst_2) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R _inst_2) c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R _inst_2) c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R _inst_2) c) (RingCon.Quotient.hasCoeT.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R _inst_2) c))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R _inst_2))))) (OfNat.ofNat.{u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R _inst_2) c) 1 (OfNat.mk.{u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R _inst_2) c) 1 (One.one.{u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R _inst_2) c) (RingCon.Quotient.hasOne.{u1} R _inst_1 _inst_2 c))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Add.{u1} R] [_inst_2 : MulOneClass.{u1} R] (c : RingCon.{u1} R _inst_1 (MulOneClass.toMul.{u1} R _inst_2)), Eq.{succ u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R _inst_2) c) (RingCon.toQuotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R _inst_2) c (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (MulOneClass.toOne.{u1} R _inst_2)))) (OfNat.ofNat.{u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R _inst_2) c) 1 (One.toOfNat1.{u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R _inst_2) c) (RingCon.instOneQuotientToMul.{u1} R _inst_1 _inst_2 c)))
Case conversion may be inaccurate. Consider using '#align ring_con.coe_one RingCon.coe_oneₓ'. -/
@[simp, norm_cast]
theorem coe_one : (↑(1 : R) : c.Quotient) = 1 :=
  rfl
#align ring_con.coe_one RingCon.coe_one

end One

section Smul

variable [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R] (c : RingCon R)

instance : SMul α c.Quotient :=
  c.toCon.HasSmul

/- warning: ring_con.coe_smul -> RingCon.coe_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : Add.{u2} R] [_inst_2 : MulOneClass.{u2} R] [_inst_3 : SMul.{u1, u2} α R] [_inst_4 : IsScalarTower.{u1, u2, u2} α R R _inst_3 (Mul.toSMul.{u2} R (MulOneClass.toHasMul.{u2} R _inst_2)) _inst_3] (c : RingCon.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2)) (a : α) (x : R), Eq.{succ u2} (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) R (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c) (HasLiftT.mk.{succ u2, succ u2} R (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c) (CoeTCₓ.coe.{succ u2, succ u2} R (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c) (RingCon.Quotient.hasCoeT.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c))) (SMul.smul.{u1, u2} α R _inst_3 a x)) (SMul.smul.{u1, u2} α (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c) (RingCon.Quotient.hasSmul.{u1, u2} α R _inst_1 _inst_2 _inst_3 _inst_4 c) a ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) R (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c) (HasLiftT.mk.{succ u2, succ u2} R (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c) (CoeTCₓ.coe.{succ u2, succ u2} R (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c) (RingCon.Quotient.hasCoeT.{u2} R _inst_1 (MulOneClass.toHasMul.{u2} R _inst_2) c))) x))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : Add.{u2} R] [_inst_2 : MulOneClass.{u2} R] [_inst_3 : SMul.{u1, u2} α R] [_inst_4 : IsScalarTower.{u1, u2, u2} α R R _inst_3 (Mul.toSMul.{u2} R (MulOneClass.toMul.{u2} R _inst_2)) _inst_3] (c : RingCon.{u2} R _inst_1 (MulOneClass.toMul.{u2} R _inst_2)) (a : α) (x : R), Eq.{succ u2} (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toMul.{u2} R _inst_2) c) (RingCon.toQuotient.{u2} R _inst_1 (MulOneClass.toMul.{u2} R _inst_2) c (HSMul.hSMul.{u1, u2, u2} α R R (instHSMul.{u1, u2} α R _inst_3) a x)) (HSMul.hSMul.{u1, u2, u2} α (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toMul.{u2} R _inst_2) c) (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toMul.{u2} R _inst_2) c) (instHSMul.{u1, u2} α (RingCon.Quotient.{u2} R _inst_1 (MulOneClass.toMul.{u2} R _inst_2) c) (RingCon.instSMulQuotientToMul.{u1, u2} α R _inst_1 _inst_2 _inst_3 _inst_4 c)) a (RingCon.toQuotient.{u2} R _inst_1 (MulOneClass.toMul.{u2} R _inst_2) c x))
Case conversion may be inaccurate. Consider using '#align ring_con.coe_smul RingCon.coe_smulₓ'. -/
@[simp, norm_cast]
theorem coe_smul (a : α) (x : R) : (↑(a • x) : c.Quotient) = a • x :=
  rfl
#align ring_con.coe_smul RingCon.coe_smul

end Smul

section NegSubZsmul

variable [AddGroup R] [Mul R] (c : RingCon R)

instance : Neg c.Quotient :=
  c.toAddCon

/- warning: ring_con.coe_neg -> RingCon.coe_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2) (x : R), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c))) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) x)) (Neg.neg.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasNeg.{u1} R _inst_1 _inst_2 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2) (x : R), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c (Neg.neg.{u1} R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (AddGroup.toSubtractionMonoid.{u1} R _inst_1)))) x)) (Neg.neg.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.instNegQuotientToAddToAddZeroClassToAddMonoidToSubNegMonoid.{u1} R _inst_1 _inst_2 c) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c x))
Case conversion may be inaccurate. Consider using '#align ring_con.coe_neg RingCon.coe_negₓ'. -/
@[simp, norm_cast]
theorem coe_neg (x : R) : (↑(-x) : c.Quotient) = -x :=
  rfl
#align ring_con.coe_neg RingCon.coe_neg

instance : Sub c.Quotient :=
  c.toAddCon

/- warning: ring_con.coe_sub -> RingCon.coe_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2) (x : R) (y : R), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))) x y)) (HSub.hSub.{u1, u1, u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (instHSub.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasSub.{u1} R _inst_1 _inst_2 c)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c))) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2) (x : R) (y : R), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))) x y)) (HSub.hSub.{u1, u1, u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (instHSub.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.instSubQuotientToAddToAddZeroClassToAddMonoidToSubNegMonoid.{u1} R _inst_1 _inst_2 c)) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c x) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c y))
Case conversion may be inaccurate. Consider using '#align ring_con.coe_sub RingCon.coe_subₓ'. -/
@[simp, norm_cast]
theorem coe_sub (x y : R) : (↑(x - y) : c.Quotient) = x - y :=
  rfl
#align ring_con.coe_sub RingCon.coe_sub

/- warning: ring_con.has_zsmul -> RingCon.hasZsmul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2), SMul.{0, u1} Int (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2), SMul.{0, u1} Int (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c)
Case conversion may be inaccurate. Consider using '#align ring_con.has_zsmul RingCon.hasZsmulₓ'. -/
instance hasZsmul : SMul ℤ c.Quotient :=
  c.toAddCon
#align ring_con.has_zsmul RingCon.hasZsmul

/- warning: ring_con.coe_zsmul -> RingCon.coe_zsmul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2) (z : Int) (x : R), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c))) (SMul.smul.{0, u1} Int R (SubNegMonoid.SMulInt.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) z x)) (SMul.smul.{0, u1} Int (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.hasZsmul.{u1} R _inst_1 _inst_2 c) z ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2) (z : Int) (x : R), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c (HSMul.hSMul.{0, u1, u1} Int R R (instHSMul.{0, u1} Int R (SubNegMonoid.SMulInt.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))) z x)) (HSMul.hSMul.{0, u1, u1} Int (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (instHSMul.{0, u1} Int (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c) (RingCon.hasZsmul.{u1} R _inst_1 _inst_2 c)) z (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)))) _inst_2 c x))
Case conversion may be inaccurate. Consider using '#align ring_con.coe_zsmul RingCon.coe_zsmulₓ'. -/
@[simp, norm_cast]
theorem coe_zsmul (z : ℤ) (x : R) : (↑(z • x) : c.Quotient) = z • x :=
  rfl
#align ring_con.coe_zsmul RingCon.coe_zsmul

end NegSubZsmul

section Nsmul

variable [AddMonoid R] [Mul R] (c : RingCon R)

/- warning: ring_con.has_nsmul -> RingCon.hasNsmul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2), SMul.{0, u1} Nat (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2), SMul.{0, u1} Nat (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c)
Case conversion may be inaccurate. Consider using '#align ring_con.has_nsmul RingCon.hasNsmulₓ'. -/
instance hasNsmul : SMul ℕ c.Quotient :=
  c.toAddCon
#align ring_con.has_nsmul RingCon.hasNsmul

/- warning: ring_con.coe_nsmul -> RingCon.coe_nsmul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2) (n : Nat) (x : R), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c))) (SMul.smul.{0, u1} Nat R (AddMonoid.SMul.{u1} R _inst_1) n x)) (SMul.smul.{0, u1} Nat (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (RingCon.hasNsmul.{u1} R _inst_1 _inst_2 c) n ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2) (n : Nat) (x : R), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c (HSMul.hSMul.{0, u1, u1} Nat R R (instHSMul.{0, u1} Nat R (AddMonoid.SMul.{u1} R _inst_1)) n x)) (HSMul.hSMul.{0, u1, u1} Nat (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (instHSMul.{0, u1} Nat (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c) (RingCon.hasNsmul.{u1} R _inst_1 _inst_2 c)) n (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) _inst_2 c x))
Case conversion may be inaccurate. Consider using '#align ring_con.coe_nsmul RingCon.coe_nsmulₓ'. -/
@[simp, norm_cast]
theorem coe_nsmul (n : ℕ) (x : R) : (↑(n • x) : c.Quotient) = n • x :=
  rfl
#align ring_con.coe_nsmul RingCon.coe_nsmul

end Nsmul

section Pow

variable [Add R] [Monoid R] (c : RingCon R)

instance : Pow c.Quotient ℕ :=
  c.toCon

/- warning: ring_con.coe_pow -> RingCon.coe_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Add.{u1} R] [_inst_2 : Monoid.{u1} R] (c : RingCon.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2))) (x : R) (n : Nat), Eq.{succ u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) (RingCon.Quotient.hasCoeT.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_2)) x n)) (HPow.hPow.{u1, 0, u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) Nat (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) (instHPow.{u1, 0} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) Nat (RingCon.Nat.hasPow.{u1} R _inst_1 _inst_2 c)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) (RingCon.Quotient.hasCoeT.{u1} R _inst_1 (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c))) x) n)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Add.{u1} R] [_inst_2 : Monoid.{u1} R] (c : RingCon.{u1} R _inst_1 (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2))) (x : R) (n : Nat), Eq.{succ u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) (RingCon.toQuotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_2)) x n)) (HPow.hPow.{u1, 0, u1} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) Nat (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) (instHPow.{u1, 0} (RingCon.Quotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c) Nat (RingCon.instPowQuotientToMulToMulOneClassNat.{u1} R _inst_1 _inst_2 c)) (RingCon.toQuotient.{u1} R _inst_1 (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) c x) n)
Case conversion may be inaccurate. Consider using '#align ring_con.coe_pow RingCon.coe_powₓ'. -/
@[simp, norm_cast]
theorem coe_pow (x : R) (n : ℕ) : (↑(x ^ n) : c.Quotient) = x ^ n :=
  rfl
#align ring_con.coe_pow RingCon.coe_pow

end Pow

section NatCast

variable [AddMonoidWithOne R] [Mul R] (c : RingCon R)

instance : NatCast c.Quotient :=
  ⟨fun n => ↑(n : R)⟩

/- warning: ring_con.coe_nat_cast -> RingCon.coe_nat_cast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2) (n : Nat), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) (HasLiftT.mk.{1, succ u1} Nat (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) (CoeTCₓ.coe.{1, succ u1} Nat (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) (Nat.castCoe.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) (RingCon.Quotient.hasNatCast.{u1} R _inst_1 _inst_2 c)))) n)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2) (n : Nat), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n)) (Nat.cast.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) _inst_2 c) (RingCon.instNatCastQuotientToAddToAddZeroClassToAddMonoid.{u1} R _inst_1 _inst_2 c) n)
Case conversion may be inaccurate. Consider using '#align ring_con.coe_nat_cast RingCon.coe_nat_castₓ'. -/
@[simp, norm_cast]
theorem coe_nat_cast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_nat_cast RingCon.coe_nat_cast

end NatCast

section IntCast

variable [AddGroupWithOne R] [Mul R] (c : RingCon R)

instance : IntCast c.Quotient :=
  ⟨fun z => ↑(z : R)⟩

/- warning: ring_con.coe_int_cast -> RingCon.coe_int_cast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2) (n : Nat), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) (HasLiftT.mk.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) (CoeTCₓ.coe.{succ u1, succ u1} R (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasCoeT.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) (HasLiftT.mk.{1, succ u1} Nat (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) (CoeTCₓ.coe.{1, succ u1} Nat (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) (Nat.castCoe.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) (RingCon.Quotient.hasNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1) _inst_2 c)))) n)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] [_inst_2 : Mul.{u1} R] (c : RingCon.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2) (n : Nat), Eq.{succ u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) (RingCon.toQuotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) n)) (Nat.cast.{u1} (RingCon.Quotient.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) _inst_2 c) (RingCon.instNatCastQuotientToAddToAddZeroClassToAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1) _inst_2 c) n)
Case conversion may be inaccurate. Consider using '#align ring_con.coe_int_cast RingCon.coe_int_castₓ'. -/
@[simp, norm_cast]
theorem coe_int_cast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_int_cast RingCon.coe_int_cast

end IntCast

instance [Inhabited R] [Add R] [Mul R] (c : RingCon R) : Inhabited c.Quotient :=
  ⟨↑(default : R)⟩

end Data

/-! ### Algebraic structure

The operations above on the quotient by `c : ring_con R` preseverse the algebraic structure of `R`.
-/


section Algebraic

instance [NonUnitalNonAssocSemiring R] (c : RingCon R) : NonUnitalNonAssocSemiring c.Quotient :=
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocSemiring R] (c : RingCon R) : NonAssocSemiring c.Quotient :=
  Function.Surjective.nonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalSemiring R] (c : RingCon R) : NonUnitalSemiring c.Quotient :=
  Function.Surjective.nonUnitalSemiring _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [Semiring R] (c : RingCon R) : Semiring c.Quotient :=
  Function.Surjective.semiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [CommSemiring R] (c : RingCon R) : CommSemiring c.Quotient :=
  Function.Surjective.commSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalNonAssocRing R] (c : RingCon R) : NonUnitalNonAssocRing c.Quotient :=
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocRing R] (c : RingCon R) : NonAssocRing c.Quotient :=
  Function.Surjective.nonAssocRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

instance [NonUnitalRing R] (c : RingCon R) : NonUnitalRing c.Quotient :=
  Function.Surjective.nonUnitalRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [Ring R] (c : RingCon R) : Ring c.Quotient :=
  Function.Surjective.ring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance [CommRing R] (c : RingCon R) : CommRing c.Quotient :=
  Function.Surjective.commRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance [Monoid α] [NonAssocSemiring R] [DistribMulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : DistribMulAction α c.Quotient :=
  { c.toCon.MulAction with
    smul := (· • ·)
    smul_zero := fun r => congr_arg Quotient.mk'' <| smul_zero _
    smul_add := fun r => Quotient.ind₂' fun m₁ m₂ => congr_arg Quotient.mk'' <| smul_add _ _ _ }

instance [Monoid α] [Semiring R] [MulSemiringAction α R] [IsScalarTower α R R] (c : RingCon R) :
    MulSemiringAction α c.Quotient :=
  { c, c.toCon.MulDistribMulAction with smul := (· • ·) }

end Algebraic

/- warning: ring_con.mk' -> RingCon.mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] (c : RingCon.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))), RingHom.{u1, u1} R (RingCon.Quotient.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) c) _inst_1 (RingCon.Quotient.nonAssocSemiring.{u1} R _inst_1 c)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] (c : RingCon.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))), RingHom.{u1, u1} R (RingCon.Quotient.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) c) _inst_1 (RingCon.instNonAssocSemiringQuotientToAddToDistribToNonUnitalNonAssocSemiringToMul.{u1} R _inst_1 c)
Case conversion may be inaccurate. Consider using '#align ring_con.mk' RingCon.mk'ₓ'. -/
/-- The natural homomorphism from a ring to its quotient by a congruence relation. -/
def mk' [NonAssocSemiring R] (c : RingCon R) : R →+* c.Quotient
    where
  toFun := Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align ring_con.mk' RingCon.mk'

end Quotient

end RingCon

