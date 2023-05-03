/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module data.sign
! leanprover-community/mathlib commit e46da4e335b8671848ac711ccb34b42538c0d800
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Data.Int.Lemmas
import Mathbin.Tactic.DeriveFintype

/-!
# Sign function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the sign function for types with zero and a decidable less-than relation, and
proves some basic theorems about it.
-/


#print SignType /-
/-- The type of signs. -/
inductive SignType
  | zero
  | neg
  | Pos
  deriving DecidableEq, Inhabited, Fintype
#align sign_type SignType
-/

namespace SignType

instance : Zero SignType :=
  ⟨zero⟩

instance : One SignType :=
  ⟨pos⟩

instance : Neg SignType :=
  ⟨fun s =>
    match s with
    | neg => pos
    | zero => zero
    | Pos => neg⟩

#print SignType.zero_eq_zero /-
@[simp]
theorem zero_eq_zero : zero = 0 :=
  rfl
#align sign_type.zero_eq_zero SignType.zero_eq_zero
-/

#print SignType.neg_eq_neg_one /-
@[simp]
theorem neg_eq_neg_one : neg = -1 :=
  rfl
#align sign_type.neg_eq_neg_one SignType.neg_eq_neg_one
-/

#print SignType.pos_eq_one /-
@[simp]
theorem pos_eq_one : pos = 1 :=
  rfl
#align sign_type.pos_eq_one SignType.pos_eq_one
-/

instance : Mul SignType :=
  ⟨fun x y =>
    match x with
    | neg => -y
    | zero => zero
    | Pos => y⟩

#print SignType.Le /-
/-- The less-than relation on signs. -/
inductive Le : SignType → SignType → Prop
  | of_neg (a) : le neg a
  | zero : le zero zero
  | of_pos (a) : le a pos
#align sign_type.le SignType.Le
-/

instance : LE SignType :=
  ⟨Le⟩

instance : DecidableRel Le := fun a b => by
  cases a <;> cases b <;> first |exact is_false (by rintro ⟨⟩)|exact is_true (by constructor)

/- We can define a `field` instance on `sign_type`, but it's not mathematically sensible,
so we only define the `comm_group_with_zero`. -/
instance : CommGroupWithZero SignType where
  zero := 0
  one := 1
  mul := (· * ·)
  inv := id
  mul_zero a := by cases a <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  mul_inv_cancel a ha := by cases a <;> trivial
  mul_comm a b := by casesm*_ <;> rfl
  mul_assoc a b c := by casesm*_ <;> rfl
  exists_pair_ne := ⟨0, 1, by rintro ⟨⟩⟩
  inv_zero := rfl

instance : LinearOrder SignType where
  le := (· ≤ ·)
  le_refl a := by cases a <;> constructor
  le_total a b := by casesm*_ <;> decide
  le_antisymm a b ha hb := by casesm*_ <;> rfl
  le_trans a b c hab hbc := by casesm*_ <;> constructor
  decidableLe := Le.decidableRel

instance : BoundedOrder SignType where
  top := 1
  le_top := Le.of_pos
  bot := -1
  bot_le := Le.of_neg

instance : HasDistribNeg SignType :=
  { SignType.hasNeg with
    neg_neg := fun x => by cases x <;> rfl
    neg_mul := fun x y => by casesm*_ <;> rfl
    mul_neg := fun x y => by casesm*_ <;> rfl }

#print SignType.fin3Equiv /-
/-- `sign_type` is equivalent to `fin 3`. -/
def fin3Equiv : SignType ≃* Fin 3
    where
  toFun a := a.recOn 0 (-1) 1
  invFun a :=
    match a with
    | ⟨0, h⟩ => 0
    | ⟨1, h⟩ => 1
    | ⟨2, h⟩ => -1
    | ⟨n + 3, h⟩ => (h.not_le le_add_self).elim
  left_inv a := by cases a <;> rfl
  right_inv a :=
    match a with
    | ⟨0, h⟩ => rfl
    | ⟨1, h⟩ => rfl
    | ⟨2, h⟩ => rfl
    | ⟨n + 3, h⟩ => (h.not_le le_add_self).elim
  map_mul' x y := by casesm*_ <;> rfl
#align sign_type.fin3_equiv SignType.fin3Equiv
-/

section CaseBashing

#print SignType.nonneg_iff /-
theorem nonneg_iff {a : SignType} : 0 ≤ a ↔ a = 0 ∨ a = 1 := by decide!
#align sign_type.nonneg_iff SignType.nonneg_iff
-/

#print SignType.nonneg_iff_ne_neg_one /-
theorem nonneg_iff_ne_neg_one {a : SignType} : 0 ≤ a ↔ a ≠ -1 := by decide!
#align sign_type.nonneg_iff_ne_neg_one SignType.nonneg_iff_ne_neg_one
-/

/- warning: sign_type.neg_one_lt_iff -> SignType.neg_one_lt_iff is a dubious translation:
lean 3 declaration is
  forall {a : SignType}, Iff (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (Neg.neg.{0} SignType SignType.hasNeg (OfNat.ofNat.{0} SignType 1 (OfNat.mk.{0} SignType 1 (One.one.{0} SignType SignType.hasOne)))) a) (LE.le.{0} SignType SignType.hasLe (OfNat.ofNat.{0} SignType 0 (OfNat.mk.{0} SignType 0 (Zero.zero.{0} SignType SignType.hasZero))) a)
but is expected to have type
  forall {a : SignType}, Iff (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType)))))) (Neg.neg.{0} SignType SignType.instNegSignType (OfNat.ofNat.{0} SignType 1 (One.toOfNat1.{0} SignType SignType.instOneSignType))) a) (LE.le.{0} SignType SignType.instLESignType (OfNat.ofNat.{0} SignType 0 (Zero.toOfNat0.{0} SignType SignType.instZeroSignType)) a)
Case conversion may be inaccurate. Consider using '#align sign_type.neg_one_lt_iff SignType.neg_one_lt_iffₓ'. -/
theorem neg_one_lt_iff {a : SignType} : -1 < a ↔ 0 ≤ a := by decide!
#align sign_type.neg_one_lt_iff SignType.neg_one_lt_iff

#print SignType.nonpos_iff /-
theorem nonpos_iff {a : SignType} : a ≤ 0 ↔ a = -1 ∨ a = 0 := by decide!
#align sign_type.nonpos_iff SignType.nonpos_iff
-/

#print SignType.nonpos_iff_ne_one /-
theorem nonpos_iff_ne_one {a : SignType} : a ≤ 0 ↔ a ≠ 1 := by decide!
#align sign_type.nonpos_iff_ne_one SignType.nonpos_iff_ne_one
-/

/- warning: sign_type.lt_one_iff -> SignType.lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {a : SignType}, Iff (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) a (OfNat.ofNat.{0} SignType 1 (OfNat.mk.{0} SignType 1 (One.one.{0} SignType SignType.hasOne)))) (LE.le.{0} SignType SignType.hasLe a (OfNat.ofNat.{0} SignType 0 (OfNat.mk.{0} SignType 0 (Zero.zero.{0} SignType SignType.hasZero))))
but is expected to have type
  forall {a : SignType}, Iff (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType)))))) a (OfNat.ofNat.{0} SignType 1 (One.toOfNat1.{0} SignType SignType.instOneSignType))) (LE.le.{0} SignType SignType.instLESignType a (OfNat.ofNat.{0} SignType 0 (Zero.toOfNat0.{0} SignType SignType.instZeroSignType)))
Case conversion may be inaccurate. Consider using '#align sign_type.lt_one_iff SignType.lt_one_iffₓ'. -/
theorem lt_one_iff {a : SignType} : a < 1 ↔ a ≤ 0 := by decide!
#align sign_type.lt_one_iff SignType.lt_one_iff

/- warning: sign_type.neg_iff -> SignType.neg_iff is a dubious translation:
lean 3 declaration is
  forall {a : SignType}, Iff (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) a (OfNat.ofNat.{0} SignType 0 (OfNat.mk.{0} SignType 0 (Zero.zero.{0} SignType SignType.hasZero)))) (Eq.{1} SignType a (Neg.neg.{0} SignType SignType.hasNeg (OfNat.ofNat.{0} SignType 1 (OfNat.mk.{0} SignType 1 (One.one.{0} SignType SignType.hasOne)))))
but is expected to have type
  forall {a : SignType}, Iff (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType)))))) a (OfNat.ofNat.{0} SignType 0 (Zero.toOfNat0.{0} SignType SignType.instZeroSignType))) (Eq.{1} SignType a (Neg.neg.{0} SignType SignType.instNegSignType (OfNat.ofNat.{0} SignType 1 (One.toOfNat1.{0} SignType SignType.instOneSignType))))
Case conversion may be inaccurate. Consider using '#align sign_type.neg_iff SignType.neg_iffₓ'. -/
@[simp]
theorem neg_iff {a : SignType} : a < 0 ↔ a = -1 := by decide!
#align sign_type.neg_iff SignType.neg_iff

#print SignType.le_neg_one_iff /-
@[simp]
theorem le_neg_one_iff {a : SignType} : a ≤ -1 ↔ a = -1 :=
  le_bot_iff
#align sign_type.le_neg_one_iff SignType.le_neg_one_iff
-/

/- warning: sign_type.pos_iff -> SignType.pos_iff is a dubious translation:
lean 3 declaration is
  forall {a : SignType}, Iff (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (OfNat.ofNat.{0} SignType 0 (OfNat.mk.{0} SignType 0 (Zero.zero.{0} SignType SignType.hasZero))) a) (Eq.{1} SignType a (OfNat.ofNat.{0} SignType 1 (OfNat.mk.{0} SignType 1 (One.one.{0} SignType SignType.hasOne))))
but is expected to have type
  forall {a : SignType}, Iff (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType)))))) (OfNat.ofNat.{0} SignType 0 (Zero.toOfNat0.{0} SignType SignType.instZeroSignType)) a) (Eq.{1} SignType a (OfNat.ofNat.{0} SignType 1 (One.toOfNat1.{0} SignType SignType.instOneSignType)))
Case conversion may be inaccurate. Consider using '#align sign_type.pos_iff SignType.pos_iffₓ'. -/
@[simp]
theorem pos_iff {a : SignType} : 0 < a ↔ a = 1 := by decide!
#align sign_type.pos_iff SignType.pos_iff

#print SignType.one_le_iff /-
@[simp]
theorem one_le_iff {a : SignType} : 1 ≤ a ↔ a = 1 :=
  top_le_iff
#align sign_type.one_le_iff SignType.one_le_iff
-/

#print SignType.neg_one_le /-
@[simp]
theorem neg_one_le (a : SignType) : -1 ≤ a :=
  bot_le
#align sign_type.neg_one_le SignType.neg_one_le
-/

#print SignType.le_one /-
@[simp]
theorem le_one (a : SignType) : a ≤ 1 :=
  le_top
#align sign_type.le_one SignType.le_one
-/

/- warning: sign_type.not_lt_neg_one -> SignType.not_lt_neg_one is a dubious translation:
lean 3 declaration is
  forall (a : SignType), Not (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) a (Neg.neg.{0} SignType SignType.hasNeg (OfNat.ofNat.{0} SignType 1 (OfNat.mk.{0} SignType 1 (One.one.{0} SignType SignType.hasOne)))))
but is expected to have type
  forall (a : SignType), Not (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType)))))) a (Neg.neg.{0} SignType SignType.instNegSignType (OfNat.ofNat.{0} SignType 1 (One.toOfNat1.{0} SignType SignType.instOneSignType))))
Case conversion may be inaccurate. Consider using '#align sign_type.not_lt_neg_one SignType.not_lt_neg_oneₓ'. -/
@[simp]
theorem not_lt_neg_one (a : SignType) : ¬a < -1 :=
  not_lt_bot
#align sign_type.not_lt_neg_one SignType.not_lt_neg_one

/- warning: sign_type.not_one_lt -> SignType.not_one_lt is a dubious translation:
lean 3 declaration is
  forall (a : SignType), Not (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (OfNat.ofNat.{0} SignType 1 (OfNat.mk.{0} SignType 1 (One.one.{0} SignType SignType.hasOne))) a)
but is expected to have type
  forall (a : SignType), Not (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType)))))) (OfNat.ofNat.{0} SignType 1 (One.toOfNat1.{0} SignType SignType.instOneSignType)) a)
Case conversion may be inaccurate. Consider using '#align sign_type.not_one_lt SignType.not_one_ltₓ'. -/
@[simp]
theorem not_one_lt (a : SignType) : ¬1 < a :=
  not_top_lt
#align sign_type.not_one_lt SignType.not_one_lt

#print SignType.self_eq_neg_iff /-
@[simp]
theorem self_eq_neg_iff (a : SignType) : a = -a ↔ a = 0 := by decide!
#align sign_type.self_eq_neg_iff SignType.self_eq_neg_iff
-/

#print SignType.neg_eq_self_iff /-
@[simp]
theorem neg_eq_self_iff (a : SignType) : -a = a ↔ a = 0 := by decide!
#align sign_type.neg_eq_self_iff SignType.neg_eq_self_iff
-/

/- warning: sign_type.neg_one_lt_one -> SignType.neg_one_lt_one is a dubious translation:
lean 3 declaration is
  LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (Neg.neg.{0} SignType SignType.hasNeg (OfNat.ofNat.{0} SignType 1 (OfNat.mk.{0} SignType 1 (One.one.{0} SignType SignType.hasOne)))) (OfNat.ofNat.{0} SignType 1 (OfNat.mk.{0} SignType 1 (One.one.{0} SignType SignType.hasOne)))
but is expected to have type
  LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType)))))) (Neg.neg.{0} SignType SignType.instNegSignType (OfNat.ofNat.{0} SignType 1 (One.toOfNat1.{0} SignType SignType.instOneSignType))) (OfNat.ofNat.{0} SignType 1 (One.toOfNat1.{0} SignType SignType.instOneSignType))
Case conversion may be inaccurate. Consider using '#align sign_type.neg_one_lt_one SignType.neg_one_lt_oneₓ'. -/
@[simp]
theorem neg_one_lt_one : (-1 : SignType) < 1 :=
  bot_lt_top
#align sign_type.neg_one_lt_one SignType.neg_one_lt_one

end CaseBashing

section cast

variable {α : Type _} [Zero α] [One α] [Neg α]

#print SignType.cast /-
/-- Turn a `sign_type` into zero, one, or minus one. This is a coercion instance, but note it is
only a `has_coe_t` instance: see note [use has_coe_t]. -/
def cast : SignType → α
  | zero => 0
  | Pos => 1
  | neg => -1
#align sign_type.cast SignType.cast
-/

instance : CoeTC SignType α :=
  ⟨cast⟩

@[simp]
theorem cast_eq_coe (a : SignType) : (cast a : α) = a :=
  rfl
#align sign_type.cast_eq_coe SignType.cast_eq_coe

#print SignType.coe_zero /-
@[simp]
theorem coe_zero : ↑(0 : SignType) = (0 : α) :=
  rfl
#align sign_type.coe_zero SignType.coe_zero
-/

#print SignType.coe_one /-
@[simp]
theorem coe_one : ↑(1 : SignType) = (1 : α) :=
  rfl
#align sign_type.coe_one SignType.coe_one
-/

#print SignType.coe_neg_one /-
@[simp]
theorem coe_neg_one : ↑(-1 : SignType) = (-1 : α) :=
  rfl
#align sign_type.coe_neg_one SignType.coe_neg_one
-/

end cast

/- warning: sign_type.cast_hom -> SignType.castHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_1))], MonoidWithZeroHom.{0, u1} SignType α (MonoidWithZero.toMulZeroOneClass.{0} SignType (GroupWithZero.toMonoidWithZero.{0} SignType (CommGroupWithZero.toGroupWithZero.{0} SignType SignType.commGroupWithZero))) _inst_1
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_1))], MonoidWithZeroHom.{0, u1} SignType α (MonoidWithZero.toMulZeroOneClass.{0} SignType (GroupWithZero.toMonoidWithZero.{0} SignType (CommGroupWithZero.toGroupWithZero.{0} SignType SignType.instCommGroupWithZeroSignType))) _inst_1
Case conversion may be inaccurate. Consider using '#align sign_type.cast_hom SignType.castHomₓ'. -/
/-- `sign_type.cast` as a `mul_with_zero_hom`. -/
@[simps]
def castHom {α} [MulZeroOneClass α] [HasDistribNeg α] : SignType →*₀ α
    where
  toFun := cast
  map_zero' := rfl
  map_one' := rfl
  map_mul' x y := by cases x <;> cases y <;> simp
#align sign_type.cast_hom SignType.castHom

#print SignType.range_eq /-
theorem range_eq {α} (f : SignType → α) : Set.range f = {f zero, f neg, f pos} := by
  classical simpa only [← Finset.coe_singleton, ← Finset.image_singleton, ← Fintype.coe_image_univ,
      Finset.coe_image, ← Set.image_insert_eq]
#align sign_type.range_eq SignType.range_eq
-/

end SignType

variable {α : Type _}

open SignType

section Preorder

variable [Zero α] [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)] {a : α}

/- warning: sign -> SignType.sign is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : DecidableRel.{succ u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))], OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Data.Sign._hyg.4987 : α) (x._@.Mathlib.Data.Sign._hyg.4989 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Data.Sign._hyg.4987 x._@.Mathlib.Data.Sign._hyg.4989)], OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType)))))
Case conversion may be inaccurate. Consider using '#align sign SignType.signₓ'. -/
/-- The sign of an element is 1 if it's positive, -1 if negative, 0 otherwise. -/
def SignType.sign : α →o SignType :=
  ⟨fun a => if 0 < a then 1 else if a < 0 then -1 else 0, fun a b h =>
    by
    dsimp
    split_ifs with h₁ h₂ h₃ h₄ _ _ h₂ h₃ <;> try constructor
    · cases lt_irrefl 0 (h₁.trans <| h.trans_lt h₃)
    · cases h₂ (h₁.trans_le h)
    · cases h₄ (h.trans_lt h₃)⟩
#align sign SignType.sign

#print sign_apply /-
theorem sign_apply : SignType.sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0) :=
  rfl
#align sign_apply sign_apply
-/

#print sign_zero /-
@[simp]
theorem sign_zero : SignType.sign (0 : α) = 0 := by simp [sign_apply]
#align sign_zero sign_zero
-/

#print sign_pos /-
@[simp]
theorem sign_pos (ha : 0 < a) : SignType.sign a = 1 := by rwa [sign_apply, if_pos]
#align sign_pos sign_pos
-/

#print sign_neg /-
@[simp]
theorem sign_neg (ha : a < 0) : SignType.sign a = -1 := by
  rwa [sign_apply, if_neg <| asymm ha, if_pos]
#align sign_neg sign_neg
-/

#print sign_eq_one_iff /-
theorem sign_eq_one_iff : SignType.sign a = 1 ↔ 0 < a :=
  by
  refine' ⟨fun h => _, fun h => sign_pos h⟩
  by_contra hn
  rw [sign_apply, if_neg hn] at h
  split_ifs  at h <;> simpa using h
#align sign_eq_one_iff sign_eq_one_iff
-/

#print sign_eq_neg_one_iff /-
theorem sign_eq_neg_one_iff : SignType.sign a = -1 ↔ a < 0 :=
  by
  refine' ⟨fun h => _, fun h => sign_neg h⟩
  rw [sign_apply] at h
  split_ifs  at h
  · simpa using h
  · exact h_2
  · simpa using h
#align sign_eq_neg_one_iff sign_eq_neg_one_iff
-/

end Preorder

section LinearOrder

variable [Zero α] [LinearOrder α] {a : α}

#print sign_eq_zero_iff /-
@[simp]
theorem sign_eq_zero_iff : SignType.sign a = 0 ↔ a = 0 :=
  by
  refine' ⟨fun h => _, fun h => h.symm ▸ sign_zero⟩
  rw [sign_apply] at h
  split_ifs  at h <;> cases h
  exact (le_of_not_lt h_1).eq_of_not_lt h_2
#align sign_eq_zero_iff sign_eq_zero_iff
-/

#print sign_ne_zero /-
theorem sign_ne_zero : SignType.sign a ≠ 0 ↔ a ≠ 0 :=
  sign_eq_zero_iff.Not
#align sign_ne_zero sign_ne_zero
-/

#print sign_nonneg_iff /-
@[simp]
theorem sign_nonneg_iff : 0 ≤ SignType.sign a ↔ 0 ≤ a :=
  by
  rcases lt_trichotomy 0 a with (h | rfl | h)
  · simp [h, h.le]
  · simp
  · simpa [h, h.not_le]
#align sign_nonneg_iff sign_nonneg_iff
-/

#print sign_nonpos_iff /-
@[simp]
theorem sign_nonpos_iff : SignType.sign a ≤ 0 ↔ a ≤ 0 :=
  by
  rcases lt_trichotomy 0 a with (h | rfl | h)
  · simp [h, h.not_le]
  · simp
  · simp [h, h.le]
#align sign_nonpos_iff sign_nonpos_iff
-/

end LinearOrder

section OrderedSemiring

variable [OrderedSemiring α] [DecidableRel ((· < ·) : α → α → Prop)] [Nontrivial α]

/- warning: sign_one -> sign_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))))] [_inst_3 : Nontrivial.{u1} α], Eq.{1} SignType (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))))))) (OfNat.ofNat.{0} SignType 1 (OfNat.mk.{0} SignType 1 (One.one.{0} SignType SignType.hasOne)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Data.Sign._hyg.5946 : α) (x._@.Mathlib.Data.Sign._hyg.5948 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Data.Sign._hyg.5946 x._@.Mathlib.Data.Sign._hyg.5948)] [_inst_3 : Nontrivial.{u1} α], Eq.{1} SignType (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1)) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1)) (fun (a : α) (b : α) => _inst_2 a b)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{0} SignType 1 (One.toOfNat1.{0} SignType SignType.instOneSignType))
Case conversion may be inaccurate. Consider using '#align sign_one sign_oneₓ'. -/
@[simp]
theorem sign_one : SignType.sign (1 : α) = 1 :=
  sign_pos zero_lt_one
#align sign_one sign_one

end OrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing α] {a b : α}

/- I'm not sure why this is necessary, see https://leanprover.zulipchat.com/#narrow/stream/
113488-general/topic/type.20class.20inference.20issues/near/276937942 -/
attribute [local instance] LinearOrderedRing.decidableLt

/- warning: sign_mul -> sign_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (x : α) (y : α), Eq.{1} SignType (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (fun (a : α) (b : α) => LinearOrderedRing.decidableLt.{u1} α _inst_1 a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) x y)) (HMul.hMul.{0, 0, 0} SignType SignType SignType (instHMul.{0} SignType SignType.hasMul) (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (fun (a : α) (b : α) => LinearOrderedRing.decidableLt.{u1} α _inst_1 a b)) x) (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (fun (a : α) (b : α) => LinearOrderedRing.decidableLt.{u1} α _inst_1 a b)) y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (x : α) (y : α), Eq.{1} SignType (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (fun (a : α) (b : α) => LinearOrderedRing.decidable_lt.{u1} α _inst_1 a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) x y)) (HMul.hMul.{0, 0, 0} SignType SignType SignType (instHMul.{0} SignType SignType.instMulSignType) (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (fun (a : α) (b : α) => LinearOrderedRing.decidable_lt.{u1} α _inst_1 a b)) x) (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (fun (a : α) (b : α) => LinearOrderedRing.decidable_lt.{u1} α _inst_1 a b)) y))
Case conversion may be inaccurate. Consider using '#align sign_mul sign_mulₓ'. -/
theorem sign_mul (x y : α) : SignType.sign (x * y) = SignType.sign x * SignType.sign y := by
  rcases lt_trichotomy x 0 with (hx | hx | hx) <;> rcases lt_trichotomy y 0 with (hy | hy | hy) <;>
    simp only [sign_zero, MulZeroClass.mul_zero, MulZeroClass.zero_mul, sign_pos, sign_neg, hx, hy,
      mul_one, neg_one_mul, neg_neg, one_mul, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos,
      neg_zero, mul_neg_of_pos_of_neg, mul_pos]
#align sign_mul sign_mul

/- warning: sign_hom -> signHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α], MonoidWithZeroHom.{u1, 0} α SignType (NonAssocSemiring.toMulZeroOneClass.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) (MonoidWithZero.toMulZeroOneClass.{0} SignType (GroupWithZero.toMonoidWithZero.{0} SignType (CommGroupWithZero.toGroupWithZero.{0} SignType SignType.commGroupWithZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α], MonoidWithZeroHom.{u1, 0} α SignType (NonAssocSemiring.toMulZeroOneClass.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) (MonoidWithZero.toMulZeroOneClass.{0} SignType (GroupWithZero.toMonoidWithZero.{0} SignType (CommGroupWithZero.toGroupWithZero.{0} SignType SignType.instCommGroupWithZeroSignType)))
Case conversion may be inaccurate. Consider using '#align sign_hom signHomₓ'. -/
/-- `sign` as a `monoid_with_zero_hom` for a nontrivial ordered semiring. Note that linearity
is required; consider ℂ with the order `z ≤ w` iff they have the same imaginary part and
`z - w ≤ 0` in the reals; then `1 + i` and `1 - i` are incomparable to zero, and thus we have:
`0 * 0 = sign (1 + i) * sign (1 - i) ≠ sign 2 = 1`. (`complex.ordered_comm_ring`) -/
def signHom : α →*₀ SignType where
  toFun := SignType.sign
  map_zero' := sign_zero
  map_one' := sign_one
  map_mul' := sign_mul
#align sign_hom signHom

/- warning: sign_pow -> sign_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (x : α) (n : Nat), Eq.{1} SignType (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (fun (a : α) (b : α) => LinearOrderedRing.decidableLt.{u1} α _inst_1 a b)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) x n)) (HPow.hPow.{0, 0, 0} SignType Nat SignType (instHPow.{0, 0} SignType Nat (Monoid.Pow.{0} SignType (MonoidWithZero.toMonoid.{0} SignType (GroupWithZero.toMonoidWithZero.{0} SignType (CommGroupWithZero.toGroupWithZero.{0} SignType SignType.commGroupWithZero))))) (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (fun (a : α) (b : α) => LinearOrderedRing.decidableLt.{u1} α _inst_1 a b)) x) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (x : α) (n : Nat), Eq.{1} SignType (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (fun (a : α) (b : α) => LinearOrderedRing.decidable_lt.{u1} α _inst_1 a b)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1))))))) x n)) (HPow.hPow.{0, 0, 0} SignType Nat SignType (instHPow.{0, 0} SignType Nat (Monoid.Pow.{0} SignType (MonoidWithZero.toMonoid.{0} SignType (GroupWithZero.toMonoidWithZero.{0} SignType (CommGroupWithZero.toGroupWithZero.{0} SignType SignType.instCommGroupWithZeroSignType))))) (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (fun (a : α) (b : α) => LinearOrderedRing.decidable_lt.{u1} α _inst_1 a b)) x) n)
Case conversion may be inaccurate. Consider using '#align sign_pow sign_powₓ'. -/
theorem sign_pow (x : α) (n : ℕ) : SignType.sign (x ^ n) = SignType.sign x ^ n :=
  by
  change signHom (x ^ n) = signHom x ^ n
  exact map_pow _ _ _
#align sign_pow sign_pow

end LinearOrderedRing

section AddGroup

variable [AddGroup α] [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)]

/- warning: left.sign_neg -> Left.sign_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : DecidableRel.{succ u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] (a : α), Eq.{1} SignType (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))) _inst_2 (fun (a : α) (b : α) => _inst_3 a b)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) a)) (Neg.neg.{0} SignType SignType.hasNeg (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))) _inst_2 (fun (a : α) (b : α) => _inst_3 a b)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Data.Sign._hyg.6467 : α) (x._@.Mathlib.Data.Sign._hyg.6469 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Data.Sign._hyg.6467 x._@.Mathlib.Data.Sign._hyg.6469)] [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Data.Sign._hyg.6486 : α) (x._@.Mathlib.Data.Sign._hyg.6488 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Sign._hyg.6486 x._@.Mathlib.Data.Sign._hyg.6488) (fun (x._@.Mathlib.Data.Sign._hyg.6501 : α) (x._@.Mathlib.Data.Sign._hyg.6503 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Data.Sign._hyg.6501 x._@.Mathlib.Data.Sign._hyg.6503)] (a : α), Eq.{1} SignType (OrderHom.toFun.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) _inst_2 (fun (a : α) (b : α) => _inst_3 a b)) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) a)) (Neg.neg.{0} SignType SignType.instNegSignType (OrderHom.toFun.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) _inst_2 (fun (a : α) (b : α) => _inst_3 a b)) a))
Case conversion may be inaccurate. Consider using '#align left.sign_neg Left.sign_negₓ'. -/
theorem Left.sign_neg [CovariantClass α α (· + ·) (· < ·)] (a : α) :
    SignType.sign (-a) = -SignType.sign a :=
  by
  simp_rw [sign_apply, Left.neg_pos_iff, Left.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp
#align left.sign_neg Left.sign_neg

/- warning: right.sign_neg -> Right.sign_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : DecidableRel.{succ u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] (a : α), Eq.{1} SignType (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))) _inst_2 (fun (a : α) (b : α) => _inst_3 a b)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) a)) (Neg.neg.{0} SignType SignType.hasNeg (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))) _inst_2 (fun (a : α) (b : α) => _inst_3 a b)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Data.Sign._hyg.6585 : α) (x._@.Mathlib.Data.Sign._hyg.6587 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Data.Sign._hyg.6585 x._@.Mathlib.Data.Sign._hyg.6587)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Data.Sign._hyg.6607 : α) (x._@.Mathlib.Data.Sign._hyg.6609 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Sign._hyg.6607 x._@.Mathlib.Data.Sign._hyg.6609)) (fun (x._@.Mathlib.Data.Sign._hyg.6622 : α) (x._@.Mathlib.Data.Sign._hyg.6624 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Data.Sign._hyg.6622 x._@.Mathlib.Data.Sign._hyg.6624)] (a : α), Eq.{1} SignType (OrderHom.toFun.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) _inst_2 (fun (a : α) (b : α) => _inst_3 a b)) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) a)) (Neg.neg.{0} SignType SignType.instNegSignType (OrderHom.toFun.{u1, 0} α SignType _inst_2 (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) _inst_2 (fun (a : α) (b : α) => _inst_3 a b)) a))
Case conversion may be inaccurate. Consider using '#align right.sign_neg Right.sign_negₓ'. -/
theorem Right.sign_neg [CovariantClass α α (Function.swap (· + ·)) (· < ·)] (a : α) :
    SignType.sign (-a) = -SignType.sign a :=
  by
  simp_rw [sign_apply, Right.neg_pos_iff, Right.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp
#align right.sign_neg Right.sign_neg

end AddGroup

section LinearOrderedAddCommGroup

open BigOperators

variable [LinearOrderedAddCommGroup α]

/- I'm not sure why this is necessary, see
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Decidable.20vs.20decidable_rel -/
attribute [local instance] LinearOrderedAddCommGroup.decidableLt

/- warning: sign_sum -> sign_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedAddCommGroup.{u1} α] {ι : Type.{u2}} {s : Finset.{u2} ι} {f : ι -> α}, (Finset.Nonempty.{u2} ι s) -> (forall (t : SignType), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Eq.{1} SignType (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (fun (a : α) (b : α) => LinearOrderedAddCommGroup.decidableLt.{u1} α _inst_1 a b)) (f i)) t)) -> (Eq.{1} SignType (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (fun (a : α) (b : α) => LinearOrderedAddCommGroup.decidableLt.{u1} α _inst_1 a b)) (Finset.sum.{u1, u2} α ι (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) s (fun (i : ι) => f i))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedAddCommGroup.{u1} α] {ι : Type.{u2}} {s : Finset.{u2} ι} {f : ι -> α}, (Finset.Nonempty.{u2} ι s) -> (forall (t : SignType), (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{1} SignType (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (fun (a : α) (b : α) => LinearOrderedAddCommGroup.decidable_lt.{u1} α _inst_1 a b)) (f i)) t)) -> (Eq.{1} SignType (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (fun (a : α) (b : α) => LinearOrderedAddCommGroup.decidable_lt.{u1} α _inst_1 a b)) (Finset.sum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u1} α _inst_1))) s (fun (i : ι) => f i))) t))
Case conversion may be inaccurate. Consider using '#align sign_sum sign_sumₓ'. -/
theorem sign_sum {ι : Type _} {s : Finset ι} {f : ι → α} (hs : s.Nonempty) (t : SignType)
    (h : ∀ i ∈ s, SignType.sign (f i) = t) : SignType.sign (∑ i in s, f i) = t :=
  by
  cases t
  · simp_rw [zero_eq_zero, sign_eq_zero_iff] at h⊢
    exact Finset.sum_eq_zero h
  · simp_rw [neg_eq_neg_one, sign_eq_neg_one_iff] at h⊢
    exact Finset.sum_neg h hs
  · simp_rw [pos_eq_one, sign_eq_one_iff] at h⊢
    exact Finset.sum_pos h hs
#align sign_sum sign_sum

end LinearOrderedAddCommGroup

namespace Int

#print Int.sign_eq_sign /-
theorem sign_eq_sign (n : ℤ) : n.sign = SignType.sign n :=
  by
  obtain (_ | _) | _ := n
  · exact congr_arg coe sign_zero.symm
  · exact congr_arg coe (sign_pos <| Int.succ_coe_nat_pos _).symm
  · exact congr_arg coe (_root_.sign_neg <| neg_succ_lt_zero _).symm
#align int.sign_eq_sign Int.sign_eq_sign
-/

end Int

open Finset Nat

open BigOperators

private theorem exists_signed_sum_aux [DecidableEq α] (s : Finset α) (f : α → ℤ) :
    ∃ (β : Type u_1)(t : Finset β)(sgn : β → SignType)(g : β → α),
      (∀ b, g b ∈ s) ∧
        (t.card = ∑ a in s, (f a).natAbs) ∧
          ∀ a ∈ s, (∑ b in t, if g b = a then (sgn b : ℤ) else 0) = f a :=
  by
  refine'
    ⟨Σa : { x // x ∈ s }, ℕ, finset.univ.sigma fun a => range (f a).natAbs, fun a =>
      SignType.sign (f a.1), fun a => a.1, fun a => a.1.Prop, _, _⟩
  · simp [@sum_attach _ _ _ _ fun a => (f a).natAbs]
  · intro x hx
    simp [sum_sigma, hx, ← Int.sign_eq_sign, Int.sign_mul_abs, mul_comm (|f _|),
      @sum_attach _ _ _ _ fun a => ∑ j in range (f a).natAbs, if a = x then (f a).sign else 0]
#align exists_signed_sum_aux exists_signed_sum_aux

/- warning: exists_signed_sum -> exists_signed_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (f : α -> Int), Exists.{succ (succ u1)} Type.{u1} (fun (β : Type.{u1}) => Exists.{succ u1} (Fintype.{u1} β) (fun (_x : Fintype.{u1} β) => Exists.{succ u1} (β -> SignType) (fun (sgn : β -> SignType) => Exists.{succ u1} (β -> α) (fun (g : β -> α) => And (forall (b : β), Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (g b) s) (And (Eq.{1} Nat (Fintype.card.{u1} β _x) (Finset.sum.{0, u1} Nat α Nat.addCommMonoid s (fun (a : α) => Int.natAbs (f a)))) (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Eq.{1} Int (Finset.sum.{0, u1} Int β Int.addCommMonoid (Finset.univ.{u1} β _x) (fun (b : β) => ite.{1} Int (Eq.{succ u1} α (g b) a) (_inst_1 (g b) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) SignType Int (HasLiftT.mk.{1, 1} SignType Int (CoeTCₓ.coe.{1, 1} SignType Int (SignType.hasCoeT.{0} Int Int.hasZero Int.hasOne Int.hasNeg))) (sgn b)) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))) (f a))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (f : α -> Int), Exists.{succ (succ u1)} Type.{u1} (fun (β : Type.{u1}) => Exists.{succ u1} (Fintype.{u1} β) (fun (_x : Fintype.{u1} β) => Exists.{succ u1} (β -> SignType) (fun (sgn : β -> SignType) => Exists.{succ u1} (β -> α) (fun (g : β -> α) => And (forall (b : β), Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (g b) s) (And (Eq.{1} Nat (Fintype.card.{u1} β _x) (Finset.sum.{0, u1} Nat α Nat.addCommMonoid s (fun (a : α) => Int.natAbs (f a)))) (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Eq.{1} Int (Finset.sum.{0, u1} Int β Int.instAddCommMonoidInt (Finset.univ.{u1} β _x) (fun (b : β) => ite.{1} Int (Eq.{succ u1} α (g b) a) (_inst_1 (g b) a) (SignType.cast.{0} Int (CommMonoidWithZero.toZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (NonAssocRing.toOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.instNegInt (sgn b)) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))) (f a))))))))
Case conversion may be inaccurate. Consider using '#align exists_signed_sum exists_signed_sumₓ'. -/
/-- We can decompose a sum of absolute value `n` into a sum of `n` signs. -/
theorem exists_signed_sum [DecidableEq α] (s : Finset α) (f : α → ℤ) :
    ∃ (β : Type u_1)(_ : Fintype β)(sgn : β → SignType)(g : β → α),
      (∀ b, g b ∈ s) ∧
        (Fintype.card β = ∑ a in s, (f a).natAbs) ∧
          ∀ a ∈ s, (∑ b, if g b = a then (sgn b : ℤ) else 0) = f a :=
  let ⟨β, t, sgn, g, hg, ht, hf⟩ := exists_signed_sum_aux s f
  ⟨t, inferInstance, fun b => sgn b, fun b => g b, fun b => hg b, by simp [ht], fun a ha =>
    (@sum_attach _ _ t _ fun b => ite (g b = a) (sgn b : ℤ) 0).trans <| hf _ ha⟩
#align exists_signed_sum exists_signed_sum

/- warning: exists_signed_sum' -> exists_signed_sum' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (f : α -> Int) (n : Nat), (LE.le.{0} Nat Nat.hasLe (Finset.sum.{0, u1} Nat α Nat.addCommMonoid s (fun (i : α) => Int.natAbs (f i))) n) -> (Exists.{succ (succ u1)} Type.{u1} (fun (β : Type.{u1}) => Exists.{succ u1} (Fintype.{u1} β) (fun (_x : Fintype.{u1} β) => Exists.{succ u1} (β -> SignType) (fun (sgn : β -> SignType) => Exists.{succ u1} (β -> α) (fun (g : β -> α) => And (forall (b : β), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (g b) s)) -> (Eq.{1} SignType (sgn b) (OfNat.ofNat.{0} SignType 0 (OfNat.mk.{0} SignType 0 (Zero.zero.{0} SignType SignType.hasZero))))) (And (Eq.{1} Nat (Fintype.card.{u1} β _x) n) (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Eq.{1} Int (Finset.sum.{0, u1} Int β Int.addCommMonoid (Finset.univ.{u1} β _x) (fun (i : β) => ite.{1} Int (Eq.{succ u1} α (g i) a) (_inst_2 (g i) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) SignType Int (HasLiftT.mk.{1, 1} SignType Int (CoeTCₓ.coe.{1, 1} SignType Int (SignType.hasCoeT.{0} Int Int.hasZero Int.hasOne Int.hasNeg))) (sgn i)) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))) (f a)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (f : α -> Int) (n : Nat), (LE.le.{0} Nat instLENat (Finset.sum.{0, u1} Nat α Nat.addCommMonoid s (fun (i : α) => Int.natAbs (f i))) n) -> (Exists.{succ (succ u1)} Type.{u1} (fun (β : Type.{u1}) => Exists.{succ u1} (Fintype.{u1} β) (fun (_x : Fintype.{u1} β) => Exists.{succ u1} (β -> SignType) (fun (sgn : β -> SignType) => Exists.{succ u1} (β -> α) (fun (g : β -> α) => And (forall (b : β), (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (g b) s)) -> (Eq.{1} SignType (sgn b) (OfNat.ofNat.{0} SignType 0 (Zero.toOfNat0.{0} SignType SignType.instZeroSignType)))) (And (Eq.{1} Nat (Fintype.card.{u1} β _x) n) (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Eq.{1} Int (Finset.sum.{0, u1} Int β Int.instAddCommMonoidInt (Finset.univ.{u1} β _x) (fun (i : β) => ite.{1} Int (Eq.{succ u1} α (g i) a) (_inst_2 (g i) a) (SignType.cast.{0} Int (CommMonoidWithZero.toZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (NonAssocRing.toOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.instNegInt (sgn i)) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))) (f a)))))))))
Case conversion may be inaccurate. Consider using '#align exists_signed_sum' exists_signed_sum'ₓ'. -/
/-- We can decompose a sum of absolute value less than `n` into a sum of at most `n` signs. -/
theorem exists_signed_sum' [Nonempty α] [DecidableEq α] (s : Finset α) (f : α → ℤ) (n : ℕ)
    (h : (∑ i in s, (f i).natAbs) ≤ n) :
    ∃ (β : Type u_1)(_ : Fintype β)(sgn : β → SignType)(g : β → α),
      (∀ b, g b ∉ s → sgn b = 0) ∧
        Fintype.card β = n ∧ ∀ a ∈ s, (∑ i, if g i = a then (sgn i : ℤ) else 0) = f a :=
  by
  obtain ⟨β, _, sgn, g, hg, hβ, hf⟩ := exists_signed_sum s f
  skip
  refine'
    ⟨Sum β (Fin (n - ∑ i in s, (f i).natAbs)), inferInstance, Sum.elim sgn 0,
      Sum.elim g <| Classical.arbitrary _, _, by simp [hβ, h], fun a ha => by simp [hf _ ha]⟩
  rintro (b | b) hb
  · cases hb (hg _)
  · rfl
#align exists_signed_sum' exists_signed_sum'

