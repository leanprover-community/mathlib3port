/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn

! This file was ported from Lean 3 source module data.set.mul_antidiagonal
! leanprover-community/mathlib commit b6da1a0b3e7cd83b1f744c49ce48ef8c6307d2f6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.WellFoundedSet

/-! # Multiplication antidiagonal 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


namespace Set

variable {α : Type _}

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ : Set α} {a : α} {x : α × α}

#print Set.mulAntidiagonal /-
/-- `set.mul_antidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that multiply to `a`. -/
@[to_additive
      "`set.add_antidiagonal s t a` is the set of all pairs of an element in `s` and an\nelement in `t` that add to `a`."]
def mulAntidiagonal (s t : Set α) (a : α) : Set (α × α) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a }
#align set.mul_antidiagonal Set.mulAntidiagonal
#align set.add_antidiagonal Set.addAntidiagonal
-/

#print Set.mem_mulAntidiagonal /-
@[simp, to_additive]
theorem mem_mulAntidiagonal : x ∈ mulAntidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a :=
  Iff.rfl
#align set.mem_mul_antidiagonal Set.mem_mulAntidiagonal
#align set.mem_add_antidiagonal Set.mem_addAntidiagonal
-/

#print Set.mulAntidiagonal_mono_left /-
@[to_additive]
theorem mulAntidiagonal_mono_left (h : s₁ ⊆ s₂) : mulAntidiagonal s₁ t a ⊆ mulAntidiagonal s₂ t a :=
  fun x hx => ⟨h hx.1, hx.2.1, hx.2.2⟩
#align set.mul_antidiagonal_mono_left Set.mulAntidiagonal_mono_left
#align set.add_antidiagonal_mono_left Set.addAntidiagonal_mono_left
-/

#print Set.mulAntidiagonal_mono_right /-
@[to_additive]
theorem mulAntidiagonal_mono_right (h : t₁ ⊆ t₂) :
    mulAntidiagonal s t₁ a ⊆ mulAntidiagonal s t₂ a := fun x hx => ⟨hx.1, h hx.2.1, hx.2.2⟩
#align set.mul_antidiagonal_mono_right Set.mulAntidiagonal_mono_right
#align set.add_antidiagonal_mono_right Set.addAntidiagonal_mono_right
-/

end Mul

/- warning: set.swap_mem_mul_antidiagonal -> Set.swap_mem_mulAntidiagonal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {x : Prod.{u1, u1} α α}, Iff (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.swap.{u1, u1} α α x) (Set.mulAntidiagonal.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) s t a)) (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) t s a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {x : Prod.{u1, u1} α α}, Iff (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.swap.{u1, u1} α α x) (Set.mulAntidiagonal.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) s t a)) (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) t s a))
Case conversion may be inaccurate. Consider using '#align set.swap_mem_mul_antidiagonal Set.swap_mem_mulAntidiagonalₓ'. -/
@[simp, to_additive]
theorem swap_mem_mulAntidiagonal [CommSemigroup α] {s t : Set α} {a : α} {x : α × α} :
    x.symm ∈ Set.mulAntidiagonal s t a ↔ x ∈ Set.mulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]
#align set.swap_mem_mul_antidiagonal Set.swap_mem_mulAntidiagonal
#align set.swap_mem_add_antidiagonal Set.swap_mem_addAntidiagonal

namespace MulAntidiagonal

section CancelCommMonoid

variable [CancelCommMonoid α] {s t : Set α} {a : α} {x y : mulAntidiagonal s t a}

/- warning: set.mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd -> Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align set.mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_sndₓ'. -/
@[to_additive]
theorem fst_eq_fst_iff_snd_eq_snd : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2 :=
  ⟨fun h => mul_left_cancel (y.Prop.2.2.trans <| by rw [← h]; exact x.2.2.2.symm).symm, fun h =>
    mul_right_cancel (y.Prop.2.2.trans <| by rw [← h]; exact x.2.2.2.symm).symm⟩
#align set.mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_snd
#align set.add_antidiagonal.fst_eq_fst_iff_snd_eq_snd Set.AddAntidiagonal.fst_eq_fst_iff_snd_eq_snd

/- warning: set.mul_antidiagonal.eq_of_fst_eq_fst -> Set.MulAntidiagonal.eq_of_fst_eq_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)} {y : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)}, (Eq.{succ u1} α (Prod.fst.{u1, u1} α α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (coeSubtype.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)))))) x)) (Prod.fst.{u1, u1} α α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (coeSubtype.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)))))) y))) -> (Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {x : Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)} {y : Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)}, (Eq.{succ u1} α (Prod.fst.{u1, u1} α α (Subtype.val.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) x)) (Prod.fst.{u1, u1} α α (Subtype.val.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) y))) -> (Eq.{succ u1} (Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) x y)
Case conversion may be inaccurate. Consider using '#align set.mul_antidiagonal.eq_of_fst_eq_fst Set.MulAntidiagonal.eq_of_fst_eq_fstₓ'. -/
@[to_additive]
theorem eq_of_fst_eq_fst (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h
#align set.mul_antidiagonal.eq_of_fst_eq_fst Set.MulAntidiagonal.eq_of_fst_eq_fst
#align set.add_antidiagonal.eq_of_fst_eq_fst Set.AddAntidiagonal.eq_of_fst_eq_fst

/- warning: set.mul_antidiagonal.eq_of_snd_eq_snd -> Set.MulAntidiagonal.eq_of_snd_eq_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)} {y : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)}, (Eq.{succ u1} α (Prod.snd.{u1, u1} α α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (coeSubtype.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)))))) x)) (Prod.snd.{u1, u1} α α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) (Prod.{u1, u1} α α) (coeSubtype.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)))))) y))) -> (Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {x : Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)} {y : Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)}, (Eq.{succ u1} α (Prod.snd.{u1, u1} α α (Subtype.val.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) x)) (Prod.snd.{u1, u1} α α (Subtype.val.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) x (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) y))) -> (Eq.{succ u1} (Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α _inst_1))))) s t a)) x y)
Case conversion may be inaccurate. Consider using '#align set.mul_antidiagonal.eq_of_snd_eq_snd Set.MulAntidiagonal.eq_of_snd_eq_sndₓ'. -/
@[to_additive]
theorem eq_of_snd_eq_snd (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h
#align set.mul_antidiagonal.eq_of_snd_eq_snd Set.MulAntidiagonal.eq_of_snd_eq_snd
#align set.add_antidiagonal.eq_of_snd_eq_snd Set.AddAntidiagonal.eq_of_snd_eq_snd

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] (s t : Set α) (a : α) {x y : mulAntidiagonal s t a}

/- warning: set.mul_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd -> Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align set.mul_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_sndₓ'. -/
@[to_additive]
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × α).1 ≤ (y : α × α).1)
    (h₂ : (x : α × α).2 ≤ (y : α × α).2) : x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (mul_lt_mul_of_lt_of_le hlt h₂).Ne <|
        (mem_mulAntidiagonal.1 x.2).2.2.trans (mem_mulAntidiagonal.1 y.2).2.2.symm
#align set.mul_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd
#align set.add_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd

variable {s t}

/- warning: set.mul_antidiagonal.finite_of_is_pwo -> Set.MulAntidiagonal.finite_of_isPwo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.IsPwo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1)) s) -> (Set.IsPwo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1)) t) -> (forall (a : α), Set.Finite.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))))) s t a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.IsPwo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1)) s) -> (Set.IsPwo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1)) t) -> (forall (a : α), Set.Finite.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))))) s t a))
Case conversion may be inaccurate. Consider using '#align set.mul_antidiagonal.finite_of_is_pwo Set.MulAntidiagonal.finite_of_isPwoₓ'. -/
@[to_additive]
theorem finite_of_isPwo (hs : s.IsPwo) (ht : t.IsPwo) (a) : (mulAntidiagonal s t a).Finite :=
  by
  refine' not_infinite.1 fun h => _
  have h1 : (mul_antidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) := fun f hf =>
    hs (Prod.fst ∘ f) fun n => (mem_mul_antidiagonal.1 (hf n)).1
  have h2 : (mul_antidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) := fun f hf =>
    ht (Prod.snd ∘ f) fun n => (mem_mul_antidiagonal.1 (hf n)).2.1
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq (fun n => h.nat_embedding _ n) fun n => (h.nat_embedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 (fun x => (h.nat_embedding _) (g x)) fun n => (h.nat_embedding _ _).2
  refine' mn.ne (g.injective <| (h.nat_embedding _).Injective _)
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2'
#align set.mul_antidiagonal.finite_of_is_pwo Set.MulAntidiagonal.finite_of_isPwo
#align set.add_antidiagonal.finite_of_is_pwo Set.AddAntidiagonal.finite_of_isPwo

end OrderedCancelCommMonoid

/- warning: set.mul_antidiagonal.finite_of_is_wf -> Set.MulAntidiagonal.finite_of_isWf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCancelCommMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.IsWf.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1)))) s) -> (Set.IsWf.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1)))) t) -> (forall (a : α), Set.Finite.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1))))))) s t a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCancelCommMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.IsWf.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1)))) s) -> (Set.IsWf.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1)))) t) -> (forall (a : α), Set.Finite.{u1} (Prod.{u1, u1} α α) (Set.mulAntidiagonal.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1))))))) s t a))
Case conversion may be inaccurate. Consider using '#align set.mul_antidiagonal.finite_of_is_wf Set.MulAntidiagonal.finite_of_isWfₓ'. -/
@[to_additive]
theorem finite_of_isWf [LinearOrderedCancelCommMonoid α] {s t : Set α} (hs : s.IsWf) (ht : t.IsWf)
    (a) : (mulAntidiagonal s t a).Finite :=
  finite_of_isPwo hs.IsPwo ht.IsPwo a
#align set.mul_antidiagonal.finite_of_is_wf Set.MulAntidiagonal.finite_of_isWf
#align set.add_antidiagonal.finite_of_is_wf Set.AddAntidiagonal.finite_of_isWf

end MulAntidiagonal

end Set

