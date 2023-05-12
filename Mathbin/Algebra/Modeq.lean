/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.modeq
! leanprover-community/mathlib commit a07d750983b94c530ab69a726862c2ab6802b38c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Modeq
import Mathbin.GroupTheory.QuotientGroup

/-!
# Equality modulo an element

This file defines equality modulo an element in a commutative group.

## Main definitions

* `a ≡ b [PMOD p]`: `a` and `b` are congruent modulo a`p`.

## See also

`smodeq` is a generalisation to arbitrary submodules.

## TODO

Delete `int.modeq` in favour of `add_comm_group.modeq`. Generalise `smodeq` to `add_subgroup` and
redefine `add_comm_group.modeq` using it. Once this is done, we can rename `add_comm_group.modeq`
to `add_subgroup.modeq` and multiplicativise it. Longer term, we could generalise to submonoids and
also unify with `nat.modeq`.
-/


namespace AddCommGroup

variable {α : Type _}

section AddCommGroup

variable [AddCommGroup α] {p a a₁ a₂ b b₁ b₂ c : α} {n : ℕ} {z : ℤ}

#print AddCommGroup.ModEq /-
/-- `a ≡ b [PMOD p]` means that `b` is congruent to `a` modulo `p`.

Equivalently (as shown in `algebra.order.to_interval_mod`), `b` does not lie in the open interval
`(a, a + p)` modulo `p`, or `to_Ico_mod hp a` disagrees with `to_Ioc_mod hp a` at `b`, or
`to_Ico_div hp a` disagrees with `to_Ioc_div hp a` at `b`. -/
def ModEq (p a b : α) : Prop :=
  ∃ z : ℤ, b - a = z • p
#align add_comm_group.modeq AddCommGroup.ModEq
-/

-- mathport name: «expr ≡ [PMOD ]»
notation:50 a " ≡ " b " [PMOD " p "]" => ModEq p a b

#print AddCommGroup.modEq_refl /-
@[refl, simp]
theorem modEq_refl (a : α) : a ≡ a [PMOD p] :=
  ⟨0, by simp⟩
#align add_comm_group.modeq_refl AddCommGroup.modEq_refl
-/

#print AddCommGroup.modEq_rfl /-
theorem modEq_rfl : a ≡ a [PMOD p] :=
  modEq_refl _
#align add_comm_group.modeq_rfl AddCommGroup.modEq_rfl
-/

#print AddCommGroup.modEq_comm /-
theorem modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p] :=
  (Equiv.neg _).exists_congr_left.trans <| by simp [modeq, ← neg_eq_iff_eq_neg]
#align add_comm_group.modeq_comm AddCommGroup.modEq_comm
-/

alias modeq_comm ↔ modeq.symm _
#align add_comm_group.modeq.symm AddCommGroup.ModEq.symm

attribute [symm] modeq.symm

#print AddCommGroup.ModEq.trans /-
@[trans]
theorem ModEq.trans : a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p] := fun ⟨m, hm⟩ ⟨n, hn⟩ =>
  ⟨m + n, by simp [add_smul, ← hm, ← hn]⟩
#align add_comm_group.modeq.trans AddCommGroup.ModEq.trans
-/

instance : IsRefl _ (ModEq p) :=
  ⟨modEq_refl⟩

/- warning: add_comm_group.neg_modeq_neg -> AddCommGroup.neg_modEq_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) a) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) b)) (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) a) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) b)) (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.neg_modeq_neg AddCommGroup.neg_modEq_negₓ'. -/
@[simp]
theorem neg_modEq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [modeq]
#align add_comm_group.neg_modeq_neg AddCommGroup.neg_modEq_neg

/- warning: add_comm_group.modeq.of_neg -> AddCommGroup.ModEq.of_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) a) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) a) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.of_neg AddCommGroup.ModEq.of_negₓ'. -/
/- warning: add_comm_group.modeq.neg -> AddCommGroup.ModEq.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) a) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) a) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) b))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.neg AddCommGroup.ModEq.negₓ'. -/
alias neg_modeq_neg ↔ modeq.of_neg modeq.neg
#align add_comm_group.modeq.of_neg AddCommGroup.ModEq.of_neg
#align add_comm_group.modeq.neg AddCommGroup.ModEq.neg

/- warning: add_comm_group.modeq_neg -> AddCommGroup.modEq_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) p) a b) (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) p) a b) (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq_neg AddCommGroup.modEq_negₓ'. -/
@[simp]
theorem modEq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [modeq, ← neg_eq_iff_eq_neg]
#align add_comm_group.modeq_neg AddCommGroup.modEq_neg

/- warning: add_comm_group.modeq.of_neg' -> AddCommGroup.ModEq.of_neg' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, (AddCommGroup.ModEq.{u1} α _inst_1 (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) p) a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, (AddCommGroup.ModEq.{u1} α _inst_1 (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) p) a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.of_neg' AddCommGroup.ModEq.of_neg'ₓ'. -/
/- warning: add_comm_group.modeq.neg' -> AddCommGroup.ModEq.neg' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) p) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) p) a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.neg' AddCommGroup.ModEq.neg'ₓ'. -/
alias modeq_neg ↔ modeq.of_neg' modeq.neg'
#align add_comm_group.modeq.of_neg' AddCommGroup.ModEq.of_neg'
#align add_comm_group.modeq.neg' AddCommGroup.ModEq.neg'

/- warning: add_comm_group.modeq_sub -> AddCommGroup.modEq_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] (a : α) (b : α), AddCommGroup.ModEq.{u1} α _inst_1 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b a) a b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] (a : α) (b : α), AddCommGroup.ModEq.{u1} α _inst_1 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b a) a b
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq_sub AddCommGroup.modEq_subₓ'. -/
theorem modEq_sub (a b : α) : a ≡ b [PMOD b - a] :=
  ⟨1, (one_smul _ _).symm⟩
#align add_comm_group.modeq_sub AddCommGroup.modEq_sub

/- warning: add_comm_group.modeq_zero -> AddCommGroup.modEq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))))) a b) (Eq.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))))) a b) (Eq.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq_zero AddCommGroup.modEq_zeroₓ'. -/
@[simp]
theorem modEq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [modeq, sub_eq_zero, eq_comm]
#align add_comm_group.modeq_zero AddCommGroup.modEq_zero

/- warning: add_comm_group.self_modeq_zero -> AddCommGroup.self_modEq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α}, AddCommGroup.ModEq.{u1} α _inst_1 p p (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α}, AddCommGroup.ModEq.{u1} α _inst_1 p p (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align add_comm_group.self_modeq_zero AddCommGroup.self_modEq_zeroₓ'. -/
@[simp]
theorem self_modEq_zero : p ≡ 0 [PMOD p] :=
  ⟨-1, by simp⟩
#align add_comm_group.self_modeq_zero AddCommGroup.self_modEq_zero

/- warning: add_comm_group.zsmul_modeq_zero -> AddCommGroup.zsmul_modEq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} (z : Int), AddCommGroup.ModEq.{u1} α _inst_1 p (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z p) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} (z : Int), AddCommGroup.ModEq.{u1} α _inst_1 p (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z p) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align add_comm_group.zsmul_modeq_zero AddCommGroup.zsmul_modEq_zeroₓ'. -/
@[simp]
theorem zsmul_modEq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] :=
  ⟨-z, by simp⟩
#align add_comm_group.zsmul_modeq_zero AddCommGroup.zsmul_modEq_zero

/- warning: add_comm_group.add_zsmul_modeq -> AddCommGroup.add_zsmul_modEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} (z : Int), AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z p)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} (z : Int), AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z p)) a
Case conversion may be inaccurate. Consider using '#align add_comm_group.add_zsmul_modeq AddCommGroup.add_zsmul_modEqₓ'. -/
theorem add_zsmul_modEq (z : ℤ) : a + z • p ≡ a [PMOD p] :=
  ⟨-z, by simp⟩
#align add_comm_group.add_zsmul_modeq AddCommGroup.add_zsmul_modEq

/- warning: add_comm_group.zsmul_add_modeq -> AddCommGroup.zsmul_add_modEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} (z : Int), AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z p) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} (z : Int), AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z p) a) a
Case conversion may be inaccurate. Consider using '#align add_comm_group.zsmul_add_modeq AddCommGroup.zsmul_add_modEqₓ'. -/
theorem zsmul_add_modEq (z : ℤ) : z • p + a ≡ a [PMOD p] :=
  ⟨-z, by simp⟩
#align add_comm_group.zsmul_add_modeq AddCommGroup.zsmul_add_modEq

/- warning: add_comm_group.add_nsmul_modeq -> AddCommGroup.add_nsmul_modEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} (n : Nat), AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n p)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} (n : Nat), AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n p)) a
Case conversion may be inaccurate. Consider using '#align add_comm_group.add_nsmul_modeq AddCommGroup.add_nsmul_modEqₓ'. -/
theorem add_nsmul_modEq (n : ℕ) : a + n • p ≡ a [PMOD p] :=
  ⟨-n, by simp⟩
#align add_comm_group.add_nsmul_modeq AddCommGroup.add_nsmul_modEq

/- warning: add_comm_group.nsmul_add_modeq -> AddCommGroup.nsmul_add_modEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} (n : Nat), AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n p) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} (n : Nat), AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n p) a) a
Case conversion may be inaccurate. Consider using '#align add_comm_group.nsmul_add_modeq AddCommGroup.nsmul_add_modEqₓ'. -/
theorem nsmul_add_modEq (n : ℕ) : n • p + a ≡ a [PMOD p] :=
  ⟨-n, by simp⟩
#align add_comm_group.nsmul_add_modeq AddCommGroup.nsmul_add_modEq

namespace Modeq

/- warning: add_comm_group.modeq.add_zsmul -> AddCommGroup.ModEq.add_zsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (z : Int), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z p)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (z : Int), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z p)) b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_zsmul AddCommGroup.ModEq.add_zsmulₓ'. -/
protected theorem add_zsmul (z : ℤ) : a ≡ b [PMOD p] → a + z • p ≡ b [PMOD p] :=
  (add_zsmul_modEq _).trans
#align add_comm_group.modeq.add_zsmul AddCommGroup.ModEq.add_zsmul

/- warning: add_comm_group.modeq.zsmul_add -> AddCommGroup.ModEq.zsmul_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (z : Int), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z p) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (z : Int), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z p) a) b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.zsmul_add AddCommGroup.ModEq.zsmul_addₓ'. -/
protected theorem zsmul_add (z : ℤ) : a ≡ b [PMOD p] → z • p + a ≡ b [PMOD p] :=
  (zsmul_add_modEq _).trans
#align add_comm_group.modeq.zsmul_add AddCommGroup.ModEq.zsmul_add

/- warning: add_comm_group.modeq.add_nsmul -> AddCommGroup.ModEq.add_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (n : Nat), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n p)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (n : Nat), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n p)) b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_nsmul AddCommGroup.ModEq.add_nsmulₓ'. -/
protected theorem add_nsmul (n : ℕ) : a ≡ b [PMOD p] → a + n • p ≡ b [PMOD p] :=
  (add_nsmul_modEq _).trans
#align add_comm_group.modeq.add_nsmul AddCommGroup.ModEq.add_nsmul

/- warning: add_comm_group.modeq.nsmul_add -> AddCommGroup.ModEq.nsmul_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (n : Nat), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n p) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (n : Nat), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n p) a) b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.nsmul_add AddCommGroup.ModEq.nsmul_addₓ'. -/
protected theorem nsmul_add (n : ℕ) : a ≡ b [PMOD p] → n • p + a ≡ b [PMOD p] :=
  (nsmul_add_modEq _).trans
#align add_comm_group.modeq.nsmul_add AddCommGroup.ModEq.nsmul_add

#print AddCommGroup.ModEq.of_zsmul /-
protected theorem of_zsmul : a ≡ b [PMOD z • p] → a ≡ b [PMOD p] := fun ⟨m, hm⟩ =>
  ⟨m * z, by rwa [mul_smul]⟩
#align add_comm_group.modeq.of_zsmul AddCommGroup.ModEq.of_zsmul
-/

#print AddCommGroup.ModEq.of_nsmul /-
protected theorem of_nsmul : a ≡ b [PMOD n • p] → a ≡ b [PMOD p] := fun ⟨m, hm⟩ =>
  ⟨m * n, by rwa [mul_smul, coe_nat_zsmul]⟩
#align add_comm_group.modeq.of_nsmul AddCommGroup.ModEq.of_nsmul
-/

#print AddCommGroup.ModEq.zsmul /-
protected theorem zsmul : a ≡ b [PMOD p] → z • a ≡ z • b [PMOD z • p] :=
  Exists.imp fun m hm => by rw [← smul_sub, hm, smul_comm]
#align add_comm_group.modeq.zsmul AddCommGroup.ModEq.zsmul
-/

#print AddCommGroup.ModEq.nsmul /-
protected theorem nsmul : a ≡ b [PMOD p] → n • a ≡ n • b [PMOD n • p] :=
  Exists.imp fun m hm => by rw [← smul_sub, hm, smul_comm]
#align add_comm_group.modeq.nsmul AddCommGroup.ModEq.nsmul
-/

end Modeq

/- warning: add_comm_group.zsmul_modeq_zsmul -> AddCommGroup.zsmul_modEq_zsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {z : Int} [_inst_2 : NoZeroSMulDivisors.{0, u1} Int α Int.hasZero (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))], (Ne.{1} Int z (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z p) (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z a) (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z b)) (AddCommGroup.ModEq.{u1} α _inst_1 p a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {z : Int} [_inst_2 : NoZeroSMulDivisors.{0, u1} Int α (CommMonoidWithZero.toZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))], (Ne.{1} Int z (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z p) (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z a) (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z b)) (AddCommGroup.ModEq.{u1} α _inst_1 p a b))
Case conversion may be inaccurate. Consider using '#align add_comm_group.zsmul_modeq_zsmul AddCommGroup.zsmul_modEq_zsmulₓ'. -/
@[simp]
theorem zsmul_modEq_zsmul [NoZeroSMulDivisors ℤ α] (hn : z ≠ 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] :=
  exists_congr fun m => by rw [← smul_sub, smul_comm, smul_right_inj hn] <;> infer_instance
#align add_comm_group.zsmul_modeq_zsmul AddCommGroup.zsmul_modEq_zsmul

/- warning: add_comm_group.nsmul_modeq_nsmul -> AddCommGroup.nsmul_modEq_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {n : Nat} [_inst_2 : NoZeroSMulDivisors.{0, u1} Nat α Nat.hasZero (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))], (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n p) (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n a) (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n b)) (AddCommGroup.ModEq.{u1} α _inst_1 p a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {n : Nat} [_inst_2 : NoZeroSMulDivisors.{0, u1} Nat α (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))], (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n p) (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n a) (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n b)) (AddCommGroup.ModEq.{u1} α _inst_1 p a b))
Case conversion may be inaccurate. Consider using '#align add_comm_group.nsmul_modeq_nsmul AddCommGroup.nsmul_modEq_nsmulₓ'. -/
@[simp]
theorem nsmul_modEq_nsmul [NoZeroSMulDivisors ℕ α] (hn : n ≠ 0) :
    n • a ≡ n • b [PMOD n • p] ↔ a ≡ b [PMOD p] :=
  exists_congr fun m => by rw [← smul_sub, smul_comm, smul_right_inj hn] <;> infer_instance
#align add_comm_group.nsmul_modeq_nsmul AddCommGroup.nsmul_modEq_nsmul

/- warning: add_comm_group.modeq.zsmul_cancel -> AddCommGroup.ModEq.zsmul_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {z : Int} [_inst_2 : NoZeroSMulDivisors.{0, u1} Int α Int.hasZero (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))], (Ne.{1} Int z (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (AddCommGroup.ModEq.{u1} α _inst_1 (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z p) (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z a) (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {z : Int} [_inst_2 : NoZeroSMulDivisors.{0, u1} Int α (CommMonoidWithZero.toZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))], (Ne.{1} Int z (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (AddCommGroup.ModEq.{u1} α _inst_1 (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z p) (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z a) (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.zsmul_cancel AddCommGroup.ModEq.zsmul_cancelₓ'. -/
alias zsmul_modeq_zsmul ↔ modeq.zsmul_cancel _
#align add_comm_group.modeq.zsmul_cancel AddCommGroup.ModEq.zsmul_cancel

/- warning: add_comm_group.modeq.nsmul_cancel -> AddCommGroup.ModEq.nsmul_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {n : Nat} [_inst_2 : NoZeroSMulDivisors.{0, u1} Nat α Nat.hasZero (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))], (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (AddCommGroup.ModEq.{u1} α _inst_1 (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n p) (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n a) (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) n b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {n : Nat} [_inst_2 : NoZeroSMulDivisors.{0, u1} Nat α (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))) (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))], (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (AddCommGroup.ModEq.{u1} α _inst_1 (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n p) (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n a) (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) n b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.nsmul_cancel AddCommGroup.ModEq.nsmul_cancelₓ'. -/
alias nsmul_modeq_nsmul ↔ modeq.nsmul_cancel _
#align add_comm_group.modeq.nsmul_cancel AddCommGroup.ModEq.nsmul_cancel

namespace Modeq

/- warning: add_comm_group.modeq.add_iff_left -> AddCommGroup.ModEq.add_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂)) (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂)) (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_iff_left AddCommGroup.ModEq.add_iff_leftₓ'. -/
@[simp]
protected theorem add_iff_left :
    a₁ ≡ b₁ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.addLeft m).symm.exists_congr_left.trans <| by simpa [add_sub_add_comm, hm, add_smul]
#align add_comm_group.modeq.add_iff_left AddCommGroup.ModEq.add_iff_left

/- warning: add_comm_group.modeq.add_iff_right -> AddCommGroup.ModEq.add_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂)) (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂)) (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_iff_right AddCommGroup.ModEq.add_iff_rightₓ'. -/
@[simp]
protected theorem add_iff_right :
    a₂ ≡ b₂ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.addRight m).symm.exists_congr_left.trans <| by simpa [add_sub_add_comm, hm, add_smul]
#align add_comm_group.modeq.add_iff_right AddCommGroup.ModEq.add_iff_right

/- warning: add_comm_group.modeq.sub_iff_left -> AddCommGroup.ModEq.sub_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂)) (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂)) (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.sub_iff_left AddCommGroup.ModEq.sub_iff_leftₓ'. -/
@[simp]
protected theorem sub_iff_left :
    a₁ ≡ b₁ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.subLeft m).symm.exists_congr_left.trans <| by simpa [sub_sub_sub_comm, hm, sub_smul]
#align add_comm_group.modeq.sub_iff_left AddCommGroup.ModEq.sub_iff_left

/- warning: add_comm_group.modeq.sub_iff_right -> AddCommGroup.ModEq.sub_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂)) (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂)) (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.sub_iff_right AddCommGroup.ModEq.sub_iff_rightₓ'. -/
@[simp]
protected theorem sub_iff_right :
    a₂ ≡ b₂ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.subRight m).symm.exists_congr_left.trans <| by simpa [sub_sub_sub_comm, hm, sub_smul]
#align add_comm_group.modeq.sub_iff_right AddCommGroup.ModEq.sub_iff_right

/- warning: add_comm_group.modeq.add_left_cancel -> AddCommGroup.ModEq.add_left_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_left_cancel AddCommGroup.ModEq.add_left_cancelₓ'. -/
/- warning: add_comm_group.modeq.add -> AddCommGroup.ModEq.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add AddCommGroup.ModEq.addₓ'. -/
alias modeq.add_iff_left ↔ add_left_cancel add
#align add_comm_group.modeq.add_left_cancel AddCommGroup.ModEq.add_left_cancel
#align add_comm_group.modeq.add AddCommGroup.ModEq.add

/- warning: add_comm_group.modeq.add_right_cancel -> AddCommGroup.ModEq.add_right_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b₁ b₂)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_right_cancel AddCommGroup.ModEq.add_right_cancelₓ'. -/
alias modeq.add_iff_right ↔ add_right_cancel _
#align add_comm_group.modeq.add_right_cancel AddCommGroup.ModEq.add_right_cancel

/- warning: add_comm_group.modeq.sub_left_cancel -> AddCommGroup.ModEq.sub_left_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.sub_left_cancel AddCommGroup.ModEq.sub_left_cancelₓ'. -/
/- warning: add_comm_group.modeq.sub -> AddCommGroup.ModEq.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.sub AddCommGroup.ModEq.subₓ'. -/
alias modeq.sub_iff_left ↔ sub_left_cancel sub
#align add_comm_group.modeq.sub_left_cancel AddCommGroup.ModEq.sub_left_cancel
#align add_comm_group.modeq.sub AddCommGroup.ModEq.sub

/- warning: add_comm_group.modeq.sub_right_cancel -> AddCommGroup.ModEq.sub_right_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (AddCommGroup.ModEq.{u1} α _inst_1 p a₂ b₂) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b₁ b₂)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a₁ b₁)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.sub_right_cancel AddCommGroup.ModEq.sub_right_cancelₓ'. -/
alias modeq.sub_iff_right ↔ sub_right_cancel _
#align add_comm_group.modeq.sub_right_cancel AddCommGroup.ModEq.sub_right_cancel

attribute [protected] add_left_cancel add_right_cancel add sub_left_cancel sub_right_cancel sub

/- warning: add_comm_group.modeq.add_left -> AddCommGroup.ModEq.add_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_left AddCommGroup.ModEq.add_leftₓ'. -/
protected theorem add_left (c : α) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] :=
  modEq_rfl.add h
#align add_comm_group.modeq.add_left AddCommGroup.ModEq.add_left

/- warning: add_comm_group.modeq.sub_left -> AddCommGroup.ModEq.sub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c b))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.sub_left AddCommGroup.ModEq.sub_leftₓ'. -/
protected theorem sub_left (c : α) (h : a ≡ b [PMOD p]) : c - a ≡ c - b [PMOD p] :=
  modEq_rfl.sub h
#align add_comm_group.modeq.sub_left AddCommGroup.ModEq.sub_left

/- warning: add_comm_group.modeq.add_right -> AddCommGroup.ModEq.add_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_right AddCommGroup.ModEq.add_rightₓ'. -/
protected theorem add_right (c : α) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] :=
  h.add modEq_rfl
#align add_comm_group.modeq.add_right AddCommGroup.ModEq.add_right

/- warning: add_comm_group.modeq.sub_right -> AddCommGroup.ModEq.sub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p a b) -> (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.sub_right AddCommGroup.ModEq.sub_rightₓ'. -/
protected theorem sub_right (c : α) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] :=
  h.sub modEq_rfl
#align add_comm_group.modeq.sub_right AddCommGroup.ModEq.sub_right

/- warning: add_comm_group.modeq.add_left_cancel' -> AddCommGroup.ModEq.add_left_cancel' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_left_cancel' AddCommGroup.ModEq.add_left_cancel'ₓ'. -/
protected theorem add_left_cancel' (c : α) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_left_cancel
#align add_comm_group.modeq.add_left_cancel' AddCommGroup.ModEq.add_left_cancel'

/- warning: add_comm_group.modeq.add_right_cancel' -> AddCommGroup.ModEq.add_right_cancel' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.add_right_cancel' AddCommGroup.ModEq.add_right_cancel'ₓ'. -/
protected theorem add_right_cancel' (c : α) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_right_cancel
#align add_comm_group.modeq.add_right_cancel' AddCommGroup.ModEq.add_right_cancel'

/- warning: add_comm_group.modeq.sub_left_cancel' -> AddCommGroup.ModEq.sub_left_cancel' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c b)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.sub_left_cancel' AddCommGroup.ModEq.sub_left_cancel'ₓ'. -/
protected theorem sub_left_cancel' (c : α) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_left_cancel
#align add_comm_group.modeq.sub_left_cancel' AddCommGroup.ModEq.sub_left_cancel'

/- warning: add_comm_group.modeq.sub_right_cancel' -> AddCommGroup.ModEq.sub_right_cancel' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b c)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} (c : α), (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b c)) -> (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.sub_right_cancel' AddCommGroup.ModEq.sub_right_cancel'ₓ'. -/
protected theorem sub_right_cancel' (c : α) : a - c ≡ b - c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_right_cancel
#align add_comm_group.modeq.sub_right_cancel' AddCommGroup.ModEq.sub_right_cancel'

end Modeq

/- warning: add_comm_group.modeq_sub_iff_add_modeq' -> AddCommGroup.modEq_sub_iff_add_modEq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {c : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b c)) (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {c : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b c)) (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c a) b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq_sub_iff_add_modeq' AddCommGroup.modEq_sub_iff_add_modEq'ₓ'. -/
theorem modEq_sub_iff_add_modEq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by
  simp [modeq, sub_sub]
#align add_comm_group.modeq_sub_iff_add_modeq' AddCommGroup.modEq_sub_iff_add_modEq'

/- warning: add_comm_group.modeq_sub_iff_add_modeq -> AddCommGroup.modEq_sub_iff_add_modEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {c : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b c)) (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {c : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) b c)) (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a c) b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq_sub_iff_add_modeq AddCommGroup.modEq_sub_iff_add_modEqₓ'. -/
theorem modEq_sub_iff_add_modEq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] :=
  modEq_sub_iff_add_modEq'.trans <| by rw [add_comm]
#align add_comm_group.modeq_sub_iff_add_modeq AddCommGroup.modEq_sub_iff_add_modEq

/- warning: add_comm_group.sub_modeq_iff_modeq_add' -> AddCommGroup.sub_modEq_iff_modEq_add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {c : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c) (AddCommGroup.ModEq.{u1} α _inst_1 p a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {c : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c) (AddCommGroup.ModEq.{u1} α _inst_1 p a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align add_comm_group.sub_modeq_iff_modeq_add' AddCommGroup.sub_modEq_iff_modEq_add'ₓ'. -/
theorem sub_modEq_iff_modEq_add' : a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p] :=
  modEq_comm.trans <| modEq_sub_iff_add_modEq'.trans modEq_comm
#align add_comm_group.sub_modeq_iff_modeq_add' AddCommGroup.sub_modEq_iff_modEq_add'

/- warning: add_comm_group.sub_modeq_iff_modeq_add -> AddCommGroup.sub_modEq_iff_modEq_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {c : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c) (AddCommGroup.ModEq.{u1} α _inst_1 p a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α} {c : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c) (AddCommGroup.ModEq.{u1} α _inst_1 p a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align add_comm_group.sub_modeq_iff_modeq_add AddCommGroup.sub_modEq_iff_modEq_addₓ'. -/
theorem sub_modEq_iff_modEq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p] :=
  modEq_comm.trans <| modEq_sub_iff_add_modEq.trans modEq_comm
#align add_comm_group.sub_modeq_iff_modeq_add AddCommGroup.sub_modEq_iff_modEq_add

/- warning: add_comm_group.sub_modeq_zero -> AddCommGroup.sub_modEq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))))) (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1)))))))) (AddCommGroup.ModEq.{u1} α _inst_1 p a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.sub_modeq_zero AddCommGroup.sub_modEq_zeroₓ'. -/
@[simp]
theorem sub_modEq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] := by simp [sub_modeq_iff_modeq_add]
#align add_comm_group.sub_modeq_zero AddCommGroup.sub_modEq_zero

/- warning: add_comm_group.add_modeq_left -> AddCommGroup.add_modEq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) a) (AddCommGroup.ModEq.{u1} α _inst_1 p b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) a) (AddCommGroup.ModEq.{u1} α _inst_1 p b (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align add_comm_group.add_modeq_left AddCommGroup.add_modEq_leftₓ'. -/
@[simp]
theorem add_modEq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] := by simp [← modeq_sub_iff_add_modeq']
#align add_comm_group.add_modeq_left AddCommGroup.add_modEq_left

/- warning: add_comm_group.add_modeq_right -> AddCommGroup.add_modEq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) b) (AddCommGroup.ModEq.{u1} α _inst_1 p a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) b) (AddCommGroup.ModEq.{u1} α _inst_1 p a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align add_comm_group.add_modeq_right AddCommGroup.add_modEq_rightₓ'. -/
@[simp]
theorem add_modEq_right : a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p] := by simp [← modeq_sub_iff_add_modeq]
#align add_comm_group.add_modeq_right AddCommGroup.add_modEq_right

/- warning: add_comm_group.modeq_iff_eq_add_zsmul -> AddCommGroup.modEq_iff_eq_add_zsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p a b) (Exists.{1} Int (fun (z : Int) => Eq.{succ u1} α b (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z p))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (AddCommGroup.ModEq.{u1} α _inst_1 p a b) (Exists.{1} Int (fun (z : Int) => Eq.{succ u1} α b (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z p))))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq_iff_eq_add_zsmul AddCommGroup.modEq_iff_eq_add_zsmulₓ'. -/
theorem modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p := by
  simp_rw [modeq, sub_eq_iff_eq_add']
#align add_comm_group.modeq_iff_eq_add_zsmul AddCommGroup.modEq_iff_eq_add_zsmul

/- warning: add_comm_group.not_modeq_iff_ne_add_zsmul -> AddCommGroup.not_modEq_iff_ne_add_zsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (Not (AddCommGroup.ModEq.{u1} α _inst_1 p a b)) (forall (z : Int), Ne.{succ u1} α b (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (SMul.smul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) z p)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] {p : α} {a : α} {b : α}, Iff (Not (AddCommGroup.ModEq.{u1} α _inst_1 p a b)) (forall (z : Int), Ne.{succ u1} α b (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (HSMul.hSMul.{0, u1, u1} Int α α (instHSMul.{0, u1} Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) z p)))
Case conversion may be inaccurate. Consider using '#align add_comm_group.not_modeq_iff_ne_add_zsmul AddCommGroup.not_modEq_iff_ne_add_zsmulₓ'. -/
theorem not_modEq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  rw [modeq_iff_eq_add_zsmul, not_exists]
#align add_comm_group.not_modeq_iff_ne_add_zsmul AddCommGroup.not_modEq_iff_ne_add_zsmul

#print AddCommGroup.modEq_iff_eq_mod_zmultiples /-
theorem modEq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (b : α ⧸ AddSubgroup.zmultiples p) = a := by
  simp_rw [modeq_iff_eq_add_zsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff,
    eq_sub_iff_add_eq', eq_comm]
#align add_comm_group.modeq_iff_eq_mod_zmultiples AddCommGroup.modEq_iff_eq_mod_zmultiples
-/

#print AddCommGroup.not_modEq_iff_ne_mod_zmultiples /-
theorem not_modEq_iff_ne_mod_zmultiples :
    ¬a ≡ b [PMOD p] ↔ (b : α ⧸ AddSubgroup.zmultiples p) ≠ a :=
  modEq_iff_eq_mod_zmultiples.Not
#align add_comm_group.not_modeq_iff_ne_mod_zmultiples AddCommGroup.not_modEq_iff_ne_mod_zmultiples
-/

end AddCommGroup

/- warning: add_comm_group.modeq_iff_int_modeq -> AddCommGroup.modEq_iff_int_modEq is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int} {z : Int}, Iff (AddCommGroup.ModEq.{0} Int Int.addCommGroup z a b) (Int.ModEq z a b)
but is expected to have type
  forall {a : Int} {b : Int} {z : Int}, Iff (AddCommGroup.ModEq.{0} Int Int.instAddCommGroupInt z a b) (Int.ModEq z a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq_iff_int_modeq AddCommGroup.modEq_iff_int_modEqₓ'. -/
@[simp]
theorem modEq_iff_int_modEq {a b z : ℤ} : a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z] := by
  simp [modeq, dvd_iff_exists_eq_mul_left, Int.modEq_iff_dvd]
#align add_comm_group.modeq_iff_int_modeq AddCommGroup.modEq_iff_int_modEq

section AddCommGroupWithOne

variable [AddCommGroupWithOne α] [CharZero α]

/- warning: add_comm_group.int_cast_modeq_int_cast -> AddCommGroup.int_cast_modEq_int_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))] {a : Int} {b : Int} {z : Int}, Iff (AddCommGroup.ModEq.{u1} α (AddCommGroupWithOne.toAddCommGroup.{u1} α _inst_1) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))))) z) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))))) b)) (AddCommGroup.ModEq.{0} Int Int.addCommGroup z a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))] {a : Int} {b : Int} {z : Int}, Iff (AddCommGroup.ModEq.{u1} α (AddCommGroupWithOne.toAddCommGroup.{u1} α _inst_1) (Int.cast.{u1} α (AddCommGroupWithOne.toIntCast.{u1} α _inst_1) z) (Int.cast.{u1} α (AddCommGroupWithOne.toIntCast.{u1} α _inst_1) a) (Int.cast.{u1} α (AddCommGroupWithOne.toIntCast.{u1} α _inst_1) b)) (AddCommGroup.ModEq.{0} Int Int.instAddCommGroupInt z a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.int_cast_modeq_int_cast AddCommGroup.int_cast_modEq_int_castₓ'. -/
@[simp, norm_cast]
theorem int_cast_modEq_int_cast {a b z : ℤ} : a ≡ b [PMOD (z : α)] ↔ a ≡ b [PMOD z] := by
  simp_rw [modeq, ← Int.cast_mul_eq_zsmul_cast] <;> norm_cast
#align add_comm_group.int_cast_modeq_int_cast AddCommGroup.int_cast_modEq_int_cast

#print AddCommGroup.nat_cast_modEq_nat_cast /-
@[simp, norm_cast]
theorem nat_cast_modEq_nat_cast {a b n : ℕ} : a ≡ b [PMOD (n : α)] ↔ a ≡ b [MOD n] := by
  simp_rw [← Int.coe_nat_modEq_iff, ← modeq_iff_int_modeq, ← @int_cast_modeq_int_cast α,
    Int.cast_ofNat]
#align add_comm_group.nat_cast_modeq_nat_cast AddCommGroup.nat_cast_modEq_nat_cast
-/

/- warning: add_comm_group.modeq.of_int_cast -> AddCommGroup.ModEq.of_int_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))] {a : Int} {b : Int} {z : Int}, (AddCommGroup.ModEq.{u1} α (AddCommGroupWithOne.toAddCommGroup.{u1} α _inst_1) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))))) z) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))))) b)) -> (AddCommGroup.ModEq.{0} Int Int.addCommGroup z a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))] {a : Int} {b : Int} {z : Int}, (AddCommGroup.ModEq.{u1} α (AddCommGroupWithOne.toAddCommGroup.{u1} α _inst_1) (Int.cast.{u1} α (AddCommGroupWithOne.toIntCast.{u1} α _inst_1) z) (Int.cast.{u1} α (AddCommGroupWithOne.toIntCast.{u1} α _inst_1) a) (Int.cast.{u1} α (AddCommGroupWithOne.toIntCast.{u1} α _inst_1) b)) -> (AddCommGroup.ModEq.{0} Int Int.instAddCommGroupInt z a b)
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.of_int_cast AddCommGroup.ModEq.of_int_castₓ'. -/
/- warning: add_comm_group.modeq.int_cast -> AddCommGroup.ModEq.int_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))] {a : Int} {b : Int} {z : Int}, (AddCommGroup.ModEq.{0} Int Int.addCommGroup z a b) -> (AddCommGroup.ModEq.{u1} α (AddCommGroupWithOne.toAddCommGroup.{u1} α _inst_1) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))))) z) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α _inst_1))] {a : Int} {b : Int} {z : Int}, (AddCommGroup.ModEq.{0} Int Int.instAddCommGroupInt z a b) -> (AddCommGroup.ModEq.{u1} α (AddCommGroupWithOne.toAddCommGroup.{u1} α _inst_1) (Int.cast.{u1} α (AddCommGroupWithOne.toIntCast.{u1} α _inst_1) z) (Int.cast.{u1} α (AddCommGroupWithOne.toIntCast.{u1} α _inst_1) a) (Int.cast.{u1} α (AddCommGroupWithOne.toIntCast.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align add_comm_group.modeq.int_cast AddCommGroup.ModEq.int_castₓ'. -/
alias int_cast_modeq_int_cast ↔ modeq.of_int_cast modeq.int_cast
#align add_comm_group.modeq.of_int_cast AddCommGroup.ModEq.of_int_cast
#align add_comm_group.modeq.int_cast AddCommGroup.ModEq.int_cast

alias nat_cast_modeq_nat_cast ↔ _root_.nat.modeq.of_nat_cast modeq.nat_cast
#align nat.modeq.of_nat_cast Nat.ModEq.of_nat_cast
#align add_comm_group.modeq.nat_cast AddCommGroup.ModEq.nat_cast

end AddCommGroupWithOne

end AddCommGroup

