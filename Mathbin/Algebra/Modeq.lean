/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Data.Int.Modeq
import GroupTheory.QuotientGroup

#align_import algebra.modeq from "leanprover-community/mathlib"@"6cf5900728239efa287df7761ec2a1ac9cf39b29"

/-!
# Equality modulo an element

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

alias ⟨modeq.symm, _⟩ := modeq_comm
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

#print AddCommGroup.neg_modEq_neg /-
@[simp]
theorem neg_modEq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [modeq]
#align add_comm_group.neg_modeq_neg AddCommGroup.neg_modEq_neg
-/

alias ⟨modeq.of_neg, modeq.neg⟩ := neg_modeq_neg
#align add_comm_group.modeq.of_neg AddCommGroup.ModEq.of_neg
#align add_comm_group.modeq.neg AddCommGroup.ModEq.neg

#print AddCommGroup.modEq_neg /-
@[simp]
theorem modEq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [modeq, ← neg_eq_iff_eq_neg]
#align add_comm_group.modeq_neg AddCommGroup.modEq_neg
-/

alias ⟨modeq.of_neg', modeq.neg'⟩ := modeq_neg
#align add_comm_group.modeq.of_neg' AddCommGroup.ModEq.of_neg'
#align add_comm_group.modeq.neg' AddCommGroup.ModEq.neg'

#print AddCommGroup.modEq_sub /-
theorem modEq_sub (a b : α) : a ≡ b [PMOD b - a] :=
  ⟨1, (one_smul _ _).symm⟩
#align add_comm_group.modeq_sub AddCommGroup.modEq_sub
-/

#print AddCommGroup.modEq_zero /-
@[simp]
theorem modEq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [modeq, sub_eq_zero, eq_comm]
#align add_comm_group.modeq_zero AddCommGroup.modEq_zero
-/

#print AddCommGroup.self_modEq_zero /-
@[simp]
theorem self_modEq_zero : p ≡ 0 [PMOD p] :=
  ⟨-1, by simp⟩
#align add_comm_group.self_modeq_zero AddCommGroup.self_modEq_zero
-/

#print AddCommGroup.zsmul_modEq_zero /-
@[simp]
theorem zsmul_modEq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] :=
  ⟨-z, by simp⟩
#align add_comm_group.zsmul_modeq_zero AddCommGroup.zsmul_modEq_zero
-/

#print AddCommGroup.add_zsmul_modEq /-
theorem add_zsmul_modEq (z : ℤ) : a + z • p ≡ a [PMOD p] :=
  ⟨-z, by simp⟩
#align add_comm_group.add_zsmul_modeq AddCommGroup.add_zsmul_modEq
-/

#print AddCommGroup.zsmul_add_modEq /-
theorem zsmul_add_modEq (z : ℤ) : z • p + a ≡ a [PMOD p] :=
  ⟨-z, by simp⟩
#align add_comm_group.zsmul_add_modeq AddCommGroup.zsmul_add_modEq
-/

#print AddCommGroup.add_nsmul_modEq /-
theorem add_nsmul_modEq (n : ℕ) : a + n • p ≡ a [PMOD p] :=
  ⟨-n, by simp⟩
#align add_comm_group.add_nsmul_modeq AddCommGroup.add_nsmul_modEq
-/

#print AddCommGroup.nsmul_add_modEq /-
theorem nsmul_add_modEq (n : ℕ) : n • p + a ≡ a [PMOD p] :=
  ⟨-n, by simp⟩
#align add_comm_group.nsmul_add_modeq AddCommGroup.nsmul_add_modEq
-/

namespace Modeq

#print AddCommGroup.ModEq.add_zsmul /-
protected theorem add_zsmul (z : ℤ) : a ≡ b [PMOD p] → a + z • p ≡ b [PMOD p] :=
  (add_zsmul_modEq _).trans
#align add_comm_group.modeq.add_zsmul AddCommGroup.ModEq.add_zsmul
-/

#print AddCommGroup.ModEq.zsmul_add /-
protected theorem zsmul_add (z : ℤ) : a ≡ b [PMOD p] → z • p + a ≡ b [PMOD p] :=
  (zsmul_add_modEq _).trans
#align add_comm_group.modeq.zsmul_add AddCommGroup.ModEq.zsmul_add
-/

#print AddCommGroup.ModEq.add_nsmul /-
protected theorem add_nsmul (n : ℕ) : a ≡ b [PMOD p] → a + n • p ≡ b [PMOD p] :=
  (add_nsmul_modEq _).trans
#align add_comm_group.modeq.add_nsmul AddCommGroup.ModEq.add_nsmul
-/

#print AddCommGroup.ModEq.nsmul_add /-
protected theorem nsmul_add (n : ℕ) : a ≡ b [PMOD p] → n • p + a ≡ b [PMOD p] :=
  (nsmul_add_modEq _).trans
#align add_comm_group.modeq.nsmul_add AddCommGroup.ModEq.nsmul_add
-/

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

#print AddCommGroup.zsmul_modEq_zsmul /-
@[simp]
theorem zsmul_modEq_zsmul [NoZeroSMulDivisors ℤ α] (hn : z ≠ 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] :=
  exists_congr fun m => by rw [← smul_sub, smul_comm, smul_right_inj hn] <;> infer_instance
#align add_comm_group.zsmul_modeq_zsmul AddCommGroup.zsmul_modEq_zsmul
-/

#print AddCommGroup.nsmul_modEq_nsmul /-
@[simp]
theorem nsmul_modEq_nsmul [NoZeroSMulDivisors ℕ α] (hn : n ≠ 0) :
    n • a ≡ n • b [PMOD n • p] ↔ a ≡ b [PMOD p] :=
  exists_congr fun m => by rw [← smul_sub, smul_comm, smul_right_inj hn] <;> infer_instance
#align add_comm_group.nsmul_modeq_nsmul AddCommGroup.nsmul_modEq_nsmul
-/

alias ⟨modeq.zsmul_cancel, _⟩ := zsmul_modeq_zsmul
#align add_comm_group.modeq.zsmul_cancel AddCommGroup.ModEq.zsmul_cancel

alias ⟨modeq.nsmul_cancel, _⟩ := nsmul_modeq_nsmul
#align add_comm_group.modeq.nsmul_cancel AddCommGroup.ModEq.nsmul_cancel

namespace Modeq

#print AddCommGroup.ModEq.add_iff_left /-
@[simp]
protected theorem add_iff_left :
    a₁ ≡ b₁ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.addLeft m).symm.exists_congr_left.trans <| by simpa [add_sub_add_comm, hm, add_smul]
#align add_comm_group.modeq.add_iff_left AddCommGroup.ModEq.add_iff_left
-/

#print AddCommGroup.ModEq.add_iff_right /-
@[simp]
protected theorem add_iff_right :
    a₂ ≡ b₂ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.addRight m).symm.exists_congr_left.trans <| by simpa [add_sub_add_comm, hm, add_smul]
#align add_comm_group.modeq.add_iff_right AddCommGroup.ModEq.add_iff_right
-/

#print AddCommGroup.ModEq.sub_iff_left /-
@[simp]
protected theorem sub_iff_left :
    a₁ ≡ b₁ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.subLeft m).symm.exists_congr_left.trans <| by simpa [sub_sub_sub_comm, hm, sub_smul]
#align add_comm_group.modeq.sub_iff_left AddCommGroup.ModEq.sub_iff_left
-/

#print AddCommGroup.ModEq.sub_iff_right /-
@[simp]
protected theorem sub_iff_right :
    a₂ ≡ b₂ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.subRight m).symm.exists_congr_left.trans <| by simpa [sub_sub_sub_comm, hm, sub_smul]
#align add_comm_group.modeq.sub_iff_right AddCommGroup.ModEq.sub_iff_right
-/

alias ⟨add_left_cancel, add⟩ := modeq.add_iff_left
#align add_comm_group.modeq.add_left_cancel AddCommGroup.ModEq.add_left_cancel
#align add_comm_group.modeq.add AddCommGroup.ModEq.add

alias ⟨add_right_cancel, _⟩ := modeq.add_iff_right
#align add_comm_group.modeq.add_right_cancel AddCommGroup.ModEq.add_right_cancel

alias ⟨sub_left_cancel, sub⟩ := modeq.sub_iff_left
#align add_comm_group.modeq.sub_left_cancel AddCommGroup.ModEq.sub_left_cancel
#align add_comm_group.modeq.sub AddCommGroup.ModEq.sub

alias ⟨sub_right_cancel, _⟩ := modeq.sub_iff_right
#align add_comm_group.modeq.sub_right_cancel AddCommGroup.ModEq.sub_right_cancel

attribute [protected] add_left_cancel add_right_cancel add sub_left_cancel sub_right_cancel sub

#print AddCommGroup.ModEq.add_left /-
protected theorem add_left (c : α) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] :=
  modEq_rfl.add h
#align add_comm_group.modeq.add_left AddCommGroup.ModEq.add_left
-/

#print AddCommGroup.ModEq.sub_left /-
protected theorem sub_left (c : α) (h : a ≡ b [PMOD p]) : c - a ≡ c - b [PMOD p] :=
  modEq_rfl.sub h
#align add_comm_group.modeq.sub_left AddCommGroup.ModEq.sub_left
-/

#print AddCommGroup.ModEq.add_right /-
protected theorem add_right (c : α) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] :=
  h.add modEq_rfl
#align add_comm_group.modeq.add_right AddCommGroup.ModEq.add_right
-/

#print AddCommGroup.ModEq.sub_right /-
protected theorem sub_right (c : α) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] :=
  h.sub modEq_rfl
#align add_comm_group.modeq.sub_right AddCommGroup.ModEq.sub_right
-/

#print AddCommGroup.ModEq.add_left_cancel' /-
protected theorem add_left_cancel' (c : α) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_left_cancel
#align add_comm_group.modeq.add_left_cancel' AddCommGroup.ModEq.add_left_cancel'
-/

#print AddCommGroup.ModEq.add_right_cancel' /-
protected theorem add_right_cancel' (c : α) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_right_cancel
#align add_comm_group.modeq.add_right_cancel' AddCommGroup.ModEq.add_right_cancel'
-/

#print AddCommGroup.ModEq.sub_left_cancel' /-
protected theorem sub_left_cancel' (c : α) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_left_cancel
#align add_comm_group.modeq.sub_left_cancel' AddCommGroup.ModEq.sub_left_cancel'
-/

#print AddCommGroup.ModEq.sub_right_cancel' /-
protected theorem sub_right_cancel' (c : α) : a - c ≡ b - c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_right_cancel
#align add_comm_group.modeq.sub_right_cancel' AddCommGroup.ModEq.sub_right_cancel'
-/

end Modeq

#print AddCommGroup.modEq_sub_iff_add_modEq' /-
theorem modEq_sub_iff_add_modEq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by
  simp [modeq, sub_sub]
#align add_comm_group.modeq_sub_iff_add_modeq' AddCommGroup.modEq_sub_iff_add_modEq'
-/

#print AddCommGroup.modEq_sub_iff_add_modEq /-
theorem modEq_sub_iff_add_modEq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] :=
  modEq_sub_iff_add_modEq'.trans <| by rw [add_comm]
#align add_comm_group.modeq_sub_iff_add_modeq AddCommGroup.modEq_sub_iff_add_modEq
-/

#print AddCommGroup.sub_modEq_iff_modEq_add' /-
theorem sub_modEq_iff_modEq_add' : a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p] :=
  modEq_comm.trans <| modEq_sub_iff_add_modEq'.trans modEq_comm
#align add_comm_group.sub_modeq_iff_modeq_add' AddCommGroup.sub_modEq_iff_modEq_add'
-/

#print AddCommGroup.sub_modEq_iff_modEq_add /-
theorem sub_modEq_iff_modEq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p] :=
  modEq_comm.trans <| modEq_sub_iff_add_modEq.trans modEq_comm
#align add_comm_group.sub_modeq_iff_modeq_add AddCommGroup.sub_modEq_iff_modEq_add
-/

#print AddCommGroup.sub_modEq_zero /-
@[simp]
theorem sub_modEq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] := by simp [sub_modeq_iff_modeq_add]
#align add_comm_group.sub_modeq_zero AddCommGroup.sub_modEq_zero
-/

#print AddCommGroup.add_modEq_left /-
@[simp]
theorem add_modEq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] := by simp [← modeq_sub_iff_add_modeq']
#align add_comm_group.add_modeq_left AddCommGroup.add_modEq_left
-/

#print AddCommGroup.add_modEq_right /-
@[simp]
theorem add_modEq_right : a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p] := by simp [← modeq_sub_iff_add_modeq]
#align add_comm_group.add_modeq_right AddCommGroup.add_modEq_right
-/

#print AddCommGroup.modEq_iff_eq_add_zsmul /-
theorem modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p := by
  simp_rw [modeq, sub_eq_iff_eq_add']
#align add_comm_group.modeq_iff_eq_add_zsmul AddCommGroup.modEq_iff_eq_add_zsmul
-/

#print AddCommGroup.not_modEq_iff_ne_add_zsmul /-
theorem not_modEq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  rw [modeq_iff_eq_add_zsmul, not_exists]
#align add_comm_group.not_modeq_iff_ne_add_zsmul AddCommGroup.not_modEq_iff_ne_add_zsmul
-/

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

#print AddCommGroup.modEq_iff_int_modEq /-
@[simp]
theorem modEq_iff_int_modEq {a b z : ℤ} : a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z] := by
  simp [modeq, dvd_iff_exists_eq_mul_left, Int.modEq_iff_dvd]
#align add_comm_group.modeq_iff_int_modeq AddCommGroup.modEq_iff_int_modEq
-/

section AddCommGroupWithOne

variable [AddCommGroupWithOne α] [CharZero α]

#print AddCommGroup.int_cast_modEq_int_cast /-
@[simp, norm_cast]
theorem int_cast_modEq_int_cast {a b z : ℤ} : a ≡ b [PMOD (z : α)] ↔ a ≡ b [PMOD z] := by
  simp_rw [modeq, ← Int.cast_mul_eq_zsmul_cast] <;> norm_cast
#align add_comm_group.int_cast_modeq_int_cast AddCommGroup.int_cast_modEq_int_cast
-/

#print AddCommGroup.nat_cast_modEq_nat_cast /-
@[simp, norm_cast]
theorem nat_cast_modEq_nat_cast {a b n : ℕ} : a ≡ b [PMOD (n : α)] ↔ a ≡ b [MOD n] := by
  simp_rw [← Int.coe_nat_modEq_iff, ← modeq_iff_int_modeq, ← @int_cast_modeq_int_cast α,
    Int.cast_ofNat]
#align add_comm_group.nat_cast_modeq_nat_cast AddCommGroup.nat_cast_modEq_nat_cast
-/

alias ⟨modeq.of_int_cast, modeq.int_cast⟩ := int_cast_modeq_int_cast
#align add_comm_group.modeq.of_int_cast AddCommGroup.ModEq.of_int_cast
#align add_comm_group.modeq.int_cast AddCommGroup.ModEq.int_cast

alias ⟨_root_.nat.modeq.of_nat_cast, modeq.nat_cast⟩ := nat_cast_modeq_nat_cast
#align nat.modeq.of_nat_cast Nat.ModEq.of_nat_cast
#align add_comm_group.modeq.nat_cast AddCommGroup.ModEq.nat_cast

end AddCommGroupWithOne

end AddCommGroup

