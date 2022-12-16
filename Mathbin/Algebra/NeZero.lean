/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module algebra.ne_zero
! leanprover-community/mathlib commit b3f25363ae62cb169e72cd6b8b1ac97bacf21ca7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Basic

/-!
# `ne_zero` typeclass

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/557
> Any changes to this file require a corresponding PR to mathlib4.

We create a typeclass `ne_zero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `ne_zero`: `n ≠ 0` as a typeclass.

-/


#print NeZero /-
/-- A type-class version of `n ≠ 0`.  -/
class NeZero {R} [Zero R] (n : R) : Prop where
  out : n ≠ 0
#align ne_zero NeZero
-/

#print NeZero.ne /-
theorem NeZero.ne {R} [Zero R] (n : R) [h : NeZero n] : n ≠ 0 :=
  h.out
#align ne_zero.ne NeZero.ne
-/

#print NeZero.ne' /-
theorem NeZero.ne' {R} [Zero R] (n : R) [h : NeZero n] : 0 ≠ n :=
  h.out.symm
#align ne_zero.ne' NeZero.ne'
-/

#print neZero_iff /-
theorem neZero_iff {R : Type _} [Zero R] {n : R} : NeZero n ↔ n ≠ 0 :=
  ⟨fun h => h.out, NeZero.mk⟩
#align ne_zero_iff neZero_iff
-/

#print not_neZero /-
theorem not_neZero {R : Type _} [Zero R] {n : R} : ¬NeZero n ↔ n = 0 := by simp [neZero_iff]
#align not_ne_zero not_neZero
-/

#print eq_zero_or_neZero /-
theorem eq_zero_or_neZero {α} [Zero α] (a : α) : a = 0 ∨ NeZero a :=
  (eq_or_ne a 0).imp_right NeZero.mk
#align eq_zero_or_ne_zero eq_zero_or_neZero
-/

section

variable {α : Type _} [Zero α] [One α]

#print zero_ne_one /-
@[simp]
theorem zero_ne_one [NeZero (1 : α)] : (0 : α) ≠ 1 :=
  NeZero.ne' (1 : α)
#align zero_ne_one zero_ne_one
-/

#print one_ne_zero /-
@[simp]
theorem one_ne_zero [NeZero (1 : α)] : (1 : α) ≠ 0 :=
  NeZero.ne (1 : α)
#align one_ne_zero one_ne_zero
-/

/- warning: two_ne_zero -> two_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : Add.{u1} α] [_inst_4 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α _inst_3 (One.one.{u1} α _inst_2))))], Ne.{succ u1} α (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α _inst_3 (One.one.{u1} α _inst_2)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : OfNat.{u1} α (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] [_inst_3 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 2 _inst_2)], Ne.{succ u1} α (OfNat.ofNat.{u1} α 2 _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align two_ne_zero two_ne_zeroₓ'. -/
theorem two_ne_zero [Add α] [NeZero (2 : α)] : (2 : α) ≠ 0 :=
  NeZero.ne (2 : α)
#align two_ne_zero two_ne_zero

/- warning: three_ne_zero -> three_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : Add.{u1} α] [_inst_4 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 3 (OfNat.mk.{u1} α 3 (bit1.{u1} α _inst_2 _inst_3 (One.one.{u1} α _inst_2))))], Ne.{succ u1} α (OfNat.ofNat.{u1} α 3 (OfNat.mk.{u1} α 3 (bit1.{u1} α _inst_2 _inst_3 (One.one.{u1} α _inst_2)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : OfNat.{u1} α (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))] [_inst_3 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 3 _inst_2)], Ne.{succ u1} α (OfNat.ofNat.{u1} α 3 _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align three_ne_zero three_ne_zeroₓ'. -/
theorem three_ne_zero [Add α] [NeZero (3 : α)] : (3 : α) ≠ 0 :=
  NeZero.ne (3 : α)
#align three_ne_zero three_ne_zero

/- warning: four_ne_zero -> four_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : Add.{u1} α] [_inst_4 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 4 (OfNat.mk.{u1} α 4 (bit0.{u1} α _inst_3 (bit0.{u1} α _inst_3 (One.one.{u1} α _inst_2)))))], Ne.{succ u1} α (OfNat.ofNat.{u1} α 4 (OfNat.mk.{u1} α 4 (bit0.{u1} α _inst_3 (bit0.{u1} α _inst_3 (One.one.{u1} α _inst_2))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : OfNat.{u1} α (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))] [_inst_3 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 4 _inst_2)], Ne.{succ u1} α (OfNat.ofNat.{u1} α 4 _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align four_ne_zero four_ne_zeroₓ'. -/
theorem four_ne_zero [Add α] [NeZero (4 : α)] : (4 : α) ≠ 0 :=
  NeZero.ne (4 : α)
#align four_ne_zero four_ne_zero

#print ne_zero_of_eq_one /-
theorem ne_zero_of_eq_one [NeZero (1 : α)] {a : α} (h : a = 1) : a ≠ 0 :=
  calc
    a = 1 := h
    _ ≠ 0 := one_ne_zero
    
#align ne_zero_of_eq_one ne_zero_of_eq_one
-/

variable (α)

#print zero_ne_one' /-
theorem zero_ne_one' [NeZero (1 : α)] : (0 : α) ≠ 1 :=
  NeZero.ne' (1 : α)
#align zero_ne_one' zero_ne_one'
-/

#print one_ne_zero' /-
theorem one_ne_zero' [NeZero (1 : α)] : (1 : α) ≠ 0 :=
  NeZero.ne (1 : α)
#align one_ne_zero' one_ne_zero'
-/

/- warning: two_ne_zero' -> two_ne_zero' is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : Add.{u1} α] [_inst_4 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α _inst_3 (One.one.{u1} α _inst_2))))], Ne.{succ u1} α (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α _inst_3 (One.one.{u1} α _inst_2)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Zero.{u1} α] [_inst_2 : OfNat.{u1} α (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] [_inst_3 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 2 _inst_2)], Ne.{succ u1} α (OfNat.ofNat.{u1} α 2 _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align two_ne_zero' two_ne_zero'ₓ'. -/
theorem two_ne_zero' [Add α] [NeZero (2 : α)] : (2 : α) ≠ 0 :=
  NeZero.ne (2 : α)
#align two_ne_zero' two_ne_zero'

/- warning: three_ne_zero' -> three_ne_zero' is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : Add.{u1} α] [_inst_4 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 3 (OfNat.mk.{u1} α 3 (bit1.{u1} α _inst_2 _inst_3 (One.one.{u1} α _inst_2))))], Ne.{succ u1} α (OfNat.ofNat.{u1} α 3 (OfNat.mk.{u1} α 3 (bit1.{u1} α _inst_2 _inst_3 (One.one.{u1} α _inst_2)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Zero.{u1} α] [_inst_2 : OfNat.{u1} α (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))] [_inst_3 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 3 _inst_2)], Ne.{succ u1} α (OfNat.ofNat.{u1} α 3 _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align three_ne_zero' three_ne_zero'ₓ'. -/
theorem three_ne_zero' [Add α] [NeZero (3 : α)] : (3 : α) ≠ 0 :=
  NeZero.ne (3 : α)
#align three_ne_zero' three_ne_zero'

/- warning: four_ne_zero' -> four_ne_zero' is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : Add.{u1} α] [_inst_4 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 4 (OfNat.mk.{u1} α 4 (bit0.{u1} α _inst_3 (bit0.{u1} α _inst_3 (One.one.{u1} α _inst_2)))))], Ne.{succ u1} α (OfNat.ofNat.{u1} α 4 (OfNat.mk.{u1} α 4 (bit0.{u1} α _inst_3 (bit0.{u1} α _inst_3 (One.one.{u1} α _inst_2))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Zero.{u1} α] [_inst_2 : OfNat.{u1} α (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))] [_inst_3 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 4 _inst_2)], Ne.{succ u1} α (OfNat.ofNat.{u1} α 4 _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align four_ne_zero' four_ne_zero'ₓ'. -/
theorem four_ne_zero' [Add α] [NeZero (4 : α)] : (4 : α) ≠ 0 :=
  NeZero.ne (4 : α)
#align four_ne_zero' four_ne_zero'

end

namespace NeZero

variable {R S M F : Type _} {r : R} {x y : M} {n p : ℕ}

#print NeZero.succ /-
--{a : ℕ+}
instance succ : NeZero (n + 1) :=
  ⟨n.succ_ne_zero⟩
#align ne_zero.succ NeZero.succ
-/

#print NeZero.of_pos /-
theorem of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x :=
  ⟨ne_of_gt h⟩
#align ne_zero.of_pos NeZero.of_pos
-/

instance coe_trans [Zero M] [Coe R S] [CoeTC S M] [h : NeZero (r : M)] : NeZero ((r : S) : M) :=
  ⟨h.out⟩
#align ne_zero.coe_trans NeZero.coe_trans

theorem trans [Zero M] [Coe R S] [CoeTC S M] (h : NeZero ((r : S) : M)) : NeZero (r : M) :=
  ⟨h.out⟩
#align ne_zero.trans NeZero.trans

end NeZero

