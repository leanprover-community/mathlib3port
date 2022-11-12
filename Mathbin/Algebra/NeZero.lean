/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
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

