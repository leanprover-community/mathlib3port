/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Algebra.FreeMonoid.Basic
import Data.List.Count

#align_import algebra.free_monoid.count from "leanprover-community/mathlib"@"f2f413b9d4be3a02840d0663dace76e8fe3da053"

/-!
# `list.count` as a bundled homomorphism

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `free_monoid.countp`, `free_monoid.count`, `free_add_monoid.countp`, and
`free_add_monoid.count`. These are `list.countp` and `list.count` bundled as multiplicative and
additive homomorphisms from `free_monoid` and `free_add_monoid`.

We do not use `to_additive` because it can't map `multiplicative ℕ` to `ℕ`.
-/


variable {α : Type _} (p : α → Prop) [DecidablePred p]

namespace FreeAddMonoid

#print FreeAddMonoid.countP /-
/-- `list.countp` as a bundled additive monoid homomorphism. -/
def countP (p : α → Prop) [DecidablePred p] : FreeAddMonoid α →+ ℕ :=
  ⟨List.countP p, List.countP_nil p, List.countP_append _⟩
#align free_add_monoid.countp FreeAddMonoid.countP
-/

#print FreeAddMonoid.countP_of /-
theorem countP_of (x : α) : countP p (of x) = if p x then 1 else 0 :=
  rfl
#align free_add_monoid.countp_of FreeAddMonoid.countP_of
-/

#print FreeAddMonoid.countP_apply /-
theorem countP_apply (l : FreeAddMonoid α) : countP p l = List.countP p l :=
  rfl
#align free_add_monoid.countp_apply FreeAddMonoid.countP_apply
-/

#print FreeAddMonoid.count /-
/-- `list.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ :=
  countP (Eq x)
#align free_add_monoid.count FreeAddMonoid.count
-/

#print FreeAddMonoid.count_of /-
theorem count_of [DecidableEq α] (x y : α) : count x (of y) = Pi.single x 1 y := by
  simp only [count, countp_of, Pi.single_apply, eq_comm]
#align free_add_monoid.count_of FreeAddMonoid.count_of
-/

#print FreeAddMonoid.count_apply /-
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : count x l = List.count x l :=
  rfl
#align free_add_monoid.count_apply FreeAddMonoid.count_apply
-/

end FreeAddMonoid

namespace FreeMonoid

#print FreeMonoid.countP /-
/-- `list.countp` as a bundled multiplicative monoid homomorphism. -/
def countP (p : α → Prop) [DecidablePred p] : FreeMonoid α →* Multiplicative ℕ :=
  (FreeAddMonoid.countP p).toMultiplicative
#align free_monoid.countp FreeMonoid.countP
-/

#print FreeMonoid.countP_of' /-
theorem countP_of' (x : α) :
    countP p (of x) = if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 :=
  rfl
#align free_monoid.countp_of' FreeMonoid.countP_of'
-/

#print FreeMonoid.countP_of /-
theorem countP_of (x : α) : countP p (of x) = if p x then Multiplicative.ofAdd 1 else 1 := by
  rw [countp_of', ofAdd_zero]
#align free_monoid.countp_of FreeMonoid.countP_of
-/

#print FreeMonoid.countP_apply /-
-- `rfl` is not transitive
theorem countP_apply (l : FreeAddMonoid α) : countP p l = Multiplicative.ofAdd (List.countP p l) :=
  rfl
#align free_monoid.countp_apply FreeMonoid.countP_apply
-/

#print FreeMonoid.count /-
/-- `list.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ :=
  countP (Eq x)
#align free_monoid.count FreeMonoid.count
-/

#print FreeMonoid.count_apply /-
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    count x l = Multiplicative.ofAdd (List.count x l) :=
  rfl
#align free_monoid.count_apply FreeMonoid.count_apply
-/

#print FreeMonoid.count_of /-
theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = @Pi.mulSingle α (fun _ => Multiplicative ℕ) _ _ x (Multiplicative.ofAdd 1) y :=
  by simp only [count, countp_of, Pi.mulSingle_apply, eq_comm]
#align free_monoid.count_of FreeMonoid.count_of
-/

end FreeMonoid

