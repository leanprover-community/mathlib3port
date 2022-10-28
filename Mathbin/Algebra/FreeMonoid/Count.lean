/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.FreeMonoid.Basic
import Mathbin.Data.List.Count

/-!
# `list.count` as a bundled homomorphism

In this file we define `free_monoid.countp`, `free_monoid.count`, `free_add_monoid.countp`, and
`free_add_monoid.count`. These are `list.countp` and `list.count` bundled as multiplicative and
additive homomorphisms from `free_monoid` and `free_add_monoid`.

We do not use `to_additive` because it can't map `multiplicative ℕ` to `ℕ`.
-/


variable {α : Type _} (p : α → Prop) [DecidablePred p]

namespace FreeAddMonoid

/-- `list.countp` as a bundled additive monoid homomorphism. -/
def countp (p : α → Prop) [DecidablePred p] : FreeAddMonoid α →+ ℕ :=
  ⟨List.countp p, List.countp_nil p, List.countp_append _⟩

theorem countp_of (x : α) : countp p (of x) = if p x then 1 else 0 :=
  rfl

theorem countp_apply (l : FreeAddMonoid α) : countp p l = List.countp p l :=
  rfl

/-- `list.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ :=
  countp (Eq x)

theorem count_of [DecidableEq α] (x y : α) : count x (of y) = Pi.single x 1 y := by
  simp only [count, countp_of, Pi.single_apply, eq_comm]

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : count x l = List.count x l :=
  rfl

end FreeAddMonoid

namespace FreeMonoid

/-- `list.countp` as a bundled multiplicative monoid homomorphism. -/
def countp (p : α → Prop) [DecidablePred p] : FreeMonoid α →* Multiplicative ℕ :=
  (FreeAddMonoid.countp p).toMultiplicative

theorem countp_of' (x : α) : countp p (of x) = if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 :=
  rfl

theorem countp_of (x : α) : countp p (of x) = if p x then Multiplicative.ofAdd 1 else 1 := by
  rw [countp_of', of_add_zero]

-- `rfl` is not transitive
theorem countp_apply (l : FreeAddMonoid α) : countp p l = Multiplicative.ofAdd (List.countp p l) :=
  rfl

/-- `list.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ :=
  countp (Eq x)

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : count x l = Multiplicative.ofAdd (List.count x l) :=
  rfl

theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = @Pi.mulSingle α (fun _ => Multiplicative ℕ) _ _ x (Multiplicative.ofAdd 1) y := by
  simp only [count, countp_of, Pi.mul_single_apply, eq_comm]

end FreeMonoid

