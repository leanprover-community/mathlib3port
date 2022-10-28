/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Algebra.Order.Sub.Basic
import Mathbin.Algebra.Order.Monoid.WithTop

/-!
# Lemma about subtraction in ordered monoids with a top element adjoined.
-/


variable {α : Type _}

namespace WithTop

section

variable [Sub α] [Zero α]

/-- If `α` has subtraction and `0`, we can extend the subtraction to `with_top α`. -/
protected def sub : ∀ a b : WithTop α, WithTop α
  | _, ⊤ => 0
  | ⊤, (x : α) => ⊤
  | (x : α), (y : α) => (x - y : α)

instance : Sub (WithTop α) :=
  ⟨WithTop.sub⟩

@[simp, norm_cast]
theorem coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b :=
  rfl

@[simp]
theorem top_sub_coe {a : α} : (⊤ : WithTop α) - a = ⊤ :=
  rfl

@[simp]
theorem sub_top {a : WithTop α} : a - ⊤ = 0 := by cases a <;> rfl

end

variable [CanonicallyOrderedAddMonoid α] [Sub α] [HasOrderedSub α]

instance : HasOrderedSub (WithTop α) := by
  constructor
  rintro x y z
  induction y using WithTop.recTopCoe
  · simp
    
  induction x using WithTop.recTopCoe
  · simp
    
  induction z using WithTop.recTopCoe
  · simp
    
  norm_cast
  exact tsub_le_iff_right

end WithTop

