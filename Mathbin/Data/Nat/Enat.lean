/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.Nat.Lattice
import Mathbin.Data.Nat.SuccPred

/-!
# Definition and basic properties of extended natural numbers

In this file we define `enat` (notation: `ℕ∞`) to be `with_top ℕ` and prove some basic lemmas
about this type.
-/


/-- Extended natural numbers `ℕ∞ = with_top ℕ`. -/
def Enat : Type :=
  WithTop ℕ deriving Zero, AddCommMonoidWithOne, CanonicallyOrderedCommSemiring, Nontrivial, LinearOrderₓ, OrderBot,
  OrderTop, HasBot, HasTop, CanonicallyLinearOrderedAddMonoid, Sub, HasOrderedSub, CompleteLinearOrder,
  LinearOrderedAddCommMonoidWithTop, SuccOrder

-- mathport name: «exprℕ∞»
notation "ℕ∞" => Enat

namespace Enat

instance : Inhabited ℕ∞ :=
  ⟨0⟩

variable {m n : ℕ∞}

@[simp, norm_cast]
theorem coe_zero : ((0 : ℕ) : ℕ∞) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℕ) : ℕ∞) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) :=
  WithTop.coe_mul

instance : CanLift ℕ∞ ℕ :=
  WithTop.canLift

/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNat : MonoidWithZeroHom ℕ∞ ℕ where
  toFun := WithTop.untop' 0
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untop'_zero_mul

@[simp]
theorem succ_def (m : ℕ∞) : Order.succ m = m + 1 := by
  cases m <;> rfl

theorem add_one_le_of_lt (h : m < n) : m + 1 ≤ n :=
  m.succ_def ▸ Order.succ_le_of_lt h

theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  m.succ_def ▸
    (Order.succ_le_iff_of_not_is_max <| by
      rwa [is_max_iff_eq_top])

theorem one_le_iff_pos : 1 ≤ n ↔ 0 < n :=
  add_one_le_iff WithTop.zero_ne_top

theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
  one_le_iff_pos.trans pos_iff_ne_zero

theorem le_of_lt_add_one (h : m < n + 1) : m ≤ n :=
  Order.le_of_lt_succ <| n.succ_def.symm ▸ h

@[elabAsElim]
theorem nat_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a := by
  have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc
  cases a
  exacts[htop A, A a]

end Enat

