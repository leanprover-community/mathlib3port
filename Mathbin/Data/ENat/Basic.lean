/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Data.Nat.SuccPred
import Algebra.CharZero.Lemmas
import Algebra.Order.Sub.WithTop
import Algebra.Order.Ring.WithTop

#align_import data.enat.basic from "leanprover-community/mathlib"@"ceb887ddf3344dab425292e497fa2af91498437c"

/-!
# Definition and basic properties of extended natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `enat` (notation: `ℕ∞`) to be `with_top ℕ` and prove some basic lemmas
about this type.
-/


/- ././././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler has_coe_t[has_coe_t] exprℕ() -/
#print ENat /-
/-- Extended natural numbers `ℕ∞ = with_top ℕ`. -/
def ENat : Type :=
  WithTop ℕ
deriving Zero, AddCommMonoidWithOne, CanonicallyOrderedCommSemiring, Nontrivial, LinearOrder,
  OrderBot, OrderTop, Bot, Top, CanonicallyLinearOrderedAddCommMonoid, Sub, OrderedSub,
  LinearOrderedAddCommMonoidWithTop, SuccOrder, WellFoundedLT, WellFoundedRelation, CharZero,
  «././././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler has_coe_t[has_coe_t] exprℕ()»
#align enat ENat
-/

notation "ℕ∞" => ENat

namespace ENat

instance : Inhabited ℕ∞ :=
  ⟨0⟩

instance : IsWellOrder ℕ∞ (· < ·) where

variable {m n : ℕ∞}

#print ENat.coe_zero /-
-- eligible for `dsimp`
@[simp, nolint simp_nf, norm_cast]
theorem coe_zero : ((0 : ℕ) : ℕ∞) = 0 :=
  rfl
#align enat.coe_zero ENat.coe_zero
-/

#print ENat.coe_one /-
@[simp, norm_cast]
theorem coe_one : ((1 : ℕ) : ℕ∞) = 1 :=
  rfl
#align enat.coe_one ENat.coe_one
-/

#print ENat.coe_add /-
@[simp, norm_cast]
theorem coe_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) :=
  rfl
#align enat.coe_add ENat.coe_add
-/

#print ENat.coe_sub /-
@[simp, norm_cast]
theorem coe_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) :=
  rfl
#align enat.coe_sub ENat.coe_sub
-/

#print ENat.coe_mul /-
@[simp, norm_cast]
theorem coe_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) :=
  WithTop.coe_mul
#align enat.coe_mul ENat.coe_mul
-/

#print ENat.canLift /-
instance canLift : CanLift ℕ∞ ℕ coe fun n => n ≠ ⊤ :=
  WithTop.canLift
#align enat.can_lift ENat.canLift
-/

#print ENat.toNat /-
/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNat : MonoidWithZeroHom ℕ∞ ℕ
    where
  toFun := WithTop.untop' 0
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untop'_zero_mul
#align enat.to_nat ENat.toNat
-/

#print ENat.toNat_coe /-
@[simp]
theorem toNat_coe (n : ℕ) : toNat n = n :=
  rfl
#align enat.to_nat_coe ENat.toNat_coe
-/

#print ENat.toNat_top /-
@[simp]
theorem toNat_top : toNat ⊤ = 0 :=
  rfl
#align enat.to_nat_top ENat.toNat_top
-/

#print ENat.coe_toNat_eq_self /-
@[simp]
theorem coe_toNat_eq_self : ↑n.toNat = n ↔ n ≠ ⊤ :=
  WithTop.recTopCoe (by simp) (by simp) n
#align enat.coe_to_nat_eq_self ENat.coe_toNat_eq_self
-/

alias ⟨_, coe_to_nat⟩ := coe_to_nat_eq_self
#align enat.coe_to_nat ENat.coe_toNat

#print ENat.coe_toNat_le_self /-
theorem coe_toNat_le_self (n : ℕ∞) : ↑(toNat n) ≤ n :=
  WithTop.recTopCoe le_top (fun k => le_rfl) n
#align enat.coe_to_nat_le_self ENat.coe_toNat_le_self
-/

#print ENat.toNat_add /-
theorem toNat_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) : toNat (m + n) = toNat m + toNat n := by
  lift m to ℕ using hm; lift n to ℕ using hn; rfl
#align enat.to_nat_add ENat.toNat_add
-/

#print ENat.toNat_sub /-
theorem toNat_sub {n : ℕ∞} (hn : n ≠ ⊤) (m : ℕ∞) : toNat (m - n) = toNat m - toNat n :=
  by
  lift n to ℕ using hn
  induction m using WithTop.recTopCoe
  · rw [WithTop.top_sub_coe, to_nat_top, zero_tsub]
  · rw [← coe_sub, to_nat_coe, to_nat_coe, to_nat_coe]
#align enat.to_nat_sub ENat.toNat_sub
-/

#print ENat.toNat_eq_iff /-
theorem toNat_eq_iff {m : ℕ∞} {n : ℕ} (hn : n ≠ 0) : m.toNat = n ↔ m = n := by
  induction m using WithTop.recTopCoe <;> simp [hn.symm]
#align enat.to_nat_eq_iff ENat.toNat_eq_iff
-/

#print ENat.succ_def /-
@[simp]
theorem succ_def (m : ℕ∞) : Order.succ m = m + 1 := by cases m <;> rfl
#align enat.succ_def ENat.succ_def
-/

#print ENat.add_one_le_of_lt /-
theorem add_one_le_of_lt (h : m < n) : m + 1 ≤ n :=
  m.succ_def ▸ Order.succ_le_of_lt h
#align enat.add_one_le_of_lt ENat.add_one_le_of_lt
-/

#print ENat.add_one_le_iff /-
theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  m.succ_def ▸ (Order.succ_le_iff_of_not_isMax <| by rwa [isMax_iff_eq_top])
#align enat.add_one_le_iff ENat.add_one_le_iff
-/

#print ENat.one_le_iff_pos /-
theorem one_le_iff_pos : 1 ≤ n ↔ 0 < n :=
  add_one_le_iff WithTop.zero_ne_top
#align enat.one_le_iff_pos ENat.one_le_iff_pos
-/

#print ENat.one_le_iff_ne_zero /-
theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
  one_le_iff_pos.trans pos_iff_ne_zero
#align enat.one_le_iff_ne_zero ENat.one_le_iff_ne_zero
-/

#print ENat.le_of_lt_add_one /-
theorem le_of_lt_add_one (h : m < n + 1) : m ≤ n :=
  Order.le_of_lt_succ <| n.succ_def.symm ▸ h
#align enat.le_of_lt_add_one ENat.le_of_lt_add_one
-/

#print ENat.nat_induction /-
@[elab_as_elim]
theorem nat_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a :=
  by
  have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc
  cases a
  exacts [htop A, A a]
#align enat.nat_induction ENat.nat_induction
-/

end ENat

