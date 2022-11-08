/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
import Mathbin.Order.Basic
import Mathbin.Algebra.NeZero

/-!
# The positive natural numbers

This file contains the definitions, and basic results.
Most algebraic facts are deferred to `data.pnat.basic`, as they need more imports.
-/


/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def Pnat :=
  { n : ℕ // 0 < n }deriving DecidableEq, LinearOrder

-- mathport name: «exprℕ+»
notation "ℕ+" => Pnat

instance : One ℕ+ :=
  ⟨⟨1, Nat.zero_lt_one⟩⟩

instance coePnatNat : Coe ℕ+ ℕ :=
  ⟨Subtype.val⟩

instance : Repr ℕ+ :=
  ⟨fun n => repr n.1⟩

namespace Pnat

@[simp]
theorem mk_coe (n h) : ((⟨n, h⟩ : ℕ+) : ℕ) = n :=
  rfl

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
def natPred (i : ℕ+) : ℕ :=
  i - 1

@[simp]
theorem nat_pred_eq_pred {n : ℕ} (h : 0 < n) : natPred (⟨n, h⟩ : ℕ+) = n.pred :=
  rfl

end Pnat

namespace Nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def toPnat (n : ℕ) (h : 0 < n := by decide) : ℕ+ :=
  ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
def succPnat (n : ℕ) : ℕ+ :=
  ⟨succ n, succ_pos n⟩

@[simp]
theorem succ_pnat_coe (n : ℕ) : (succPnat n : ℕ) = succ n :=
  rfl

@[simp]
theorem nat_pred_succ_pnat (n : ℕ) : n.succPnat.natPred = n :=
  rfl

@[simp]
theorem _root_.pnat.succ_pnat_nat_pred (n : ℕ+) : n.natPred.succPnat = n :=
  Subtype.eq <| succ_pred_eq_of_pos n.2

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def toPnat' (n : ℕ) : ℕ+ :=
  succPnat (pred n)

@[simp]
theorem to_pnat'_coe : ∀ n : ℕ, (toPnat' n : ℕ) = ite (0 < n) n 1
  | 0 => rfl
  | m + 1 => by
    rw [if_pos (succ_pos m)]
    rfl

end Nat

namespace Pnat

open Nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/
@[simp]
theorem mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k :=
  Iff.rfl

@[simp]
theorem mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k :=
  Iff.rfl

@[simp]
theorem pos (n : ℕ+) : 0 < (n : ℕ) :=
  n.2

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n :=
  Subtype.eq

theorem coe_injective : Function.Injective (coe : ℕ+ → ℕ) :=
  Subtype.coe_injective

@[simp]
theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 :=
  n.2.ne'

instance _root_.ne_zero.pnat {a : ℕ+} : NeZero (a : ℕ) :=
  ⟨a.NeZero⟩

theorem to_pnat'_coe {n : ℕ} : 0 < n → (n.toPnat' : ℕ) = n :=
  succ_pred_eq_of_pos

@[simp]
theorem coe_to_pnat' (n : ℕ+) : (n : ℕ).toPnat' = n :=
  eq (to_pnat'_coe n.Pos)

@[simp]
theorem one_le (n : ℕ+) : (1 : ℕ+) ≤ n :=
  n.2

@[simp]
theorem not_lt_one (n : ℕ+) : ¬n < 1 :=
  not_lt_of_le n.one_le

instance : Inhabited ℕ+ :=
  ⟨1⟩

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
theorem mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) :=
  rfl

@[norm_cast]
theorem one_coe : ((1 : ℕ+) : ℕ) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 :=
  Subtype.coe_injective.eq_iff' one_coe

instance : HasWellFounded ℕ+ :=
  ⟨(· < ·), measure_wf coe⟩

/-- Strong induction on `ℕ+`. -/
def strongInductionOn {p : ℕ+ → Sort _} : ∀ (n : ℕ+) (h : ∀ k, (∀ m, m < k → p m) → p k), p n
  | n => fun IH => IH _ fun a h => strong_induction_on a IH

/-- We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def modDivAux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
  | k, 0, q => ⟨k, q.pred⟩
  | k, r + 1, q => ⟨⟨r + 1, Nat.succ_pos r⟩, q⟩

/-- `mod_div m k = (m % k, m / k)`.
  We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def modDiv (m k : ℕ+) : ℕ+ × ℕ :=
  modDivAux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
def mod (m k : ℕ+) : ℕ+ :=
  (modDiv m k).1

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
def div (m k : ℕ+) : ℕ :=
  (modDiv m k).2

theorem mod_coe (m k : ℕ+) : (mod m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) := by
  dsimp [mod, mod_div]
  cases (m : ℕ) % (k : ℕ)
  · rw [if_pos rfl]
    rfl
    
  · rw [if_neg n.succ_ne_zero]
    rfl
    

theorem div_coe (m k : ℕ+) : (div m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) :=
  by
  dsimp [div, mod_div]
  cases (m : ℕ) % (k : ℕ)
  · rw [if_pos rfl]
    rfl
    
  · rw [if_neg n.succ_ne_zero]
    rfl
    

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
def divExact (m k : ℕ+) : ℕ+ :=
  ⟨(div m k).succ, Nat.succ_pos _⟩

end Pnat

section CanLift

instance Nat.canLiftPnat : CanLift ℕ ℕ+ coe ((· < ·) 0) :=
  ⟨fun n hn => ⟨Nat.toPnat' n, Pnat.to_pnat'_coe hn⟩⟩

instance Int.canLiftPnat : CanLift ℤ ℕ+ coe ((· < ·) 0) :=
  ⟨fun n hn =>
    ⟨Nat.toPnat' (Int.natAbs n), by
      rw [coe_coe, Nat.to_pnat'_coe, if_pos (Int.nat_abs_pos_of_ne_zero hn.ne'), Int.nat_abs_of_nonneg hn.le]⟩⟩

end CanLift

