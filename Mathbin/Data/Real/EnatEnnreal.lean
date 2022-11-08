/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.Real.Ennreal
import Mathbin.Data.Enat.Basic

/-!
# Coercion from `ℕ∞` to `ℝ≥0∞`

In this file we define a coercion from `ℕ∞` to `ℝ≥0∞` and prove some basic lemmas about this map.
-/


open Classical Nnreal Ennreal

noncomputable section

namespace Enat

variable {m n : ℕ∞}

instance hasCoeEnnreal : CoeTC ℕ∞ ℝ≥0∞ :=
  ⟨WithTop.map coe⟩

@[simp]
theorem map_coe_nnreal : WithTop.map (coe : ℕ → ℝ≥0) = (coe : ℕ∞ → ℝ≥0∞) :=
  rfl

/-- Coercion `ℕ∞ → ℝ≥0∞` as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def toEnnrealOrderEmbedding : ℕ∞ ↪o ℝ≥0∞ :=
  Nat.castOrderEmbedding.with_top_map

/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps (config := { fullyApplied := false })]
def toEnnrealRingHom : ℕ∞ →+* ℝ≥0∞ :=
  (Nat.castRingHom ℝ≥0).with_top_map Nat.cast_injective

@[simp, norm_cast]
theorem coe_ennreal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  toEnnrealOrderEmbedding.le_iff_le

@[simp, norm_cast]
theorem coe_ennreal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
  toEnnrealOrderEmbedding.lt_iff_lt

@[mono]
theorem coe_ennreal_mono : Monotone (coe : ℕ∞ → ℝ≥0∞) :=
  toEnnrealOrderEmbedding.Monotone

@[mono]
theorem coe_ennreal_strict_mono : StrictMono (coe : ℕ∞ → ℝ≥0∞) :=
  toEnnrealOrderEmbedding.StrictMono

@[simp, norm_cast]
theorem coe_ennreal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 :=
  map_zero toEnnrealRingHom

@[simp]
theorem coe_ennreal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
  map_add toEnnrealRingHom m n

@[simp]
theorem coe_ennreal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 :=
  map_one toEnnrealRingHom

@[simp]
theorem coe_ennreal_bit0 (n : ℕ∞) : ↑(bit0 n) = bit0 (n : ℝ≥0∞) :=
  coe_ennreal_add n n

@[simp]
theorem coe_ennreal_bit1 (n : ℕ∞) : ↑(bit1 n) = bit1 (n : ℝ≥0∞) :=
  map_bit1 toEnnrealRingHom n

@[simp]
theorem coe_ennreal_mul (m n : ℕ∞) : ↑(m * n) = (m * n : ℝ≥0∞) :=
  map_mul toEnnrealRingHom m n

@[simp]
theorem coe_ennreal_min (m n : ℕ∞) : ↑(min m n) = (min m n : ℝ≥0∞) :=
  coe_ennreal_mono.map_min

@[simp]
theorem coe_ennreal_max (m n : ℕ∞) : ↑(max m n) = (max m n : ℝ≥0∞) :=
  coe_ennreal_mono.map_max

@[simp]
theorem coe_ennreal_sub (m n : ℕ∞) : ↑(m - n) = (m - n : ℝ≥0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n

end Enat

