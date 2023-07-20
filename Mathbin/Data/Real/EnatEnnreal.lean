/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.Enat.Basic
import Mathbin.Data.Real.Ennreal

#align_import data.real.enat_ennreal from "leanprover-community/mathlib"@"ee05e9ce1322178f0c12004eb93c00d2c8c00ed2"

/-!
# Coercion from `ℕ∞` to `ℝ≥0∞`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a coercion from `ℕ∞` to `ℝ≥0∞` and prove some basic lemmas about this map.
-/


open scoped Classical NNReal ENNReal

noncomputable section

namespace ENat

variable {m n : ℕ∞}

#print ENat.hasCoeENNReal /-
instance hasCoeENNReal : CoeTC ℕ∞ ℝ≥0∞ :=
  ⟨WithTop.map coe⟩
#align enat.has_coe_ennreal ENat.hasCoeENNReal
-/

#print ENat.map_coe_nnreal /-
@[simp]
theorem map_coe_nnreal : WithTop.map (coe : ℕ → ℝ≥0) = (coe : ℕ∞ → ℝ≥0∞) :=
  rfl
#align enat.map_coe_nnreal ENat.map_coe_nnreal
-/

#print ENat.toENNRealOrderEmbedding /-
/-- Coercion `ℕ∞ → ℝ≥0∞` as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def toENNRealOrderEmbedding : ℕ∞ ↪o ℝ≥0∞ :=
  Nat.castOrderEmbedding.withTop_map
#align enat.to_ennreal_order_embedding ENat.toENNRealOrderEmbedding
-/

#print ENat.toENNRealRingHom /-
/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps (config := { fullyApplied := false })]
def toENNRealRingHom : ℕ∞ →+* ℝ≥0∞ :=
  (Nat.castRingHom ℝ≥0).withTop_map Nat.cast_injective
#align enat.to_ennreal_ring_hom ENat.toENNRealRingHom
-/

#print ENat.toENNReal_top /-
@[simp, norm_cast]
theorem toENNReal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ :=
  rfl
#align enat.coe_ennreal_top ENat.toENNReal_top
-/

#print ENat.toENNReal_coe /-
@[simp, norm_cast]
theorem toENNReal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n :=
  rfl
#align enat.coe_ennreal_coe ENat.toENNReal_coe
-/

#print ENat.toENNReal_le /-
@[simp, norm_cast]
theorem toENNReal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  toENNRealOrderEmbedding.le_iff_le
#align enat.coe_ennreal_le ENat.toENNReal_le
-/

#print ENat.toENNReal_lt /-
@[simp, norm_cast]
theorem toENNReal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
  toENNRealOrderEmbedding.lt_iff_lt
#align enat.coe_ennreal_lt ENat.toENNReal_lt
-/

#print ENat.toENNReal_mono /-
@[mono]
theorem toENNReal_mono : Monotone (coe : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.Monotone
#align enat.coe_ennreal_mono ENat.toENNReal_mono
-/

#print ENat.toENNReal_strictMono /-
@[mono]
theorem toENNReal_strictMono : StrictMono (coe : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.StrictMono
#align enat.coe_ennreal_strict_mono ENat.toENNReal_strictMono
-/

#print ENat.toENNReal_zero /-
@[simp, norm_cast]
theorem toENNReal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 :=
  map_zero toENNRealRingHom
#align enat.coe_ennreal_zero ENat.toENNReal_zero
-/

#print ENat.toENNReal_add /-
@[simp]
theorem toENNReal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
  map_add toENNRealRingHom m n
#align enat.coe_ennreal_add ENat.toENNReal_add
-/

#print ENat.toENNReal_one /-
@[simp]
theorem toENNReal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 :=
  map_one toENNRealRingHom
#align enat.coe_ennreal_one ENat.toENNReal_one
-/

@[simp]
theorem coe_eNNReal_bit0 (n : ℕ∞) : ↑(bit0 n) = bit0 (n : ℝ≥0∞) :=
  toENNReal_add n n
#align enat.coe_ennreal_bit0 ENat.coe_eNNReal_bit0

@[simp]
theorem coe_eNNReal_bit1 (n : ℕ∞) : ↑(bit1 n) = bit1 (n : ℝ≥0∞) :=
  map_bit1 toENNRealRingHom n
#align enat.coe_ennreal_bit1 ENat.coe_eNNReal_bit1

#print ENat.toENNReal_mul /-
@[simp]
theorem toENNReal_mul (m n : ℕ∞) : ↑(m * n) = (m * n : ℝ≥0∞) :=
  map_mul toENNRealRingHom m n
#align enat.coe_ennreal_mul ENat.toENNReal_mul
-/

#print ENat.toENNReal_min /-
@[simp]
theorem toENNReal_min (m n : ℕ∞) : ↑(min m n) = (min m n : ℝ≥0∞) :=
  toENNReal_mono.map_min
#align enat.coe_ennreal_min ENat.toENNReal_min
-/

#print ENat.toENNReal_max /-
@[simp]
theorem toENNReal_max (m n : ℕ∞) : ↑(max m n) = (max m n : ℝ≥0∞) :=
  toENNReal_mono.map_max
#align enat.coe_ennreal_max ENat.toENNReal_max
-/

#print ENat.toENNReal_sub /-
@[simp]
theorem toENNReal_sub (m n : ℕ∞) : ↑(m - n) = (m - n : ℝ≥0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n
#align enat.coe_ennreal_sub ENat.toENNReal_sub
-/

end ENat

