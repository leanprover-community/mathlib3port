/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.real.enat_ennreal
! leanprover-community/mathlib commit 6cb77a8eaff0ddd100e87b1591c6d3ad319514ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Enat.Basic
import Mathbin.Data.Real.Ennreal

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
#align enat.has_coe_ennreal Enat.hasCoeEnnreal

@[simp]
theorem map_coe_nnreal : WithTop.map (coe : ℕ → ℝ≥0) = (coe : ℕ∞ → ℝ≥0∞) :=
  rfl
#align enat.map_coe_nnreal Enat.map_coe_nnreal

/-- Coercion `ℕ∞ → ℝ≥0∞` as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def toEnnrealOrderEmbedding : ℕ∞ ↪o ℝ≥0∞ :=
  Nat.castOrderEmbedding.with_top_map
#align enat.to_ennreal_order_embedding Enat.toEnnrealOrderEmbedding

/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps (config := { fullyApplied := false })]
def toEnnrealRingHom : ℕ∞ →+* ℝ≥0∞ :=
  (Nat.castRingHom ℝ≥0).with_top_map Nat.cast_injective
#align enat.to_ennreal_ring_hom Enat.toEnnrealRingHom

@[simp, norm_cast]
theorem coe_ennreal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ :=
  rfl
#align enat.coe_ennreal_top Enat.coe_ennreal_top

@[simp, norm_cast]
theorem coe_ennreal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n :=
  rfl
#align enat.coe_ennreal_coe Enat.coe_ennreal_coe

@[simp, norm_cast]
theorem coe_ennreal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  toEnnrealOrderEmbedding.le_iff_le
#align enat.coe_ennreal_le Enat.coe_ennreal_le

@[simp, norm_cast]
theorem coe_ennreal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
  toEnnrealOrderEmbedding.lt_iff_lt
#align enat.coe_ennreal_lt Enat.coe_ennreal_lt

@[mono]
theorem coe_ennreal_mono : Monotone (coe : ℕ∞ → ℝ≥0∞) :=
  toEnnrealOrderEmbedding.Monotone
#align enat.coe_ennreal_mono Enat.coe_ennreal_mono

@[mono]
theorem coe_ennreal_strict_mono : StrictMono (coe : ℕ∞ → ℝ≥0∞) :=
  toEnnrealOrderEmbedding.StrictMono
#align enat.coe_ennreal_strict_mono Enat.coe_ennreal_strict_mono

@[simp, norm_cast]
theorem coe_ennreal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 :=
  map_zero toEnnrealRingHom
#align enat.coe_ennreal_zero Enat.coe_ennreal_zero

@[simp]
theorem coe_ennreal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
  map_add toEnnrealRingHom m n
#align enat.coe_ennreal_add Enat.coe_ennreal_add

@[simp]
theorem coe_ennreal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 :=
  map_one toEnnrealRingHom
#align enat.coe_ennreal_one Enat.coe_ennreal_one

@[simp]
theorem coe_ennreal_bit0 (n : ℕ∞) : ↑(bit0 n) = bit0 (n : ℝ≥0∞) :=
  coe_ennreal_add n n
#align enat.coe_ennreal_bit0 Enat.coe_ennreal_bit0

@[simp]
theorem coe_ennreal_bit1 (n : ℕ∞) : ↑(bit1 n) = bit1 (n : ℝ≥0∞) :=
  map_bit1 toEnnrealRingHom n
#align enat.coe_ennreal_bit1 Enat.coe_ennreal_bit1

@[simp]
theorem coe_ennreal_mul (m n : ℕ∞) : ↑(m * n) = (m * n : ℝ≥0∞) :=
  map_mul toEnnrealRingHom m n
#align enat.coe_ennreal_mul Enat.coe_ennreal_mul

@[simp]
theorem coe_ennreal_min (m n : ℕ∞) : ↑(min m n) = (min m n : ℝ≥0∞) :=
  coe_ennreal_mono.map_min
#align enat.coe_ennreal_min Enat.coe_ennreal_min

@[simp]
theorem coe_ennreal_max (m n : ℕ∞) : ↑(max m n) = (max m n : ℝ≥0∞) :=
  coe_ennreal_mono.map_max
#align enat.coe_ennreal_max Enat.coe_ennreal_max

@[simp]
theorem coe_ennreal_sub (m n : ℕ∞) : ↑(m - n) = (m - n : ℝ≥0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n
#align enat.coe_ennreal_sub Enat.coe_ennreal_sub

end Enat

