/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Analysis.Normed.Group.Quotient
import Mathbin.Topology.Instances.AddCircle

/-!
# The additive circle as a normed group

We define the normed group structure on `add_circle p`, for `p : ℝ`. For example if `p = 1` then:
`∥(x : add_circle 1)∥ = |x - round x|` for any `x : ℝ` (see `unit_add_circle.norm_eq`).

## Main definitions:

 * `add_circle.norm_eq`: a characterisation of the norm on `add_circle p`

## TODO

 * The fact `inner_product_geometry.angle (real.cos θ) (real.sin θ) = ∥(θ : real.angle)∥`

-/


noncomputable section

open Set

open Int hiding mem_zmultiples_iff

open AddSubgroup

namespace AddCircle

variable (p : ℝ)

instance : NormedAddCommGroup (AddCircle p) :=
  AddSubgroup.normedAddCommGroupQuotient _

@[simp]
theorem norm_coe_mul (x : ℝ) (t : ℝ) : ∥(↑(t * x) : AddCircle (t * p))∥ = abs t * ∥(x : AddCircle p)∥ := by
  have aux : ∀ {a b c : ℝ}, a ∈ zmultiples b → c * a ∈ zmultiples (c * b) := fun a b c h => by
    simp only [mem_zmultiples_iff] at h⊢
    obtain ⟨n, rfl⟩ := h
    exact ⟨n, (mul_smul_comm n c b).symm⟩
  rcases eq_or_ne t 0 with (rfl | ht)
  · simp
    
  have ht' : abs t ≠ 0 := (not_congr abs_eq_zero).mpr ht
  simp only [quotient_norm_eq, Real.norm_eq_abs]
  conv_rhs => rw [← smul_eq_mul, ← Real.Inf_smul_of_nonneg (abs_nonneg t)]
  simp only [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
  congr 1
  ext z
  rw [mem_smul_set_iff_inv_smul_mem₀ ht']
  show (∃ y, y - t * x ∈ zmultiples (t * p) ∧ abs y = z) ↔ ∃ w, w - x ∈ zmultiples p ∧ abs w = (abs t)⁻¹ * z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine' ⟨t⁻¹ * y, _, by rw [abs_mul, abs_inv]⟩
    rw [← inv_mul_cancel_left₀ ht x, ← inv_mul_cancel_left₀ ht p, ← mul_sub]
    exact aux hy
    
  · rintro ⟨w, hw, hw'⟩
    refine' ⟨t * w, _, by rw [← (eq_inv_mul_iff_mul_eq₀ ht').mp hw', abs_mul]⟩
    rw [← mul_sub]
    exact aux hw
    

@[simp]
theorem norm_eq_of_zero {x : ℝ} : ∥(x : AddCircle (0 : ℝ))∥ = abs x := by
  suffices { y : ℝ | (y : AddCircle (0 : ℝ)) = (x : AddCircle (0 : ℝ)) } = {x} by
    rw [quotient_norm_eq, this, image_singleton, Real.norm_eq_abs, cInf_singleton]
  ext y
  simp [QuotientAddGroup.eq_iff_sub_mem, mem_zmultiples_iff, sub_eq_zero]

theorem norm_eq {x : ℝ} : ∥(x : AddCircle p)∥ = abs (x - round (p⁻¹ * x) * p) := by
  suffices ∀ x : ℝ, ∥(x : AddCircle (1 : ℝ))∥ = abs (x - round x) by
    rcases eq_or_ne p 0 with (rfl | hp)
    · simp
      
    intros
    have hx := norm_coe_mul p x p⁻¹
    rw [abs_inv, eq_inv_mul_iff_mul_eq₀ ((not_congr abs_eq_zero).mpr hp)] at hx
    rw [← hx, inv_mul_cancel hp, this, ← abs_mul, mul_sub, mul_inv_cancel_left₀ hp, mul_comm p]
  clear x p
  intros
  rw [quotient_norm_eq, abs_sub_round_eq_min]
  have h₁ : BddBelow (abs '' { m : ℝ | (m : AddCircle (1 : ℝ)) = x }) := ⟨0, by simp [mem_lower_bounds]⟩
  have h₂ : (abs '' { m : ℝ | (m : AddCircle (1 : ℝ)) = x }).Nonempty := ⟨abs x, ⟨x, rfl, rfl⟩⟩
  apply le_antisymmₓ
  · simp only [le_min_iff, Real.norm_eq_abs, cInf_le_iff h₁ h₂]
    intro b h
    refine'
      ⟨mem_lower_bounds.1 h _ ⟨fract x, _, abs_fract⟩,
        mem_lower_bounds.1 h _ ⟨fract x - 1, _, by rw [abs_sub_comm, abs_one_sub_fract]⟩⟩
    · simp only [mem_set_of_eq, fract, sub_eq_self, QuotientAddGroup.coe_sub, QuotientAddGroup.eq_zero_iff,
        int_cast_mem_zmultiples_one]
      
    · simp only [mem_set_of_eq, fract, sub_eq_self, QuotientAddGroup.coe_sub, QuotientAddGroup.eq_zero_iff,
        int_cast_mem_zmultiples_one, sub_sub, (by norm_cast : (⌊x⌋ : ℝ) + 1 = (↑(⌊x⌋ + 1) : ℝ))]
      
    
  · simp only [QuotientAddGroup.mk'_apply, Real.norm_eq_abs, le_cInf_iff h₁ h₂]
    rintro b' ⟨b, hb, rfl⟩
    simp only [mem_set_of_eq, QuotientAddGroup.eq_iff_sub_mem, mem_zmultiples_iff, smul_one_eq_coe] at hb
    obtain ⟨z, hz⟩ := hb
    rw [(by
        rw [hz]
        abel : x = b - z),
      fract_sub_int, ← abs_sub_round_eq_min]
    exact abs_sub_round_le_abs_self _
    

end AddCircle

namespace UnitAddCircle

theorem norm_eq {x : ℝ} : ∥(x : UnitAddCircle)∥ = abs (x - round x) := by simp [AddCircle.norm_eq]

end UnitAddCircle

