import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The type of angles

In this file we define `real.angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/


open_locale Real

noncomputable section

namespace Real

/-- The type of angles -/
def angle : Type :=
  ℝ ⧸ AddSubgroup.zmultiples (2 * π)

namespace Angle

instance angle.add_comm_group : AddCommGroupₓ angle :=
  QuotientAddGroup.addCommGroup _

instance : Inhabited angle :=
  ⟨0⟩

instance : Coe ℝ angle :=
  ⟨QuotientAddGroup.mk' _⟩

/-- Coercion `ℝ → angle` as an additive homomorphism. -/
def coe_hom : ℝ →+ angle :=
  QuotientAddGroup.mk' _

@[simp]
theorem coe_coe_hom : (coe_hom : ℝ → angle) = coeₓ :=
  rfl

@[simp]
theorem coe_zero : ↑(0 : ℝ) = (0 : angle) :=
  rfl

@[simp]
theorem coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : angle) :=
  rfl

@[simp]
theorem coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : angle) :=
  rfl

@[simp]
theorem coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : angle) :=
  rfl

@[simp, norm_cast]
theorem coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) : ↑((n : ℝ) * x) = n • (↑x : angle) := by
  simpa only [nsmul_eq_mul] using coe_hom.map_nsmul x n

@[simp, norm_cast]
theorem coe_int_mul_eq_zsmul (x : ℝ) (n : ℤ) : ↑((n : ℝ) * x : ℝ) = n • (↑x : angle) := by
  simpa only [zsmul_eq_mul] using coe_hom.map_zsmul x n

theorem angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k := by
  simp only [QuotientAddGroup.eq, AddSubgroup.zmultiples_eq_closure, AddSubgroup.mem_closure_singleton, zsmul_eq_mul',
    (sub_eq_neg_add _ _).symm, eq_comm]

@[simp]
theorem coe_two_pi : ↑(2 * π : ℝ) = (0 : angle) :=
  angle_eq_iff_two_pi_dvd_sub.2
    ⟨1, by
      rw [sub_zero, Int.cast_one, mul_oneₓ]⟩

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : ℝ} : cos θ = cos ψ ↔ (θ : angle) = ψ ∨ (θ : angle) = -ψ := by
  constructor
  · intro Hcos
    rw [← sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero, eq_false_intro two_ne_zero, false_orₓ,
      sin_eq_zero_iff, sin_eq_zero_iff] at Hcos
    rcases Hcos with (⟨n, hn⟩ | ⟨n, hn⟩)
    · right
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), ← sub_eq_iff_eq_add] at hn
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assocₓ, coe_int_mul_eq_zsmul, mul_commₓ,
        coe_two_pi, zsmul_zero]
      
    · left
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), eq_sub_iff_add_eq] at hn
      rw [← hn, coe_add, mul_assocₓ, coe_int_mul_eq_zsmul, mul_commₓ, coe_two_pi, zsmul_zero, zero_addₓ]
      
    infer_instance
    
  · rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    rw [← sub_eq_zero, cos_sub_cos, H, mul_assocₓ 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_commₓ π _,
      sin_int_mul_pi, mul_zero]
    rw [← sub_eq_zero, cos_sub_cos, ← sub_neg_eq_add, H, mul_assocₓ 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _ _),
      mul_commₓ π _, sin_int_mul_pi, mul_zero, zero_mul]
    

theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : ℝ} : sin θ = sin ψ ↔ (θ : angle) = ψ ∨ (θ : angle) + ψ = π := by
  constructor
  · intro Hsin
    rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin
    cases' cos_eq_iff_eq_or_eq_neg.mp Hsin with h h
    · left
      rw [coe_sub, coe_sub] at h
      exact sub_right_inj.1 h
      
    right
    rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub, sub_add_eq_add_sub, ← coe_add, add_halves, sub_sub,
      sub_eq_zero] at h
    exact h.symm
    
  · rw [angle_eq_iff_two_pi_dvd_sub, ← eq_sub_iff_add_eq, ← coe_sub, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    rw [← sub_eq_zero, sin_sub_sin, H, mul_assocₓ 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_commₓ π _,
      sin_int_mul_pi, mul_zero, zero_mul]
    have H' : θ + ψ = 2 * k * π + π := by
      rwa [← sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add, mul_assocₓ, mul_commₓ π _, ← mul_assocₓ] at H
    rw [← sub_eq_zero, sin_sub_sin, H', add_div, mul_assocₓ 2 _ π, mul_div_cancel_left _ (@two_ne_zero ℝ _ _),
      cos_add_pi_div_two, sin_int_mul_pi, neg_zero, mul_zero]
    

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : angle) = ψ := by
  cases' cos_eq_iff_eq_or_eq_neg.mp Hcos with hc hc
  · exact hc
    
  cases' sin_eq_iff_eq_or_add_eq_pi.mp Hsin with hs hs
  · exact hs
    
  rw [eq_neg_iff_add_eq_zero, hs] at hc
  cases' Quotientₓ.exact' hc with n hn
  change n • _ = _ at hn
  rw [← neg_one_mul, add_zeroₓ, ← sub_eq_zero, zsmul_eq_mul, ← mul_assocₓ, ← sub_mul, mul_eq_zero,
    eq_false_intro (ne_of_gtₓ pi_pos), or_falseₓ, sub_neg_eq_add, ← Int.cast_zero, ← Int.cast_one, ← Int.cast_bit0, ←
    Int.cast_mul, ← Int.cast_add, Int.cast_inj] at hn
  have : (n * 2 + 1) % (2 : ℤ) = 0 % (2 : ℤ) := congr_argₓ (· % (2 : ℤ)) hn
  rw [add_commₓ, Int.add_mul_mod_self] at this
  exact absurd this one_ne_zero

end Angle

end Real

