/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathbin.Algebra.CharZero.Quotient
import Mathbin.Data.Sign

/-!
# The type of angles

In this file we define `real.angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/


open Real

noncomputable section

namespace Real

/-- The type of angles -/
def Angle : Type :=
  ℝ ⧸ AddSubgroup.zmultiples (2 * π)deriving AddCommGroupₓ, TopologicalSpace, TopologicalAddGroup

namespace Angle

instance : Inhabited Angle :=
  ⟨0⟩

instance : Coe ℝ Angle :=
  ⟨QuotientAddGroup.mk' _⟩

@[continuity]
theorem continuous_coe : Continuous (coe : ℝ → Angle) :=
  continuous_quotient_mk

/-- Coercion `ℝ → angle` as an additive homomorphism. -/
def coeHom : ℝ →+ angle :=
  QuotientAddGroup.mk' _

@[simp]
theorem coe_coe_hom : (coeHom : ℝ → Angle) = coe :=
  rfl

/-- An induction principle to deduce results for `angle` from those for `ℝ`, used with
`induction θ using real.angle.induction_on`. -/
@[elabAsElim]
protected theorem induction_on {p : Angle → Prop} (θ : Angle) (h : ∀ x : ℝ, p x) : p θ :=
  Quotientₓ.induction_on' θ h

@[simp]
theorem coe_zero : ↑(0 : ℝ) = (0 : Angle) :=
  rfl

@[simp]
theorem coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : Angle) :=
  rfl

@[simp]
theorem coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : Angle) :=
  rfl

@[simp]
theorem coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : Angle) :=
  rfl

theorem coe_nsmul (n : ℕ) (x : ℝ) : ↑(n • x : ℝ) = (n • ↑x : Angle) :=
  rfl

theorem coe_zsmul (z : ℤ) (x : ℝ) : ↑(z • x : ℝ) = (z • ↑x : Angle) :=
  rfl

@[simp, norm_cast]
theorem coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) : ↑((n : ℝ) * x) = n • (↑x : Angle) := by
  simpa only [← nsmul_eq_mul] using coe_hom.map_nsmul x n

@[simp, norm_cast]
theorem coe_int_mul_eq_zsmul (x : ℝ) (n : ℤ) : ↑((n : ℝ) * x : ℝ) = n • (↑x : Angle) := by
  simpa only [← zsmul_eq_mul] using coe_hom.map_zsmul x n

theorem angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : Angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k := by
  simp only [← QuotientAddGroup.eq, ← AddSubgroup.zmultiples_eq_closure, ← AddSubgroup.mem_closure_singleton, ←
    zsmul_eq_mul', ← (sub_eq_neg_add _ _).symm, ← eq_comm]

@[simp]
theorem coe_two_pi : ↑(2 * π : ℝ) = (0 : Angle) :=
  angle_eq_iff_two_pi_dvd_sub.2
    ⟨1, by
      rw [sub_zero, Int.cast_oneₓ, mul_oneₓ]⟩

@[simp]
theorem neg_coe_pi : -(π : Angle) = π := by
  rw [← coe_neg, angle_eq_iff_two_pi_dvd_sub]
  use -1
  simp [← two_mul, ← sub_eq_add_neg]

theorem sub_coe_pi_eq_add_coe_pi (θ : Angle) : θ - π = θ + π := by
  rw [sub_eq_add_neg, neg_coe_pi]

@[simp]
theorem two_nsmul_coe_pi : (2 : ℕ) • (π : Angle) = 0 := by
  simp [coe_nat_mul_eq_nsmul]

@[simp]
theorem two_zsmul_coe_pi : (2 : ℤ) • (π : Angle) = 0 := by
  simp [coe_int_mul_eq_zsmul]

@[simp]
theorem coe_pi_add_coe_pi : (π : Real.Angle) + π = 0 := by
  rw [← two_nsmul, two_nsmul_coe_pi]

theorem zsmul_eq_iff {ψ θ : Angle} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Finₓ z.natAbs, ψ = θ + (k : ℕ) • (2 * π / z : ℝ) :=
  QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff hz

theorem nsmul_eq_iff {ψ θ : Angle} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Finₓ n, ψ = θ + (k : ℕ) • (2 * π / n : ℝ) :=
  QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff hz

theorem two_zsmul_eq_iff {ψ θ : Angle} : (2 : ℤ) • ψ = (2 : ℤ) • θ ↔ ψ = θ ∨ ψ = θ + π := by
  rw [zsmul_eq_iff two_ne_zero, Int.nat_abs_bit0, Int.nat_abs_one, Finₓ.exists_fin_two, Finₓ.coe_zero, Finₓ.coe_one,
    zero_smul, add_zeroₓ, one_smul, Int.cast_two, mul_div_cancel_left (_ : ℝ) two_ne_zero]

theorem two_nsmul_eq_iff {ψ θ : Angle} : (2 : ℕ) • ψ = (2 : ℕ) • θ ↔ ψ = θ ∨ ψ = θ + π := by
  simp_rw [← coe_nat_zsmul, Int.coe_nat_bit0, Int.coe_nat_one, two_zsmul_eq_iff]

theorem two_nsmul_eq_zero_iff {θ : Angle} : (2 : ℕ) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  convert two_nsmul_eq_iff <;> simp

theorem two_zsmul_eq_zero_iff {θ : Angle} : (2 : ℤ) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_zero_iff]

theorem cos_eq_iff_coe_eq_or_eq_neg {θ ψ : ℝ} : cos θ = cos ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) = -ψ := by
  constructor
  · intro Hcos
    rw [← sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero, eq_false_intro two_ne_zero, false_orₓ,
      sin_eq_zero_iff, sin_eq_zero_iff] at Hcos
    rcases Hcos with (⟨n, hn⟩ | ⟨n, hn⟩)
    · right
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), ← sub_eq_iff_eq_add] at hn
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc, coe_int_mul_eq_zsmul, mul_comm, coe_two_pi,
        zsmul_zero]
      
    · left
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), eq_sub_iff_add_eq] at hn
      rw [← hn, coe_add, mul_assoc, coe_int_mul_eq_zsmul, mul_comm, coe_two_pi, zsmul_zero, zero_addₓ]
      
    infer_instance
    
  · rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _,
      sin_int_mul_pi, mul_zero]
    rw [← sub_eq_zero, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _ _),
      mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul]
    

theorem sin_eq_iff_coe_eq_or_add_eq_pi {θ ψ : ℝ} : sin θ = sin ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) + ψ = π := by
  constructor
  · intro Hsin
    rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin
    cases' cos_eq_iff_coe_eq_or_eq_neg.mp Hsin with h h
    · left
      rw [coe_sub, coe_sub] at h
      exact sub_right_inj.1 h
      
    right
    rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub, sub_add_eq_add_sub, ← coe_add, add_halves, sub_sub,
      sub_eq_zero] at h
    exact h.symm
    
  · rw [angle_eq_iff_two_pi_dvd_sub, ← eq_sub_iff_add_eq, ← coe_sub, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    rw [← sub_eq_zero, sin_sub_sin, H, mul_assoc 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _,
      sin_int_mul_pi, mul_zero, zero_mul]
    have H' : θ + ψ = 2 * k * π + π := by
      rwa [← sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add, mul_assoc, mul_comm π _, ← mul_assoc] at H
    rw [← sub_eq_zero, sin_sub_sin, H', add_div, mul_assoc 2 _ π, mul_div_cancel_left _ (@two_ne_zero ℝ _ _),
      cos_add_pi_div_two, sin_int_mul_pi, neg_zero, mul_zero]
    

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : Angle) = ψ := by
  cases' cos_eq_iff_coe_eq_or_eq_neg.mp Hcos with hc hc
  · exact hc
    
  cases' sin_eq_iff_coe_eq_or_add_eq_pi.mp Hsin with hs hs
  · exact hs
    
  rw [eq_neg_iff_add_eq_zero, hs] at hc
  obtain ⟨n, hn⟩ : ∃ n, n • _ = _ := quotient_add_group.left_rel_apply.mp (Quotientₓ.exact' hc)
  rw [← neg_one_mul, add_zeroₓ, ← sub_eq_zero, zsmul_eq_mul, ← mul_assoc, ← sub_mul, mul_eq_zero,
    eq_false_intro (ne_of_gtₓ pi_pos), or_falseₓ, sub_neg_eq_add, ← Int.cast_zeroₓ, ← Int.cast_oneₓ, ← Int.cast_bit0, ←
    Int.cast_mul, ← Int.cast_add, Int.cast_inj] at hn
  have : (n * 2 + 1) % (2 : ℤ) = 0 % (2 : ℤ) := congr_arg (· % (2 : ℤ)) hn
  rw [add_commₓ, Int.add_mul_mod_self] at this
  exact absurd this one_ne_zero

/-- The sine of a `real.angle`. -/
def sin (θ : Angle) : ℝ :=
  sin_periodic.lift θ

@[simp]
theorem sin_coe (x : ℝ) : sin (x : Angle) = Real.sin x :=
  rfl

@[continuity]
theorem continuous_sin : Continuous sin :=
  Real.continuous_sin.quotient_lift_on' _

/-- The cosine of a `real.angle`. -/
def cos (θ : Angle) : ℝ :=
  cos_periodic.lift θ

@[simp]
theorem cos_coe (x : ℝ) : cos (x : Angle) = Real.cos x :=
  rfl

@[continuity]
theorem continuous_cos : Continuous cos :=
  Real.continuous_cos.quotient_lift_on' _

theorem cos_eq_real_cos_iff_eq_or_eq_neg {θ : Angle} {ψ : ℝ} : cos θ = Real.cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction θ using Real.Angle.induction_on
  exact cos_eq_iff_coe_eq_or_eq_neg

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : Angle} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction ψ using Real.Angle.induction_on
  exact cos_eq_real_cos_iff_eq_or_eq_neg

theorem sin_eq_real_sin_iff_eq_or_add_eq_pi {θ : Angle} {ψ : ℝ} : sin θ = Real.sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction θ using Real.Angle.induction_on
  exact sin_eq_iff_coe_eq_or_add_eq_pi

theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : Angle} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction ψ using Real.Angle.induction_on
  exact sin_eq_real_sin_iff_eq_or_add_eq_pi

@[simp]
theorem sin_zero : sin (0 : Angle) = 0 := by
  rw [← coe_zero, sin_coe, Real.sin_zero]

@[simp]
theorem sin_coe_pi : sin (π : Angle) = 0 := by
  rw [sin_coe, Real.sin_pi]

theorem sin_eq_zero_iff {θ : Angle} : sin θ = 0 ↔ θ = 0 ∨ θ = π := by
  nth_rw 0[← sin_zero]
  rw [sin_eq_iff_eq_or_add_eq_pi]
  simp

@[simp]
theorem sin_neg (θ : Angle) : sin (-θ) = -sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_neg _

theorem sin_antiperiodic : Function.Antiperiodic sin (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.sin_antiperiodic θ

@[simp]
theorem sin_add_pi (θ : Angle) : sin (θ + π) = -sin θ :=
  sin_antiperiodic θ

@[simp]
theorem sin_sub_pi (θ : Angle) : sin (θ - π) = -sin θ :=
  sin_antiperiodic.sub_eq θ

@[simp]
theorem cos_zero : cos (0 : Angle) = 1 := by
  rw [← coe_zero, cos_coe, Real.cos_zero]

@[simp]
theorem cos_coe_pi : cos (π : Angle) = -1 := by
  rw [cos_coe, Real.cos_pi]

@[simp]
theorem cos_neg (θ : Angle) : cos (-θ) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_neg _

theorem cos_antiperiodic : Function.Antiperiodic cos (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.cos_antiperiodic θ

@[simp]
theorem cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ :=
  cos_antiperiodic θ

@[simp]
theorem cos_sub_pi (θ : Angle) : cos (θ - π) = -cos θ :=
  cos_antiperiodic.sub_eq θ

/-- The sign of a `real.angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly
between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the
sign of the sine of the angle. -/
def sign (θ : Angle) : SignType :=
  sign (sin θ)

@[simp]
theorem sign_zero : (0 : Angle).sign = 0 := by
  rw [sign, sin_zero, sign_zero]

@[simp]
theorem sign_coe_pi : (π : Angle).sign = 0 := by
  rw [sign, sin_coe_pi, _root_.sign_zero]

@[simp]
theorem sign_neg (θ : Angle) : (-θ).sign = -θ.sign := by
  simp_rw [sign, sin_neg, Left.sign_neg]

theorem sign_antiperiodic : Function.Antiperiodic sign (π : Angle) := fun θ => by
  rw [sign, sign, sin_add_pi, Left.sign_neg]

@[simp]
theorem sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign :=
  sign_antiperiodic θ

@[simp]
theorem sign_pi_add (θ : Angle) : ((π : Angle) + θ).sign = -θ.sign := by
  rw [add_commₓ, sign_add_pi]

@[simp]
theorem sign_sub_pi (θ : Angle) : (θ - π).sign = -θ.sign :=
  sign_antiperiodic.sub_eq θ

@[simp]
theorem sign_pi_sub (θ : Angle) : ((π : Angle) - θ).sign = θ.sign := by
  simp [← sign_antiperiodic.sub_eq']

theorem sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔ θ = 0 ∨ θ = π := by
  rw [sign, sign_eq_zero_iff, sin_eq_zero_iff]

end Angle

end Real

