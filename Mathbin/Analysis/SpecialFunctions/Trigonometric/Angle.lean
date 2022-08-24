/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathbin.Algebra.CharZero.Quotient
import Mathbin.Algebra.Order.ToIntervalMod
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
  simpa only [nsmul_eq_mul] using coe_hom.map_nsmul x n

@[simp, norm_cast]
theorem coe_int_mul_eq_zsmul (x : ℝ) (n : ℤ) : ↑((n : ℝ) * x : ℝ) = n • (↑x : Angle) := by
  simpa only [zsmul_eq_mul] using coe_hom.map_zsmul x n

theorem angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : Angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k := by
  simp only [QuotientAddGroup.eq, AddSubgroup.zmultiples_eq_closure, AddSubgroup.mem_closure_singleton, zsmul_eq_mul',
    (sub_eq_neg_add _ _).symm, eq_comm]

@[simp]
theorem coe_two_pi : ↑(2 * π : ℝ) = (0 : Angle) :=
  angle_eq_iff_two_pi_dvd_sub.2
    ⟨1, by
      rw [sub_zero, Int.cast_oneₓ, mul_oneₓ]⟩

@[simp]
theorem neg_coe_pi : -(π : Angle) = π := by
  rw [← coe_neg, angle_eq_iff_two_pi_dvd_sub]
  use -1
  simp [two_mul, sub_eq_add_neg]

theorem sub_coe_pi_eq_add_coe_pi (θ : Angle) : θ - π = θ + π := by
  rw [sub_eq_add_neg, neg_coe_pi]

@[simp]
theorem two_nsmul_coe_pi : (2 : ℕ) • (π : Angle) = 0 := by
  simp [← coe_nat_mul_eq_nsmul]

@[simp]
theorem two_zsmul_coe_pi : (2 : ℤ) • (π : Angle) = 0 := by
  simp [← coe_int_mul_eq_zsmul]

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

theorem two_nsmul_ne_zero_iff {θ : Angle} : (2 : ℕ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or_distrib, ← two_nsmul_eq_zero_iff]

theorem two_zsmul_eq_zero_iff {θ : Angle} : (2 : ℤ) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_zero_iff]

theorem two_zsmul_ne_zero_iff {θ : Angle} : (2 : ℤ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or_distrib, ← two_zsmul_eq_zero_iff]

theorem eq_neg_self_iff {θ : Angle} : θ = -θ ↔ θ = 0 ∨ θ = π := by
  rw [← add_eq_zero_iff_eq_neg, ← two_nsmul, two_nsmul_eq_zero_iff]

theorem ne_neg_self_iff {θ : Angle} : θ ≠ -θ ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or_distrib, ← eq_neg_self_iff.not]

theorem neg_eq_self_iff {θ : Angle} : -θ = θ ↔ θ = 0 ∨ θ = π := by
  rw [eq_comm, eq_neg_self_iff]

theorem neg_ne_self_iff {θ : Angle} : -θ ≠ θ ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or_distrib, ← neg_eq_self_iff.not]

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

theorem sin_ne_zero_iff {θ : Angle} : sin θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or_distrib, ← sin_eq_zero_iff]

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

@[simp]
theorem coe_to_Ico_mod (θ ψ : ℝ) : ↑(toIcoMod ψ two_pi_pos θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine' ⟨toIcoDiv ψ two_pi_pos θ, _⟩
  rw [to_Ico_mod_sub_self, zsmul_eq_mul, mul_comm]

@[simp]
theorem coe_to_Ioc_mod (θ ψ : ℝ) : ↑(toIocMod ψ two_pi_pos θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine' ⟨toIocDiv ψ two_pi_pos θ, _⟩
  rw [to_Ioc_mod_sub_self, zsmul_eq_mul, mul_comm]

/-- Convert a `real.angle` to a real number in the interval `Ioc (-π) π`. -/
def toReal (θ : Angle) : ℝ :=
  (to_Ioc_mod_periodic (-π) two_pi_pos).lift θ

theorem to_real_coe (θ : ℝ) : (θ : Angle).toReal = toIocMod (-π) two_pi_pos θ :=
  rfl

theorem to_real_coe_eq_self_iff {θ : ℝ} : (θ : Angle).toReal = θ ↔ -π < θ ∧ θ ≤ π := by
  rw [to_real_coe, to_Ioc_mod_eq_self two_pi_pos]
  ring_nf

theorem to_real_coe_eq_self_iff_mem_Ioc {θ : ℝ} : (θ : Angle).toReal = θ ↔ θ ∈ Set.Ioc (-π) π := by
  rw [to_real_coe_eq_self_iff, ← Set.mem_Ioc]

theorem to_real_injective : Function.Injective toReal := by
  intro θ ψ h
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  simpa [to_real_coe, to_Ioc_mod_eq_to_Ioc_mod, zsmul_eq_mul, mul_comm _ (2 * π), ← angle_eq_iff_two_pi_dvd_sub,
    eq_comm] using h

@[simp]
theorem to_real_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ θ = ψ :=
  to_real_injective.eq_iff

@[simp]
theorem coe_to_real (θ : Angle) : (θ.toReal : Angle) = θ := by
  induction θ using Real.Angle.induction_on
  exact coe_to_Ioc_mod _ _

theorem neg_pi_lt_to_real (θ : Angle) : -π < θ.toReal := by
  induction θ using Real.Angle.induction_on
  exact left_lt_to_Ioc_mod _ two_pi_pos _

theorem to_real_le_pi (θ : Angle) : θ.toReal ≤ π := by
  induction θ using Real.Angle.induction_on
  convert to_Ioc_mod_le_right _ two_pi_pos _
  ring

theorem abs_to_real_le_pi (θ : Angle) : abs θ.toReal ≤ π :=
  abs_le.2 ⟨(neg_pi_lt_to_real _).le, to_real_le_pi _⟩

theorem to_real_mem_Ioc (θ : Angle) : θ.toReal ∈ Set.Ioc (-π) π :=
  ⟨neg_pi_lt_to_real _, to_real_le_pi _⟩

@[simp]
theorem to_Ioc_mod_to_real (θ : Angle) : toIocMod (-π) two_pi_pos θ.toReal = θ.toReal := by
  induction θ using Real.Angle.induction_on
  rw [to_real_coe]
  exact to_Ioc_mod_to_Ioc_mod _ _ _ _

@[simp]
theorem to_real_zero : (0 : Angle).toReal = 0 := by
  rw [← coe_zero, to_real_coe_eq_self_iff]
  exact ⟨Left.neg_neg_iff.2 Real.pi_pos, real.pi_pos.le⟩

@[simp]
theorem to_real_eq_zero_iff {θ : Angle} : θ.toReal = 0 ↔ θ = 0 := by
  nth_rw 0[← to_real_zero]
  exact to_real_inj

@[simp]
theorem to_real_pi : (π : Angle).toReal = π := by
  rw [to_real_coe_eq_self_iff]
  exact ⟨Left.neg_lt_self Real.pi_pos, le_reflₓ _⟩

@[simp]
theorem to_real_eq_pi_iff {θ : Angle} : θ.toReal = π ↔ θ = π := by
  nth_rw 0[← to_real_pi]
  exact to_real_inj

theorem pi_ne_zero : (π : Angle) ≠ 0 := by
  rw [← to_real_injective.ne_iff, to_real_pi, to_real_zero]
  exact pi_ne_zero

theorem abs_to_real_coe_eq_self_iff {θ : ℝ} : abs (θ : Angle).toReal = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
  ⟨fun h => h ▸ ⟨abs_nonneg _, abs_to_real_le_pi _⟩, fun h =>
    (to_real_coe_eq_self_iff.2 ⟨(Left.neg_neg_iff.2 Real.pi_pos).trans_le h.1, h.2⟩).symm ▸ abs_eq_self.2 h.1⟩

theorem abs_to_real_neg_coe_eq_self_iff {θ : ℝ} : abs (-θ : Angle).toReal = θ ↔ 0 ≤ θ ∧ θ ≤ π := by
  refine' ⟨fun h => h ▸ ⟨abs_nonneg _, abs_to_real_le_pi _⟩, fun h => _⟩
  by_cases' hnegpi : θ = π
  · simp [hnegpi, real.pi_pos.le]
    
  rw [← coe_neg,
    to_real_coe_eq_self_iff.2 ⟨neg_lt_neg (lt_of_le_of_neₓ h.2 hnegpi), (neg_nonpos.2 h.1).trans real.pi_pos.le⟩,
    abs_neg, abs_eq_self.2 h.1]

@[simp]
theorem sin_to_real (θ : Angle) : Real.sin θ.toReal = sin θ := by
  conv_rhs => rw [← coe_to_real θ]
  rfl

@[simp]
theorem cos_to_real (θ : Angle) : Real.cos θ.toReal = cos θ := by
  conv_rhs => rw [← coe_to_real θ]
  rfl

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
  simp [sign_antiperiodic.sub_eq']

theorem sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔ θ = 0 ∨ θ = π := by
  rw [sign, sign_eq_zero_iff, sin_eq_zero_iff]

theorem sign_ne_zero_iff {θ : Angle} : θ.sign ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or_distrib, ← sign_eq_zero_iff]

theorem to_real_neg_iff_sign_neg {θ : Angle} : θ.toReal < 0 ↔ θ.sign = -1 := by
  rw [sign, ← sin_to_real, sign_eq_neg_one_iff]
  rcases lt_trichotomyₓ θ.to_real 0 with (h | h | h)
  · exact ⟨fun _ => Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_to_real θ), fun _ => h⟩
    
  · simp [h]
    
  · exact
      ⟨fun hn => False.elim (h.asymm hn), fun hn =>
        False.elim (hn.not_le (sin_nonneg_of_nonneg_of_le_pi h.le (to_real_le_pi θ)))⟩
    

theorem to_real_nonneg_iff_sign_nonneg {θ : Angle} : 0 ≤ θ.toReal ↔ 0 ≤ θ.sign := by
  rcases lt_trichotomyₓ θ.to_real 0 with (h | h | h)
  · refine' ⟨fun hn => False.elim (h.not_le hn), fun hn => _⟩
    rw [to_real_neg_iff_sign_neg.1 h] at hn
    exact
      False.elim
        (hn.not_lt
          (by
            decide))
    
  · simp [h, sign, ← sin_to_real]
    
  · refine' ⟨fun _ => _, fun _ => h.le⟩
    rw [sign, ← sin_to_real, sign_nonneg_iff]
    exact sin_nonneg_of_nonneg_of_le_pi h.le (to_real_le_pi θ)
    

@[simp]
theorem sign_to_real {θ : Angle} (h : θ ≠ π) : sign θ.toReal = θ.sign := by
  rcases lt_trichotomyₓ θ.to_real 0 with (ht | ht | ht)
  · simp [ht, to_real_neg_iff_sign_neg.1 ht]
    
  · simp [sign, ht, ← sin_to_real]
    
  · rw [sign, ← sin_to_real, sign_pos ht,
      sign_pos (sin_pos_of_pos_of_lt_pi ht ((to_real_le_pi θ).lt_of_ne (to_real_eq_pi_iff.not.2 h)))]
    

theorem coe_abs_to_real_of_sign_nonneg {θ : Angle} (h : 0 ≤ θ.sign) : ↑(abs θ.toReal) = θ := by
  rw [abs_eq_self.2 (to_real_nonneg_iff_sign_nonneg.2 h), coe_to_real]

theorem neg_coe_abs_to_real_of_sign_nonpos {θ : Angle} (h : θ.sign ≤ 0) : -↑(abs θ.toReal) = θ := by
  rw [SignType.nonpos_iff] at h
  rcases h with (h | h)
  · rw [abs_of_neg (to_real_neg_iff_sign_neg.2 h), coe_neg, neg_negₓ, coe_to_real]
    
  · rw [sign_eq_zero_iff] at h
    rcases h with (rfl | rfl) <;> simp [abs_of_pos Real.pi_pos]
    

theorem eq_iff_sign_eq_and_abs_to_real_eq {θ ψ : Angle} : θ = ψ ↔ θ.sign = ψ.sign ∧ abs θ.toReal = abs ψ.toReal := by
  refine' ⟨_, fun h => _⟩
  · rintro rfl
    exact ⟨rfl, rfl⟩
    
  rcases h with ⟨hs, hr⟩
  rw [abs_eq_abs] at hr
  rcases hr with (hr | hr)
  · exact to_real_injective hr
    
  · by_cases' h : θ = π
    · rw [h, to_real_pi, eq_neg_iff_eq_neg] at hr
      exact False.elim ((neg_pi_lt_to_real ψ).Ne hr.symm)
      
    · by_cases' h' : ψ = π
      · rw [h', to_real_pi] at hr
        exact False.elim ((neg_pi_lt_to_real θ).Ne hr.symm)
        
      · rw [← sign_to_real h, ← sign_to_real h', hr, Left.sign_neg, SignType.neg_eq_self_iff, _root_.sign_eq_zero_iff,
          to_real_eq_zero_iff] at hs
        rw [hs, to_real_zero, neg_zero, to_real_eq_zero_iff] at hr
        rw [hr, hs]
        
      
    

theorem eq_iff_abs_to_real_eq_of_sign_eq {θ ψ : Angle} (h : θ.sign = ψ.sign) : θ = ψ ↔ abs θ.toReal = abs ψ.toReal := by
  simpa [h] using @eq_iff_sign_eq_and_abs_to_real_eq θ ψ

end Angle

end Real

