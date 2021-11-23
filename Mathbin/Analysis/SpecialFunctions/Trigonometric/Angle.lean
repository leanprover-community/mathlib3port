import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The type of angles

In this file we define `real.angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/


open_locale Real

noncomputable theory

namespace Real

/-- The type of angles -/
def angle : Type :=
  QuotientAddGroup.Quotient (AddSubgroup.zmultiples (2*π))

namespace Angle

instance angle.add_comm_group : AddCommGroupₓ angle :=
  QuotientAddGroup.addCommGroup _

instance  : Inhabited angle :=
  ⟨0⟩

instance  : Coe ℝ angle :=
  ⟨QuotientAddGroup.mk' _⟩

/-- Coercion `ℝ → angle` as an additive homomorphism. -/
def coe_hom : ℝ →+ angle :=
  QuotientAddGroup.mk' _

@[simp]
theorem coe_coe_hom : (coe_hom : ℝ → angle) = coeₓ :=
  rfl

@[simp]
theorem coe_zero : «expr↑ » (0 : ℝ) = (0 : angle) :=
  rfl

@[simp]
theorem coe_add (x y : ℝ) : «expr↑ » (x+y : ℝ) = («expr↑ » x+«expr↑ » y : angle) :=
  rfl

@[simp]
theorem coe_neg (x : ℝ) : «expr↑ » (-x : ℝ) = -(«expr↑ » x : angle) :=
  rfl

@[simp]
theorem coe_sub (x y : ℝ) : «expr↑ » (x - y : ℝ) = («expr↑ » x - «expr↑ » y : angle) :=
  rfl

@[simp, normCast]
theorem coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) : «expr↑ » ((n : ℝ)*x) = n • («expr↑ » x : angle) :=
  by 
    simpa only [nsmul_eq_mul] using coe_hom.map_nsmul x n

@[simp, normCast]
theorem coe_int_mul_eq_zsmul (x : ℝ) (n : ℤ) : «expr↑ » ((n : ℝ)*x : ℝ) = n • («expr↑ » x : angle) :=
  by 
    simpa only [zsmul_eq_mul] using coe_hom.map_zsmul x n

theorem angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : angle) = ψ ↔ ∃ k : ℤ, θ - ψ = (2*π)*k :=
  by 
    simp only [QuotientAddGroup.eq, AddSubgroup.zmultiples_eq_closure, AddSubgroup.mem_closure_singleton, zsmul_eq_mul',
      (sub_eq_neg_add _ _).symm, eq_comm]

@[simp]
theorem coe_two_pi : «expr↑ » (2*π : ℝ) = (0 : angle) :=
  angle_eq_iff_two_pi_dvd_sub.2
    ⟨1,
      by 
        rw [sub_zero, Int.cast_one, mul_oneₓ]⟩

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : ℝ} : cos θ = cos ψ ↔ (θ : angle) = ψ ∨ (θ : angle) = -ψ :=
  by 
    split 
    ·
      intro Hcos 
      rw [←sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero, eq_false_intro two_ne_zero, false_orₓ,
        sin_eq_zero_iff, sin_eq_zero_iff] at Hcos 
      rcases Hcos with (⟨n, hn⟩ | ⟨n, hn⟩)
      ·
        right 
        rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), ←sub_eq_iff_eq_add] at hn 
        rw [←hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assocₓ, coe_int_mul_eq_zsmul, mul_commₓ,
          coe_two_pi, zsmul_zero]
      ·
        left 
        rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), eq_sub_iff_add_eq] at hn 
        rw [←hn, coe_add, mul_assocₓ, coe_int_mul_eq_zsmul, mul_commₓ, coe_two_pi, zsmul_zero, zero_addₓ]
      infer_instance
    ·
      rw [angle_eq_iff_two_pi_dvd_sub, ←coe_neg, angle_eq_iff_two_pi_dvd_sub]
      rintro (⟨k, H⟩ | ⟨k, H⟩)
      rw [←sub_eq_zero, cos_sub_cos, H, mul_assocₓ 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_commₓ π _,
        sin_int_mul_pi, mul_zero]
      rw [←sub_eq_zero, cos_sub_cos, ←sub_neg_eq_add, H, mul_assocₓ 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _ _),
        mul_commₓ π _, sin_int_mul_pi, mul_zero, zero_mul]

-- error in Analysis.SpecialFunctions.Trigonometric.Angle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sin_eq_iff_eq_or_add_eq_pi
{θ
 ψ : exprℝ()} : «expr ↔ »(«expr = »(sin θ, sin ψ), «expr ∨ »(«expr = »((θ : angle), ψ), «expr = »(«expr + »((θ : angle), ψ), exprπ()))) :=
begin
  split,
  { intro [ident Hsin],
    rw ["[", "<-", expr cos_pi_div_two_sub, ",", "<-", expr cos_pi_div_two_sub, "]"] ["at", ident Hsin],
    cases [expr cos_eq_iff_eq_or_eq_neg.mp Hsin] ["with", ident h, ident h],
    { left,
      rw ["[", expr coe_sub, ",", expr coe_sub, "]"] ["at", ident h],
      exact [expr sub_right_inj.1 h] },
    right,
    rw ["[", expr coe_sub, ",", expr coe_sub, ",", expr eq_neg_iff_add_eq_zero, ",", expr add_sub, ",", expr sub_add_eq_add_sub, ",", "<-", expr coe_add, ",", expr add_halves, ",", expr sub_sub, ",", expr sub_eq_zero, "]"] ["at", ident h],
    exact [expr h.symm] },
  { rw ["[", expr angle_eq_iff_two_pi_dvd_sub, ",", "<-", expr eq_sub_iff_add_eq, ",", "<-", expr coe_sub, ",", expr angle_eq_iff_two_pi_dvd_sub, "]"] [],
    rintro ["(", "⟨", ident k, ",", ident H, "⟩", "|", "⟨", ident k, ",", ident H, "⟩", ")"],
    rw ["[", "<-", expr sub_eq_zero, ",", expr sin_sub_sin, ",", expr H, ",", expr mul_assoc 2 exprπ() k, ",", expr mul_div_cancel_left _ (@two_ne_zero exprℝ() _ _), ",", expr mul_comm exprπ() _, ",", expr sin_int_mul_pi, ",", expr mul_zero, ",", expr zero_mul, "]"] [],
    have [ident H'] [":", expr «expr = »(«expr + »(θ, ψ), «expr + »(«expr * »(«expr * »(2, k), exprπ()), exprπ()))] [":=", expr by rwa ["[", "<-", expr sub_add, ",", expr sub_add_eq_add_sub, ",", expr sub_eq_iff_eq_add, ",", expr mul_assoc, ",", expr mul_comm exprπ() _, ",", "<-", expr mul_assoc, "]"] ["at", ident H]],
    rw ["[", "<-", expr sub_eq_zero, ",", expr sin_sub_sin, ",", expr H', ",", expr add_div, ",", expr mul_assoc 2 _ exprπ(), ",", expr mul_div_cancel_left _ (@two_ne_zero exprℝ() _ _), ",", expr cos_add_pi_div_two, ",", expr sin_int_mul_pi, ",", expr neg_zero, ",", expr mul_zero, "]"] [] }
end

-- error in Analysis.SpecialFunctions.Trigonometric.Angle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cos_sin_inj
{θ ψ : exprℝ()}
(Hcos : «expr = »(cos θ, cos ψ))
(Hsin : «expr = »(sin θ, sin ψ)) : «expr = »((θ : angle), ψ) :=
begin
  cases [expr cos_eq_iff_eq_or_eq_neg.mp Hcos] ["with", ident hc, ident hc],
  { exact [expr hc] },
  cases [expr sin_eq_iff_eq_or_add_eq_pi.mp Hsin] ["with", ident hs, ident hs],
  { exact [expr hs] },
  rw ["[", expr eq_neg_iff_add_eq_zero, ",", expr hs, "]"] ["at", ident hc],
  cases [expr quotient.exact' hc] ["with", ident n, ident hn],
  change [expr «expr = »(«expr • »(n, _), _)] [] ["at", ident hn],
  rw ["[", "<-", expr neg_one_mul, ",", expr add_zero, ",", "<-", expr sub_eq_zero, ",", expr zsmul_eq_mul, ",", "<-", expr mul_assoc, ",", "<-", expr sub_mul, ",", expr mul_eq_zero, ",", expr eq_false_intro (ne_of_gt pi_pos), ",", expr or_false, ",", expr sub_neg_eq_add, ",", "<-", expr int.cast_zero, ",", "<-", expr int.cast_one, ",", "<-", expr int.cast_bit0, ",", "<-", expr int.cast_mul, ",", "<-", expr int.cast_add, ",", expr int.cast_inj, "]"] ["at", ident hn],
  have [] [":", expr «expr = »(«expr % »(«expr + »(«expr * »(n, 2), 1), (2 : exprℤ())), «expr % »(0, (2 : exprℤ())))] [":=", expr congr_arg ((«expr % » (2 : exprℤ()))) hn],
  rw ["[", expr add_comm, ",", expr int.add_mul_mod_self, "]"] ["at", ident this],
  exact [expr absurd this one_ne_zero]
end

end Angle

end Real

