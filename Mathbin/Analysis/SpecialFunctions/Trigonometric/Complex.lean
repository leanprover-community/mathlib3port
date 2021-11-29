import Mathbin.Algebra.QuadraticDiscriminant 
import Mathbin.Analysis.Complex.Polynomial 
import Mathbin.FieldTheory.IsAlgClosed.Basic 
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.
-/


noncomputable theory

namespace Complex

open Set Filter

open_locale Real

-- error in Analysis.SpecialFunctions.Trigonometric.Complex: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cos_eq_zero_iff
{θ : exprℂ()} : «expr ↔ »(«expr = »(cos θ, 0), «expr∃ , »((k : exprℤ()), «expr = »(θ, «expr / »(«expr * »(«expr + »(«expr * »(2, k), 1), exprπ()), 2)))) :=
begin
  have [ident h] [":", expr «expr ↔ »(«expr = »(«expr / »(«expr + »(exp «expr * »(θ, I), exp «expr * »(«expr- »(θ), I)), 2), 0), «expr = »(exp «expr * »(«expr * »(2, θ), I), «expr- »(1)))] [],
  { rw ["[", expr @div_eq_iff _ _ «expr + »(exp «expr * »(θ, I), exp «expr * »(«expr- »(θ), I)) 2 0 two_ne_zero', ",", expr zero_mul, ",", expr add_eq_zero_iff_eq_neg, ",", expr neg_eq_neg_one_mul, ",", "<-", expr div_eq_iff (exp_ne_zero _), ",", "<-", expr exp_sub, "]"] [],
    field_simp ["only"] [] [] [],
    congr' [3] [],
    ring [] },
  rw ["[", expr cos, ",", expr h, ",", "<-", expr exp_pi_mul_I, ",", expr exp_eq_exp_iff_exists_int, ",", expr mul_right_comm, "]"] [],
  refine [expr exists_congr (λ x, _)],
  refine [expr «expr $ »(iff_of_eq, congr_arg _ _).trans «expr $ »(mul_right_inj', mul_ne_zero two_ne_zero' I_ne_zero)],
  ring []
end

theorem cos_ne_zero_iff {θ : ℂ} : cos θ ≠ 0 ↔ ∀ (k : ℤ), θ ≠ (((2*k)+1)*π) / 2 :=
  by 
    rw [←not_exists, not_iff_not, cos_eq_zero_iff]

theorem sin_eq_zero_iff {θ : ℂ} : sin θ = 0 ↔ ∃ k : ℤ, θ = k*π :=
  by 
    rw [←Complex.cos_sub_pi_div_two, cos_eq_zero_iff]
    split 
    ·
      rintro ⟨k, hk⟩
      use k+1
      fieldSimp [eq_add_of_sub_eq hk]
      ring
    ·
      rintro ⟨k, rfl⟩
      use k - 1
      fieldSimp 
      ring

theorem sin_ne_zero_iff {θ : ℂ} : sin θ ≠ 0 ↔ ∀ (k : ℤ), θ ≠ k*π :=
  by 
    rw [←not_exists, not_iff_not, sin_eq_zero_iff]

-- error in Analysis.SpecialFunctions.Trigonometric.Complex: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tan_eq_zero_iff
{θ : exprℂ()} : «expr ↔ »(«expr = »(tan θ, 0), «expr∃ , »((k : exprℤ()), «expr = »(θ, «expr / »(«expr * »(k, exprπ()), 2)))) :=
begin
  have [ident h] [] [":=", expr (sin_two_mul θ).symm],
  rw [expr mul_assoc] ["at", ident h],
  rw ["[", expr tan, ",", expr div_eq_zero_iff, ",", "<-", expr mul_eq_zero, ",", "<-", expr zero_mul («expr / »(1, 2) : exprℂ()), ",", expr mul_one_div, ",", expr cancel_factors.cancel_factors_eq_div h two_ne_zero', ",", expr mul_comm, "]"] [],
  simpa [] [] ["only"] ["[", expr zero_div, ",", expr zero_mul, ",", expr ne.def, ",", expr not_false_iff, "]"] ["with", ident field_simps] ["using", expr sin_eq_zero_iff]
end

theorem tan_ne_zero_iff {θ : ℂ} : tan θ ≠ 0 ↔ ∀ (k : ℤ), θ ≠ (k*π) / 2 :=
  by 
    rw [←not_exists, not_iff_not, tan_eq_zero_iff]

theorem tan_int_mul_pi_div_two (n : ℤ) : tan ((n*π) / 2) = 0 :=
  tan_eq_zero_iff.mpr
    (by 
      use n)

theorem cos_eq_cos_iff {x y : ℂ} : cos x = cos y ↔ ∃ k : ℤ, (y = ((2*k)*π)+x) ∨ y = ((2*k)*π) - x :=
  calc cos x = cos y ↔ cos x - cos y = 0 := sub_eq_zero.symm 
    _ ↔ (((-2)*sin ((x+y) / 2))*sin ((x - y) / 2)) = 0 :=
    by 
      rw [cos_sub_cos]
    _ ↔ sin ((x+y) / 2) = 0 ∨ sin ((x - y) / 2) = 0 :=
    by 
      simp
        [(by 
          normNum :
        (2 : ℂ) ≠ 0)]
    _ ↔ sin ((x - y) / 2) = 0 ∨ sin ((x+y) / 2) = 0 := Or.comm 
    _ ↔ (∃ k : ℤ, y = ((2*k)*π)+x) ∨ ∃ k : ℤ, y = ((2*k)*π) - x :=
    by 
      apply or_congr <;>
        fieldSimp [sin_eq_zero_iff,
          (by 
            normNum :
          -(2 : ℂ) ≠ 0),
          eq_sub_iff_add_eq', sub_eq_iff_eq_add, mul_commₓ (2 : ℂ), mul_right_commₓ _ (2 : ℂ)]
      split  <;>
        ·
          rintro ⟨k, rfl⟩
          use -k 
          simp 
    _ ↔ ∃ k : ℤ, (y = ((2*k)*π)+x) ∨ y = ((2*k)*π) - x := exists_or_distrib.symm
    

theorem sin_eq_sin_iff {x y : ℂ} : sin x = sin y ↔ ∃ k : ℤ, (y = ((2*k)*π)+x) ∨ y = (((2*k)+1)*π) - x :=
  by 
    simp only [←Complex.cos_sub_pi_div_two, cos_eq_cos_iff, sub_eq_iff_eq_add]
    refine' exists_congr fun k => or_congr _ _ <;> refine' Eq.congr rfl _ <;> fieldSimp <;> ring

theorem tan_add {x y : ℂ}
  (h :
    ((∀ (k : ℤ), x ≠ (((2*k)+1)*π) / 2) ∧ ∀ (l : ℤ), y ≠ (((2*l)+1)*π) / 2) ∨
      (∃ k : ℤ, x = (((2*k)+1)*π) / 2) ∧ ∃ l : ℤ, y = (((2*l)+1)*π) / 2) :
  tan (x+y) = (tan x+tan y) / (1 - tan x*tan y) :=
  by 
    rcases h with (⟨h1, h2⟩ | ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩)
    ·
      rw [tan, sin_add, cos_add,
        ←div_div_div_cancel_right ((sin x*cos y)+cos x*sin y)
          (mul_ne_zero (cos_ne_zero_iff.mpr h1) (cos_ne_zero_iff.mpr h2)),
        add_div, sub_div]
      simp only [←div_mul_div, ←tan, mul_oneₓ, one_mulₓ, div_self (cos_ne_zero_iff.mpr h1),
        div_self (cos_ne_zero_iff.mpr h2)]
    ·
      obtain ⟨t, hx, hy, hxy⟩ := tan_int_mul_pi_div_two, t ((2*k)+1), t ((2*l)+1), t (((2*k)+1)+(2*l)+1)
      simp only [Int.cast_add, Int.cast_bit0, Int.cast_mul, Int.cast_one, hx, hy] at hx hy hxy 
      rw [hx, hy, add_zeroₓ, zero_div, mul_div_assoc, mul_div_assoc, ←add_mulₓ ((2*(k : ℂ))+1) ((2*l)+1) (π / 2),
        ←mul_div_assoc, hxy]

theorem tan_add' {x y : ℂ} (h : (∀ (k : ℤ), x ≠ (((2*k)+1)*π) / 2) ∧ ∀ (l : ℤ), y ≠ (((2*l)+1)*π) / 2) :
  tan (x+y) = (tan x+tan y) / (1 - tan x*tan y) :=
  tan_add (Or.inl h)

theorem tan_two_mul {z : ℂ} : tan (2*z) = (2*tan z) / (1 - (tan z^2)) :=
  by 
    byCases' h : ∀ (k : ℤ), z ≠ (((2*k)+1)*π) / 2
    ·
      rw [two_mul, two_mul, sq, tan_add (Or.inl ⟨h, h⟩)]
    ·
      rw [not_forall_not] at h 
      rw [two_mul, two_mul, sq, tan_add (Or.inr ⟨h, h⟩)]

theorem tan_add_mul_I {x y : ℂ}
  (h :
    ((∀ (k : ℤ), x ≠ (((2*k)+1)*π) / 2) ∧ ∀ (l : ℤ), (y*I) ≠ (((2*l)+1)*π) / 2) ∨
      (∃ k : ℤ, x = (((2*k)+1)*π) / 2) ∧ ∃ l : ℤ, (y*I) = (((2*l)+1)*π) / 2) :
  tan (x+y*I) = (tan x+tanh y*I) / (1 - (tan x*tanh y)*I) :=
  by 
    rw [tan_add h, tan_mul_I, mul_assocₓ]

theorem tan_eq {z : ℂ}
  (h :
    ((∀ (k : ℤ), (z.re : ℂ) ≠ (((2*k)+1)*π) / 2) ∧ ∀ (l : ℤ), ((z.im : ℂ)*I) ≠ (((2*l)+1)*π) / 2) ∨
      (∃ k : ℤ, (z.re : ℂ) = (((2*k)+1)*π) / 2) ∧ ∃ l : ℤ, ((z.im : ℂ)*I) = (((2*l)+1)*π) / 2) :
  tan z = (tan z.re+tanh z.im*I) / (1 - (tan z.re*tanh z.im)*I) :=
  by 
    convert tan_add_mul_I h <;> exact (re_add_im z).symm

open_locale TopologicalSpace

theorem continuous_on_tan : ContinuousOn tan { x | cos x ≠ 0 } :=
  continuous_on_sin.div continuous_on_cos$ fun x => id

-- error in Analysis.SpecialFunctions.Trigonometric.Complex: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[continuity #[]] theorem continuous_tan : continuous (λ x : {x | «expr ≠ »(cos x, 0)}, tan x) :=
continuous_on_iff_continuous_restrict.1 continuous_on_tan

theorem cos_eq_iff_quadratic {z w : ℂ} : cos z = w ↔ (((exp (z*I)^2) - (2*w)*exp (z*I))+1) = 0 :=
  by 
    rw [←sub_eq_zero]
    fieldSimp [cos, exp_neg, exp_ne_zero]
    refine' Eq.congr _ rfl 
    ring

theorem cos_surjective : Function.Surjective cos :=
  by 
    intro x 
    obtain ⟨w, w₀, hw⟩ : ∃ (w : _)(_ : w ≠ 0), ((((1*w)*w)+((-2)*x)*w)+1) = 0
    ·
      rcases exists_quadratic_eq_zero (@one_ne_zero ℂ _ _) (IsAlgClosed.exists_eq_mul_self _) with ⟨w, hw⟩
      refine' ⟨w, _, hw⟩
      rintro rfl 
      simpa only [zero_addₓ, one_ne_zero, mul_zero] using hw 
    refine' ⟨log w / I, cos_eq_iff_quadratic.2 _⟩
    rw [div_mul_cancel _ I_ne_zero, exp_log w₀]
    convert hw 
    ring

@[simp]
theorem range_cos : range cos = Set.Univ :=
  cos_surjective.range_eq

theorem sin_surjective : Function.Surjective sin :=
  by 
    intro x 
    rcases cos_surjective x with ⟨z, rfl⟩
    exact ⟨z+π / 2, sin_add_pi_div_two z⟩

@[simp]
theorem range_sin : range sin = Set.Univ :=
  sin_surjective.range_eq

end Complex

namespace Real

open_locale Real

theorem cos_eq_zero_iff {θ : ℝ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (((2*k)+1)*π) / 2 :=
  by 
    exactModCast @Complex.cos_eq_zero_iff θ

theorem cos_ne_zero_iff {θ : ℝ} : cos θ ≠ 0 ↔ ∀ (k : ℤ), θ ≠ (((2*k)+1)*π) / 2 :=
  by 
    rw [←not_exists, not_iff_not, cos_eq_zero_iff]

theorem cos_eq_cos_iff {x y : ℝ} : cos x = cos y ↔ ∃ k : ℤ, (y = ((2*k)*π)+x) ∨ y = ((2*k)*π) - x :=
  by 
    exactModCast @Complex.cos_eq_cos_iff x y

theorem sin_eq_sin_iff {x y : ℝ} : sin x = sin y ↔ ∃ k : ℤ, (y = ((2*k)*π)+x) ∨ y = (((2*k)+1)*π) - x :=
  by 
    exactModCast @Complex.sin_eq_sin_iff x y

end Real

