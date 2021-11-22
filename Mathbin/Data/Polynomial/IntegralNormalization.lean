import Mathbin.Data.Polynomial.AlgebraMap 
import Mathbin.Data.Polynomial.Degree.Lemmas 
import Mathbin.Data.Polynomial.Monic

/-!
# Theory of monic polynomials

We define `integral_normalization`, which relate arbitrary polynomials to monic ones.
-/


open_locale BigOperators

namespace Polynomial

universe u v y

variable{R : Type u}{S : Type v}{a b : R}{m n : ℕ}{ι : Type y}

section IntegralNormalization

section Semiringₓ

variable[Semiringₓ R]

/-- If `f : polynomial R` is a nonzero polynomial with root `z`, `integral_normalization f` is
a monic polynomial with root `leading_coeff f * z`.

Moreover, `integral_normalization 0 = 0`.
-/
noncomputable def integral_normalization (f : Polynomial R) : Polynomial R :=
  ∑i in f.support, monomial i (if f.degree = i then 1 else coeff f i*f.leading_coeff ^ (f.nat_degree - 1 - i))

@[simp]
theorem integral_normalization_zero : integral_normalization (0 : Polynomial R) = 0 :=
  by 
    simp [integral_normalization]

-- error in Data.Polynomial.IntegralNormalization: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integral_normalization_coeff
{f : polynomial R}
{i : exprℕ()} : «expr = »((integral_normalization f).coeff i, if «expr = »(f.degree, i) then 1 else «expr * »(coeff f i, «expr ^ »(f.leading_coeff, «expr - »(«expr - »(f.nat_degree, 1), i)))) :=
have «expr = »(f.coeff i, 0) → «expr ≠ »(f.degree, i), from λ hc hd, coeff_ne_zero_of_eq_degree hd hc,
by simp [] [] [] ["[", expr integral_normalization, ",", expr coeff_monomial, ",", expr this, ",", expr mem_support_iff, "]"] [] [] { contextual := tt }

-- error in Data.Polynomial.IntegralNormalization: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integral_normalization_support {f : polynomial R} : «expr ⊆ »((integral_normalization f).support, f.support) :=
by { intro [],
  simp [] [] [] ["[", expr integral_normalization, ",", expr coeff_monomial, ",", expr mem_support_iff, "]"] [] [] { contextual := tt } }

theorem integral_normalization_coeff_degree {f : Polynomial R} {i : ℕ} (hi : f.degree = i) :
  (integral_normalization f).coeff i = 1 :=
  by 
    rw [integral_normalization_coeff, if_pos hi]

theorem integral_normalization_coeff_nat_degree {f : Polynomial R} (hf : f ≠ 0) :
  (integral_normalization f).coeff (nat_degree f) = 1 :=
  integral_normalization_coeff_degree (degree_eq_nat_degree hf)

theorem integral_normalization_coeff_ne_degree {f : Polynomial R} {i : ℕ} (hi : f.degree ≠ i) :
  coeff (integral_normalization f) i = coeff f i*f.leading_coeff ^ (f.nat_degree - 1 - i) :=
  by 
    rw [integral_normalization_coeff, if_neg hi]

theorem integral_normalization_coeff_ne_nat_degree {f : Polynomial R} {i : ℕ} (hi : i ≠ nat_degree f) :
  coeff (integral_normalization f) i = coeff f i*f.leading_coeff ^ (f.nat_degree - 1 - i) :=
  integral_normalization_coeff_ne_degree (degree_ne_of_nat_degree_ne hi.symm)

theorem monic_integral_normalization {f : Polynomial R} (hf : f ≠ 0) : monic (integral_normalization f) :=
  monic_of_degree_le f.nat_degree
    (Finset.sup_le$ fun i h => WithBot.coe_le_coe.2$ le_nat_degree_of_mem_supp i$ integral_normalization_support h)
    (integral_normalization_coeff_nat_degree hf)

end Semiringₓ

section IsDomain

variable[Ringₓ R][IsDomain R]

@[simp]
theorem support_integral_normalization {f : Polynomial R} : (integral_normalization f).support = f.support :=
  by 
    byCases' hf : f = 0
    ·
      simp [hf]
    ext i 
    refine' ⟨fun h => integral_normalization_support h, _⟩
    simp only [integral_normalization_coeff, mem_support_iff]
    intro hfi 
    splitIfs with hi <;> simp [hfi, hi, pow_ne_zero _ (leading_coeff_ne_zero.mpr hf)]

end IsDomain

section IsDomain

variable[CommRingₓ R][IsDomain R]

variable[CommRingₓ S]

theorem integral_normalization_eval₂_eq_zero {p : Polynomial R} (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
  (inj : ∀ x : R, f x = 0 → x = 0) : eval₂ f (z*f p.leading_coeff) (integral_normalization p) = 0 :=
  calc
    eval₂ f (z*f p.leading_coeff) (integral_normalization p) =
      p.support.attach.sum fun i => f (coeff (integral_normalization p) i.1*p.leading_coeff ^ i.1)*z ^ i.1 :=
    by 
      rw [eval₂, sum_def, support_integral_normalization]
      simp only [mul_commₓ z, mul_powₓ, mul_assocₓ, RingHom.map_pow, RingHom.map_mul]
      exact finset.sum_attach.symm 
    _ = p.support.attach.sum fun i => f (coeff p i.1*p.leading_coeff ^ (nat_degree p - 1))*z ^ i.1 :=
    by 
      byCases' hp : p = 0
      ·
        simp [hp]
      have one_le_deg : 1 ≤ nat_degree p := Nat.succ_le_of_ltₓ (nat_degree_pos_of_eval₂_root hp f hz inj)
      congr with i 
      congr 2
      byCases' hi : i.1 = nat_degree p
      ·
        rw [hi, integral_normalization_coeff_degree, one_mulₓ, leading_coeff, ←pow_succₓ,
          tsub_add_cancel_of_le one_le_deg]
        exact degree_eq_nat_degree hp
      ·
        have  : i.1 ≤ p.nat_degree - 1 :=
          Nat.le_pred_of_lt (lt_of_le_of_neₓ (le_nat_degree_of_ne_zero (mem_support_iff.mp i.2)) hi)
        rw [integral_normalization_coeff_ne_nat_degree hi, mul_assocₓ, ←pow_addₓ, tsub_add_cancel_of_le this]
    _ = (f p.leading_coeff ^ (nat_degree p - 1))*eval₂ f z p :=
    by 
      simpRw [eval₂, sum_def, fun i => mul_commₓ (coeff p i), RingHom.map_mul, RingHom.map_pow, mul_assocₓ,
        ←Finset.mul_sum]
      congr 1 
      exact @Finset.sum_attach _ _ p.support _ fun i => f (p.coeff i)*z ^ i 
    _ = 0 :=
    by 
      rw [hz, _root_.mul_zero]
    

theorem integral_normalization_aeval_eq_zero [Algebra R S] {f : Polynomial R} {z : S} (hz : aeval z f = 0)
  (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) :
  aeval (z*algebraMap R S f.leading_coeff) (integral_normalization f) = 0 :=
  integral_normalization_eval₂_eq_zero (algebraMap R S) hz inj

end IsDomain

end IntegralNormalization

end Polynomial

