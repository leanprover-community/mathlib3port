import Mathbin.Data.Polynomial.Coeff

/-!
# Theory of univariate polynomials

The main results are `induction_on` and `as_sum`.
-/


noncomputable theory

open Finsupp Finset

namespace Polynomial

universe u v w x y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z} {a b : R} {m n : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q r : Polynomial R}

theorem sum_C_mul_X_eq (p : Polynomial R) : (p.sum fun n a => C a*X ^ n) = p :=
  by 
    ext n 
    simp only [Polynomial.sum, X_pow_eq_monomial, coeff_monomial, mul_oneₓ, finset_sum_coeff, C_mul_monomial, not_not,
      mem_support_iff, Finset.sum_ite_eq', ite_eq_left_iff]
    exact fun h => h.symm

theorem sum_monomial_eq (p : Polynomial R) : (p.sum fun n a => monomial n a) = p :=
  by 
    simp only [monomial_eq_C_mul_X, sum_C_mul_X_eq]

-- error in Data.Polynomial.Induction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[elab_as_eliminator]
protected
theorem induction_on
{M : polynomial R → exprProp()}
(p : polynomial R)
(h_C : ∀ a, M (C a))
(h_add : ∀ p q, M p → M q → M «expr + »(p, q))
(h_monomial : ∀
 (n : exprℕ())
 (a : R), M «expr * »(C a, «expr ^ »(X, n)) → M «expr * »(C a, «expr ^ »(X, «expr + »(n, 1)))) : M p :=
begin
  have [ident A] [":", expr ∀ {n : exprℕ()} {a}, M «expr * »(C a, «expr ^ »(X, n))] [],
  { assume [binders (n a)],
    induction [expr n] [] ["with", ident n, ident ih] [],
    { simp [] [] ["only"] ["[", expr pow_zero, ",", expr mul_one, ",", expr h_C, "]"] [] [] },
    { exact [expr h_monomial _ _ ih] } },
  have [ident B] [":", expr ∀
   s : finset exprℕ(), M (s.sum (λ n : exprℕ(), «expr * »(C (p.coeff n), «expr ^ »(X, n))))] [],
  { apply [expr finset.induction],
    { convert [] [expr h_C 0] [],
      exact [expr C_0.symm] },
    { assume [binders (n s ns ih)],
      rw [expr sum_insert ns] [],
      exact [expr h_add _ _ A ih] } },
  rw ["[", "<-", expr sum_C_mul_X_eq p, ",", expr polynomial.sum, "]"] [],
  exact [expr B _]
end

/--
To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_eliminator]
protected theorem induction_on' {M : Polynomial R → Prop} (p : Polynomial R) (h_add : ∀ p q, M p → M q → M (p+q))
  (h_monomial : ∀ n : ℕ a : R, M (monomial n a)) : M p :=
  Polynomial.induction_on p (h_monomial 0) h_add
    fun n a h =>
      by 
        rw [←monomial_eq_C_mul_X]
        exact h_monomial _ _

section Coeff

theorem coeff_mul_monomial (p : Polynomial R) (n d : ℕ) (r : R) : coeff (p*monomial n r) (d+n) = coeff p d*r :=
  by 
    rw [monomial_eq_C_mul_X, ←X_pow_mul, ←mul_assocₓ, coeff_mul_C, coeff_mul_X_pow]

theorem coeff_monomial_mul (p : Polynomial R) (n d : ℕ) (r : R) : coeff (monomial n r*p) (d+n) = r*coeff p d :=
  by 
    rw [monomial_eq_C_mul_X, mul_assocₓ, coeff_C_mul, X_pow_mul, coeff_mul_X_pow]

theorem coeff_mul_monomial_zero (p : Polynomial R) (d : ℕ) (r : R) : coeff (p*monomial 0 r) d = coeff p d*r :=
  coeff_mul_monomial p 0 d r

theorem coeff_monomial_zero_mul (p : Polynomial R) (d : ℕ) (r : R) : coeff (monomial 0 r*p) d = r*coeff p d :=
  coeff_monomial_mul p 0 d r

end Coeff

open Submodule Polynomial Set

variable {f : Polynomial R} {I : Submodule (Polynomial R) (Polynomial R)}

/--  If the coefficients of a polynomial belong to n ideal contains the submodule span of the
coefficients of a polynomial. -/
theorem span_le_of_coeff_mem_C_inverse (cf : ∀ i : ℕ, f.coeff i ∈ C ⁻¹' I.carrier) :
  span (Polynomial R) { g | ∃ i, g = C (f.coeff i) } ≤ I :=
  by 
    refine' bInter_subset_of_mem _ 
    rintro _ ⟨i, rfl⟩
    exact set_like.mem_coe.mpr (cf i)

-- error in Data.Polynomial.Induction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_span_C_coeff : «expr ∈ »(f, span (polynomial R) {g : polynomial R | «expr∃ , »((i : exprℕ()), «expr = »(g, C (coeff f i)))}) :=
begin
  let [ident p] [] [":=", expr span (polynomial R) {g : polynomial R | «expr∃ , »((i : exprℕ()), «expr = »(g, C (coeff f i)))}],
  nth_rewrite [0] [expr (sum_C_mul_X_eq f).symm] [],
  refine [expr submodule.sum_mem _ (λ n hn, _)],
  dsimp [] [] [] [],
  have [] [":", expr «expr ∈ »(C (coeff f n), p)] [],
  by { apply [expr subset_span],
    simp [] [] [] [] [] [] },
  have [] [":", expr «expr ∈ »(«expr • »(monomial n (1 : R), C (coeff f n)), p)] [":=", expr p.smul_mem _ this],
  convert [] [expr this] ["using", 1],
  simp [] [] ["only"] ["[", expr monomial_mul_C, ",", expr one_mul, ",", expr smul_eq_mul, "]"] [] [],
  rw [expr monomial_eq_C_mul_X] []
end

theorem exists_coeff_not_mem_C_inverse : f ∉ I → ∃ i : ℕ, coeff f i ∉ C ⁻¹' I.carrier :=
  imp_of_not_imp_not _ _
    fun cf => not_not.mpr ((span_le_of_coeff_mem_C_inverse (not_exists_not.mp cf)) mem_span_C_coeff)

end Semiringₓ

end Polynomial

