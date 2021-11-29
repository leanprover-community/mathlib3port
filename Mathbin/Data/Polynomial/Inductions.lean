import Mathbin.Data.Nat.Interval 
import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Induction on polynomials

This file contains lemmas dealing with different flavours of induction on polynomials.
-/


noncomputable theory

open_locale Classical BigOperators

open Finset

namespace Polynomial

universe u v w z

variable{R : Type u}{S : Type v}{T : Type w}{A : Type z}{a b : R}{n : ℕ}

section Semiringₓ

variable[Semiringₓ R]{p q : Polynomial R}

/-- `div_X p` returns a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
def div_X (p : Polynomial R) : Polynomial R :=
  ∑n in Ico 0 p.nat_degree, monomial n (p.coeff (n+1))

@[simp]
theorem coeff_div_X : (div_X p).coeff n = p.coeff (n+1) :=
  by 
    simp only [div_X, coeff_monomial, true_andₓ, finset_sum_coeff, not_ltₓ, mem_Ico, zero_le, Finset.sum_ite_eq',
      ite_eq_left_iff]
    intro h 
    rw [coeff_eq_zero_of_nat_degree_lt (Nat.lt_succ_of_leₓ h)]

theorem div_X_mul_X_add (p : Polynomial R) : ((div_X p*X)+C (p.coeff 0)) = p :=
  ext$
    by 
      rintro ⟨_ | _⟩ <;> simp [coeff_C, Nat.succ_ne_zero, coeff_mul_X]

@[simp]
theorem div_X_C (a : R) : div_X (C a) = 0 :=
  ext$
    fun n =>
      by 
        cases n <;> simp [div_X, coeff_C] <;> simp [coeff]

theorem div_X_eq_zero_iff : div_X p = 0 ↔ p = C (p.coeff 0) :=
  ⟨fun h =>
      by 
        simpa [eq_comm, h] using div_X_mul_X_add p,
    fun h =>
      by 
        rw [h, div_X_C]⟩

theorem div_X_add : div_X (p+q) = div_X p+div_X q :=
  ext$
    by 
      simp 

-- error in Data.Polynomial.Inductions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degree_div_X_lt (hp0 : «expr ≠ »(p, 0)) : «expr < »((div_X p).degree, p.degree) :=
by haveI [] [] [":=", expr nontrivial.of_polynomial_ne hp0]; calc
  «expr < »((div_X p).degree, «expr + »(«expr * »(div_X p, X), C (p.coeff 0)).degree) : if h : «expr ≤ »(degree p, 0) then begin
    have [ident h'] [":", expr «expr ≠ »(C (p.coeff 0), 0)] [],
    by rwa ["[", "<-", expr eq_C_of_degree_le_zero h, "]"] [],
    rw ["[", expr eq_C_of_degree_le_zero h, ",", expr div_X_C, ",", expr degree_zero, ",", expr zero_mul, ",", expr zero_add, "]"] [],
    exact [expr lt_of_le_of_ne bot_le (ne.symm «expr $ »(mt degree_eq_bot.1, by simp [] [] [] ["[", expr h', "]"] [] []))]
  end else have hXp0 : «expr ≠ »(div_X p, 0), by simpa [] [] [] ["[", expr div_X_eq_zero_iff, ",", "-", ident not_le, ",", expr degree_le_zero_iff, "]"] [] ["using", expr h],
  have «expr ≠ »(«expr * »(leading_coeff (div_X p), leading_coeff X), 0), by simpa [] [] [] [] [] [],
  have «expr < »(degree (C (p.coeff 0)), degree «expr * »(div_X p, X)), from calc
    «expr ≤ »(degree (C (p.coeff 0)), 0) : degree_C_le
    «expr < »(..., 1) : exprdec_trivial()
    «expr = »(..., degree (X : polynomial R)) : degree_X.symm
    «expr ≤ »(..., degree «expr * »(div_X p, X)) : by rw ["[", "<-", expr zero_add (degree X), ",", expr degree_mul' this, "]"] []; exact [expr add_le_add (by rw ["[", expr zero_le_degree_iff, ",", expr ne.def, ",", expr div_X_eq_zero_iff, "]"] []; exact [expr λ
       h0, h «expr ▸ »(h0.symm, degree_C_le)]) (le_refl _)],
  by rw ["[", expr degree_add_eq_left_of_degree_lt this, "]"] []; exact [expr degree_lt_degree_mul_X hXp0]
  «expr = »(..., p.degree) : congr_arg _ (div_X_mul_X_add _)

-- error in Data.Polynomial.Inductions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- An induction principle for polynomials, valued in Sort* instead of Prop. -/
@[elab_as_eliminator]
noncomputable
def rec_on_horner
{M : polynomial R → Sort*} : ∀
p : polynomial R, M 0 → ∀
p
a, «expr = »(coeff p 0, 0) → «expr ≠ »(a, 0) → M p → M «expr + »(p, C a) → ∀
p, «expr ≠ »(p, 0) → M p → M «expr * »(p, X) → M p
| p := λ
M0
MC
MX, if hp : «expr = »(p, 0) then eq.rec_on hp.symm M0 else have wf : «expr < »(degree (div_X p), degree p), from degree_div_X_lt hp,
by rw ["[", "<-", expr div_X_mul_X_add p, "]"] ["at", "*"]; exact [expr if hcp0 : «expr = »(coeff p 0, 0) then by rw ["[", expr hcp0, ",", expr C_0, ",", expr add_zero, "]"] []; exact [expr MX _ (λ
   h : «expr = »(div_X p, 0), by simpa [] [] [] ["[", expr h, ",", expr hcp0, "]"] [] ["using", expr hp]) (rec_on_horner _ M0 MC MX)] else MC _ _ (coeff_mul_X_zero _) hcp0 (if hpX0 : «expr = »(div_X p, 0) then show M «expr * »(div_X p, X), by rw ["[", expr hpX0, ",", expr zero_mul, "]"] []; exact [expr M0] else MX (div_X p) hpX0 (rec_on_horner _ M0 MC MX))]

-- error in Data.Polynomial.Inductions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--  A property holds for all polynomials of positive `degree` with coefficients in a semiring `R`
if it holds for
* `a * X`, with `a ∈ R`,
* `p * X`, with `p ∈ R[X]`,
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,
with appropriate restrictions on each term.

See `nat_degree_ne_zero_induction_on` for a similar statement involving no explicit multiplication.
 -/
@[elab_as_eliminator]
theorem degree_pos_induction_on
{P : polynomial R → exprProp()}
(p : polynomial R)
(h0 : «expr < »(0, degree p))
(hC : ∀ {a}, «expr ≠ »(a, 0) → P «expr * »(C a, X))
(hX : ∀ {p}, «expr < »(0, degree p) → P p → P «expr * »(p, X))
(hadd : ∀ {p} {a}, «expr < »(0, degree p) → P p → P «expr + »(p, C a)) : P p :=
rec_on_horner p (λ
 h, by rw [expr degree_zero] ["at", ident h]; exact [expr absurd h exprdec_trivial()]) (λ
 p
 a
 _
 _
 ih
 h0, have «expr < »(0, degree p), from lt_of_not_ge (λ
  h, «expr $ »(not_lt_of_ge degree_C_le, by rwa ["[", expr eq_C_of_degree_le_zero h, ",", "<-", expr C_add, "]"] ["at", ident h0])),
 hadd this (ih this)) (λ
 p
 _
 ih
 h0', if h0 : «expr < »(0, degree p) then hX h0 (ih h0) else by rw ["[", expr eq_C_of_degree_le_zero (le_of_not_gt h0), "]"] ["at", "*"]; exact [expr hC (λ
   h : «expr = »(coeff p 0, 0), by simpa [] [] [] ["[", expr h, ",", expr nat.not_lt_zero, "]"] [] ["using", expr h0'])]) h0

end Semiringₓ

end Polynomial

