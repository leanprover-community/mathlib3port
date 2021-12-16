import Mathbin.Data.Nat.Interval 
import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Induction on polynomials

This file contains lemmas dealing with different flavours of induction on polynomials.
-/


noncomputable section 

open_locale Classical BigOperators

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q : Polynomial R}

/-- `div_X p` returns a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
def div_X (p : Polynomial R) : Polynomial R :=
  ∑ n in Ico 0 p.nat_degree, monomial n (p.coeff (n+1))

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

theorem degree_div_X_lt (hp0 : p ≠ 0) : (div_X p).degree < p.degree :=
  by 
    have  := nontrivial.of_polynomial_ne hp0 <;>
      calc (div_X p).degree < ((div_X p*X)+C (p.coeff 0)).degree :=
        if h : degree p ≤ 0 then
          by 
            have h' : C (p.coeff 0) ≠ 0
            ·
              rwa [←eq_C_of_degree_le_zero h]
            rw [eq_C_of_degree_le_zero h, div_X_C, degree_zero, zero_mul, zero_addₓ]
            exact
              lt_of_le_of_neₓ bot_le
                (Ne.symm
                  (mt degree_eq_bot.1$
                    by 
                      simp [h']))
        else
          have hXp0 : div_X p ≠ 0 :=
            by 
              simpa [div_X_eq_zero_iff, -not_leₓ, degree_le_zero_iff] using h 
          have  : (leading_coeff (div_X p)*leading_coeff X) ≠ 0 :=
            by 
              simpa 
          have  : degree (C (p.coeff 0)) < degree (div_X p*X) :=
            calc degree (C (p.coeff 0)) ≤ 0 := degree_C_le 
              _ < 1 :=
              by 
                decide 
              _ = degree (X : Polynomial R) := degree_X.symm 
              _ ≤ degree (div_X p*X) :=
              by 
                rw [←zero_addₓ (degree X), degree_mul' this] <;>
                  exact
                    add_le_add
                      (by 
                        rw [zero_le_degree_iff, Ne.def, div_X_eq_zero_iff] <;>
                          exact fun h0 => h (h0.symm ▸ degree_C_le))
                      (le_reflₓ _)
              
          by 
            rw [degree_add_eq_left_of_degree_lt this] <;> exact degree_lt_degree_mul_X hXp0 _ = p.degree :=
        congr_argₓ _ (div_X_mul_X_add _)

/-- An induction principle for polynomials, valued in Sort* instead of Prop. -/
@[elab_as_eliminator]
noncomputable def rec_on_horner {M : Polynomial R → Sort _} :
  ∀ p : Polynomial R, M 0 → (∀ p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p+C a)) → (∀ p, p ≠ 0 → M p → M (p*X)) → M p
| p =>
  fun M0 MC MX =>
    if hp : p = 0 then Eq.recOnₓ hp.symm M0 else
      have wf : degree (div_X p) < degree p := degree_div_X_lt hp 
      by 
        rw [←div_X_mul_X_add p] at * <;>
          exact
            if hcp0 : coeff p 0 = 0 then
              by 
                rw [hcp0, C_0, add_zeroₓ] <;>
                  exact
                    MX _
                      (fun h : div_X p = 0 =>
                        by 
                          simpa [h, hcp0] using hp)
                      (rec_on_horner _ M0 MC MX)
            else
              MC _ _ (coeff_mul_X_zero _) hcp0
                (if hpX0 : div_X p = 0 then
                  show M (div_X p*X)by 
                    rw [hpX0, zero_mul] <;> exact M0
                else MX (div_X p) hpX0 (rec_on_horner _ M0 MC MX))

/--  A property holds for all polynomials of positive `degree` with coefficients in a semiring `R`
if it holds for
* `a * X`, with `a ∈ R`,
* `p * X`, with `p ∈ R[X]`,
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,
with appropriate restrictions on each term.

See `nat_degree_ne_zero_induction_on` for a similar statement involving no explicit multiplication.
 -/
@[elab_as_eliminator]
theorem degree_pos_induction_on {P : Polynomial R → Prop} (p : Polynomial R) (h0 : 0 < degree p)
  (hC : ∀ {a}, a ≠ 0 → P (C a*X)) (hX : ∀ {p}, 0 < degree p → P p → P (p*X))
  (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p+C a)) : P p :=
  rec_on_horner p
    (fun h =>
      by 
        rw [degree_zero] at h <;>
          exact
            absurd h
              (by 
                decide))
    (fun p a _ _ ih h0 =>
      have  : 0 < degree p :=
        lt_of_not_geₓ
          fun h =>
            not_lt_of_geₓ degree_C_le$
              by 
                rwa [eq_C_of_degree_le_zero h, ←C_add] at h0 
      hadd this (ih this))
    (fun p _ ih h0' =>
      if h0 : 0 < degree p then hX h0 (ih h0) else
        by 
          rw [eq_C_of_degree_le_zero (le_of_not_gtₓ h0)] at * <;>
            exact
              hC
                fun h : coeff p 0 = 0 =>
                  by 
                    simpa [h, Nat.not_lt_zeroₓ] using h0')
    h0

end Semiringₓ

end Polynomial

