import Mathbin.Algebra.Order.EuclideanAbsoluteValue 
import Mathbin.Data.Polynomial.FieldDivision

/-!
# Absolute value on polynomials over a finite field.

Let `Fq` be a finite field of cardinality `q`, then the map sending a polynomial `p`
to `q ^ degree p` (where `q ^ degree 0 = 0`) is an absolute value.

## Main definitions

 * `polynomial.card_pow_degree` is an absolute value on `𝔽_q[t]`, the ring of
   polynomials over a finite field of cardinality `q`, mapping a polynomial `p`
   to `q ^ degree p` (where `q ^ degree 0 = 0`)

## Main results
 * `polynomial.card_pow_degree_is_euclidean`: `card_pow_degree` respects the
   Euclidean domain structure on the ring of polynomials

-/


namespace Polynomial

variable {Fq : Type _} [Field Fq] [Fintype Fq]

open AbsoluteValue

open_locale Classical

-- error in Data.Polynomial.Degree.CardPowDegree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `card_pow_degree` is the absolute value on `𝔽_q[t]` sending `f` to `q ^ degree f`.

`card_pow_degree 0` is defined to be `0`. -/
noncomputable
def card_pow_degree : absolute_value (polynomial Fq) exprℤ() :=
have card_pos : «expr < »(0, fintype.card Fq) := fintype.card_pos_iff.mpr infer_instance,
have pow_pos : ∀
n, «expr < »(0, «expr ^ »((fintype.card Fq : exprℤ()), n)) := λ n, pow_pos (int.coe_nat_pos.mpr card_pos) n,
{ to_fun := λ p, if «expr = »(p, 0) then 0 else «expr ^ »(fintype.card Fq, p.nat_degree),
  nonneg' := λ p, by { dsimp [] [] [] [],
    split_ifs [] [],
    { refl },
    exact [expr pow_nonneg (int.coe_zero_le _) _] },
  eq_zero' := λ
  p, «expr $ »(ite_eq_left_iff.trans, ⟨λ h, by { contrapose ["!"] [ident h],
      exact [expr ⟨h, (pow_pos _).ne'⟩] }, absurd⟩),
  add_le' := λ p q, begin
    by_cases [expr hp, ":", expr «expr = »(p, 0)],
    { simp [] [] [] ["[", expr hp, "]"] [] [] },
    by_cases [expr hq, ":", expr «expr = »(q, 0)],
    { simp [] [] [] ["[", expr hq, "]"] [] [] },
    by_cases [expr hpq, ":", expr «expr = »(«expr + »(p, q), 0)],
    { simp [] [] ["only"] ["[", expr hpq, ",", expr hp, ",", expr hq, ",", expr eq_self_iff_true, ",", expr if_true, ",", expr if_false, "]"] [] [],
      exact [expr add_nonneg (pow_pos _).le (pow_pos _).le] },
    simp [] [] ["only"] ["[", expr hpq, ",", expr hp, ",", expr hq, ",", expr if_false, "]"] [] [],
    refine [expr le_trans (pow_le_pow (by linarith [] [] []) (polynomial.nat_degree_add_le _ _)) _],
    refine [expr le_trans (le_max_iff.mpr _) (max_le_add_of_nonneg (pow_nonneg (by linarith [] [] []) _) (pow_nonneg (by linarith [] [] []) _))],
    exact [expr (max_choice p.nat_degree q.nat_degree).imp (λ
      h, by rw ["[", expr h, "]"] []) (λ h, by rw ["[", expr h, "]"] [])]
  end,
  map_mul' := λ p q, begin
    by_cases [expr hp, ":", expr «expr = »(p, 0)],
    { simp [] [] [] ["[", expr hp, "]"] [] [] },
    by_cases [expr hq, ":", expr «expr = »(q, 0)],
    { simp [] [] [] ["[", expr hq, "]"] [] [] },
    have [ident hpq] [":", expr «expr ≠ »(«expr * »(p, q), 0)] [":=", expr mul_ne_zero hp hq],
    simp [] [] ["only"] ["[", expr hpq, ",", expr hp, ",", expr hq, ",", expr eq_self_iff_true, ",", expr if_true, ",", expr if_false, ",", expr polynomial.nat_degree_mul hp hq, ",", expr pow_add, "]"] [] []
  end }

theorem card_pow_degree_apply (p : Polynomial Fq) :
  card_pow_degree p = if p = 0 then 0 else Fintype.card Fq^nat_degree p :=
  rfl

@[simp]
theorem card_pow_degree_zero : card_pow_degree (0 : Polynomial Fq) = 0 :=
  if_pos rfl

@[simp]
theorem card_pow_degree_nonzero (p : Polynomial Fq) (hp : p ≠ 0) : card_pow_degree p = (Fintype.card Fq^p.nat_degree) :=
  if_neg hp

theorem card_pow_degree_is_euclidean : is_euclidean (card_pow_degree : AbsoluteValue (Polynomial Fq) ℤ) :=
  have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance 
  have pow_pos : ∀ n, 0 < ((Fintype.card Fq : ℤ)^n) := fun n => pow_pos (Int.coe_nat_pos.mpr card_pos) n
  { map_lt_map_iff' :=
      fun p q =>
        by 
          simp only [EuclideanDomain.R, card_pow_degree_apply]
          splitIfs with hp hq hq
          ·
            simp only [hp, hq, lt_self_iff_false]
          ·
            simp only [hp, hq, degree_zero, Ne.def, bot_lt_iff_ne_bot, degree_eq_bot, pow_pos, not_false_iff]
          ·
            simp only [hp, hq, degree_zero, not_lt_bot, (pow_pos _).not_lt]
          ·
            rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq, WithBot.coe_lt_coe, pow_lt_pow_iff]
            exactModCast @Fintype.one_lt_card Fq _ _ }

end Polynomial

