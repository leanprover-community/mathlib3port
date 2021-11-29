import Mathbin.Algebra.CharP.Invertible 
import Mathbin.Order.Filter.AtTopBot 
import Mathbin.Tactic.Linarith.Default

/-!
# Quadratic discriminants and roots of a quadratic

This file defines the discriminant of a quadratic and gives the solution to a quadratic equation.

## Main definition

- `discrim a b c`: the discriminant of a quadratic `a * x * x + b * x + c` is `b * b - 4 * a * c`.

## Main statements

- `quadratic_eq_zero_iff`: roots of a quadratic can be written as
  `(-b + s) / (2 * a)` or `(-b - s) / (2 * a)`, where `s` is a square root of the discriminant.
- `quadratic_ne_zero_of_discrim_ne_sq`: if the discriminant has no square root,
  then the corresponding quadratic has no root.
- `discrim_le_zero`: if a quadratic is always non-negative, then its discriminant is non-positive.

## Tags

polynomial, quadratic, discriminant, root
-/


open Filter

section Ringₓ

variable{R : Type _}

/-- Discriminant of a quadratic -/
def discrim [Ringₓ R] (a b c : R) : R :=
  b ^ 2 - (4*a)*c

variable[CommRingₓ R][IsDomain R]{a b c : R}

-- error in Algebra.QuadraticDiscriminant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A quadratic has roots if and only if its discriminant equals some square.
-/
theorem quadratic_eq_zero_iff_discrim_eq_sq
(h2 : «expr ≠ »((2 : R), 0))
(ha : «expr ≠ »(a, 0))
(x : R) : «expr ↔ »(«expr = »(«expr + »(«expr + »(«expr * »(«expr * »(a, x), x), «expr * »(b, x)), c), 0), «expr = »(discrim a b c, «expr ^ »(«expr + »(«expr * »(«expr * »(2, a), x), b), 2))) :=
begin
  split,
  { assume [binders (h)],
    calc
      «expr = »(discrim a b c, «expr - »(«expr + »(«expr * »(«expr * »(4, a), «expr + »(«expr + »(«expr * »(«expr * »(a, x), x), «expr * »(b, x)), c)), «expr * »(b, b)), «expr * »(«expr * »(4, a), c))) : by { rw ["[", expr h, ",", expr discrim, "]"] [],
        ring [] }
      «expr = »(..., «expr ^ »(«expr + »(«expr * »(«expr * »(2, a), x), b), 2)) : by ring [] },
  { assume [binders (h)],
    have [ident ha] [":", expr «expr ≠ »(«expr * »(«expr * »(2, 2), a), 0)] [":=", expr mul_ne_zero (mul_ne_zero h2 h2) ha],
    apply [expr mul_left_cancel₀ ha],
    calc
      «expr = »(«expr * »(«expr * »(«expr * »(2, 2), a), «expr + »(«expr + »(«expr * »(«expr * »(a, x), x), «expr * »(b, x)), c)), «expr - »(«expr ^ »(«expr + »(«expr * »(«expr * »(2, a), x), b), 2), «expr - »(«expr ^ »(b, 2), «expr * »(«expr * »(4, a), c)))) : by ring []
      «expr = »(..., 0) : by { rw ["[", "<-", expr h, ",", expr discrim, "]"] [],
        ring [] }
      «expr = »(..., «expr * »(«expr * »(«expr * »(2, 2), a), 0)) : by ring [] }
end

/-- A quadratic has no root if its discriminant has no square root. -/
theorem quadratic_ne_zero_of_discrim_ne_sq (h2 : (2 : R) ≠ 0) (ha : a ≠ 0) (h : ∀ (s : R), discrim a b c ≠ s*s)
  (x : R) : ((((a*x)*x)+b*x)+c) ≠ 0 :=
  by 
    intro h' 
    rw [quadratic_eq_zero_iff_discrim_eq_sq h2 ha, sq] at h' 
    exact h _ h'

end Ringₓ

section Field

variable{K : Type _}[Field K][Invertible (2 : K)]{a b c x : K}

-- error in Algebra.QuadraticDiscriminant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Roots of a quadratic -/
theorem quadratic_eq_zero_iff
(ha : «expr ≠ »(a, 0))
{s : K}
(h : «expr = »(discrim a b c, «expr * »(s, s)))
(x : K) : «expr ↔ »(«expr = »(«expr + »(«expr + »(«expr * »(«expr * »(a, x), x), «expr * »(b, x)), c), 0), «expr ∨ »(«expr = »(x, «expr / »(«expr + »(«expr- »(b), s), «expr * »(2, a))), «expr = »(x, «expr / »(«expr - »(«expr- »(b), s), «expr * »(2, a))))) :=
begin
  have [ident h2] [":", expr «expr ≠ »((2 : K), 0)] [":=", expr nonzero_of_invertible 2],
  rw ["[", expr quadratic_eq_zero_iff_discrim_eq_sq h2 ha, ",", expr h, ",", expr sq, ",", expr mul_self_eq_mul_self_iff, "]"] [],
  have [ident ne] [":", expr «expr ≠ »(«expr * »(2, a), 0)] [":=", expr mul_ne_zero h2 ha],
  have [] [":", expr «expr = »(x, «expr / »(«expr * »(«expr * »(2, a), x), «expr * »(2, a)))] [":=", expr (mul_div_cancel_left x ne).symm],
  have [ident h₁] [":", expr «expr = »(«expr * »(«expr * »(2, a), «expr / »(«expr + »(«expr- »(b), s), «expr * »(2, a))), «expr + »(«expr- »(b), s))] [":=", expr mul_div_cancel' _ ne],
  have [ident h₂] [":", expr «expr = »(«expr * »(«expr * »(2, a), «expr / »(«expr - »(«expr- »(b), s), «expr * »(2, a))), «expr - »(«expr- »(b), s))] [":=", expr mul_div_cancel' _ ne],
  split,
  { intro [ident h'],
    rcases [expr h'],
    { left,
      rw [expr h'] [],
      simpa [] [] [] ["[", expr add_comm, "]"] [] [] },
    { right,
      rw [expr h'] [],
      simpa [] [] [] ["[", expr add_comm, ",", expr sub_eq_add_neg, "]"] [] [] } },
  { intro [ident h'],
    rcases [expr h'],
    { left,
      rw ["[", expr h', ",", expr h₁, "]"] [],
      ring [] },
    { right,
      rw ["[", expr h', ",", expr h₂, "]"] [],
      ring [] } }
end

/-- A quadratic has roots if its discriminant has square roots -/
theorem exists_quadratic_eq_zero (ha : a ≠ 0) (h : ∃ s, discrim a b c = s*s) : ∃ x, ((((a*x)*x)+b*x)+c) = 0 :=
  by 
    rcases h with ⟨s, hs⟩
    use ((-b)+s) / 2*a 
    rw [quadratic_eq_zero_iff ha hs]
    simp 

-- error in Algebra.QuadraticDiscriminant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Root of a quadratic when its discriminant equals zero -/
theorem quadratic_eq_zero_iff_of_discrim_eq_zero
(ha : «expr ≠ »(a, 0))
(h : «expr = »(discrim a b c, 0))
(x : K) : «expr ↔ »(«expr = »(«expr + »(«expr + »(«expr * »(«expr * »(a, x), x), «expr * »(b, x)), c), 0), «expr = »(x, «expr / »(«expr- »(b), «expr * »(2, a)))) :=
begin
  have [] [":", expr «expr = »(discrim a b c, «expr * »(0, 0))] [],
  by rw ["[", expr h, ",", expr mul_zero, "]"] [],
  rw ["[", expr quadratic_eq_zero_iff ha this, ",", expr add_zero, ",", expr sub_zero, ",", expr or_self, "]"] []
end

end Field

section LinearOrderedField

variable{K : Type _}[LinearOrderedField K]{a b c : K}

-- error in Algebra.QuadraticDiscriminant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a polynomial of degree 2 is always nonnegative, then its discriminant is nonpositive -/
theorem discrim_le_zero
(h : ∀
 x : K, «expr ≤ »(0, «expr + »(«expr + »(«expr * »(«expr * »(a, x), x), «expr * »(b, x)), c))) : «expr ≤ »(discrim a b c, 0) :=
begin
  rw ["[", expr discrim, ",", expr sq, "]"] [],
  obtain [ident ha, "|", ident rfl, "|", ident ha, ":", expr «expr ∨ »(«expr < »(a, 0), «expr ∨ »(«expr = »(a, 0), «expr < »(0, a))), ":=", expr lt_trichotomy a 0],
  { have [] [":", expr tendsto (λ
      x, «expr + »(«expr * »(«expr + »(«expr * »(a, x), b), x), c)) at_top at_bot] [":=", expr tendsto_at_bot_add_const_right _ c ((tendsto_at_bot_add_const_right _ b (tendsto_id.neg_const_mul_at_top ha)).at_bot_mul_at_top tendsto_id)],
    rcases [expr (this.eventually (eventually_lt_at_bot 0)).exists, "with", "⟨", ident x, ",", ident hx, "⟩"],
    exact [expr false.elim «expr $ »((h x).not_lt, by rwa ["<-", expr add_mul] [])] },
  { rcases [expr em «expr = »(b, 0), "with", "(", ident rfl, "|", ident hb, ")"],
    { simp [] [] [] [] [] [] },
    { have [] [] [":=", expr h «expr / »(«expr - »(«expr- »(c), 1), b)],
      rw ["[", expr mul_div_cancel' _ hb, "]"] ["at", ident this],
      linarith [] [] [] } },
  { have [] [] [":=", expr calc
       «expr = »(«expr * »(«expr * »(4, a), «expr + »(«expr + »(«expr * »(«expr * »(a, «expr * »(«expr- »(«expr / »(b, a)), «expr / »(1, 2))), «expr * »(«expr- »(«expr / »(b, a)), «expr / »(1, 2))), «expr * »(b, «expr * »(«expr- »(«expr / »(b, a)), «expr / »(1, 2)))), c)), «expr + »(«expr - »(«expr * »(«expr * »(a, «expr / »(b, a)), «expr * »(a, «expr / »(b, a))), «expr * »(«expr * »(2, «expr * »(a, «expr / »(b, a))), b)), «expr * »(«expr * »(4, a), c))) : by ring []
       «expr = »(..., «expr- »(«expr - »(«expr * »(b, b), «expr * »(«expr * »(4, a), c)))) : by { simp [] [] ["only"] ["[", expr mul_div_cancel' b (ne_of_gt ha), "]"] [] [],
         ring [] }],
    have [ident ha'] [":", expr «expr ≤ »(0, «expr * »(4, a))] [],
    by linarith [] [] [],
    have [ident h] [] [":=", expr mul_nonneg ha' (h «expr * »(«expr- »(«expr / »(b, a)), «expr / »(1, 2)))],
    rw [expr this] ["at", ident h],
    rwa ["<-", expr neg_nonneg] [] }
end

-- error in Algebra.QuadraticDiscriminant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If a polynomial of degree 2 is always positive, then its discriminant is negative,
at least when the coefficient of the quadratic term is nonzero.
-/
theorem discrim_lt_zero
(ha : «expr ≠ »(a, 0))
(h : ∀
 x : K, «expr < »(0, «expr + »(«expr + »(«expr * »(«expr * »(a, x), x), «expr * »(b, x)), c))) : «expr < »(discrim a b c, 0) :=
begin
  have [] [":", expr ∀
   x : K, «expr ≤ »(0, «expr + »(«expr + »(«expr * »(«expr * »(a, x), x), «expr * »(b, x)), c))] [":=", expr assume
   x, le_of_lt (h x)],
  refine [expr lt_of_le_of_ne (discrim_le_zero this) _],
  assume [binders (h')],
  have [] [] [":=", expr h «expr / »(«expr- »(b), «expr * »(2, a))],
  have [] [":", expr «expr = »(«expr + »(«expr + »(«expr * »(«expr * »(a, «expr / »(«expr- »(b), «expr * »(2, a))), «expr / »(«expr- »(b), «expr * »(2, a))), «expr * »(b, «expr / »(«expr- »(b), «expr * »(2, a)))), c), 0)] [],
  { rw ["[", expr quadratic_eq_zero_iff_of_discrim_eq_zero ha h' «expr / »(«expr- »(b), «expr * »(2, a)), "]"] [] },
  linarith [] [] []
end

end LinearOrderedField

