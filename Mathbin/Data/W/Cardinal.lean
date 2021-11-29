import Mathbin.SetTheory.CardinalOrdinal 
import Mathbin.Data.W.Basic

/-!
# Cardinality of W-types

This file proves some theorems about the cardinality of W-types. The main result is
`cardinal_mk_le_max_omega_of_fintype` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `W_type β` is at most the maximum of the
cardinality of `α` and `cardinal.omega`.
This can be used to prove theorems about the cardinality of algebraic constructions such as
polynomials. There is a surjection from a `W_type` to `mv_polynomial` for example, and
this surjection can be used to put an upper bound on the cardinality of `mv_polynomial`.

## Tags

W, W type, cardinal, first order
-/


universe u

variable{α : Type u}{β : α → Type u}

noncomputable theory

namespace WType

open_locale Cardinal

open Cardinal

-- error in Data.W.Cardinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem cardinal_mk_eq_sum : «expr = »(«expr#»() (W_type β), sum (λ
  a : α, «expr ^ »(«expr#»() (W_type β), «expr#»() (β a)))) :=
begin
  simp [] [] ["only"] ["[", expr cardinal.power_def, ",", "<-", expr cardinal.mk_sigma, "]"] [] [],
  exact [expr mk_congr (equiv_sigma β)]
end

-- error in Data.W.Cardinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- `#(W_type β)` is the least cardinal `κ` such that `sum (λ a : α, κ ^ #(β a)) ≤ κ` -/
theorem cardinal_mk_le_of_le
{κ : cardinal.{u}}
(hκ : «expr ≤ »(sum (λ a : α, «expr ^ »(κ, «expr#»() (β a))), κ)) : «expr ≤ »(«expr#»() (W_type β), κ) :=
begin
  induction [expr κ] ["using", ident cardinal.induction_on] ["with", ident γ] [],
  simp [] [] ["only"] ["[", expr cardinal.power_def, ",", "<-", expr cardinal.mk_sigma, ",", expr cardinal.le_def, "]"] [] ["at", ident hκ],
  cases [expr hκ] [],
  exact [expr cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)]
end

-- error in Data.W.Cardinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If, for any `a : α`, `β a` is finite, then the cardinality of `W_type β`
  is at most the maximum of the cardinality of `α` and `ω`  -/
theorem cardinal_mk_le_max_omega_of_fintype
[∀ a, fintype (β a)] : «expr ≤ »(«expr#»() (W_type β), max («expr#»() α) exprω()) :=
«expr $ »((is_empty_or_nonempty α).elim (begin
    introI [ident h],
    rw ["[", expr cardinal.mk_eq_zero (W_type β), "]"] [],
    exact [expr zero_le _]
  end), λ hn, let m := max («expr#»() α) exprω() in
 «expr $ »(cardinal_mk_le_of_le, calc
    «expr ≤ »(cardinal.sum (λ
      a : α, «expr ^ »(m, «expr#»() (β a))), «expr * »(«expr#»() α, cardinal.sup.{u, u} (λ
       a : α, «expr ^ »(m, cardinal.mk (β a))))) : cardinal.sum_le_sup _
    «expr ≤ »(..., «expr * »(m, cardinal.sup.{u, u} (λ
       a : α, «expr ^ »(m, «expr#»() (β a))))) : mul_le_mul' (le_max_left _ _) (le_refl _)
    «expr = »(..., m) : mul_eq_left.{u} (le_max_right _ _) (cardinal.sup_le.2 (λ i, begin
        cases [expr lt_omega.1 (lt_omega_iff_fintype.2 ⟨show fintype (β i), by apply_instance⟩)] ["with", ident n, ident hn],
        rw ["[", expr hn, "]"] [],
        exact [expr power_nat_le (le_max_right _ _)]
      end)) (pos_iff_ne_zero.1 (succ_le.1 (begin
         rw ["[", expr succ_zero, "]"] [],
         obtain ["⟨", ident a, "⟩", ":", expr nonempty α],
         from [expr hn],
         refine [expr le_trans _ (le_sup _ a)],
         rw ["[", "<-", expr @power_zero m, "]"] [],
         exact [expr power_le_power_left (pos_iff_ne_zero.1 (lt_of_lt_of_le omega_pos (le_max_right _ _))) (zero_le _)]
       end)))))

end WType

