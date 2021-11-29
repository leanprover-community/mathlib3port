import Mathbin.FieldTheory.Finite.Basic

/-!
# The Chevalley–Warning theorem

This file contains a proof of the Chevalley–Warning theorem.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Main results

1. Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
   such that the total degree of `f` is less than `(q-1)` times the cardinality of `σ`.
   Then the evaluation of `f` on all points of `σ → K` (aka `K^σ`) sums to `0`.
   (`sum_mv_polynomial_eq_zero`)
2. The Chevalley–Warning theorem (`char_dvd_card_solutions`).
   Let `f i` be a finite family of multivariate polynomials
   in finitely many variables (`X s`, `s : σ`) such that
   the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
   Then the number of common solutions of the `f i`
   is divisible by the characteristic of `K`.

## Notation

- `K` is a finite field
- `q` is notation for the cardinality of `K`
- `σ` is the indexing type for the variables of a multivariate polynomial ring over `K`

-/


universe u v

open_locale BigOperators

section FiniteField

open MvPolynomial

open Function hiding eval

open Finset FiniteField

variable {K : Type _} {σ : Type _} [Fintype K] [Field K] [Fintype σ]

local notation "q" => Fintype.card K

-- error in FieldTheory.ChevalleyWarning: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mv_polynomial.sum_mv_polynomial_eq_zero
[decidable_eq σ]
(f : mv_polynomial σ K)
(h : «expr < »(f.total_degree, «expr * »(«expr - »(exprq(), 1), fintype.card σ))) : «expr = »(«expr∑ , »((x), eval x f), 0) :=
begin
  haveI [] [":", expr decidable_eq K] [":=", expr classical.dec_eq K],
  calc
    «expr = »(«expr∑ , »((x), eval x f), «expr∑ , »((x : σ → K), «expr∑ in , »((d), f.support, «expr * »(f.coeff d, «expr∏ , »((i), «expr ^ »(x i, d i)))))) : by simp [] [] ["only"] ["[", expr eval_eq', "]"] [] []
    «expr = »(..., «expr∑ in , »((d), f.support, «expr∑ , »((x : σ → K), «expr * »(f.coeff d, «expr∏ , »((i), «expr ^ »(x i, d i)))))) : sum_comm
    «expr = »(..., 0) : sum_eq_zero _,
  intros [ident d, ident hd],
  obtain ["⟨", ident i, ",", ident hi, "⟩", ":", expr «expr∃ , »((i), «expr < »(d i, «expr - »(exprq(), 1)))],
  from [expr f.exists_degree_lt «expr - »(exprq(), 1) h hd],
  calc
    «expr = »(«expr∑ , »((x : σ → K), «expr * »(f.coeff d, «expr∏ , »((i), «expr ^ »(x i, d i)))), «expr * »(f.coeff d, «expr∑ , »((x : σ → K), «expr∏ , »((i), «expr ^ »(x i, d i))))) : mul_sum.symm
    «expr = »(..., 0) : «expr ∘ »(mul_eq_zero.mpr, or.inr) _,
  calc
    «expr = »(«expr∑ , »((x : σ → K), «expr∏ , »((i), «expr ^ »(x i, d i))), «expr∑ , »((x₀ : {j // «expr ≠ »(j, i)} → K)
      (x : {x : σ → K // «expr = »(«expr ∘ »(x, coe), x₀)}), «expr∏ , »((j), «expr ^ »((x : σ → K) j, d j)))) : (fintype.sum_fiberwise _ _).symm
    «expr = »(..., 0) : fintype.sum_eq_zero _ _,
  intros [ident x₀],
  let [ident e] [":", expr «expr ≃ »(K, {x // «expr = »(«expr ∘ »(x, coe), x₀)})] [":=", expr (equiv.subtype_equiv_codomain _).symm],
  calc
    «expr = »(«expr∑ , »((x : {x : σ → K // «expr = »(«expr ∘ »(x, coe), x₀)}), «expr∏ , »((j), «expr ^ »((x : σ → K) j, d j))), «expr∑ , »((a : K), «expr∏ , »((j : σ), «expr ^ »((e a : σ → K) j, d j)))) : (e.sum_comp _).symm
    «expr = »(..., «expr∑ , »((a : K), «expr * »(«expr∏ , »((j), «expr ^ »(x₀ j, d j)), «expr ^ »(a, d i)))) : fintype.sum_congr _ _ _
    «expr = »(..., «expr * »(«expr∏ , »((j), «expr ^ »(x₀ j, d j)), «expr∑ , »((a : K), «expr ^ »(a, d i)))) : by rw [expr mul_sum] []
    «expr = »(..., 0) : by rw ["[", expr sum_pow_lt_card_sub_one _ hi, ",", expr mul_zero, "]"] [],
  intros [ident a],
  let [ident e'] [":", expr «expr ≃ »(«expr ⊕ »({j // «expr = »(j, i)}, {j // «expr ≠ »(j, i)}), σ)] [":=", expr equiv.sum_compl _],
  letI [] [":", expr unique {j // «expr = »(j, i)}] [":=", expr { default := ⟨i, rfl⟩,
     uniq := λ ⟨j, h⟩, subtype.val_injective h }],
  calc
    «expr = »(«expr∏ , »((j : σ), «expr ^ »((e a : σ → K) j, d j)), «expr * »(«expr ^ »((e a : σ → K) i, d i), «expr∏ , »((j : {j // «expr ≠ »(j, i)}), «expr ^ »((e a : σ → K) j, d j)))) : by { rw ["[", "<-", expr e'.prod_comp, ",", expr fintype.prod_sum_type, ",", expr univ_unique, ",", expr prod_singleton, "]"] [],
      refl }
    «expr = »(..., «expr * »(«expr ^ »(a, d i), «expr∏ , »((j : {j // «expr ≠ »(j, i)}), «expr ^ »((e a : σ → K) j, d j)))) : by rw [expr equiv.subtype_equiv_codomain_symm_apply_eq] []
    «expr = »(..., «expr * »(«expr ^ »(a, d i), «expr∏ , »((j), «expr ^ »(x₀ j, d j)))) : congr_arg _ (fintype.prod_congr _ _ _)
    «expr = »(..., «expr * »(«expr∏ , »((j), «expr ^ »(x₀ j, d j)), «expr ^ »(a, d i))) : mul_comm _ _,
  { rintros ["⟨", ident j, ",", ident hj, "⟩"],
    show [expr «expr = »(«expr ^ »((e a : σ → K) j, d j), «expr ^ »(x₀ ⟨j, hj⟩, d j))],
    rw [expr equiv.subtype_equiv_codomain_symm_apply_ne] [] }
end

variable [DecidableEq K] [DecidableEq σ]

-- error in FieldTheory.ChevalleyWarning: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Chevalley–Warning theorem.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`. -/
theorem char_dvd_card_solutions_family
(p : exprℕ())
[char_p K p]
{ι : Type*}
{s : finset ι}
{f : ι → mv_polynomial σ K}
(h : «expr < »(«expr∑ in , »((i), s, (f i).total_degree), fintype.card σ)) : «expr ∣ »(p, fintype.card {x : σ → K // ∀
 i «expr ∈ » s, «expr = »(eval x (f i), 0)}) :=
begin
  have [ident hq] [":", expr «expr < »(0, «expr - »(exprq(), 1))] [],
  { rw ["[", "<-", expr fintype.card_units, ",", expr fintype.card_pos_iff, "]"] [],
    exact [expr ⟨1⟩] },
  let [ident S] [":", expr finset (σ → K)] [":=", expr {x ∈ univ | ∀ i «expr ∈ » s, «expr = »(eval x (f i), 0)}],
  have [ident hS] [":", expr ∀
   x : σ → K, «expr ↔ »(«expr ∈ »(x, S), ∀ i : ι, «expr ∈ »(i, s) → «expr = »(eval x (f i), 0))] [],
  { intros [ident x],
    simp [] [] ["only"] ["[", expr S, ",", expr true_and, ",", expr sep_def, ",", expr mem_filter, ",", expr mem_univ, "]"] [] [] },
  let [ident F] [":", expr mv_polynomial σ K] [":=", expr «expr∏ in , »((i), s, «expr - »(1, «expr ^ »(f i, «expr - »(exprq(), 1))))],
  have [ident hF] [":", expr ∀ x, «expr = »(eval x F, if «expr ∈ »(x, S) then 1 else 0)] [],
  { intro [ident x],
    calc
      «expr = »(eval x F, «expr∏ in , »((i), s, eval x «expr - »(1, «expr ^ »(f i, «expr - »(exprq(), 1))))) : eval_prod s _ x
      «expr = »(..., if «expr ∈ »(x, S) then 1 else 0) : _,
    simp [] [] ["only"] ["[", expr (eval x).map_sub, ",", expr (eval x).map_pow, ",", expr (eval x).map_one, "]"] [] [],
    split_ifs [] ["with", ident hx, ident hx],
    { apply [expr finset.prod_eq_one],
      intros [ident i, ident hi],
      rw [expr hS] ["at", ident hx],
      rw ["[", expr hx i hi, ",", expr zero_pow hq, ",", expr sub_zero, "]"] [] },
    { obtain ["⟨", ident i, ",", ident hi, ",", ident hx, "⟩", ":", expr «expr∃ , »((i : ι), «expr ∧ »(«expr ∈ »(i, s), «expr ≠ »(eval x (f i), 0)))],
      { simpa [] [] ["only"] ["[", expr hS, ",", expr not_forall, ",", expr not_imp, "]"] [] ["using", expr hx] },
      apply [expr finset.prod_eq_zero hi],
      rw ["[", expr pow_card_sub_one_eq_one (eval x (f i)) hx, ",", expr sub_self, "]"] [] } },
  have [ident key] [":", expr «expr = »(«expr∑ , »((x), eval x F), fintype.card {x : σ → K // ∀
    i «expr ∈ » s, «expr = »(eval x (f i), 0)})] [],
  rw ["[", expr fintype.card_of_subtype S hS, ",", expr card_eq_sum_ones, ",", expr nat.cast_sum, ",", expr nat.cast_one, ",", "<-", expr fintype.sum_extend_by_zero S, ",", expr sum_congr rfl (λ
    x hx, hF x), "]"] [],
  show [expr «expr ∣ »(p, fintype.card {x // ∀ i : ι, «expr ∈ »(i, s) → «expr = »(eval x (f i), 0)})],
  rw ["[", "<-", expr char_p.cast_eq_zero_iff K, ",", "<-", expr key, "]"] [],
  show [expr «expr = »(«expr∑ , »((x), eval x F), 0)],
  apply [expr F.sum_mv_polynomial_eq_zero],
  show [expr «expr < »(F.total_degree, «expr * »(«expr - »(exprq(), 1), fintype.card σ))],
  calc
    «expr ≤ »(F.total_degree, «expr∑ in , »((i), s, «expr - »(1, «expr ^ »(f i, «expr - »(exprq(), 1))).total_degree)) : total_degree_finset_prod s _
    «expr ≤ »(..., «expr∑ in , »((i), s, «expr * »(«expr - »(exprq(), 1), (f i).total_degree))) : «expr $ »(sum_le_sum, λ
     i hi, _)
    «expr = »(..., «expr * »(«expr - »(exprq(), 1), «expr∑ in , »((i), s, (f i).total_degree))) : mul_sum.symm
    «expr < »(..., «expr * »(«expr - »(exprq(), 1), fintype.card σ)) : by rwa [expr mul_lt_mul_left hq] [],
  show [expr «expr ≤ »(«expr - »(1, «expr ^ »(f i, «expr - »(exprq(), 1))).total_degree, «expr * »(«expr - »(exprq(), 1), (f i).total_degree))],
  calc
    «expr ≤ »(«expr - »(1, «expr ^ »(f i, «expr - »(exprq(), 1))).total_degree, max (1 : mv_polynomial σ K).total_degree «expr ^ »(f i, «expr - »(exprq(), 1)).total_degree) : total_degree_sub _ _
    «expr ≤ »(..., «expr ^ »(f i, «expr - »(exprq(), 1)).total_degree) : by simp [] [] ["only"] ["[", expr max_eq_right, ",", expr nat.zero_le, ",", expr total_degree_one, "]"] [] []
    «expr ≤ »(..., «expr * »(«expr - »(exprq(), 1), (f i).total_degree)) : total_degree_pow _ _
end

-- error in FieldTheory.ChevalleyWarning: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Chevalley–Warning theorem.
Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
over a finite field of characteristic `p`.
Assume that the total degree of `f` is less than the cardinality of `σ`.
Then the number of solutions of `f` is divisible by `p`.
See `char_dvd_card_solutions_family` for a version that takes a family of polynomials `f i`. -/
theorem char_dvd_card_solutions
(p : exprℕ())
[char_p K p]
{f : mv_polynomial σ K}
(h : «expr < »(f.total_degree, fintype.card σ)) : «expr ∣ »(p, fintype.card {x : σ → K // «expr = »(eval x f, 0)}) :=
begin
  let [ident F] [":", expr unit → mv_polynomial σ K] [":=", expr λ _, f],
  have [] [":", expr «expr < »(«expr∑ , »((i : unit), (F i).total_degree), fintype.card σ)] [],
  { simpa [] [] ["only"] ["[", expr fintype.univ_punit, ",", expr sum_singleton, "]"] [] ["using", expr h] },
  have [ident key] [] [":=", expr char_dvd_card_solutions_family p this],
  simp [] [] ["only"] ["[", expr F, ",", expr fintype.univ_punit, ",", expr forall_eq, ",", expr mem_singleton, "]"] [] ["at", ident key],
  convert [] [expr key] []
end

end FiniteField

