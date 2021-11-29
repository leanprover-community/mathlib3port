import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.Data.Fintype.Fin

/-!
# Big operators and `fin`

Some results about products and sums over the type `fin`.
-/


open_locale BigOperators

open Finset

namespace Finₓ

-- error in Algebra.BigOperators.Fin: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem sum_filter_zero_lt
{M : Type*}
[add_comm_monoid M]
{n : exprℕ()}
{v : fin n.succ → M} : «expr = »(«expr∑ in , »((i), univ.filter (λ
   i : fin n.succ, «expr < »(0, i)), v i), «expr∑ , »((j : fin n), v j.succ)) :=
by rw ["[", expr univ_filter_zero_lt, ",", expr sum_map, ",", expr rel_embedding.coe_fn_to_embedding, ",", expr coe_succ_embedding, "]"] []

-- error in Algebra.BigOperators.Fin: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[to_additive #[]]
theorem prod_filter_zero_lt
{M : Type*}
[comm_monoid M]
{n : exprℕ()}
{v : fin n.succ → M} : «expr = »(«expr∏ in , »((i), univ.filter (λ
   i : fin n.succ, «expr < »(0, i)), v i), «expr∏ , »((j : fin n), v j.succ)) :=
by rw ["[", expr univ_filter_zero_lt, ",", expr finset.prod_map, ",", expr rel_embedding.coe_fn_to_embedding, ",", expr coe_succ_embedding, "]"] []

theorem sum_filter_succ_lt {M : Type _} [AddCommMonoidₓ M] {n : ℕ} (j : Finₓ n) (v : Finₓ n.succ → M) :
  (∑i in univ.filter fun i => j.succ < i, v i) = ∑j in univ.filter fun i => j < i, v j.succ :=
  by 
    rw [univ_filter_succ_lt, Finset.sum_map, RelEmbedding.coe_fn_to_embedding, coe_succ_embedding]

@[toAdditive]
theorem prod_filter_succ_lt {M : Type _} [CommMonoidₓ M] {n : ℕ} (j : Finₓ n) (v : Finₓ n.succ → M) :
  (∏i in univ.filter fun i => j.succ < i, v i) = ∏j in univ.filter fun i => j < i, v j.succ :=
  by 
    rw [univ_filter_succ_lt, Finset.prod_map, RelEmbedding.coe_fn_to_embedding, coe_succ_embedding]

end Finₓ

