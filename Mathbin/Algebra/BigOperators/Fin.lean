import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Fintype.Fin

/-!
# Big operators and `fin`

Some results about products and sums over the type `fin`.
-/


open_locale BigOperators

open Finset

namespace Finₓ

@[to_additive]
theorem prod_filter_zero_lt {M : Type _} [CommMonoidₓ M] {n : ℕ} {v : Finₓ n.succ → M} :
    (∏ i in univ.filter fun i : Finₓ n.succ => 0 < i, v i) = ∏ j : Finₓ n, v j.succ := by
  rw [univ_filter_zero_lt, Finset.prod_map, RelEmbedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
theorem prod_filter_succ_lt {M : Type _} [CommMonoidₓ M] {n : ℕ} (j : Finₓ n) (v : Finₓ n.succ → M) :
    (∏ i in univ.filter fun i => j.succ < i, v i) = ∏ j in univ.filter fun i => j < i, v j.succ := by
  rw [univ_filter_succ_lt, Finset.prod_map, RelEmbedding.coe_fn_to_embedding, coe_succ_embedding]

end Finₓ

