import Mathbin.LinearAlgebra.Charpoly.Basic 
import Mathbin.LinearAlgebra.InvariantBasisNumber

/-!

# Strong rank condition for commutative rings

We prove that any nontrivial commutative ring satisfies `strong_rank_condition`, meaning that
if there is an injective linear map `(fin n → R) →ₗ[R] fin m → R`, then `n ≤ m`. This implies that
any commutative ring satisfies `invariant_basis_number`: the rank of a finitely generated free
module is well defined.

## Main result

* `comm_ring_strong_rank_condition R` : `R` has the `strong_rank_condition`.

## References

We follow the proof given in https://mathoverflow.net/a/47846/7845.
The argument is the following: it is enough to prove that for all `n`, there is no injective linear
map `(fin (n + 1) → R) →ₗ[R] fin n → R`. Given such an `f`, we get by extension an injective
linear map `g : (fin (n + 1) → R) →ₗ[R] fin (n + 1) → R`. Injectivity implies that `P`, the
minimal polynomial of `g`, has non-zero constant term `a₀ ≠ 0`. But evaluating `0 = P(g)` at the
vector `(0,...,0,1)` gives `a₀`, contradiction.

-/


variable(R : Type _)[CommRingₓ R][Nontrivial R]

open Polynomial Function Finₓ LinearMap

-- error in LinearAlgebra.FreeModule.StrongRankCondition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any commutative ring satisfies the `strong_rank_condition`. -/
@[priority 100]
instance comm_ring_strong_rank_condition : strong_rank_condition R :=
begin
  suffices [] [":", expr ∀ n, ∀ f : «expr →ₗ[ ] »(fin «expr + »(n, 1) → R, R, fin n → R), «expr¬ »(injective f)],
  { rwa [expr strong_rank_condition_iff_succ R] [] },
  intros [ident n, ident f],
  by_contradiction [ident hf],
  letI [] [] [":=", expr module.finite.of_basis (pi.basis_fun R (fin «expr + »(n, 1)))],
  let [ident g] [":", expr «expr →ₗ[ ] »(fin «expr + »(n, 1) → R, R, fin «expr + »(n, 1) → R)] [":=", expr (extend_by_zero.linear_map R cast_succ).comp f],
  have [ident hg] [":", expr injective g] [":=", expr (extend_injective (rel_embedding.injective cast_succ) 0).comp hf],
  have [ident hnex] [":", expr «expr¬ »(«expr∃ , »((i : fin n), «expr = »(cast_succ i, last n)))] [":=", expr λ
   ⟨i, hi⟩, ne_of_lt (cast_succ_lt_last i) hi],
  let [ident a₀] [] [":=", expr (minpoly R g).coeff 0],
  have [] [":", expr «expr ≠ »(a₀, 0)] [":=", expr minpoly_coeff_zero_of_injective hg],
  have [] [":", expr «expr = »(a₀, 0)] [],
  { have [ident heval] [] [":=", expr linear_map.congr_fun (minpoly.aeval R g) (pi.single (fin.last n) 1)],
    obtain ["⟨", ident P, ",", ident hP, "⟩", ":=", expr X_dvd_iff.2 (erase_same (minpoly R g) 0)],
    rw ["[", "<-", expr monomial_add_erase (minpoly R g) 0, ",", expr hP, "]"] ["at", ident heval],
    replace [ident heval] [] [":=", expr congr_fun heval (fin.last n)],
    simpa [] [] [] ["[", expr hnex, "]"] [] ["using", expr heval] },
  contradiction
end

