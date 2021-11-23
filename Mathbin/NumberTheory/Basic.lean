import Mathbin.Algebra.GeomSum 
import Mathbin.RingTheory.Ideal.Quotient

/-!
# Basic results in number theory

This file should contain basic results in number theory. So far, it only contains the essential
lemma in the construction of the ring of Witt vectors.

## Main statement

`dvd_sub_pow_of_dvd_sub` proves that for elements `a` and `b` in a commutative ring `R` and for
all natural numbers `p` and `k` if `p` divides `a-b` in `R`, then `p ^ (k + 1)` divides
`a ^ (p ^ k) - b ^ (p ^ k)`.
-/


section 

open Ideal Ideal.Quotient

-- error in NumberTheory.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dvd_sub_pow_of_dvd_sub
{R : Type*}
[comm_ring R]
{p : exprℕ()}
{a b : R}
(h : «expr ∣ »((p : R), «expr - »(a, b)))
(k : exprℕ()) : «expr ∣ »((«expr ^ »(p, «expr + »(k, 1)) : R), «expr - »(«expr ^ »(a, «expr ^ »(p, k)), «expr ^ »(b, «expr ^ »(p, k)))) :=
begin
  induction [expr k] [] ["with", ident k, ident ih] [],
  { rwa ["[", expr pow_one, ",", expr pow_zero, ",", expr pow_one, ",", expr pow_one, "]"] [] },
  rw ["[", expr pow_succ' p k, ",", expr pow_mul, ",", expr pow_mul, ",", "<-", expr geom_sum₂_mul, ",", expr pow_succ, "]"] [],
  refine [expr mul_dvd_mul _ ih],
  let [ident I] [":", expr ideal R] [":=", expr span {p}],
  let [ident f] [":", expr «expr →+* »(R, ideal.quotient I)] [":=", expr mk I],
  have [ident hp] [":", expr «expr = »((p : ideal.quotient I), 0)] [],
  { rw ["[", "<-", expr f.map_nat_cast, ",", expr eq_zero_iff_mem, ",", expr mem_span_singleton, "]"] [] },
  rw ["[", "<-", expr mem_span_singleton, ",", "<-", expr ideal.quotient.eq, "]"] ["at", ident h],
  rw ["[", "<-", expr mem_span_singleton, ",", "<-", expr eq_zero_iff_mem, ",", expr ring_hom.map_geom_sum₂, ",", expr ring_hom.map_pow, ",", expr ring_hom.map_pow, ",", expr h, ",", expr geom_sum₂_self, ",", expr hp, ",", expr zero_mul, "]"] []
end

end 

