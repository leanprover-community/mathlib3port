import Mathbin.RingTheory.Polynomial.Chebyshev 
import Mathbin.RingTheory.Localization 
import Mathbin.Data.Zmod.Basic 
import Mathbin.Algebra.CharP.Invertible

/-!
# Dickson polynomials

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `polynomial.dickson`: the generalised Dickson polynomials.

## Main statements

* `polynomial.dickson_one_one_mul`, the `(m * n)`-th Dickson polynomial of the first kind for
  parameter `1 : R` is the composition of the `m`-th and `n`-th Dickson polynomials of the first
  kind for `1 : R`.
* `polynomial.dickson_one_one_char_p`, for a prime number `p`, the `p`-th Dickson polynomial of the
  first kind associated to parameter `1 : R` is congruent to `X ^ p` modulo `p`.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `linear_recurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/


noncomputable theory

namespace Polynomial

variable{R S : Type _}[CommRingₓ R][CommRingₓ S](k : ℕ)(a : R)

/-- `dickson` is the `n`the (generalised) Dickson polynomial of the `k`-th kind associated to the
element `a ∈ R`. -/
noncomputable def dickson : ℕ → Polynomial R
| 0 => 3 - k
| 1 => X
| n+2 => (X*dickson (n+1)) - C a*dickson n

@[simp]
theorem dickson_zero : dickson k a 0 = 3 - k :=
  rfl

@[simp]
theorem dickson_one : dickson k a 1 = X :=
  rfl

theorem dickson_two : dickson k a 2 = (X^2) - C a*3 - k :=
  by 
    simp only [dickson, sq]

@[simp]
theorem dickson_add_two (n : ℕ) : dickson k a (n+2) = (X*dickson k a (n+1)) - C a*dickson k a n :=
  by 
    rw [dickson]

theorem dickson_of_two_le {n : ℕ} (h : 2 ≤ n) : dickson k a n = (X*dickson k a (n - 1)) - C a*dickson k a (n - 2) :=
  by 
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h 
    rw [add_commₓ]
    exact dickson_add_two k a n

variable{R S k a}

theorem map_dickson (f : R →+* S) : ∀ n : ℕ, map f (dickson k a n) = dickson k (f a) n
| 0 =>
  by 
    simp only [dickson_zero, map_sub, map_nat_cast, bit1, bit0, map_add, map_one]
| 1 =>
  by 
    simp only [dickson_one, map_X]
| n+2 =>
  by 
    simp only [dickson_add_two, map_sub, map_mul, map_X, map_C]
    rw [map_dickson, map_dickson]

variable{R}

@[simp]
theorem dickson_two_zero : ∀ n : ℕ, dickson 2 (0 : R) n = (X^n)
| 0 =>
  by 
    simp only [dickson_zero, pow_zeroₓ]
    normNum
| 1 =>
  by 
    simp only [dickson_one, pow_oneₓ]
| n+2 =>
  by 
    simp only [dickson_add_two, C_0, zero_mul, sub_zero]
    rw [dickson_two_zero, pow_addₓ X (n+1) 1, mul_commₓ, pow_oneₓ]

section Dickson

/-!

### A Lambda structure on `polynomial ℤ`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `polynomial ℤ` with a Lambda structure
in terms of the `dickson 1 1` polynomials defined below.
There is exactly one other Lambda structure on `polynomial ℤ` in terms of binomial polynomials.

-/


variable{R}

theorem dickson_one_one_eval_add_inv (x y : R) (h : (x*y) = 1) : ∀ n, (dickson 1 (1 : R) n).eval (x+y) = (x^n)+y^n
| 0 =>
  by 
    simp only [bit0, eval_one, eval_add, pow_zeroₓ, dickson_zero]
    normNum
| 1 =>
  by 
    simp only [eval_X, dickson_one, pow_oneₓ]
| n+2 =>
  by 
    simp only [eval_sub, eval_mul, dickson_one_one_eval_add_inv, eval_X, dickson_add_two, C_1, eval_one]
    convLHS => simp only [pow_succₓ, add_mulₓ, mul_addₓ, h, ←mul_assocₓ, mul_commₓ y x, one_mulₓ]
    ringExp

variable(R)

theorem dickson_one_one_eq_chebyshev_T [Invertible (2 : R)] :
  ∀ n, dickson 1 (1 : R) n = 2*(chebyshev.T R n).comp (C (⅟ 2)*X)
| 0 =>
  by 
    simp only [chebyshev.T_zero, mul_oneₓ, one_comp, dickson_zero]
    normNum
| 1 =>
  by 
    rw [dickson_one, chebyshev.T_one, X_comp, ←mul_assocₓ, ←C_1, ←C_bit0, ←C_mul, mul_inv_of_self, C_1, one_mulₓ]
| n+2 =>
  by 
    simp only [dickson_add_two, chebyshev.T_add_two, dickson_one_one_eq_chebyshev_T (n+1),
      dickson_one_one_eq_chebyshev_T n, sub_comp, mul_comp, add_comp, X_comp, bit0_comp, one_comp]
    simp only [←C_1, ←C_bit0, ←mul_assocₓ, ←C_mul, mul_inv_of_self]
    rw [C_1, one_mulₓ]
    ring

theorem chebyshev_T_eq_dickson_one_one [Invertible (2 : R)] (n : ℕ) :
  chebyshev.T R n = C (⅟ 2)*(dickson 1 1 n).comp (2*X) :=
  by 
    rw [dickson_one_one_eq_chebyshev_T]
    simp only [comp_assoc, mul_comp, C_comp, X_comp, ←mul_assocₓ, ←C_1, ←C_bit0, ←C_mul]
    rw [inv_of_mul_self, C_1, one_mulₓ, one_mulₓ, comp_X]

-- error in RingTheory.Polynomial.Dickson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `(m * n)`-th Dickson polynomial of the first kind is the composition of the `m`-th and
`n`-th. -/
theorem dickson_one_one_mul
(m n : exprℕ()) : «expr = »(dickson 1 (1 : R) «expr * »(m, n), (dickson 1 1 m).comp (dickson 1 1 n)) :=
begin
  have [ident h] [":", expr «expr = »((1 : R), int.cast_ring_hom R 1)] [],
  simp [] [] ["only"] ["[", expr ring_hom.eq_int_cast, ",", expr int.cast_one, "]"] [] [],
  rw [expr h] [],
  simp [] [] ["only"] ["[", "<-", expr map_dickson (int.cast_ring_hom R), ",", "<-", expr map_comp, "]"] [] [],
  congr' [1] [],
  apply [expr map_injective (int.cast_ring_hom exprℚ()) int.cast_injective],
  simp [] [] ["only"] ["[", expr map_dickson, ",", expr map_comp, ",", expr ring_hom.eq_int_cast, ",", expr int.cast_one, ",", expr dickson_one_one_eq_chebyshev_T, ",", expr chebyshev.T_mul, ",", expr two_mul, ",", "<-", expr add_comp, "]"] [] [],
  simp [] [] ["only"] ["[", "<-", expr two_mul, ",", "<-", expr comp_assoc, "]"] [] [],
  apply [expr eval₂_congr rfl rfl],
  rw ["[", expr comp_assoc, "]"] [],
  apply [expr eval₂_congr rfl _ rfl],
  rw ["[", expr mul_comp, ",", expr C_comp, ",", expr X_comp, ",", "<-", expr mul_assoc, ",", "<-", expr C_1, ",", "<-", expr C_bit0, ",", "<-", expr C_mul, ",", expr inv_of_mul_self, ",", expr C_1, ",", expr one_mul, "]"] []
end

theorem dickson_one_one_comp_comm (m n : ℕ) :
  (dickson 1 (1 : R) m).comp (dickson 1 1 n) = (dickson 1 1 n).comp (dickson 1 1 m) :=
  by 
    rw [←dickson_one_one_mul, mul_commₓ, dickson_one_one_mul]

-- error in RingTheory.Polynomial.Dickson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dickson_one_one_zmod_p (p : exprℕ()) [fact p.prime] : «expr = »(dickson 1 (1 : zmod p) p, «expr ^ »(X, p)) :=
begin
  obtain ["⟨", ident K, ",", "_", ",", "_", ",", ident H, "⟩", ":", expr «expr∃ , »((K : Type)
    (_ : field K), by exactI [expr «expr∃ , »((_ : char_p K p), infinite K)])],
  { let [ident K] [] [":=", expr fraction_ring (polynomial (zmod p))],
    let [ident f] [":", expr «expr →+* »(zmod p, K)] [":=", expr (algebra_map _ (fraction_ring _)).comp C],
    haveI [] [":", expr char_p K p] [],
    { rw ["<-", expr f.char_p_iff_char_p] [],
      apply_instance },
    haveI [] [":", expr infinite K] [":=", expr infinite.of_injective (algebra_map (polynomial (zmod p)) (fraction_ring (polynomial (zmod p)))) (is_fraction_ring.injective _ _)],
    refine [expr ⟨K, _, _, _⟩]; apply_instance },
  resetI,
  apply [expr map_injective (zmod.cast_hom (dvd_refl p) K) (ring_hom.injective _)],
  rw ["[", expr map_dickson, ",", expr map_pow, ",", expr map_X, "]"] [],
  apply [expr eq_of_infinite_eval_eq],
  apply [expr @set.infinite.mono _ {x : K | «expr∃ , »((y), «expr ∧ »(«expr = »(x, «expr + »(y, «expr ⁻¹»(y))), «expr ≠ »(y, 0)))}],
  { rintro ["_", "⟨", ident x, ",", ident rfl, ",", ident hx, "⟩"],
    simp [] [] ["only"] ["[", expr eval_X, ",", expr eval_pow, ",", expr set.mem_set_of_eq, ",", expr @add_pow_char K _ p, ",", expr dickson_one_one_eval_add_inv _ _ (mul_inv_cancel hx), ",", expr inv_pow₀, ",", expr zmod.cast_hom_apply, ",", expr zmod.cast_one', "]"] [] [] },
  { intro [ident h],
    rw ["<-", expr set.infinite_univ_iff] ["at", ident H],
    apply [expr H],
    suffices [] [":", expr «expr = »((set.univ : set K), «expr >>= »({x : K | «expr∃ , »((y : K), «expr ∧ »(«expr = »(x, «expr + »(y, «expr ⁻¹»(y))), «expr ≠ »(y, 0)))}, λ
       x, {y | «expr ∨ »(«expr = »(x, «expr + »(y, «expr ⁻¹»(y))), «expr = »(y, 0))}))],
    { rw [expr this] [],
      clear [ident this],
      refine [expr h.bUnion (λ x hx, _)],
      let [ident φ] [":", expr polynomial K] [":=", expr «expr + »(«expr - »(«expr ^ »(X, 2), «expr * »(C x, X)), 1)],
      have [ident hφ] [":", expr «expr ≠ »(φ, 0)] [],
      { intro [ident H],
        have [] [":", expr «expr = »(φ.eval 0, 0)] [],
        by rw ["[", expr H, ",", expr eval_zero, "]"] [],
        simpa [] [] [] ["[", expr eval_X, ",", expr eval_one, ",", expr eval_pow, ",", expr eval_sub, ",", expr sub_zero, ",", expr eval_add, ",", expr eval_mul, ",", expr mul_zero, ",", expr sq, ",", expr zero_add, ",", expr one_ne_zero, "]"] [] [] },
      classical,
      convert [] [expr «expr ∪ »(φ.roots, {0}).to_finset.finite_to_set] ["using", 1],
      ext1 [] [ident y],
      simp [] [] ["only"] ["[", expr multiset.mem_to_finset, ",", expr set.mem_set_of_eq, ",", expr finset.mem_coe, ",", expr multiset.mem_union, ",", expr mem_roots hφ, ",", expr is_root, ",", expr eval_add, ",", expr eval_sub, ",", expr eval_pow, ",", expr eval_mul, ",", expr eval_X, ",", expr eval_C, ",", expr eval_one, ",", expr multiset.mem_singleton, "]"] [] [],
      by_cases [expr hy, ":", expr «expr = »(y, 0)],
      { simp [] [] ["only"] ["[", expr hy, ",", expr eq_self_iff_true, ",", expr or_true, "]"] [] [] },
      apply [expr or_congr _ iff.rfl],
      rw ["[", "<-", expr mul_left_inj' hy, ",", expr eq_comm, ",", "<-", expr sub_eq_zero, ",", expr add_mul, ",", expr inv_mul_cancel hy, "]"] [],
      apply [expr eq_iff_eq_cancel_right.mpr],
      ring [] },
    { apply [expr (set.eq_univ_of_forall _).symm],
      intro [ident x],
      simp [] [] ["only"] ["[", expr exists_prop, ",", expr set.mem_Union, ",", expr set.bind_def, ",", expr ne.def, ",", expr set.mem_set_of_eq, "]"] [] [],
      by_cases [expr hx, ":", expr «expr = »(x, 0)],
      { simp [] [] ["only"] ["[", expr hx, ",", expr and_true, ",", expr eq_self_iff_true, ",", expr inv_zero, ",", expr or_true, "]"] [] [],
        exact [expr ⟨_, 1, rfl, one_ne_zero⟩] },
      { simp [] [] ["only"] ["[", expr hx, ",", expr or_false, ",", expr exists_eq_right, "]"] [] [],
        exact [expr ⟨_, rfl, hx⟩] } } }
end

-- error in RingTheory.Polynomial.Dickson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dickson_one_one_char_p
(p : exprℕ())
[fact p.prime]
[char_p R p] : «expr = »(dickson 1 (1 : R) p, «expr ^ »(X, p)) :=
begin
  have [ident h] [":", expr «expr = »((1 : R), zmod.cast_hom (dvd_refl p) R 1)] [],
  simp [] [] ["only"] ["[", expr zmod.cast_hom_apply, ",", expr zmod.cast_one', "]"] [] [],
  rw ["[", expr h, ",", "<-", expr map_dickson (zmod.cast_hom (dvd_refl p) R), ",", expr dickson_one_one_zmod_p, ",", expr map_pow, ",", expr map_X, "]"] []
end

end Dickson

end Polynomial

