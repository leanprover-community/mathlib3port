import Mathbin.Analysis.SpecialFunctions.Complex.Log 
import Mathbin.RingTheory.RootsOfUnity

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`.

## Main declarations

* `complex.mem_roots_of_unity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`.
* `complex.card_roots_of_unity`: the number of `n`-th roots of unity is exactly `n`.

-/


namespace Complex

open Polynomial Real

open_locale Nat Real

-- error in Analysis.Complex.RootsOfUnity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_primitive_root_exp_of_coprime
(i n : exprℕ())
(h0 : «expr ≠ »(n, 0))
(hi : i.coprime n) : is_primitive_root (exp «expr * »(«expr * »(«expr * »(2, exprπ()), I), «expr / »(i, n))) n :=
begin
  rw [expr is_primitive_root.iff_def] [],
  simp [] [] ["only"] ["[", "<-", expr exp_nat_mul, ",", expr exp_eq_one_iff, "]"] [] [],
  have [ident hn0] [":", expr «expr ≠ »((n : exprℂ()), 0)] [],
  by exact_mod_cast [expr h0],
  split,
  { use [expr i],
    field_simp [] ["[", expr hn0, ",", expr mul_comm (i : exprℂ()), ",", expr mul_comm (n : exprℂ()), "]"] [] [] },
  { simp [] [] ["only"] ["[", expr hn0, ",", expr mul_right_comm _ _ «expr↑ »(n), ",", expr mul_left_inj' two_pi_I_ne_zero, ",", expr ne.def, ",", expr not_false_iff, ",", expr mul_comm _ (i : exprℂ()), ",", "<-", expr mul_assoc _ (i : exprℂ()), ",", expr exists_imp_distrib, "]"] ["with", ident field_simps] [],
    norm_cast [],
    rintro [ident l, ident k, ident hk],
    have [] [":", expr «expr ∣ »(n, «expr * »(i, l))] [],
    { rw ["[", "<-", expr int.coe_nat_dvd, ",", expr hk, "]"] [],
      apply [expr dvd_mul_left] },
    exact [expr hi.symm.dvd_of_dvd_mul_left this] }
end

theorem is_primitive_root_exp (n : ℕ) (h0 : n ≠ 0) : IsPrimitiveRoot (exp (((2*π)*I) / n)) n :=
  by 
    simpa only [Nat.cast_one, one_div] using is_primitive_root_exp_of_coprime 1 n h0 n.coprime_one_left

-- error in Analysis.Complex.RootsOfUnity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_primitive_root_iff
(ζ : exprℂ())
(n : exprℕ())
(hn : «expr ≠ »(n, 0)) : «expr ↔ »(is_primitive_root ζ n, «expr∃ , »((i «expr < » (n : exprℕ()))
  (hi : i.coprime n), «expr = »(exp «expr * »(«expr * »(«expr * »(2, exprπ()), I), «expr / »(i, n)), ζ))) :=
begin
  have [ident hn0] [":", expr «expr ≠ »((n : exprℂ()), 0)] [":=", expr by exact_mod_cast [expr hn]],
  split,
  swap,
  { rintro ["⟨", ident i, ",", "-", ",", ident hi, ",", ident rfl, "⟩"],
    exact [expr is_primitive_root_exp_of_coprime i n hn hi] },
  intro [ident h],
  obtain ["⟨", ident i, ",", ident hi, ",", ident rfl, "⟩", ":=", expr (is_primitive_root_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one (nat.pos_of_ne_zero hn)],
  refine [expr ⟨i, hi, ((is_primitive_root_exp n hn).pow_iff_coprime (nat.pos_of_ne_zero hn) i).mp h, _⟩],
  rw ["[", "<-", expr exp_nat_mul, "]"] [],
  congr' [1] [],
  field_simp [] ["[", expr hn0, ",", expr mul_comm (i : exprℂ()), "]"] [] []
end

-- error in Analysis.Complex.RootsOfUnity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`. -/
theorem mem_roots_of_unity
(n : «exprℕ+»())
(x : units exprℂ()) : «expr ↔ »(«expr ∈ »(x, roots_of_unity n exprℂ()), «expr∃ , »((i «expr < » (n : exprℕ())), «expr = »(exp «expr * »(«expr * »(«expr * »(2, exprπ()), I), «expr / »(i, n)), x))) :=
begin
  rw ["[", expr mem_roots_of_unity, ",", expr units.ext_iff, ",", expr units.coe_pow, ",", expr units.coe_one, "]"] [],
  have [ident hn0] [":", expr «expr ≠ »((n : exprℂ()), 0)] [":=", expr by exact_mod_cast [expr n.ne_zero]],
  split,
  { intro [ident h],
    obtain ["⟨", ident i, ",", ident hi, ",", ident H, "⟩", ":", expr «expr∃ , »((i «expr < » (n : exprℕ())), «expr = »(«expr ^ »(exp «expr / »(«expr * »(«expr * »(2, exprπ()), I), n), i), x))],
    { simpa [] [] ["only"] [] [] ["using", expr (is_primitive_root_exp n n.ne_zero).eq_pow_of_pow_eq_one h n.pos] },
    refine [expr ⟨i, hi, _⟩],
    rw ["[", "<-", expr H, ",", "<-", expr exp_nat_mul, "]"] [],
    congr' [1] [],
    field_simp [] ["[", expr hn0, ",", expr mul_comm (i : exprℂ()), "]"] [] [] },
  { rintro ["⟨", ident i, ",", ident hi, ",", ident H, "⟩"],
    rw ["[", "<-", expr H, ",", "<-", expr exp_nat_mul, ",", expr exp_eq_one_iff, "]"] [],
    use [expr i],
    field_simp [] ["[", expr hn0, ",", expr mul_comm ((n : exprℕ()) : exprℂ()), ",", expr mul_comm (i : exprℂ()), "]"] [] [] }
end

theorem card_roots_of_unity (n : ℕ+) : Fintype.card (rootsOfUnity n ℂ) = n :=
  (is_primitive_root_exp n n.ne_zero).card_roots_of_unity

theorem card_primitive_roots (k : ℕ) (h : k ≠ 0) : (primitiveRoots k ℂ).card = φ k :=
  (is_primitive_root_exp k h).card_primitive_roots (Nat.pos_of_ne_zeroₓ h)

end Complex

