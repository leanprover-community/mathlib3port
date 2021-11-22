import Mathbin.RingTheory.Polynomial.Cyclotomic 
import Mathbin.Topology.Algebra.Polynomial 
import Mathbin.FieldTheory.Finite.Basic

/-!
# Primes congruent to one

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/


namespace Nat

open Polynomial Nat Filter

-- error in NumberTheory.PrimesCongruentOne: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
theorem exists_prime_ge_modeq_one
(k n : exprℕ())
(hpos : «expr < »(0, k)) : «expr∃ , »((p : exprℕ()), «expr ∧ »(nat.prime p, «expr ∧ »(«expr ≤ »(n, p), «expr ≡ [MOD ]»(p, 1, k)))) :=
begin
  have [ident hli] [":", expr tendsto «expr ∘ »(abs, λ a : exprℕ(), «expr| |»((a : exprℚ()))) at_top at_top] [],
  { simp [] [] ["only"] ["[", expr («expr ∘ »), ",", expr abs_cast, "]"] [] [],
    exact [expr nat.strict_mono_cast.monotone.tendsto_at_top_at_top exists_nat_ge] },
  have [ident hcff] [":", expr «expr ≠ »(int.cast_ring_hom exprℚ() (cyclotomic k exprℤ()).leading_coeff, 0)] [],
  { simp [] [] ["only"] ["[", expr cyclotomic.monic, ",", expr ring_hom.eq_int_cast, ",", expr monic.leading_coeff, ",", expr int.cast_one, ",", expr ne.def, ",", expr not_false_iff, ",", expr one_ne_zero, "]"] [] [] },
  obtain ["⟨", ident a, ",", ident ha, "⟩", ":=", expr tendsto_at_top_at_top.1 (tendsto_abv_eval₂_at_top (int.cast_ring_hom exprℚ()) abs (cyclotomic k exprℤ()) (degree_cyclotomic_pos k exprℤ() hpos) hcff hli) 2],
  let [ident b] [] [":=", expr «expr * »(a, «expr * »(k, n.factorial))],
  have [ident hgt] [":", expr «expr < »(1, (eval «expr↑ »(«expr * »(a, «expr * »(k, n.factorial))) (cyclotomic k exprℤ())).nat_abs)] [],
  { suffices [ident hgtabs] [":", expr «expr < »(1, «expr| |»(eval «expr↑ »(b) (cyclotomic k exprℤ())))],
    { rw ["[", expr int.abs_eq_nat_abs, "]"] ["at", ident hgtabs],
      exact_mod_cast [expr hgtabs] },
    suffices [ident hgtrat] [":", expr «expr < »(1, «expr| |»(eval «expr↑ »(b) (cyclotomic k exprℚ())))],
    { rw ["[", "<-", expr map_cyclotomic_int k exprℚ(), ",", "<-", expr int.cast_coe_nat, ",", "<-", expr int.coe_cast_ring_hom, ",", expr eval_map, ",", expr eval₂_hom, ",", expr int.coe_cast_ring_hom, "]"] ["at", ident hgtrat],
      assumption_mod_cast },
    suffices [ident hleab] [":", expr «expr ≤ »(a, b)],
    { replace [ident ha] [] [":=", expr lt_of_lt_of_le one_lt_two (ha b hleab)],
      rwa ["[", "<-", expr eval_map, ",", expr map_cyclotomic_int k exprℚ(), ",", expr abs_cast, "]"] ["at", ident ha] },
    exact [expr le_mul_of_pos_right (mul_pos hpos (factorial_pos n))] },
  let [ident p] [] [":=", expr min_fac (eval «expr↑ »(b) (cyclotomic k exprℤ())).nat_abs],
  haveI [ident hprime] [":", expr fact p.prime] [":=", expr ⟨min_fac_prime (ne_of_lt hgt).symm⟩],
  have [ident hroot] [":", expr is_root (cyclotomic k (zmod p)) (cast_ring_hom (zmod p) b)] [],
  { rw ["[", expr is_root.def, ",", "<-", expr map_cyclotomic_int k (zmod p), ",", expr eval_map, ",", expr coe_cast_ring_hom, ",", "<-", expr int.cast_coe_nat, ",", "<-", expr int.coe_cast_ring_hom, ",", expr eval₂_hom, ",", expr int.coe_cast_ring_hom, ",", expr zmod.int_coe_zmod_eq_zero_iff_dvd _ _, "]"] [],
    apply [expr int.dvd_nat_abs.1],
    exact_mod_cast [expr min_fac_dvd (eval «expr↑ »(b) (cyclotomic k exprℤ())).nat_abs] },
  refine [expr ⟨p, hprime.1, _, _⟩],
  { by_contra [ident habs],
    exact [expr (prime.dvd_iff_not_coprime hprime.1).1 (dvd_factorial (min_fac_pos _) (le_of_not_ge habs)) (coprime_of_root_cyclotomic hpos hroot).symm.coprime_mul_left_right.coprime_mul_left_right] },
  { have [ident hdiv] [] [":=", expr order_of_dvd_of_pow_eq_one (zmod.units_pow_card_sub_one_eq_one p (zmod.unit_of_coprime b (coprime_of_root_cyclotomic hpos hroot)))],
    have [] [":", expr «expr¬ »(«expr ∣ »(p, k))] [":=", expr hprime.1.coprime_iff_not_dvd.1 (coprime_of_root_cyclotomic hpos hroot).symm.coprime_mul_left_right.coprime_mul_right_right],
    rw ["[", expr order_of_root_cyclotomic_eq hpos this hroot, "]"] ["at", ident hdiv],
    exact [expr ((modeq_iff_dvd' hprime.1.pos).2 hdiv).symm] }
end

theorem frequently_at_top_modeq_one (k : ℕ) (hpos : 0 < k) : ∃ᶠp in at_top, Nat.Prime p ∧ p ≡ 1 [MOD k] :=
  by 
    refine' frequently_at_top.2 fun n => _ 
    obtain ⟨p, hp⟩ := exists_prime_ge_modeq_one k n hpos 
    exact ⟨p, ⟨hp.2.1, hp.1, hp.2.2⟩⟩

theorem infinite_set_of_prime_modeq_one (k : ℕ) (hpos : 0 < k) : Set.Infinite { p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k] } :=
  frequently_at_top_iff_infinite.1 (frequently_at_top_modeq_one k hpos)

end Nat

