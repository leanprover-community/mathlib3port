import Mathbin.Algebra.Order.Archimedean 
import Mathbin.Order.Filter.AtTopBot

/-!
# `at_top` filter and archimedean (semi)rings/fields

In this file we prove that for a linear ordered archimedean semiring `R` and a function `f : α → ℕ`,
the function `coe ∘ f : α → R` tends to `at_top` along a filter `l` if and only if so does `f`.
We also prove that `coe : ℕ → R` tends to `at_top` along `at_top`, as well as version of these
two results for `ℤ` (and a ring `R`) and `ℚ` (and a field `R`).
-/


variable{α R : Type _}

open Filter Set

theorem tendsto_coe_nat_at_top_iff [OrderedSemiring R] [Nontrivial R] [Archimedean R] {f : α → ℕ} {l : Filter α} :
  tendsto (fun n => (f n : R)) l at_top ↔ tendsto f l at_top :=
  tendsto_at_top_embedding (fun a₁ a₂ => Nat.cast_le) exists_nat_ge

theorem tendsto_coe_nat_at_top_at_top [OrderedSemiring R] [Archimedean R] : tendsto (coeₓ : ℕ → R) at_top at_top :=
  Nat.mono_cast.tendsto_at_top_at_top exists_nat_ge

theorem tendsto_coe_int_at_top_iff [OrderedRing R] [Nontrivial R] [Archimedean R] {f : α → ℤ} {l : Filter α} :
  tendsto (fun n => (f n : R)) l at_top ↔ tendsto f l at_top :=
  (tendsto_at_top_embedding fun a₁ a₂ => Int.cast_le)$
    fun r =>
      let ⟨n, hn⟩ := exists_nat_ge r
      ⟨(n : ℤ), hn⟩

theorem tendsto_coe_int_at_top_at_top [OrderedRing R] [Archimedean R] : tendsto (coeₓ : ℤ → R) at_top at_top :=
  Int.cast_mono.tendsto_at_top_at_top$
    fun b =>
      let ⟨n, hn⟩ := exists_nat_ge b
      ⟨n, hn⟩

theorem tendsto_coe_rat_at_top_iff [LinearOrderedField R] [Archimedean R] {f : α → ℚ} {l : Filter α} :
  tendsto (fun n => (f n : R)) l at_top ↔ tendsto f l at_top :=
  (tendsto_at_top_embedding fun a₁ a₂ => Rat.cast_le)$
    fun r =>
      let ⟨n, hn⟩ := exists_nat_ge r
      ⟨(n : ℚ),
        by 
          assumptionModCast⟩

-- error in Order.Filter.Archimedean: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem at_top_countable_basis_of_archimedean
[linear_ordered_semiring R]
[archimedean R] : (at_top : filter R).has_countable_basis (λ n : exprℕ(), true) (λ n, Ici n) :=
{ countable := countable_encodable _,
  to_has_basis := at_top_basis.to_has_basis (λ x hx, let ⟨n, hn⟩ := exists_nat_ge x in
   ⟨n, trivial, Ici_subset_Ici.2 hn⟩) (λ n hn, ⟨n, trivial, subset.rfl⟩) }

-- error in Order.Filter.Archimedean: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem at_bot_countable_basis_of_archimedean
[linear_ordered_ring R]
[archimedean R] : (at_bot : filter R).has_countable_basis (λ m : exprℤ(), true) (λ m, Iic m) :=
{ countable := countable_encodable _,
  to_has_basis := at_bot_basis.to_has_basis (λ x hx, let ⟨m, hm⟩ := exists_int_lt x in
   ⟨m, trivial, Iic_subset_Iic.2 hm.le⟩) (λ m hm, ⟨m, trivial, subset.rfl⟩) }

instance (priority := 100)at_top_countably_generated_of_archimedean [LinearOrderedSemiring R] [Archimedean R] :
  (at_top : Filter R).IsCountablyGenerated :=
  at_top_countable_basis_of_archimedean.IsCountablyGenerated

instance (priority := 100)at_bot_countably_generated_of_archimedean [LinearOrderedRing R] [Archimedean R] :
  (at_bot : Filter R).IsCountablyGenerated :=
  at_bot_countable_basis_of_archimedean.IsCountablyGenerated

variable[LinearOrderedSemiring R][Archimedean R]

variable{l : Filter α}{f : α → R}{r : R}

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.const_mul_at_top`). -/
theorem Filter.Tendsto.const_mul_at_top' (hr : 0 < r) (hf : tendsto f l at_top) : tendsto (fun x => r*f x) l at_top :=
  by 
    apply tendsto_at_top.2 fun b => _ 
    obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := Archimedean.arch 1 hr 
    rw [nsmul_eq_mul'] at hn 
    filterUpwards [tendsto_at_top.1 hf (n*max b 0)]
    intro x hx 
    calc b ≤ 1*max b 0 :=
      by 
        rw [one_mulₓ]
        exact le_max_leftₓ _ _ _ ≤ (r*n)*max b 0 :=
      mul_le_mul_of_nonneg_right hn (le_max_rightₓ _ _)_ = r*n*max b 0 :=
      by 
        rw [mul_assocₓ]_ ≤ r*f x :=
      mul_le_mul_of_nonneg_left hx (le_of_ltₓ hr)

-- error in Order.Filter.Archimedean: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.at_top_mul_const`). -/
theorem filter.tendsto.at_top_mul_const'
(hr : «expr < »(0, r))
(hf : tendsto f l at_top) : tendsto (λ x, «expr * »(f x, r)) l at_top :=
begin
  apply [expr tendsto_at_top.2 (λ b, _)],
  obtain ["⟨", ident n, ":", expr exprℕ(), ",", ident hn, ":", expr «expr ≤ »(1, «expr • »(n, r)), "⟩", ":=", expr archimedean.arch 1 hr],
  have [ident hn'] [":", expr «expr ≤ »(1, «expr * »((n : R), r))] [],
  by rwa [expr nsmul_eq_mul] ["at", ident hn],
  filter_upwards ["[", expr tendsto_at_top.1 hf «expr * »(max b 0, n), "]"] [],
  assume [binders (x hx)],
  calc
    «expr ≤ »(b, «expr * »(max b 0, 1)) : by { rw ["[", expr mul_one, "]"] [],
      exact [expr le_max_left _ _] }
    «expr ≤ »(..., «expr * »(max b 0, «expr * »(n, r))) : mul_le_mul_of_nonneg_left hn' (le_max_right _ _)
    «expr = »(..., «expr * »(«expr * »(max b 0, n), r)) : by rw ["[", expr mul_assoc, "]"] []
    «expr ≤ »(..., «expr * »(f x, r)) : mul_le_mul_of_nonneg_right hx (le_of_lt hr)
end

