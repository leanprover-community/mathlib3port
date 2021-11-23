import Mathbin.Algebra.Order.WithZero 
import Mathbin.Data.Polynomial.Monic

/-!
# Lemmas for the interaction between polynomials and `∑` and `∏`.

Recall that `∑` and `∏` are notation for `finset.sum` and `finset.prod` respectively.

## Main results

- `polynomial.nat_degree_prod_of_monic` : the degree of a product of monic polynomials is the
  product of degrees. We prove this only for `[comm_semiring R]`,
  but it ought to be true for `[semiring R]` and `list.prod`.
- `polynomial.nat_degree_prod` : for polynomials over an integral domain,
  the degree of the product is the sum of degrees.
- `polynomial.leading_coeff_prod` : for polynomials over an integral domain,
  the leading coefficient is the product of leading coefficients.
- `polynomial.prod_X_sub_C_coeff_card_pred` carries most of the content for computing
  the second coefficient of the characteristic polynomial.
-/


open Finset

open Multiset

open_locale BigOperators

universe u w

variable{R : Type u}{ι : Type w}

namespace Polynomial

variable(s : Finset ι)

section Semiringₓ

variable{α : Type _}[Semiringₓ α]

theorem nat_degree_list_sum_le (l : List (Polynomial α)) : nat_degree l.sum ≤ (l.map nat_degree).foldr max 0 :=
  List.sum_le_foldr_max nat_degree
    (by 
      simp )
    nat_degree_add_le _

theorem nat_degree_multiset_sum_le (l : Multiset (Polynomial α)) :
  nat_degree l.sum ≤ (l.map nat_degree).foldr max max_left_commₓ 0 :=
  Quotientₓ.induction_on l
    (by 
      simpa using nat_degree_list_sum_le)

theorem nat_degree_sum_le (f : ι → Polynomial α) : nat_degree (∑i in s, f i) ≤ s.fold max 0 (nat_degree ∘ f) :=
  by 
    simpa using nat_degree_multiset_sum_le (s.val.map f)

theorem degree_list_sum_le (l : List (Polynomial α)) : degree l.sum ≤ (l.map nat_degree).maximum :=
  by 
    byCases' h : l.sum = 0
    ·
      simp [h]
    ·
      rw [degree_eq_nat_degree h]
      suffices  : (l.map nat_degree).maximum = ((l.map nat_degree).foldr max 0 : ℕ)
      ·
        rw [this]
        simpa [this] using nat_degree_list_sum_le l 
      rw [List.maximum_eq_coe_foldr_max_of_ne_nil]
      ·
        congr 
      contrapose! h 
      rw [List.map_eq_nil] at h 
      simp [h]

theorem nat_degree_list_prod_le (l : List (Polynomial α)) : nat_degree l.prod ≤ (l.map nat_degree).Sum :=
  by 
    induction' l with hd tl IH
    ·
      simp 
    ·
      simpa using nat_degree_mul_le.trans (add_le_add_left IH _)

-- error in Algebra.Polynomial.BigOperators: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coeff_list_prod_of_nat_degree_le
(l : list (polynomial α))
(n : exprℕ())
(hl : ∀
 p «expr ∈ » l, «expr ≤ »(nat_degree p, n)) : «expr = »(coeff (list.prod l) «expr * »(l.length, n), (l.map (λ
   p, coeff p n)).prod) :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident IH] [],
  { simp [] [] [] [] [] [] },
  { have [ident hl'] [":", expr ∀
     p «expr ∈ » tl, «expr ≤ »(nat_degree p, n)] [":=", expr λ p hp, hl p (list.mem_cons_of_mem _ hp)],
    simp [] [] ["only"] ["[", expr list.prod_cons, ",", expr list.map, ",", expr list.length, "]"] [] [],
    rw ["[", expr add_mul, ",", expr one_mul, ",", expr add_comm, ",", "<-", expr IH hl', ",", expr mul_comm tl.length, "]"] [],
    have [ident h] [":", expr «expr ≤ »(nat_degree tl.prod, «expr * »(n, tl.length))] [],
    { refine [expr (nat_degree_list_prod_le _).trans _],
      rw ["[", "<-", expr tl.length_map nat_degree, ",", expr mul_comm, "]"] [],
      refine [expr list.sum_le_of_forall_le _ _ _],
      simpa [] [] [] [] [] ["using", expr hl'] },
    have [ident hdn] [":", expr «expr ≤ »(nat_degree hd, n)] [":=", expr hl _ (list.mem_cons_self _ _)],
    rcases [expr hdn.eq_or_lt, "with", ident rfl, "|", ident hdn'],
    { cases [expr h.eq_or_lt] ["with", ident h', ident h'],
      { rw ["[", "<-", expr h', ",", expr coeff_mul_degree_add_degree, ",", expr leading_coeff, ",", expr leading_coeff, "]"] [] },
      { rw ["[", expr coeff_eq_zero_of_nat_degree_lt, ",", expr coeff_eq_zero_of_nat_degree_lt h', ",", expr mul_zero, "]"] [],
        exact [expr nat_degree_mul_le.trans_lt (add_lt_add_left h' _)] } },
    { rw ["[", expr coeff_eq_zero_of_nat_degree_lt hdn', ",", expr coeff_eq_zero_of_nat_degree_lt, ",", expr zero_mul, "]"] [],
      exact [expr nat_degree_mul_le.trans_lt (add_lt_add_of_lt_of_le hdn' h)] } }
end

end Semiringₓ

section CommSemiringₓ

variable[CommSemiringₓ R](f : ι → Polynomial R)(t : Multiset (Polynomial R))

theorem nat_degree_multiset_prod_le : t.prod.nat_degree ≤ (t.map nat_degree).Sum :=
  Quotientₓ.induction_on t
    (by 
      simpa using nat_degree_list_prod_le)

theorem nat_degree_prod_le : (∏i in s, f i).natDegree ≤ ∑i in s, (f i).natDegree :=
  by 
    simpa using nat_degree_multiset_prod_le (s.1.map f)

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `polynomial.leading_coeff_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem leading_coeff_multiset_prod' (h : (t.map leading_coeff).Prod ≠ 0) :
  t.prod.leading_coeff = (t.map leading_coeff).Prod :=
  by 
    induction' t using Multiset.induction_on with a t ih
    ·
      simp 
    simp only [map_cons, Multiset.prod_cons] at h⊢
    rw [Polynomial.leading_coeff_mul'] <;>
      ·
        rwa [ih]
        apply right_ne_zero_of_mul h

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `polynomial.leading_coeff_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem leading_coeff_prod' (h : (∏i in s, (f i).leadingCoeff) ≠ 0) :
  (∏i in s, f i).leadingCoeff = ∏i in s, (f i).leadingCoeff :=
  by 
    simpa using
      leading_coeff_multiset_prod' (s.1.map f)
        (by 
          simpa using h)

/--
The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `polynomial.nat_degree_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem nat_degree_multiset_prod' (h : (t.map fun f => leading_coeff f).Prod ≠ 0) :
  t.prod.nat_degree = (t.map fun f => nat_degree f).Sum :=
  by 
    revert h 
    refine' Multiset.induction_on t _ fun a t ih ht => _
    ·
      simp 
    rw [map_cons, Multiset.prod_cons] at ht⊢
    rw [Multiset.sum_cons, Polynomial.nat_degree_mul', ih]
    ·
      apply right_ne_zero_of_mul ht
    ·
      rwa [Polynomial.leading_coeff_multiset_prod']
      apply right_ne_zero_of_mul ht

/--
The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `polynomial.nat_degree_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem nat_degree_prod' (h : (∏i in s, (f i).leadingCoeff) ≠ 0) :
  (∏i in s, f i).natDegree = ∑i in s, (f i).natDegree :=
  by 
    simpa using
      nat_degree_multiset_prod' (s.1.map f)
        (by 
          simpa using h)

theorem nat_degree_multiset_prod_of_monic [Nontrivial R] (h : ∀ f _ : f ∈ t, monic f) :
  t.prod.nat_degree = (t.map nat_degree).Sum :=
  by 
    apply nat_degree_multiset_prod' 
    suffices  : (t.map fun f => leading_coeff f).Prod = 1
    ·
      rw [this]
      simp 
    convert prod_repeat (1 : R) t.card
    ·
      simp only [eq_repeat, Multiset.card_map, eq_self_iff_true, true_andₓ]
      rintro i hi 
      obtain ⟨i, hi, rfl⟩ := multiset.mem_map.mp hi 
      apply h 
      assumption
    ·
      simp 

theorem nat_degree_prod_of_monic [Nontrivial R] (h : ∀ i _ : i ∈ s, (f i).Monic) :
  (∏i in s, f i).natDegree = ∑i in s, (f i).natDegree :=
  by 
    simpa using
      nat_degree_multiset_prod_of_monic (s.1.map f)
        (by 
          simpa using h)

theorem coeff_multiset_prod_of_nat_degree_le (n : ℕ) (hl : ∀ p _ : p ∈ t, nat_degree p ≤ n) :
  coeff t.prod (t.card*n) = (t.map fun p => coeff p n).Prod :=
  by 
    induction t using Quotientₓ.induction_on 
    simpa using coeff_list_prod_of_nat_degree_le _ _ hl

theorem coeff_prod_of_nat_degree_le (f : ι → Polynomial R) (n : ℕ) (h : ∀ p _ : p ∈ s, nat_degree (f p) ≤ n) :
  coeff (∏i in s, f i) (s.card*n) = ∏i in s, coeff (f i) n :=
  by 
    cases' s with l hl 
    convert coeff_multiset_prod_of_nat_degree_le (l.map f) _ _
    ·
      simp 
    ·
      simp 
    ·
      simpa using h

theorem coeff_zero_multiset_prod : t.prod.coeff 0 = (t.map fun f => coeff f 0).Prod :=
  by 
    refine' Multiset.induction_on t _ fun a t ht => _
    ·
      simp 
    rw [Multiset.prod_cons, map_cons, Multiset.prod_cons, Polynomial.mul_coeff_zero, ht]

theorem coeff_zero_prod : (∏i in s, f i).coeff 0 = ∏i in s, (f i).coeff 0 :=
  by 
    simpa using coeff_zero_multiset_prod (s.1.map f)

end CommSemiringₓ

section CommRingₓ

variable[CommRingₓ R]

open Monic

theorem multiset_prod_X_sub_C_next_coeff [Nontrivial R] (t : Multiset R) :
  next_coeff (t.map fun x => X - C x).Prod = -t.sum :=
  by 
    rw [next_coeff_multiset_prod]
    ·
      simp only [next_coeff_X_sub_C]
      refine' t.sum_hom ⟨Neg.neg, _, _⟩ <;> simp [add_commₓ]
    ·
      intros 
      apply monic_X_sub_C

theorem prod_X_sub_C_next_coeff [Nontrivial R] {s : Finset ι} (f : ι → R) :
  next_coeff (∏i in s, X - C (f i)) = -∑i in s, f i :=
  by 
    simpa using multiset_prod_X_sub_C_next_coeff (s.1.map f)

theorem multiset_prod_X_sub_C_coeff_card_pred [Nontrivial R] (t : Multiset R) (ht : 0 < t.card) :
  (t.map fun x => X - C x).Prod.coeff (t.card - 1) = -t.sum :=
  by 
    convert
      multiset_prod_X_sub_C_next_coeff
        (by 
          assumption)
    rw [next_coeff]
    splitIfs
    ·
      rw [nat_degree_multiset_prod_of_monic] at h <;> simp only [Multiset.mem_map] at *
      swap
      ·
        rintro _ ⟨_, _, rfl⟩
        apply monic_X_sub_C 
      simpRw [Multiset.sum_eq_zero_iff, Multiset.mem_map]  at h 
      contrapose! h 
      obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp ht 
      exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, nat_degree_X_sub_C _⟩, one_ne_zero⟩
    congr 
    rw [nat_degree_multiset_prod_of_monic] <;>
      ·
        simp [nat_degree_X_sub_C, monic_X_sub_C]

theorem prod_X_sub_C_coeff_card_pred [Nontrivial R] (s : Finset ι) (f : ι → R) (hs : 0 < s.card) :
  (∏i in s, X - C (f i)).coeff (s.card - 1) = -∑i in s, f i :=
  by 
    simpa using
      multiset_prod_X_sub_C_coeff_card_pred (s.1.map f)
        (by 
          simpa using hs)

end CommRingₓ

section NoZeroDivisors

variable[CommRingₓ R][NoZeroDivisors R](f : ι → Polynomial R)(t : Multiset (Polynomial R))

/--
The degree of a product of polynomials is equal to
the sum of the degrees.

See `polynomial.nat_degree_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem nat_degree_prod [Nontrivial R] (h : ∀ i _ : i ∈ s, f i ≠ 0) :
  (∏i in s, f i).natDegree = ∑i in s, (f i).natDegree :=
  by 
    apply nat_degree_prod' 
    rw [prod_ne_zero_iff]
    intro x hx 
    simp [h x hx]

theorem nat_degree_multiset_prod [Nontrivial R] (s : Multiset (Polynomial R)) (h : (0 : Polynomial R) ∉ s) :
  nat_degree s.prod = (s.map nat_degree).Sum :=
  by 
    rw [nat_degree_multiset_prod']
    simpRw [Ne.def, Multiset.prod_eq_zero_iff, Multiset.mem_map, leading_coeff_eq_zero]
    rintro ⟨_, h, rfl⟩
    contradiction

/--
The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
theorem degree_multiset_prod [Nontrivial R] : t.prod.degree = (t.map fun f => degree f).Sum :=
  by 
    refine' Multiset.induction_on t _ fun a t ht => _
    ·
      simp 
    ·
      rw [Multiset.prod_cons, degree_mul, ht, map_cons, Multiset.sum_cons]

/--
The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
theorem degree_prod [Nontrivial R] : (∏i in s, f i).degree = ∑i in s, (f i).degree :=
  by 
    simpa using degree_multiset_prod (s.1.map f)

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `polynomial.leading_coeff_multiset_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leading_coeff_multiset_prod : t.prod.leading_coeff = (t.map fun f => leading_coeff f).Prod :=
  by 
    rw [←leading_coeff_hom_apply, MonoidHom.map_multiset_prod]
    rfl

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `polynomial.leading_coeff_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leading_coeff_prod : (∏i in s, f i).leadingCoeff = ∏i in s, (f i).leadingCoeff :=
  by 
    simpa using leading_coeff_multiset_prod (s.1.map f)

end NoZeroDivisors

end Polynomial

