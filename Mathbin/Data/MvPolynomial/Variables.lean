import Mathbin.Algebra.BigOperators.Order 
import Mathbin.Data.MvPolynomial.Monad 
import Mathbin.Data.Set.Pairwise

/-!
# Degrees and variables of polynomials

This file establishes many results about the degree and variable sets of a multivariate polynomial.

The *variable set* of a polynomial $P \in R[X]$ is a `finset` containing each $x \in X$
that appears in a monomial in $P$.

The *degree set* of a polynomial $P \in R[X]$ is a `multiset` containing, for each $x$ in the
variable set, $n$ copies of $x$, where $n$ is the maximum number of copies of $x$ appearing in a
monomial of $P$.

## Main declarations

* `mv_polynomial.degrees p` : the multiset of variables representing the union of the multisets
  corresponding to each non-zero monomial in `p`.
  For example if `7 ≠ 0` in `R` and `p = x²y+7y³` then `degrees p = {x, x, y, y, y}`

* `mv_polynomial.vars p` : the finset of variables occurring in `p`.
  For example if `p = x⁴y+yz` then `vars p = {x, y, z}`

* `mv_polynomial.degree_of n p : ℕ` : the total degree of `p` with respect to the variable `n`.
  For example if `p = x⁴y+yz` then `degree_of y p = 1`.

* `mv_polynomial.total_degree p : ℕ` :
  the max of the sizes of the multisets `s` whose monomials `X^s` occur in `p`.
  For example if `p = x⁴y+yz` then `total_degree p = 5`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `r : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/


noncomputable theory

open_locale Classical BigOperators

open Set Function Finsupp AddMonoidAlgebra

open_locale BigOperators

universe u v w

variable{R : Type u}{S : Type v}

namespace MvPolynomial

variable{σ τ : Type _}{r : R}{e : ℕ}{n m : σ}{s : σ →₀ ℕ}

section CommSemiringₓ

variable[CommSemiringₓ R]{p q : MvPolynomial σ R}

section Degrees

/-! ### `degrees` -/


-- error in Data.MvPolynomial.Variables: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset.

(For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
-/ def degrees (p : mv_polynomial σ R) : multiset σ :=
p.support.sup (λ s : «expr →₀ »(σ, exprℕ()), s.to_multiset)

-- error in Data.MvPolynomial.Variables: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degrees_monomial (s : «expr →₀ »(σ, exprℕ())) (a : R) : «expr ≤ »(degrees (monomial s a), s.to_multiset) :=
«expr $ »(finset.sup_le, assume t h, begin
   have [] [] [":=", expr finsupp.support_single_subset h],
   rw ["[", expr finset.mem_singleton, "]"] ["at", ident this],
   rw [expr this] []
 end)

theorem degrees_monomial_eq (s : σ →₀ ℕ) (a : R) (ha : a ≠ 0) : degrees (monomial s a) = s.to_multiset :=
  le_antisymmₓ (degrees_monomial s a)$
    Finset.le_sup$
      by 
        rw [support_monomial, if_neg ha, Finset.mem_singleton]

theorem degrees_C (a : R) : degrees (C a : MvPolynomial σ R) = 0 :=
  Multiset.le_zero.1$ degrees_monomial _ _

theorem degrees_X' (n : σ) : degrees (X n : MvPolynomial σ R) ≤ {n} :=
  le_transₓ (degrees_monomial _ _)$ le_of_eqₓ$ to_multiset_single _ _

@[simp]
theorem degrees_X [Nontrivial R] (n : σ) : degrees (X n : MvPolynomial σ R) = {n} :=
  (degrees_monomial_eq _ (1 : R) one_ne_zero).trans (to_multiset_single _ _)

@[simp]
theorem degrees_zero : degrees (0 : MvPolynomial σ R) = 0 :=
  by 
    rw [←C_0]
    exact degrees_C 0

@[simp]
theorem degrees_one : degrees (1 : MvPolynomial σ R) = 0 :=
  degrees_C 1

-- error in Data.MvPolynomial.Variables: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degrees_add (p q : mv_polynomial σ R) : «expr ≤ »(«expr + »(p, q).degrees, «expr ⊔ »(p.degrees, q.degrees)) :=
begin
  refine [expr finset.sup_le (assume b hb, _)],
  have [] [] [":=", expr finsupp.support_add hb],
  rw [expr finset.mem_union] ["at", ident this],
  cases [expr this] [],
  { exact [expr le_sup_of_le_left (finset.le_sup this)] },
  { exact [expr le_sup_of_le_right (finset.le_sup this)] }
end

theorem degrees_sum {ι : Type _} (s : Finset ι) (f : ι → MvPolynomial σ R) :
  (∑i in s, f i).degrees ≤ s.sup fun i => (f i).degrees :=
  by 
    refine' s.induction _ _
    ·
      simp only [Finset.sum_empty, Finset.sup_empty, degrees_zero]
      exact le_reflₓ _
    ·
      intro i s his ih 
      rw [Finset.sup_insert, Finset.sum_insert his]
      exact le_transₓ (degrees_add _ _) (sup_le_sup_left ih _)

-- error in Data.MvPolynomial.Variables: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degrees_mul (p q : mv_polynomial σ R) : «expr ≤ »(«expr * »(p, q).degrees, «expr + »(p.degrees, q.degrees)) :=
begin
  refine [expr finset.sup_le (assume b hb, _)],
  have [] [] [":=", expr support_mul p q hb],
  simp [] [] ["only"] ["[", expr finset.mem_bUnion, ",", expr finset.mem_singleton, "]"] [] ["at", ident this],
  rcases [expr this, "with", "⟨", ident a₁, ",", ident h₁, ",", ident a₂, ",", ident h₂, ",", ident rfl, "⟩"],
  rw ["[", expr finsupp.to_multiset_add, "]"] [],
  exact [expr add_le_add (finset.le_sup h₁) (finset.le_sup h₂)]
end

theorem degrees_prod {ι : Type _} (s : Finset ι) (f : ι → MvPolynomial σ R) :
  (∏i in s, f i).degrees ≤ ∑i in s, (f i).degrees :=
  by 
    refine' s.induction _ _
    ·
      simp only [Finset.prod_empty, Finset.sum_empty, degrees_one]
    ·
      intro i s his ih 
      rw [Finset.prod_insert his, Finset.sum_insert his]
      exact le_transₓ (degrees_mul _ _) (add_le_add_left ih _)

theorem degrees_pow (p : MvPolynomial σ R) : ∀ (n : ℕ), (p ^ n).degrees ≤ n • p.degrees
| 0 =>
  by 
    rw [pow_zeroₓ, degrees_one]
    exact Multiset.zero_le _
| n+1 =>
  by 
    rw [pow_succₓ, add_smul, add_commₓ, one_smul]
    exact le_transₓ (degrees_mul _ _) (add_le_add_left (degrees_pow n) _)

theorem mem_degrees {p : MvPolynomial σ R} {i : σ} : i ∈ p.degrees ↔ ∃ d, p.coeff d ≠ 0 ∧ i ∈ d.support :=
  by 
    simp only [degrees, Multiset.mem_sup, ←mem_support_iff, Finsupp.mem_to_multiset, exists_prop]

theorem le_degrees_add {p q : MvPolynomial σ R} (h : p.degrees.disjoint q.degrees) : p.degrees ≤ (p+q).degrees :=
  by 
    apply Finset.sup_le 
    intro d hd 
    rw [Multiset.disjoint_iff_ne] at h 
    rw [Multiset.le_iff_count]
    intro i 
    rw [degrees, Multiset.count_sup]
    simp only [Finsupp.count_to_multiset]
    byCases' h0 : d = 0
    ·
      simp only [h0, zero_le, Finsupp.zero_apply]
    ·
      refine' @Finset.le_sup _ _ _ _ (p+q).support _ d _ 
      rw [mem_support_iff, coeff_add]
      suffices  : q.coeff d = 0
      ·
        rwa [this, add_zeroₓ, coeff, ←Finsupp.mem_support_iff]
      rw [←Finsupp.support_eq_empty, ←Ne.def, ←Finset.nonempty_iff_ne_empty] at h0 
      obtain ⟨j, hj⟩ := h0 
      contrapose! h 
      rw [mem_support_iff] at hd 
      refine' ⟨j, _, j, _, rfl⟩
      all_goals 
        rw [mem_degrees]
        refine' ⟨d, _, hj⟩
        assumption

theorem degrees_add_of_disjoint {p q : MvPolynomial σ R} (h : Multiset.Disjoint p.degrees q.degrees) :
  (p+q).degrees = p.degrees ∪ q.degrees :=
  by 
    apply le_antisymmₓ
    ·
      apply degrees_add
    ·
      apply Multiset.union_le
      ·
        apply le_degrees_add h
      ·
        rw [add_commₓ]
        apply le_degrees_add h.symm

theorem degrees_map [CommSemiringₓ S] (p : MvPolynomial σ R) (f : R →+* S) : (map f p).degrees ⊆ p.degrees :=
  by 
    dsimp only [degrees]
    apply Multiset.subset_of_le 
    apply Finset.sup_mono 
    apply MvPolynomial.support_map_subset

theorem degrees_rename (f : σ → τ) (φ : MvPolynomial σ R) : (rename f φ).degrees ⊆ φ.degrees.map f :=
  by 
    intro i 
    rw [mem_degrees, Multiset.mem_map]
    rintro ⟨d, hd, hi⟩
    obtain ⟨x, rfl, hx⟩ := coeff_rename_ne_zero _ _ _ hd 
    simp only [map_domain, Finsupp.mem_support_iff] at hi 
    rw [sum_apply, Finsupp.sum] at hi 
    contrapose! hi 
    rw [Finset.sum_eq_zero]
    intro j hj 
    simp only [exists_prop, mem_degrees] at hi 
    specialize hi j ⟨x, hx, hj⟩
    rw [single_apply, if_neg hi]

theorem degrees_map_of_injective [CommSemiringₓ S] (p : MvPolynomial σ R) {f : R →+* S} (hf : injective f) :
  (map f p).degrees = p.degrees :=
  by 
    simp only [degrees, MvPolynomial.support_map_of_injective _ hf]

end Degrees

section Vars

/-! ### `vars` -/


/-- `vars p` is the set of variables appearing in the polynomial `p` -/
def vars (p : MvPolynomial σ R) : Finset σ :=
  p.degrees.to_finset

@[simp]
theorem vars_0 : (0 : MvPolynomial σ R).vars = ∅ :=
  by 
    rw [vars, degrees_zero, Multiset.to_finset_zero]

@[simp]
theorem vars_monomial (h : r ≠ 0) : (monomial s r).vars = s.support :=
  by 
    rw [vars, degrees_monomial_eq _ _ h, Finsupp.to_finset_to_multiset]

@[simp]
theorem vars_C : (C r : MvPolynomial σ R).vars = ∅ :=
  by 
    rw [vars, degrees_C, Multiset.to_finset_zero]

@[simp]
theorem vars_X [Nontrivial R] : (X n : MvPolynomial σ R).vars = {n} :=
  by 
    rw [X, vars_monomial (@one_ne_zero R _ _), Finsupp.support_single_ne_zero (one_ne_zero : 1 ≠ 0)]

theorem mem_vars (i : σ) : i ∈ p.vars ↔ ∃ (d : σ →₀ ℕ)(H : d ∈ p.support), i ∈ d.support :=
  by 
    simp only [vars, Multiset.mem_to_finset, mem_degrees, mem_support_iff, exists_prop]

theorem mem_support_not_mem_vars_zero {f : MvPolynomial σ R} {x : σ →₀ ℕ} (H : x ∈ f.support) {v : σ} (h : v ∉ vars f) :
  x v = 0 :=
  by 
    rw [vars, Multiset.mem_to_finset] at h 
    rw [←Finsupp.not_mem_support_iff]
    contrapose! h 
    unfold degrees 
    rw [show f.support = insert x f.support from Eq.symm$ Finset.insert_eq_of_mem H]
    rw [Finset.sup_insert]
    simp only [Multiset.mem_union, Multiset.sup_eq_union]
    left 
    rwa [←to_finset_to_multiset, Multiset.mem_to_finset] at h

theorem vars_add_subset (p q : MvPolynomial σ R) : (p+q).vars ⊆ p.vars ∪ q.vars :=
  by 
    intro x hx 
    simp only [vars, Finset.mem_union, Multiset.mem_to_finset] at hx⊢
    simpa using Multiset.mem_of_le (degrees_add _ _) hx

theorem vars_add_of_disjoint (h : Disjoint p.vars q.vars) : (p+q).vars = p.vars ∪ q.vars :=
  by 
    apply Finset.Subset.antisymm (vars_add_subset p q)
    intro x hx 
    simp only [vars, Multiset.disjoint_to_finset] at h hx⊢
    rw [degrees_add_of_disjoint h, Multiset.to_finset_union]
    exact hx

section Mul

-- error in Data.MvPolynomial.Variables: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem vars_mul (φ ψ : mv_polynomial σ R) : «expr ⊆ »(«expr * »(φ, ψ).vars, «expr ∪ »(φ.vars, ψ.vars)) :=
begin
  intro [ident i],
  simp [] [] ["only"] ["[", expr mem_vars, ",", expr finset.mem_union, "]"] [] [],
  rintro ["⟨", ident d, ",", ident hd, ",", ident hi, "⟩"],
  rw ["[", expr mem_support_iff, ",", expr coeff_mul, "]"] ["at", ident hd],
  contrapose ["!"] [ident hd],
  cases [expr hd] [],
  rw [expr finset.sum_eq_zero] [],
  rintro ["⟨", ident d₁, ",", ident d₂, "⟩", ident H],
  rw [expr finsupp.mem_antidiagonal] ["at", ident H],
  subst [expr H],
  obtain [ident H, "|", ident H, ":", expr «expr ∨ »(«expr ∈ »(i, d₁.support), «expr ∈ »(i, d₂.support))],
  { simpa [] [] ["only"] ["[", expr finset.mem_union, "]"] [] ["using", expr finsupp.support_add hi] },
  { suffices [] [":", expr «expr = »(coeff d₁ φ, 0)],
    by simp [] [] [] ["[", expr this, "]"] [] [],
    rw ["[", expr coeff, ",", "<-", expr finsupp.not_mem_support_iff, "]"] [],
    intro [],
    solve_by_elim [] [] [] [] },
  { suffices [] [":", expr «expr = »(coeff d₂ ψ, 0)],
    by simp [] [] [] ["[", expr this, "]"] [] [],
    rw ["[", expr coeff, ",", "<-", expr finsupp.not_mem_support_iff, "]"] [],
    intro [],
    solve_by_elim [] [] [] [] }
end

@[simp]
theorem vars_one : (1 : MvPolynomial σ R).vars = ∅ :=
  vars_C

theorem vars_pow (φ : MvPolynomial σ R) (n : ℕ) : (φ ^ n).vars ⊆ φ.vars :=
  by 
    induction' n with n ih
    ·
      simp 
    ·
      rw [pow_succₓ]
      apply Finset.Subset.trans (vars_mul _ _)
      exact Finset.union_subset (Finset.Subset.refl _) ih

/--
The variables of the product of a family of polynomials
are a subset of the union of the sets of variables of each polynomial.
-/
theorem vars_prod {ι : Type _} {s : Finset ι} (f : ι → MvPolynomial σ R) :
  (∏i in s, f i).vars ⊆ s.bUnion fun i => (f i).vars :=
  by 
    apply s.induction_on
    ·
      simp 
    ·
      intro a s hs hsub 
      simp only [hs, Finset.bUnion_insert, Finset.prod_insert, not_false_iff]
      apply Finset.Subset.trans (vars_mul _ _)
      exact Finset.union_subset_union (Finset.Subset.refl _) hsub

section IsDomain

variable{A : Type _}[CommRingₓ A][IsDomain A]

theorem vars_C_mul (a : A) (ha : a ≠ 0) (φ : MvPolynomial σ A) : (C a*φ).vars = φ.vars :=
  by 
    ext1 i 
    simp only [mem_vars, exists_prop, mem_support_iff]
    apply exists_congr 
    intro d 
    apply and_congr _ Iff.rfl 
    rw [coeff_C_mul, mul_ne_zero_iff, eq_true_intro ha, true_andₓ]

end IsDomain

end Mul

section Sum

variable{ι : Type _}(t : Finset ι)(φ : ι → MvPolynomial σ R)

theorem vars_sum_subset : (∑i in t, φ i).vars ⊆ Finset.bUnion t fun i => (φ i).vars :=
  by 
    apply t.induction_on
    ·
      simp 
    ·
      intro a s has hsum 
      rw [Finset.bUnion_insert, Finset.sum_insert has]
      refine' Finset.Subset.trans (vars_add_subset _ _) (Finset.union_subset_union (Finset.Subset.refl _) _)
      assumption

theorem vars_sum_of_disjoint (h : Pairwise$ (Disjoint on fun i => (φ i).vars)) :
  (∑i in t, φ i).vars = Finset.bUnion t fun i => (φ i).vars :=
  by 
    apply t.induction_on
    ·
      simp 
    ·
      intro a s has hsum 
      rw [Finset.bUnion_insert, Finset.sum_insert has, vars_add_of_disjoint, hsum]
      unfold Pairwise on_fun  at h 
      rw [hsum]
      simp only [Finset.disjoint_iff_ne] at h⊢
      intro v hv v2 hv2 
      rw [Finset.mem_bUnion] at hv2 
      rcases hv2 with ⟨i, his, hi⟩
      refine' h a i _ _ hv _ hi 
      rintro rfl 
      contradiction

end Sum

section Map

variable[CommSemiringₓ S](f : R →+* S)

variable(p)

theorem vars_map : (map f p).vars ⊆ p.vars :=
  by 
    simp [vars, degrees_map]

variable{f}

theorem vars_map_of_injective (hf : injective f) : (map f p).vars = p.vars :=
  by 
    simp [vars, degrees_map_of_injective _ hf]

theorem vars_monomial_single (i : σ) {e : ℕ} {r : R} (he : e ≠ 0) (hr : r ≠ 0) :
  (monomial (Finsupp.single i e) r).vars = {i} :=
  by 
    rw [vars_monomial hr, Finsupp.support_single_ne_zero he]

theorem vars_eq_support_bUnion_support : p.vars = p.support.bUnion Finsupp.support :=
  by 
    ext i 
    rw [mem_vars, Finset.mem_bUnion]

end Map

end Vars

section DegreeOf

/-! ### `degree_of` -/


/-- `degree_of n p` gives the highest power of X_n that appears in `p` -/
def degree_of (n : σ) (p : MvPolynomial σ R) : ℕ :=
  p.degrees.count n

end DegreeOf

section TotalDegree

/-! ### `total_degree` -/


/-- `total_degree p` gives the maximum |s| over the monomials X^s in `p` -/
def total_degree (p : MvPolynomial σ R) : ℕ :=
  p.support.sup fun s => s.sum$ fun n e => e

theorem total_degree_eq (p : MvPolynomial σ R) : p.total_degree = p.support.sup fun m => m.to_multiset.card :=
  by 
    rw [total_degree]
    congr 
    funext m 
    exact (Finsupp.card_to_multiset _).symm

theorem total_degree_le_degrees_card (p : MvPolynomial σ R) : p.total_degree ≤ p.degrees.card :=
  by 
    rw [total_degree_eq]
    exact Finset.sup_le fun s hs => Multiset.card_le_of_le$ Finset.le_sup hs

@[simp]
theorem total_degree_C (a : R) : (C a : MvPolynomial σ R).totalDegree = 0 :=
  Nat.eq_zero_of_le_zeroₓ$
    Finset.sup_le$
      fun n hn =>
        have  := Finsupp.support_single_subset hn 
        by 
          rw [Finset.mem_singleton] at this 
          subst this 
          exact le_reflₓ _

@[simp]
theorem total_degree_zero : (0 : MvPolynomial σ R).totalDegree = 0 :=
  by 
    rw [←C_0] <;> exact total_degree_C (0 : R)

@[simp]
theorem total_degree_one : (1 : MvPolynomial σ R).totalDegree = 0 :=
  total_degree_C (1 : R)

@[simp]
theorem total_degree_X {R} [CommSemiringₓ R] [Nontrivial R] (s : σ) : (X s : MvPolynomial σ R).totalDegree = 1 :=
  by 
    rw [total_degree, support_X]
    simp only [Finset.sup, sum_single_index, Finset.fold_singleton, sup_bot_eq]

theorem total_degree_add (a b : MvPolynomial σ R) : (a+b).totalDegree ≤ max a.total_degree b.total_degree :=
  Finset.sup_le$
    fun n hn =>
      have  := Finsupp.support_add hn 
      by 
        rw [Finset.mem_union] at this 
        cases this
        ·
          exact le_max_of_le_left (Finset.le_sup this)
        ·
          exact le_max_of_le_right (Finset.le_sup this)

theorem total_degree_mul (a b : MvPolynomial σ R) : (a*b).totalDegree ≤ a.total_degree+b.total_degree :=
  Finset.sup_le$
    fun n hn =>
      have  := AddMonoidAlgebra.support_mul a b hn 
      by 
        simp only [Finset.mem_bUnion, Finset.mem_singleton] at this 
        rcases this with ⟨a₁, h₁, a₂, h₂, rfl⟩
        rw [Finsupp.sum_add_index]
        ·
          exact add_le_add (Finset.le_sup h₁) (Finset.le_sup h₂)
        ·
          intro a 
          rfl
        ·
          intro a b₁ b₂ 
          rfl

theorem total_degree_pow (a : MvPolynomial σ R) (n : ℕ) : (a ^ n).totalDegree ≤ n*a.total_degree :=
  by 
    induction' n with n ih
    ·
      simp only [Nat.nat_zero_eq_zero, zero_mul, pow_zeroₓ, total_degree_one]
    rw [pow_succₓ]
    calc total_degree (a*a ^ n) ≤ a.total_degree+(a ^ n).totalDegree :=
      total_degree_mul _ _ _ ≤ a.total_degree+n*a.total_degree := add_le_add_left ih _ _ = (n+1)*a.total_degree :=
      by 
        rw [add_mulₓ, one_mulₓ, add_commₓ]

theorem total_degree_list_prod :
  ∀ (s : List (MvPolynomial σ R)), s.prod.total_degree ≤ (s.map MvPolynomial.totalDegree).Sum
| [] =>
  by 
    rw [@List.prod_nil (MvPolynomial σ R) _, total_degree_one] <;> rfl
| p :: ps =>
  by 
    rw [@List.prod_cons (MvPolynomial σ R) _, List.map, List.sum_cons]
    exact le_transₓ (total_degree_mul _ _) (add_le_add_left (total_degree_list_prod ps) _)

theorem total_degree_multiset_prod (s : Multiset (MvPolynomial σ R)) :
  s.prod.total_degree ≤ (s.map MvPolynomial.totalDegree).Sum :=
  by 
    refine' Quotientₓ.induction_on s fun l => _ 
    rw [Multiset.quot_mk_to_coe, Multiset.coe_prod, Multiset.coe_map, Multiset.coe_sum]
    exact total_degree_list_prod l

theorem total_degree_finset_prod {ι : Type _} (s : Finset ι) (f : ι → MvPolynomial σ R) :
  (s.prod f).totalDegree ≤ ∑i in s, (f i).totalDegree :=
  by 
    refine' le_transₓ (total_degree_multiset_prod _) _ 
    rw [Multiset.map_map]
    rfl

theorem exists_degree_lt [Fintype σ] (f : MvPolynomial σ R) (n : ℕ) (h : f.total_degree < n*Fintype.card σ) {d : σ →₀ ℕ}
  (hd : d ∈ f.support) : ∃ i, d i < n :=
  by 
    contrapose! h 
    calc (n*Fintype.card σ) = ∑s : σ, n :=
      by 
        rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_commₓ, Finset.card_univ]_ ≤ ∑s, d s :=
      Finset.sum_le_sum fun s _ => h s _ ≤ d.sum fun i e => e :=
      by 
        rw [Finsupp.sum_fintype]
        intros 
        rfl _ ≤ f.total_degree :=
      Finset.le_sup hd

theorem coeff_eq_zero_of_total_degree_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ}
  (h : f.total_degree < ∑i in d.support, d i) : coeff d f = 0 :=
  by 
    classical 
    rw [total_degree, Finset.sup_lt_iff] at h
    ·
      specialize h d 
      rw [mem_support_iff] at h 
      refine' not_not.mp (mt h _)
      exact lt_irreflₓ _
    ·
      exact lt_of_le_of_ltₓ (Nat.zero_leₓ _) h

-- error in Data.MvPolynomial.Variables: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem total_degree_rename_le
(f : σ → τ)
(p : mv_polynomial σ R) : «expr ≤ »((rename f p).total_degree, p.total_degree) :=
«expr $ »(finset.sup_le, assume b, begin
   assume [binders (h)],
   rw [expr rename_eq] ["at", ident h],
   have [ident h'] [] [":=", expr finsupp.map_domain_support h],
   rw [expr finset.mem_image] ["at", ident h'],
   rcases [expr h', "with", "⟨", ident s, ",", ident hs, ",", ident rfl, "⟩"],
   rw [expr finsupp.sum_map_domain_index] [],
   exact [expr le_trans (le_refl _) (finset.le_sup hs)],
   exact [expr assume _, rfl],
   exact [expr assume _ _ _, rfl]
 end)

end TotalDegree

section EvalVars

/-! ### `vars` and `eval` -/


variable[CommSemiringₓ S]

theorem eval₂_hom_eq_constant_coeff_of_vars (f : R →+* S) {g : σ → S} {p : MvPolynomial σ R}
  (hp : ∀ i (_ : i ∈ p.vars), g i = 0) : eval₂_hom f g p = f (constant_coeff p) :=
  by 
    convLHS => rw [p.as_sum]
    simp only [RingHom.map_sum, eval₂_hom_monomial]
    byCases' h0 : constant_coeff p = 0
    workOnGoal 0
      rw [h0, f.map_zero, Finset.sum_eq_zero]
      intro d hd 
    workOnGoal 1
      rw [Finset.sum_eq_single (0 : σ →₀ ℕ)]
      ·
        rw [Finsupp.prod_zero_index, mul_oneₓ]
        rfl 
      intro d hd hd0 
    repeat' 
      obtain ⟨i, hi⟩ : d.support.nonempty
      ·
        rw [constant_coeff_eq, coeff, ←Finsupp.not_mem_support_iff] at h0 
        rw [Finset.nonempty_iff_ne_empty, Ne.def, Finsupp.support_eq_empty]
        rintro rfl 
        contradiction 
      rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
      rw [hp, zero_pow (Nat.pos_of_ne_zeroₓ$ finsupp.mem_support_iff.mp hi)]
      rw [mem_vars]
      exact ⟨d, hd, hi⟩
    ·
      rw [constant_coeff_eq, coeff, ←Ne.def, ←Finsupp.mem_support_iff] at h0 
      intro 
      contradiction

theorem aeval_eq_constant_coeff_of_vars [Algebra R S] {g : σ → S} {p : MvPolynomial σ R}
  (hp : ∀ i (_ : i ∈ p.vars), g i = 0) : aeval g p = algebraMap _ _ (constant_coeff p) :=
  eval₂_hom_eq_constant_coeff_of_vars _ hp

-- error in Data.MvPolynomial.Variables: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eval₂_hom_congr'
{f₁ f₂ : «expr →+* »(R, S)}
{g₁ g₂ : σ → S}
{p₁
 p₂ : mv_polynomial σ R} : «expr = »(f₁, f₂) → ∀
i, «expr ∈ »(i, p₁.vars) → «expr ∈ »(i, p₂.vars) → «expr = »(g₁ i, g₂ i) → «expr = »(p₁, p₂) → «expr = »(eval₂_hom f₁ g₁ p₁, eval₂_hom f₂ g₂ p₂) :=
begin
  rintro [ident rfl, ident h, ident rfl],
  rename ["[", ident p₁, ident p, ",", ident f₁, ident f, "]"],
  rw [expr p.as_sum] [],
  simp [] [] ["only"] ["[", expr ring_hom.map_sum, ",", expr eval₂_hom_monomial, "]"] [] [],
  apply [expr finset.sum_congr rfl],
  intros [ident d, ident hd],
  congr' [1] [],
  simp [] [] ["only"] ["[", expr finsupp.prod, "]"] [] [],
  apply [expr finset.prod_congr rfl],
  intros [ident i, ident hi],
  have [] [":", expr «expr ∈ »(i, p.vars)] [],
  { rw [expr mem_vars] [],
    exact [expr ⟨d, hd, hi⟩] },
  rw [expr h i this this] []
end

/-- If `f₁` and `f₂` are ring homs out of the polynomial ring and `p₁` and `p₂` are polynomials,
  then `f₁ p₁ = f₂ p₂` if `p₁ = p₂` and `f₁` and `f₂` are equal on `R` and on the variables
  of `p₁`.  -/
theorem hom_congr_vars {f₁ f₂ : MvPolynomial σ R →+* S} {p₁ p₂ : MvPolynomial σ R} (hC : f₁.comp C = f₂.comp C)
  (hv : ∀ i, i ∈ p₁.vars → i ∈ p₂.vars → f₁ (X i) = f₂ (X i)) (hp : p₁ = p₂) : f₁ p₁ = f₂ p₂ :=
  calc f₁ p₁ = eval₂_hom (f₁.comp C) (f₁ ∘ X) p₁ :=
    RingHom.congr_fun
      (by 
        ext <;> simp )
      _ 
    _ = eval₂_hom (f₂.comp C) (f₂ ∘ X) p₂ := eval₂_hom_congr' hC hv hp 
    _ = f₂ p₂ :=
    RingHom.congr_fun
      (by 
        ext <;> simp )
      _
    

-- error in Data.MvPolynomial.Variables: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem exists_rename_eq_of_vars_subset_range
(p : mv_polynomial σ R)
(f : τ → σ)
(hfi : injective f)
(hf : «expr ⊆ »(«expr↑ »(p.vars), set.range f)) : «expr∃ , »((q : mv_polynomial τ R), «expr = »(rename f q, p)) :=
⟨bind₁ (λ i : σ, option.elim (partial_inv f i) 0 X) p, begin
   show [expr «expr = »((rename f).to_ring_hom.comp _ p, ring_hom.id _ p)],
   refine [expr hom_congr_vars _ _ _],
   { ext1 [] [],
     simp [] [] [] ["[", expr algebra_map_eq, "]"] [] [] },
   { intros [ident i, ident hip, "_"],
     rcases [expr hf hip, "with", "⟨", ident i, ",", ident rfl, "⟩"],
     simp [] [] [] ["[", expr partial_inv_left hfi, "]"] [] [] },
   { refl }
 end⟩

-- error in Data.MvPolynomial.Variables: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem vars_bind₁
(f : σ → mv_polynomial τ R)
(φ : mv_polynomial σ R) : «expr ⊆ »((bind₁ f φ).vars, φ.vars.bUnion (λ i, (f i).vars)) :=
begin
  calc
    «expr = »((bind₁ f φ).vars, (φ.support.sum (λ
       x : «expr →₀ »(σ, exprℕ()), bind₁ f (monomial x (coeff x φ)))).vars) : by { rw ["[", "<-", expr alg_hom.map_sum, ",", "<-", expr φ.as_sum, "]"] [] }
    «expr ≤ »(..., φ.support.bUnion (λ
      i : «expr →₀ »(σ, exprℕ()), (bind₁ f (monomial i (coeff i φ))).vars)) : vars_sum_subset _ _
    «expr = »(..., φ.support.bUnion (λ
      d : «expr →₀ »(σ, exprℕ()), «expr * »(C (coeff d φ), «expr∏ in , »((i), d.support, «expr ^ »(f i, d i))).vars)) : by simp [] [] ["only"] ["[", expr bind₁_monomial, "]"] [] []
    «expr ≤ »(..., φ.support.bUnion (λ d : «expr →₀ »(σ, exprℕ()), d.support.bUnion (λ i, (f i).vars))) : _
    «expr ≤ »(..., φ.vars.bUnion (λ i : σ, (f i).vars)) : _,
  { apply [expr finset.bUnion_mono],
    intros [ident d, ident hd],
    calc
      «expr ≤ »(«expr * »(C (coeff d φ), «expr∏ in , »((i : σ), d.support, «expr ^ »(f i, d i))).vars, «expr ∪ »((C (coeff d φ)).vars, «expr∏ in , »((i : σ), d.support, «expr ^ »(f i, d i)).vars)) : vars_mul _ _
      «expr ≤ »(..., «expr∏ in , »((i : σ), d.support, «expr ^ »(f i, d i)).vars) : by simp [] [] ["only"] ["[", expr finset.empty_union, ",", expr vars_C, ",", expr finset.le_iff_subset, ",", expr finset.subset.refl, "]"] [] []
      «expr ≤ »(..., d.support.bUnion (λ i : σ, «expr ^ »(f i, d i).vars)) : vars_prod _
      «expr ≤ »(..., d.support.bUnion (λ i : σ, (f i).vars)) : _,
    apply [expr finset.bUnion_mono],
    intros [ident i, ident hi],
    apply [expr vars_pow] },
  { intro [ident j],
    simp_rw [expr finset.mem_bUnion] [],
    rintro ["⟨", ident d, ",", ident hd, ",", "⟨", ident i, ",", ident hi, ",", ident hj, "⟩", "⟩"],
    exact [expr ⟨i, (mem_vars _).mpr ⟨d, hd, hi⟩, hj⟩] }
end

theorem mem_vars_bind₁ (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) {j : τ} (h : j ∈ (bind₁ f φ).vars) :
  ∃ i : σ, i ∈ φ.vars ∧ j ∈ (f i).vars :=
  by 
    simpa only [exists_prop, Finset.mem_bUnion, mem_support_iff, Ne.def] using vars_bind₁ f φ h

theorem vars_rename (f : σ → τ) (φ : MvPolynomial σ R) : (rename f φ).vars ⊆ φ.vars.image f :=
  by 
    intro i hi 
    simp only [vars, exists_prop, Multiset.mem_to_finset, Finset.mem_image] at hi⊢
    simpa only [Multiset.mem_map] using degrees_rename _ _ hi

theorem mem_vars_rename (f : σ → τ) (φ : MvPolynomial σ R) {j : τ} (h : j ∈ (rename f φ).vars) :
  ∃ i : σ, i ∈ φ.vars ∧ f i = j :=
  by 
    simpa only [exists_prop, Finset.mem_image] using vars_rename f φ h

end EvalVars

end CommSemiringₓ

end MvPolynomial

