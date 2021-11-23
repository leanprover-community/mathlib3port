import Mathbin.Algebra.DirectSum.Internal 
import Mathbin.Algebra.GradedMonoid 
import Mathbin.Data.Fintype.Card 
import Mathbin.Data.MvPolynomial.Variables

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneous_submodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneous_component n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous components

-/


open_locale BigOperators

namespace MvPolynomial

variable{σ : Type _}{τ : Type _}{R : Type _}{S : Type _}

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`. -/
def is_homogeneous [CommSemiringₓ R] (φ : MvPolynomial σ R) (n : ℕ) :=
  ∀ ⦃d⦄, coeff d φ ≠ 0 → (∑i in d.support, d i) = n

variable(σ R)

/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
noncomputable def homogeneous_submodule [CommSemiringₓ R] (n : ℕ) : Submodule R (MvPolynomial σ R) :=
  { Carrier := { x | x.is_homogeneous n },
    smul_mem' :=
      fun r a ha c hc =>
        by 
          rw [coeff_smul] at hc 
          apply ha 
          intro h 
          apply hc 
          rw [h]
          exact smul_zero r,
    zero_mem' := fun d hd => False.elim (hd$ coeff_zero _),
    add_mem' :=
      fun a b ha hb c hc =>
        by 
          rw [coeff_add] at hc 
          obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0
          ·
            contrapose! hc 
            simp only [hc, add_zeroₓ]
          ·
            exact ha h
          ·
            exact hb h }

variable{σ R}

@[simp]
theorem mem_homogeneous_submodule [CommSemiringₓ R] (n : ℕ) (p : MvPolynomial σ R) :
  p ∈ homogeneous_submodule σ R n ↔ p.is_homogeneous n :=
  Iff.rfl

variable(σ R)

/-- While equal, the former has a convenient definitional reduction. -/
theorem homogeneous_submodule_eq_finsupp_supported [CommSemiringₓ R] (n : ℕ) :
  homogeneous_submodule σ R n = Finsupp.supported _ R { d | (∑i in d.support, d i) = n } :=
  by 
    ext 
    rw [Finsupp.mem_supported, Set.subset_def]
    simp only [Finsupp.mem_support_iff, Finset.mem_coe]
    rfl

variable{σ R}

-- error in RingTheory.Polynomial.Homogeneous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem homogeneous_submodule_mul
[comm_semiring R]
(m
 n : exprℕ()) : «expr ≤ »(«expr * »(homogeneous_submodule σ R m, homogeneous_submodule σ R n), homogeneous_submodule σ R «expr + »(m, n)) :=
begin
  rw [expr submodule.mul_le] [],
  intros [ident φ, ident hφ, ident ψ, ident hψ, ident c, ident hc],
  rw ["[", expr coeff_mul, "]"] ["at", ident hc],
  obtain ["⟨", "⟨", ident d, ",", ident e, "⟩", ",", ident hde, ",", ident H, "⟩", ":=", expr finset.exists_ne_zero_of_sum_ne_zero hc],
  have [ident aux] [":", expr «expr ∧ »(«expr ≠ »(coeff d φ, 0), «expr ≠ »(coeff e ψ, 0))] [],
  { contrapose ["!"] [ident H],
    by_cases [expr h, ":", expr «expr = »(coeff d φ, 0)]; simp [] [] ["only"] ["[", "*", ",", expr ne.def, ",", expr not_false_iff, ",", expr zero_mul, ",", expr mul_zero, "]"] [] ["at", "*"] },
  specialize [expr hφ aux.1],
  specialize [expr hψ aux.2],
  rw [expr finsupp.mem_antidiagonal] ["at", ident hde],
  classical,
  have [ident hd'] [":", expr «expr ⊆ »(d.support, «expr ∪ »(d.support, e.support))] [":=", expr finset.subset_union_left _ _],
  have [ident he'] [":", expr «expr ⊆ »(e.support, «expr ∪ »(d.support, e.support))] [":=", expr finset.subset_union_right _ _],
  rw ["[", "<-", expr hde, ",", "<-", expr hφ, ",", "<-", expr hψ, ",", expr finset.sum_subset finsupp.support_add, ",", expr finset.sum_subset hd', ",", expr finset.sum_subset he', ",", "<-", expr finset.sum_add_distrib, "]"] [],
  { congr },
  all_goals { intros [ident i, ident hi],
    apply [expr finsupp.not_mem_support_iff.mp] }
end

section 

variable[CommSemiringₓ R]

variable{σ R}

theorem is_homogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : (∑i in d.support, d i) = n) :
  is_homogeneous (monomial d r) n :=
  by 
    intro c hc 
    classical 
    rw [coeff_monomial] at hc 
    splitIfs  at hc with h
    ·
      subst c 
      exact hn
    ·
      contradiction

variable(σ){R}

theorem is_homogeneous_C (r : R) : is_homogeneous (C r : MvPolynomial σ R) 0 :=
  by 
    apply is_homogeneous_monomial 
    simp only [Finsupp.zero_apply, Finset.sum_const_zero]

variable(σ R)

theorem is_homogeneous_zero (n : ℕ) : is_homogeneous (0 : MvPolynomial σ R) n :=
  (homogeneous_submodule σ R n).zero_mem

theorem is_homogeneous_one : is_homogeneous (1 : MvPolynomial σ R) 0 :=
  is_homogeneous_C _ _

variable{σ}(R)

theorem is_homogeneous_X (i : σ) : is_homogeneous (X i : MvPolynomial σ R) 1 :=
  by 
    apply is_homogeneous_monomial 
    simp only [Finsupp.support_single_ne_zero one_ne_zero, Finset.sum_singleton]
    exact Finsupp.single_eq_same

end 

namespace IsHomogeneous

variable[CommSemiringₓ R]{φ ψ : MvPolynomial σ R}{m n : ℕ}

-- error in RingTheory.Polynomial.Homogeneous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coeff_eq_zero
(hφ : is_homogeneous φ n)
(d : «expr →₀ »(σ, exprℕ()))
(hd : «expr ≠ »(«expr∑ in , »((i), d.support, d i), n)) : «expr = »(coeff d φ, 0) :=
by { have [ident aux] [] [":=", expr mt (@hφ d) hd],
  classical,
  rwa [expr not_not] ["at", ident aux] }

theorem inj_right (hm : is_homogeneous φ m) (hn : is_homogeneous φ n) (hφ : φ ≠ 0) : m = n :=
  by 
    obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ 
    rw [←hm hd, ←hn hd]

theorem add (hφ : is_homogeneous φ n) (hψ : is_homogeneous ψ n) : is_homogeneous (φ+ψ) n :=
  (homogeneous_submodule σ R n).add_mem hφ hψ

theorem Sum {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ℕ) (h : ∀ i _ : i ∈ s, is_homogeneous (φ i) n) :
  is_homogeneous (∑i in s, φ i) n :=
  (homogeneous_submodule σ R n).sum_mem h

theorem mul (hφ : is_homogeneous φ m) (hψ : is_homogeneous ψ n) : is_homogeneous (φ*ψ) (m+n) :=
  homogeneous_submodule_mul m n$ Submodule.mul_mem_mul hφ hψ

theorem Prod {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → ℕ)
  (h : ∀ i _ : i ∈ s, is_homogeneous (φ i) (n i)) : is_homogeneous (∏i in s, φ i) (∑i in s, n i) :=
  by 
    classical 
    revert h 
    apply Finset.induction_on s
    ·
      intro 
      simp only [is_homogeneous_one, Finset.sum_empty, Finset.prod_empty]
    ·
      intro i s his IH h 
      simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
      apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
      intro j hjs 
      exact h j (Finset.mem_insert_of_mem hjs)

theorem total_degree (hφ : is_homogeneous φ n) (h : φ ≠ 0) : total_degree φ = n :=
  by 
    rw [total_degree]
    apply le_antisymmₓ
    ·
      apply Finset.sup_le 
      intro d hd 
      rw [mem_support_iff] at hd 
      rw [Finsupp.sum, hφ hd]
    ·
      obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h 
      simp only [←hφ hd, Finsupp.sum]
      replace hd := finsupp.mem_support_iff.mpr hd 
      exact Finset.le_sup hd

/--
The homogeneous submodules form a graded ring. This instance is used by `direct_sum.comm_semiring`
and `direct_sum.algebra`. -/
instance homogeneous_submodule.gcomm_semiring : SetLike.GradedMonoid (homogeneous_submodule σ R) :=
  { one_mem := is_homogeneous_one σ R, mul_mem := fun i j xi xj => is_homogeneous.mul }

open_locale DirectSum

noncomputable example  : CommSemiringₓ (⨁i, homogeneous_submodule σ R i) :=
  inferInstance

noncomputable example  : Algebra R (⨁i, homogeneous_submodule σ R i) :=
  inferInstance

end IsHomogeneous

section 

noncomputable theory

open_locale Classical

open Finset

/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneous_component [CommSemiringₓ R] (n : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (Submodule.subtype _).comp$ Finsupp.restrictDom _ _ { d | (∑i in d.support, d i) = n }

section HomogeneousComponent

open Finset

variable[CommSemiringₓ R](n : ℕ)(φ : MvPolynomial σ R)

theorem coeff_homogeneous_component (d : σ →₀ ℕ) :
  coeff d (homogeneous_component n φ) = if (∑i in d.support, d i) = n then coeff d φ else 0 :=
  by 
    convert Finsupp.filter_apply (fun d : σ →₀ ℕ => (∑i in d.support, d i) = n) φ d

theorem homogeneous_component_apply :
  homogeneous_component n φ = ∑d in φ.support.filter fun d => (∑i in d.support, d i) = n, monomial d (coeff d φ) :=
  by 
    convert Finsupp.filter_eq_sum (fun d : σ →₀ ℕ => (∑i in d.support, d i) = n) φ

theorem homogeneous_component_is_homogeneous : (homogeneous_component n φ).IsHomogeneous n :=
  by 
    intro d hd 
    contrapose! hd 
    rw [coeff_homogeneous_component, if_neg hd]

theorem homogeneous_component_zero : homogeneous_component 0 φ = C (coeff 0 φ) :=
  by 
    ext1 d 
    rcases em (d = 0) with (rfl | hd)
    ·
      simp only [coeff_homogeneous_component, sum_eq_zero_iff, Finsupp.zero_apply, if_true, coeff_C, eq_self_iff_true,
        forall_true_iff]
    ·
      rw [coeff_homogeneous_component, if_neg, coeff_C, if_neg (Ne.symm hd)]
      simp only [Finsupp.ext_iff, Finsupp.zero_apply] at hd 
      simp [hd]

theorem homogeneous_component_eq_zero' (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → (∑i in d.support, d i) ≠ n) :
  homogeneous_component n φ = 0 :=
  by 
    rw [homogeneous_component_apply, sum_eq_zero]
    intro d hd 
    rw [mem_filter] at hd 
    exfalso 
    exact h _ hd.1 hd.2

theorem homogeneous_component_eq_zero (h : φ.total_degree < n) : homogeneous_component n φ = 0 :=
  by 
    apply homogeneous_component_eq_zero' 
    rw [total_degree, Finset.sup_lt_iff] at h
    ·
      intro d hd 
      exact ne_of_ltₓ (h d hd)
    ·
      exact lt_of_le_of_ltₓ (Nat.zero_leₓ _) h

theorem sum_homogeneous_component : (∑i in range (φ.total_degree+1), homogeneous_component i φ) = φ :=
  by 
    ext1 d 
    suffices  : φ.total_degree < d.support.sum d → 0 = coeff d φ
    ·
      simpa [coeff_sum, coeff_homogeneous_component]
    exact fun h => (coeff_eq_zero_of_total_degree_lt h).symm

end HomogeneousComponent

end 

end MvPolynomial

