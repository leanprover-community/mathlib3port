import Mathbin.Data.Fintype.Card 
import Mathbin.Data.MvPolynomial.Rename 
import Mathbin.Data.MvPolynomial.CommRing 
import Mathbin.Algebra.Algebra.Subalgebra

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `mv_polynomial`s and elementary symmetric `mv_polynomial`s.
We also prove some basic facts about them.

## Main declarations

* `mv_polynomial.is_symmetric`

* `mv_polynomial.symmetric_subalgebra`

* `mv_polynomial.esymm`

## Notation

+ `esymm σ R n`, is the `n`th elementary symmetric polynomial in `mv_polynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[comm_semiring R]` `[comm_semiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : mv_polynomial σ R`

-/


open equiv(Perm)

open_locale BigOperators

noncomputable theory

namespace MvPolynomial

variable {σ : Type _} {R : Type _}

variable {τ : Type _} {S : Type _}

/-- A `mv_polynomial φ` is symmetric if it is invariant under
permutations of its variables by the  `rename` operation -/
def is_symmetric [CommSemiringₓ R] (φ : MvPolynomial σ R) : Prop :=
  ∀ e : perm σ, rename e φ = φ

variable (σ R)

/-- The subalgebra of symmetric `mv_polynomial`s. -/
def symmetric_subalgebra [CommSemiringₓ R] : Subalgebra R (MvPolynomial σ R) :=
  { Carrier := SetOf is_symmetric, algebra_map_mem' := fun r e => rename_C e r,
    mul_mem' :=
      fun a b ha hb e =>
        by 
          rw [AlgHom.map_mul, ha, hb],
    add_mem' :=
      fun a b ha hb e =>
        by 
          rw [AlgHom.map_add, ha, hb] }

variable {σ R}

@[simp]
theorem mem_symmetric_subalgebra [CommSemiringₓ R] (p : MvPolynomial σ R) :
  p ∈ symmetric_subalgebra σ R ↔ p.is_symmetric :=
  Iff.rfl

namespace IsSymmetric

section CommSemiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ S] {φ ψ : MvPolynomial σ R}

@[simp]
theorem C (r : R) : is_symmetric (C r : MvPolynomial σ R) :=
  (symmetric_subalgebra σ R).algebra_map_mem r

@[simp]
theorem zero : is_symmetric (0 : MvPolynomial σ R) :=
  (symmetric_subalgebra σ R).zero_mem

@[simp]
theorem one : is_symmetric (1 : MvPolynomial σ R) :=
  (symmetric_subalgebra σ R).one_mem

theorem add (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ+ψ) :=
  (symmetric_subalgebra σ R).add_mem hφ hψ

theorem mul (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ*ψ) :=
  (symmetric_subalgebra σ R).mul_mem hφ hψ

theorem smul (r : R) (hφ : is_symmetric φ) : is_symmetric (r • φ) :=
  (symmetric_subalgebra σ R).smul_mem hφ r

@[simp]
theorem map (hφ : is_symmetric φ) (f : R →+* S) : is_symmetric (map f φ) :=
  fun e =>
    by 
      rw [←map_rename, hφ]

end CommSemiringₓ

section CommRingₓ

variable [CommRingₓ R] {φ ψ : MvPolynomial σ R}

theorem neg (hφ : is_symmetric φ) : is_symmetric (-φ) :=
  (symmetric_subalgebra σ R).neg_mem hφ

theorem sub (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ - ψ) :=
  (symmetric_subalgebra σ R).sub_mem hφ hψ

end CommRingₓ

end IsSymmetric

section ElementarySymmetric

open Finset

variable (σ R) [CommSemiringₓ R] [CommSemiringₓ S] [Fintype σ] [Fintype τ]

/-- The `n`th elementary symmetric `mv_polynomial σ R`. -/
def esymm (n : ℕ) : MvPolynomial σ R :=
  ∑t in powerset_len n univ, ∏i in t, X i

/-- We can define `esymm σ R n` by summing over a subtype instead of over `powerset_len`. -/
theorem esymm_eq_sum_subtype (n : ℕ) : esymm σ R n = ∑t : { s : Finset σ // s.card = n }, ∏i in (t : Finset σ), X i :=
  by 
    rw [esymm]
    let i : ∀ a : Finset σ, a ∈ powerset_len n univ → { s : Finset σ // s.card = n } :=
      fun a ha => ⟨_, (mem_powerset_len.mp ha).2⟩
    refine' sum_bij i (fun a ha => mem_univ (i a ha)) _ (fun _ _ _ _ hi => subtype.ext_iff_val.mp hi) _
    ·
      intros 
      apply prod_congr 
      simp only [Subtype.coe_mk]
      intros 
      rfl
    ·
      refine' fun b H => ⟨b.val, mem_powerset_len.mpr ⟨subset_univ b.val, b.property⟩, _⟩
      simp [i]

/-- We can define `esymm σ R n` as a sum over explicit monomials -/
theorem esymm_eq_sum_monomial (n : ℕ) :
  esymm σ R n = ∑t in powerset_len n univ, monomial (∑i in t, Finsupp.single i 1) 1 :=
  by 
    refine' sum_congr rfl fun x hx => _ 
    rw [monic_monomial_eq]
    rw [Finsupp.prod_pow]
    rw [←prod_subset (fun y _ => Finset.mem_univ y : x ⊆ univ) fun y _ hy => _]
    ·
      refine' prod_congr rfl fun x' hx' => _ 
      convert (pow_oneₓ _).symm 
      convert (Finsupp.applyAddHom x' : (σ →₀ ℕ) →+ ℕ).map_sum _ x 
      classical 
      simp [Finsupp.single_apply, Finset.filter_eq', apply_ite, apply_ite Finset.card]
      rw [if_pos hx']
    ·
      convert pow_zeroₓ _ 
      convert (Finsupp.applyAddHom y : (σ →₀ ℕ) →+ ℕ).map_sum _ x 
      classical 
      simp [Finsupp.single_apply, Finset.filter_eq', apply_ite, apply_ite Finset.card]
      rw [if_neg hy]

@[simp]
theorem esymm_zero : esymm σ R 0 = 1 :=
  by 
    simp only [esymm, powerset_len_zero, sum_singleton, prod_empty]

theorem map_esymm (n : ℕ) (f : R →+* S) : map f (esymm σ R n) = esymm σ S n :=
  by 
    rw [esymm, (map f).map_sum]
    refine' sum_congr rfl fun x hx => _ 
    rw [(map f).map_prod]
    simp 

theorem rename_esymm (n : ℕ) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
  by 
    rw [esymm_eq_sum_subtype, esymm_eq_sum_subtype, (rename («expr⇑ » e)).map_sum]
    let e' : { s : Finset σ // s.card = n } ≃ { s : Finset τ // s.card = n } :=
      Equiv.subtypeEquiv (Equiv.finsetCongr e)
        (by 
          simp )
    rw [←Equiv.sum_comp e'.symm]
    apply Fintype.sum_congr 
    intro 
    calc _ = ∏i in (e'.symm a : Finset σ), (rename e) (X i) :=
      (rename e).map_prod _ _ _ = ∏i in (a : Finset τ), (rename e) (X (e.symm i)) :=
      prod_mapₓ (a : Finset τ) _ _ _ = _ := _ 
    apply Finset.prod_congr rfl 
    intros 
    simp 

theorem esymm_is_symmetric (n : ℕ) : is_symmetric (esymm σ R n) :=
  by 
    intro 
    rw [rename_esymm]

-- error in RingTheory.Polynomial.Symmetric: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem support_esymm''
(n : exprℕ())
[decidable_eq σ]
[nontrivial R] : «expr = »((esymm σ R n).support, (powerset_len n (univ : finset σ)).bUnion (λ
  t, (finsupp.single «expr∑ in , »((i : σ), t, finsupp.single i 1) (1 : R)).support)) :=
begin
  rw [expr esymm_eq_sum_monomial] [],
  simp [] [] ["only"] ["[", "<-", expr single_eq_monomial, "]"] [] [],
  convert [] [expr finsupp.support_sum_eq_bUnion (powerset_len n (univ : finset σ)) _] [],
  intros [ident s, ident t, ident hst, ident d],
  simp [] [] ["only"] ["[", expr finsupp.support_single_ne_zero one_ne_zero, ",", expr and_imp, ",", expr inf_eq_inter, ",", expr mem_inter, ",", expr mem_singleton, "]"] [] [],
  rintro [ident h, ident rfl],
  have [] [] [":=", expr congr_arg finsupp.support h],
  rw ["[", expr finsupp.support_sum_eq_bUnion, ",", expr finsupp.support_sum_eq_bUnion, "]"] ["at", ident this],
  { simp [] [] ["only"] ["[", expr finsupp.support_single_ne_zero one_ne_zero, ",", expr bUnion_singleton_eq_self, "]"] [] ["at", ident this],
    exact [expr absurd this hst.symm] },
  all_goals { intros [ident x, ident y],
    simp [] [] [] ["[", expr finsupp.support_single_disjoint, "]"] [] [] }
end

theorem support_esymm' (n : ℕ) [DecidableEq σ] [Nontrivial R] :
  (esymm σ R n).support = (powerset_len n (univ : Finset σ)).bUnion fun t => {∑i : σ in t, Finsupp.single i 1} :=
  by 
    rw [support_esymm'']
    congr 
    funext 
    exact Finsupp.support_single_ne_zero one_ne_zero

theorem support_esymm (n : ℕ) [DecidableEq σ] [Nontrivial R] :
  (esymm σ R n).support = (powerset_len n (univ : Finset σ)).Image fun t => ∑i : σ in t, Finsupp.single i 1 :=
  by 
    rw [support_esymm']
    exact bUnion_singleton

-- error in RingTheory.Polynomial.Symmetric: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degrees_esymm
[nontrivial R]
(n : exprℕ())
(hpos : «expr < »(0, n))
(hn : «expr ≤ »(n, fintype.card σ)) : «expr = »((esymm σ R n).degrees, (univ : finset σ).val) :=
begin
  classical,
  have [] [":", expr «expr = »(«expr ∘ »(finsupp.to_multiset, λ
     t : finset σ, «expr∑ in , »((i : σ), t, finsupp.single i 1)), finset.val)] [],
  { funext [],
    simp [] [] [] ["[", expr finsupp.to_multiset_sum_single, "]"] [] [] },
  rw ["[", expr degrees, ",", expr support_esymm, ",", expr sup_finset_image, ",", expr this, ",", "<-", expr comp_sup_eq_sup_comp, "]"] [],
  { obtain ["⟨", ident k, ",", ident rfl, "⟩", ":=", expr nat.exists_eq_succ_of_ne_zero hpos.ne'],
    simpa [] [] [] [] [] ["using", expr powerset_len_sup _ _ (nat.lt_of_succ_le hn)] },
  { intros [],
    simp [] [] ["only"] ["[", expr union_val, ",", expr sup_eq_union, "]"] [] [],
    congr },
  { refl }
end

end ElementarySymmetric

end MvPolynomial

