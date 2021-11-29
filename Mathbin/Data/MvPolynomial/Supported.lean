import Mathbin.RingTheory.Adjoin.Polynomial 
import Mathbin.Data.MvPolynomial.Variables

/-!
# Polynomials supported by a set of variables

This file contains the definition and lemmas about `mv_polynomial.supported`.

## Main definitions

* `mv_polynomial.supported` : Given a set `s : set σ`, `supported R s` is the subalgebra of
  `mv_polynomial σ R` consisting of polynomials whose set of variables is contained in `s`.
  This subalgebra is isomorphic to `mv_polynomial s R`

## Tags
variables, polynomial, vars
-/


universe u v w

namespace MvPolynomial

variable {σ τ : Type _} {R : Type u} {S : Type v} {r : R} {e : ℕ} {n m : σ}

section CommSemiringₓ

variable [CommSemiringₓ R] {p q : MvPolynomial σ R}

variable (R)

/-- The set of polynomials whose variables are contained in `s` as a `subalgebra` over `R`. -/
noncomputable def supported (s : Set σ) : Subalgebra R (MvPolynomial σ R) :=
  Algebra.adjoin R (X '' s)

variable {σ R}

open_locale Classical

open Algebra

theorem supported_eq_range_rename (s : Set σ) : supported R s = (rename (coeₓ : s → σ)).range :=
  by 
    rw [supported, Set.image_eq_range, adjoin_range_eq_range_aeval, rename]

/--The isomorphism between the subalgebra of polynomials supported by `s` and `mv_polynomial s R`-/
noncomputable def supported_equiv_mv_polynomial (s : Set σ) : supported R s ≃ₐ[R] MvPolynomial s R :=
  (Subalgebra.equivOfEq _ _ (supported_eq_range_rename s)).trans
    (AlgEquiv.ofInjective (rename (coeₓ : s → σ)) (rename_injective _ Subtype.val_injective)).symm

@[simp]
theorem supported_equiv_mv_polynomial_symm_C (s : Set σ) (x : R) :
  (supported_equiv_mv_polynomial s).symm (C x) = algebraMap R (supported R s) x :=
  by 
    ext1 
    simp [supported_equiv_mv_polynomial, MvPolynomial.algebra_map_eq]

@[simp]
theorem supported_equiv_mv_polynomial_symm_X (s : Set σ) (i : s) :
  («expr↑ » ((supported_equiv_mv_polynomial s).symm (X i : MvPolynomial s R)) : MvPolynomial σ R) = X i :=
  by 
    simp [supported_equiv_mv_polynomial]

variable {s t : Set σ}

theorem mem_supported : p ∈ supported R s ↔ «expr↑ » p.vars ⊆ s :=
  by 
    rw [supported_eq_range_rename, AlgHom.mem_range]
    split 
    ·
      rintro ⟨p, rfl⟩
      refine' trans (Finset.coe_subset.2 (vars_rename _ _)) _ 
      simp 
    ·
      intro hs 
      exact
        exists_rename_eq_of_vars_subset_range p (coeₓ : s → σ) Subtype.val_injective
          (by 
            simpa)

theorem supported_eq_vars_subset : (supported R s : Set (MvPolynomial σ R)) = { p | «expr↑ » p.vars ⊆ s } :=
  Set.ext$ fun _ => mem_supported

@[simp]
theorem mem_supported_vars (p : MvPolynomial σ R) : p ∈ supported R («expr↑ » p.vars : Set σ) :=
  by 
    rw [mem_supported]

variable (s)

theorem supported_eq_adjoin_X : supported R s = Algebra.adjoin R (X '' s) :=
  rfl

@[simp]
theorem supported_univ : supported R (Set.Univ : Set σ) = ⊤ :=
  by 
    simp [Algebra.eq_top_iff, mem_supported]

@[simp]
theorem supported_empty : supported R (∅ : Set σ) = ⊥ :=
  by 
    simp [supported_eq_adjoin_X]

variable {s}

theorem supported_mono (st : s ⊆ t) : supported R s ≤ supported R t :=
  Algebra.adjoin_mono (Set.image_subset _ st)

@[simp]
theorem X_mem_supported [Nontrivial R] {i : σ} : X i ∈ supported R s ↔ i ∈ s :=
  by 
    simp [mem_supported]

@[simp]
theorem supported_le_supported_iff [Nontrivial R] : supported R s ≤ supported R t ↔ s ⊆ t :=
  by 
    split 
    ·
      intro h i 
      simpa using @h (X i)
    ·
      exact supported_mono

theorem supported_strict_mono [Nontrivial R] : StrictMono (supported R : Set σ → Subalgebra R (MvPolynomial σ R)) :=
  strict_mono_of_le_iff_le fun _ _ => supported_le_supported_iff.symm

end CommSemiringₓ

end MvPolynomial

