import Mathbin.Algebra.Algebra.Basic 
import Mathbin.Tactic.NoncommRing

/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolvent_set a : set R`: the resolvent set of an element `a : A` where
  `A` is an  `R`-algebra.
* `spectrum a : set R`: the spectrum of an element `a : A` where
  `A` is an  `R`-algebra.
* `resolvent : R → A`: the resolvent function is `λ r, ring.inverse (↑ₐr - a)`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐr - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_iff_mem_swap_mul` and `spectrum.preimage_units_mul_eq_swap_mul`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.

## Notations

* `σ a` : `spectrum R a` of `a : A`

## TODO

* Prove the *spectral mapping theorem* for the polynomial functional calculus
-/


universe u v

section Defs

variable (R : Type u) {A : Type v}

variable [CommRingₓ R] [Ringₓ A] [Algebra R A]

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`.  -/
def ResolventSet (a : A) : Set R :=
  { r : R | IsUnit (algebraMap R A r - a) }

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent set.  -/
def Spectrum (a : A) : Set R :=
  ResolventSet R aᶜ

variable {R}

/-- Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
    a map `R → A` which sends `r : R` to `(algebra_map R A r - a)⁻¹` when
    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/
noncomputable def resolvent (a : A) (r : R) : A :=
  Ring.inverse (algebraMap R A r - a)

end Defs

theorem IsUnit.smul_sub_iff_sub_inv_smul {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] {r : Units R}
  {a : A} : IsUnit (r • 1 - a) ↔ IsUnit (1 - r⁻¹ • a) :=
  by 
    have a_eq : a = r • r⁻¹ • a
    ·
      simp 
    nthRw 0[a_eq]
    rw [←smul_sub, is_unit_smul_iff]

namespace Spectrum

section ScalarRing

variable {R : Type u} {A : Type v}

variable [CommRingₓ R] [Ringₓ A] [Algebra R A]

local notation "σ" => Spectrum R

local notation "↑ₐ" => algebraMap R A

theorem mem_iff {r : R} {a : A} : r ∈ σ a ↔ ¬IsUnit (↑ₐ r - a) :=
  Iff.rfl

theorem not_mem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r - a) :=
  by 
    apply not_iff_not.mp 
    simp [Set.not_not_mem, mem_iff]

theorem mem_resolvent_set_of_left_right_inverse {r : R} {a b c : A} (h₁ : ((↑ₐ r - a)*b) = 1) (h₂ : (c*↑ₐ r - a) = 1) :
  r ∈ ResolventSet R a :=
  Units.is_unit
    ⟨↑ₐ r - a, b, h₁,
      by 
        rwa [←left_inv_eq_right_invₓ h₂ h₁]⟩

theorem mem_resolvent_set_iff {r : R} {a : A} : r ∈ ResolventSet R a ↔ IsUnit (↑ₐ r - a) :=
  Iff.rfl

theorem resolvent_eq {a : A} {r : R} (h : r ∈ ResolventSet R a) : resolvent a r = ↑h.unit⁻¹ :=
  Ring.inverse_unit h.unit

theorem add_mem_iff {a : A} {r s : R} : r ∈ σ a ↔ (r+s) ∈ σ (↑ₐ s+a) :=
  by 
    apply not_iff_not.mpr 
    simp only [mem_resolvent_set_iff]
    have h_eq : (↑ₐ (r+s) - ↑ₐ s+a) = ↑ₐ r - a
    ·
      simp 
      noncommRing 
    rw [h_eq]

theorem smul_mem_smul_iff {a : A} {s : R} {r : Units R} : r • s ∈ σ (r • a) ↔ s ∈ σ a :=
  by 
    apply not_iff_not.mpr 
    simp only [mem_resolvent_set_iff, Algebra.algebra_map_eq_smul_one]
    have h_eq : (r • s) • (1 : A) = r • s • 1
    ·
      simp 
    rw [h_eq, ←smul_sub, is_unit_smul_iff]

open_locale Pointwise

theorem unit_smul_eq_smul (a : A) (r : Units R) : σ (r • a) = r • σ a :=
  by 
    ext 
    have x_eq : x = r • r⁻¹ • x
    ·
      simp 
    nthRw 0[x_eq]
    rw [smul_mem_smul_iff]
    constructor
    ·
      exact
        fun h =>
          ⟨r⁻¹ • x,
            ⟨h,
              by 
                simp ⟩⟩
    ·
      rintro ⟨_, _, x'_eq⟩
      simpa [←x'_eq]

theorem left_add_coset_eq (a : A) (r : R) : LeftAddCoset r (σ a) = σ (↑ₐ r+a) :=
  by 
    ext 
    rw [mem_left_add_coset_iff, neg_add_eq_sub, add_mem_iff]
    nthRw 1[←sub_add_cancel x r]

theorem unit_mem_mul_iff_mem_swap_mul {a b : A} {r : Units R} : ↑r ∈ σ (a*b) ↔ ↑r ∈ σ (b*a) :=
  by 
    apply not_iff_not.mpr 
    simp only [mem_resolvent_set_iff, Algebra.algebra_map_eq_smul_one]
    have coe_smul_eq : ↑r • 1 = r • (1 : A)
    exact rfl 
    rw [coe_smul_eq]
    simp only [IsUnit.smul_sub_iff_sub_inv_smul]
    have right_inv_of_swap : ∀ {x y z : A} h : ((1 - x*y)*z) = 1, ((1 - y*x)*1+(y*z)*x) = 1 
    exact
      fun x y z h =>
        calc ((1 - y*x)*1+(y*z)*x) = (1 - y*x)+(y*(1 - x*y)*z)*x :=
          by 
            noncommRing 
          _ = 1 :=
          by 
            simp [h]
          
    have left_inv_of_swap : ∀ {x y z : A} h : (z*1 - x*y) = 1, ((1+(y*z)*x)*1 - y*x) = 1 
    exact
      fun x y z h =>
        calc ((1+(y*z)*x)*1 - y*x) = (1 - y*x)+(y*z*1 - x*y)*x :=
          by 
            noncommRing 
          _ = 1 :=
          by 
            simp [h]
          
    have is_unit_one_sub_mul_of_swap : ∀ {x y : A} h : IsUnit (1 - x*y), IsUnit (1 - y*x)
    exact
      fun x y h =>
        by 
          let h₁ := right_inv_of_swap h.unit.val_inv 
          let h₂ := left_inv_of_swap h.unit.inv_val 
          exact ⟨⟨1 - y*x, 1+(y*h.unit.inv)*x, h₁, h₂⟩, rfl⟩
    have is_unit_one_sub_mul_iff_swap : ∀ {x y : A}, IsUnit (1 - x*y) ↔ IsUnit (1 - y*x)
    ·
      ·
        intros 
        constructor 
        repeat' 
          apply is_unit_one_sub_mul_of_swap 
    rw [←smul_mul_assoc, ←mul_smul_comm (r⁻¹) b a, is_unit_one_sub_mul_iff_swap]

theorem preimage_units_mul_eq_swap_mul {a b : A} : (coeₓ : Units R → R) ⁻¹' σ (a*b) = coeₓ ⁻¹' σ (b*a) :=
  by 
    ext 
    exact unit_mem_mul_iff_mem_swap_mul

end ScalarRing

section ScalarField

variable {𝕜 : Type u} {A : Type v}

variable [Field 𝕜] [Ringₓ A] [Algebra 𝕜 A]

local notation "σ" => Spectrum 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

/-- Without the assumption `nontrivial A`, then `0 : A` would be invertible. -/
@[simp]
theorem zero_eq [Nontrivial A] : σ (0 : A) = {0} :=
  by 
    refine'
      Set.Subset.antisymm _
        (by 
          simp [Algebra.algebra_map_eq_smul_one, mem_iff])
    rw [Spectrum, Set.compl_subset_comm]
    intro k hk 
    rw [Set.mem_compl_singleton_iff] at hk 
    have  : IsUnit (Units.mk0 k hk • (1 : A)) := IsUnit.smul (Units.mk0 k hk) is_unit_one 
    simpa [mem_resolvent_set_iff, Algebra.algebra_map_eq_smul_one]

@[simp]
theorem scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k} :=
  by 
    have coset_eq : LeftAddCoset k {0} = {k}
    ·
      ·
        ext 
        constructor
        ·
          intro hx 
          simp [LeftAddCoset] at hx 
          exact hx
        ·
          intro hx 
          simp  at hx 
          exact
            ⟨0,
              ⟨Set.mem_singleton 0,
                by 
                  simp [hx]⟩⟩
    calc σ (↑ₐ k) = σ (↑ₐ k+0) :=
      by 
        simp _ = LeftAddCoset k (σ (0 : A)) :=
      by 
        rw [←left_add_coset_eq]_ = LeftAddCoset k {0} :=
      by 
        rw [zero_eq]_ = {k} :=
      coset_eq

@[simp]
theorem one_eq [Nontrivial A] : σ (1 : A) = {1} :=
  calc σ (1 : A) = σ (↑ₐ 1) :=
    by 
      simp [Algebra.algebra_map_eq_smul_one]
    _ = {1} := scalar_eq 1
    

open_locale Pointwise

/-- the assumption `(σ a).nonempty` is necessary and cannot be removed without
    further conditions on the algebra `A` and scalar field `𝕜`. -/
theorem smul_eq_smul [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty) : σ (k • a) = k • σ a :=
  by 
    rcases eq_or_ne k 0 with (rfl | h)
    ·
      simpa [ha, zero_smul_set]
    ·
      exact unit_smul_eq_smul a (Units.mk0 k h)

theorem nonzero_mul_eq_swap_mul (a b : A) : σ (a*b) \ {0} = σ (b*a) \ {0} :=
  by 
    suffices h : ∀ x y : A, σ (x*y) \ {0} ⊆ σ (y*x) \ {0}
    ·
      exact Set.eq_of_subset_of_subset (h a b) (h b a)
    ·
      rintro _ _ k ⟨k_mem, k_neq⟩
      change k with ↑Units.mk0 k k_neq at k_mem 
      exact ⟨unit_mem_mul_iff_mem_swap_mul.mp k_mem, k_neq⟩

end ScalarField

end Spectrum

