/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio

! This file was ported from Lean 3 source module ring_theory.dedekind_domain.integral_closure
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.DedekindDomain.Basic
import Mathbin.RingTheory.Trace

/-!
# Integral closure of Dedekind domains

This file shows the integral closure of a Dedekind domain (in particular, the ring of integers
of a number field) is a Dedekind domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type _) [CommRing R] [CommRing A] [Field K]

open nonZeroDivisors Polynomial

variable [IsDomain A]

section IsIntegralClosure

/-! ### `is_integral_closure` section

We show that an integral closure of a Dedekind domain in a finite separable
field extension is again a Dedekind domain. This implies the ring of integers
of a number field is a Dedekind domain. -/


open Algebra

open BigOperators

variable {A K} [Algebra A K] [IsFractionRing A K]

variable {L : Type _} [Field L] (C : Type _) [CommRing C]

variable [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L]

variable [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]

theorem IsIntegralClosure.range_le_span_dualBasis [IsSeparable K L] {ι : Type _} [Fintype ι]
    [DecidableEq ι] (b : Basis ι K L) (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    ((Algebra.linearMap C L).restrictScalars A).range ≤
      Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceFormNondegenerate K L) b) :=
  by
  let db := (trace_form K L).dualBasis (traceFormNondegenerate K L) b
  rintro _ ⟨x, rfl⟩
  simp only [LinearMap.coe_restrictScalars_eq_coe, Algebra.linearMap_apply]
  have hx : IsIntegral A (algebraMap C L x) := (IsIntegralClosure.isIntegral A L x).algebraMap
  rsuffices ⟨c, x_eq⟩ : ∃ c : ι → A, algebraMap C L x = ∑ i, c i • db i
  · rw [x_eq]
    refine' Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span _)
    rw [Set.mem_range]
    exact ⟨i, rfl⟩
  suffices ∃ c : ι → K, (∀ i, IsIntegral A (c i)) ∧ algebraMap C L x = ∑ i, c i • db i
    by
    obtain ⟨c, hc, hx⟩ := this
    have hc' : ∀ i, IsLocalization.IsInteger A (c i) := fun i =>
      is_integrally_closed.is_integral_iff.mp (hc i)
    use fun i => Classical.choose (hc' i)
    refine' hx.trans (Finset.sum_congr rfl fun i _ => _)
    conv_lhs => rw [← Classical.choose_spec (hc' i)]
    rw [← IsScalarTower.algebraMap_smul K (Classical.choose (hc' i)) (db i)]
  refine' ⟨fun i => db.repr (algebraMap C L x) i, fun i => _, (db.sum_repr _).symm⟩
  rw [BilinForm.dualBasis_repr_apply]
  exact is_integral_trace (isIntegral_mul hx (hb_int i))
#align is_integral_closure.range_le_span_dual_basis IsIntegralClosure.range_le_span_dualBasis

theorem integralClosure_le_span_dualBasis [IsSeparable K L] {ι : Type _} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    (integralClosure A L).toSubmodule ≤
      Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceFormNondegenerate K L) b) :=
  by
  refine' le_trans _ (IsIntegralClosure.range_le_span_dualBasis (integralClosure A L) b hb_int)
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩
#align integral_closure_le_span_dual_basis integralClosure_le_span_dualBasis

variable (A) (K)

include K

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (y «expr ≠ » (0 : A)) -/
/-- Send a set of `x`'es in a finite extension `L` of the fraction field of `R`
to `(y : R) • x ∈ integral_closure R L`. -/
theorem exists_integral_multiples (s : Finset L) :
    ∃ (y : _)(_ : y ≠ (0 : A)), ∀ x ∈ s, IsIntegral A (y • x) :=
  by
  haveI := Classical.decEq L
  refine' s.induction _ _
  · use 1, one_neZero
    rintro x ⟨⟩
  · rintro x s hx ⟨y, hy, hs⟩
    obtain ⟨x', y', hy', hx'⟩ :=
      exists_integral_multiple
        ((IsFractionRing.isAlgebraic_iff A K L).mpr (is_algebraic_of_finite _ _ x))
        ((injective_iff_map_eq_zero (algebraMap A L)).mp _)
    refine' ⟨y * y', mul_ne_zero hy hy', fun x'' hx'' => _⟩
    rcases finset.mem_insert.mp hx'' with (rfl | hx'')
    · rw [mul_smul, Algebra.smul_def, Algebra.smul_def, mul_comm _ x'', hx']
      exact isIntegral_mul isIntegral_algebraMap x'.2
    · rw [mul_comm, mul_smul, Algebra.smul_def]
      exact isIntegral_mul isIntegral_algebraMap (hs _ hx'')
    · rw [IsScalarTower.algebraMap_eq A K L]
      apply (algebraMap K L).Injective.comp
      exact IsFractionRing.injective _ _
#align exists_integral_multiples exists_integral_multiples

variable (L)

/-- If `L` is a finite extension of `K = Frac(A)`,
then `L` has a basis over `A` consisting of integral elements. -/
theorem FiniteDimensional.exists_is_basis_integral :
    ∃ (s : Finset L)(b : Basis s K L), ∀ x, IsIntegral A (b x) :=
  by
  letI := Classical.decEq L
  letI : IsNoetherian K L := IsNoetherian.iff_fg.2 inferInstance
  let s' := IsNoetherian.finsetBasisIndex K L
  let bs' := IsNoetherian.finsetBasis K L
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (finset.univ.image bs')
  have hy' : algebraMap A L y ≠ 0 :=
    by
    refine' mt ((injective_iff_map_eq_zero (algebraMap A L)).mp _ _) hy
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).Injective.comp (IsFractionRing.injective A K)
  refine'
    ⟨s',
      bs'.map
        {
          Algebra.lmul _ _
            (algebraMap A L y) with
          toFun := fun x => algebraMap A L y * x
          invFun := fun x => (algebraMap A L y)⁻¹ * x
          left_inv := _
          right_inv := _ },
      _⟩
  · intro x
    simp only [inv_mul_cancel_left₀ hy']
  · intro x
    simp only [mul_inv_cancel_left₀ hy']
  · rintro ⟨x', hx'⟩
    simp only [Algebra.smul_def, Finset.mem_image, exists_prop, Finset.mem_univ, true_and_iff] at
      his'
    simp only [Basis.map_apply, LinearEquiv.coe_mk]
    exact his' _ ⟨_, rfl⟩
#align finite_dimensional.exists_is_basis_integral FiniteDimensional.exists_is_basis_integral

variable (A K L) [IsSeparable K L]

include L

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian over `A`. -/
theorem IsIntegralClosure.isNoetherian [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherian A C := by
  haveI := Classical.decEq L
  obtain ⟨s, b, hb_int⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' := (trace_form K L).dualBasis (traceFormNondegenerate K L) b
  letI := isNoetherianSpanOfFinite A (Set.finite_range b')
  let f : C →ₗ[A] Submodule.span A (Set.range b') :=
    (Submodule.ofLe (IsIntegralClosure.range_le_span_dualBasis C b hb_int)).comp
      ((Algebra.linearMap C L).restrictScalars A).range_restrict
  refine' isNoetherianOfKerBot f _
  rw [LinearMap.ker_comp, Submodule.ker_ofLe, Submodule.comap_bot, LinearMap.ker_codRestrict]
  exact LinearMap.ker_eq_bot_of_injective (IsIntegralClosure.algebraMap_injective C A L)
#align is_integral_closure.is_noetherian IsIntegralClosure.isNoetherian

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian. -/
theorem IsIntegralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing C :=
  isNoetherianRing_iff.mpr <| isNoetherianOfTower A (IsIntegralClosure.isNoetherian A K L C)
#align is_integral_closure.is_noetherian_ring IsIntegralClosure.isNoetherianRing

variable {A K}

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure of `A` in `L` is
Noetherian. -/
theorem integralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing (integralClosure A L) :=
  IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)
#align integral_closure.is_noetherian_ring integralClosure.isNoetherianRing

variable (A K) [IsDomain C]

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure `C` of `A` in `L` is a Dedekind domain.

Can't be an instance since `A`, `K` or `L` can't be inferred. See also the instance
`integral_closure.is_dedekind_domain_fraction_ring` where `K := fraction_ring A`
and `C := integral_closure A L`.
-/
theorem IsIntegralClosure.isDedekindDomain [h : IsDedekindDomain A] : IsDedekindDomain C :=
  haveI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  ⟨IsIntegralClosure.isNoetherianRing A K L C, h.dimension_le_one.is_integral_closure _ L _,
    (isIntegrallyClosed_iff L).mpr fun x hx =>
      ⟨IsIntegralClosure.mk' C x (isIntegral_trans (IsIntegralClosure.isIntegral_algebra A L) _ hx),
        IsIntegralClosure.algebraMap_mk' _ _ _⟩⟩
#align is_integral_closure.is_dedekind_domain IsIntegralClosure.isDedekindDomain

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

Can't be an instance since `K` can't be inferred. See also the instance
`integral_closure.is_dedekind_domain_fraction_ring` where `K := fraction_ring A`.
-/
theorem integralClosure.isDedekindDomain [h : IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)
#align integral_closure.is_dedekind_domain integralClosure.isDedekindDomain

omit K

variable [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]

variable [FiniteDimensional (FractionRing A) L] [IsSeparable (FractionRing A) L]

/- If `L` is a finite separable extension of `Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

See also the lemma `integral_closure.is_dedekind_domain` where you can choose
the field of fractions yourself.
-/
instance integralClosure.isDedekindDomainFractionRing [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  integralClosure.isDedekindDomain A (FractionRing A) L
#align integral_closure.is_dedekind_domain_fraction_ring integralClosure.isDedekindDomainFractionRing

end IsIntegralClosure

