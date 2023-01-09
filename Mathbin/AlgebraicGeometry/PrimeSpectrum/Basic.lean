/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebraic_geometry.prime_spectrum.basic
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.PunitInstances
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.RingTheory.Ideal.Over
import Mathbin.RingTheory.Ideal.Prod
import Mathbin.RingTheory.Localization.Away
import Mathbin.RingTheory.Nilpotent
import Mathbin.Topology.Sets.Closeds
import Mathbin.Topology.Sober

/-!
# Prime spectrum of a commutative ring

The prime spectrum of a commutative ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `algebraic_geometry.structure_sheaf`.)

## Main definitions

* `prime_spectrum R`: The prime spectrum of a commutative ring `R`,
  i.e., the set of all prime ideals of `R`.
* `zero_locus s`: The zero locus of a subset `s` of `R`
  is the subset of `prime_spectrum R` consisting of all prime ideals that contain `s`.
* `vanishing_ideal t`: The vanishing ideal of a subset `t` of `prime_spectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).
-/


noncomputable section

open Classical

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]

/-- The prime spectrum of a commutative ring `R` is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `algebraic_geometry.structure_sheaf`).
It is a fundamental building block in algebraic geometry. -/
@[ext]
structure PrimeSpectrum where
  asIdeal : Ideal R
  IsPrime : as_ideal.IsPrime
#align prime_spectrum PrimeSpectrum

attribute [instance] PrimeSpectrum.isPrime

namespace PrimeSpectrum

variable {R S}

instance [Nontrivial R] : Nonempty <| PrimeSpectrum R :=
  let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI.IsPrime⟩⟩

/-- The prime spectrum of the zero ring is empty. -/
theorem punit (x : PrimeSpectrum PUnit) : False :=
  x.1.ne_top_iff_one.1 x.2.1 <| Subsingleton.elim (0 : PUnit) 1 ▸ x.1.zero_mem
#align prime_spectrum.punit PrimeSpectrum.punit

variable (R S)

/-- The map from the direct sum of prime spectra to the prime spectrum of a direct product. -/
@[simp]
def primeSpectrumProdOfSum : Sum (PrimeSpectrum R) (PrimeSpectrum S) → PrimeSpectrum (R × S)
  | Sum.inl ⟨I, hI⟩ => ⟨Ideal.prod I ⊤, Ideal.isPrimeIdealProdTop⟩
  | Sum.inr ⟨J, hJ⟩ => ⟨Ideal.prod ⊤ J, Ideal.isPrimeIdealProdTop'⟩
#align prime_spectrum.prime_spectrum_prod_of_sum PrimeSpectrum.primeSpectrumProdOfSum

/-- The prime spectrum of `R × S` is in bijection with the disjoint unions of the prime spectrum of
`R` and the prime spectrum of `S`. -/
noncomputable def primeSpectrumProd :
    PrimeSpectrum (R × S) ≃ Sum (PrimeSpectrum R) (PrimeSpectrum S) :=
  Equiv.symm <|
    Equiv.ofBijective (primeSpectrumProdOfSum R S)
      (by
        constructor
        · rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;>
            simp only [Ideal.prod.ext_iff, prime_spectrum_prod_of_sum] at h
          · simp only [h]
          · exact False.elim (hI.ne_top h.left)
          · exact False.elim (hJ.ne_top h.right)
          · simp only [h]
        · rintro ⟨I, hI⟩
          rcases(Ideal.ideal_prod_prime I).mp hI with (⟨p, ⟨hp, rfl⟩⟩ | ⟨p, ⟨hp, rfl⟩⟩)
          · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
          · exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩)
#align prime_spectrum.prime_spectrum_prod PrimeSpectrum.primeSpectrumProd

variable {R S}

@[simp]
theorem prime_spectrum_prod_symm_inl_as_ideal (x : PrimeSpectrum R) :
    ((primeSpectrumProd R S).symm <| Sum.inl x).asIdeal = Ideal.prod x.asIdeal ⊤ :=
  by
  cases x
  rfl
#align
  prime_spectrum.prime_spectrum_prod_symm_inl_as_ideal PrimeSpectrum.prime_spectrum_prod_symm_inl_as_ideal

@[simp]
theorem prime_spectrum_prod_symm_inr_as_ideal (x : PrimeSpectrum S) :
    ((primeSpectrumProd R S).symm <| Sum.inr x).asIdeal = Ideal.prod ⊤ x.asIdeal :=
  by
  cases x
  rfl
#align
  prime_spectrum.prime_spectrum_prod_symm_inr_as_ideal PrimeSpectrum.prime_spectrum_prod_symm_inr_as_ideal

/-- The zero locus of a set `s` of elements of a commutative ring `R` is the set of all prime ideals
of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function on the prime spectrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in the quotient ring
`R` modulo the prime ideal `x`. In this manner, `zero_locus s` is exactly the subset of
`prime_spectrum R` where all "functions" in `s` vanish simultaneously.
-/
def zeroLocus (s : Set R) : Set (PrimeSpectrum R) :=
  { x | s ⊆ x.asIdeal }
#align prime_spectrum.zero_locus PrimeSpectrum.zeroLocus

@[simp]
theorem mem_zero_locus (x : PrimeSpectrum R) (s : Set R) : x ∈ zeroLocus s ↔ s ⊆ x.asIdeal :=
  Iff.rfl
#align prime_spectrum.mem_zero_locus PrimeSpectrum.mem_zero_locus

@[simp]
theorem zero_locus_span (s : Set R) : zeroLocus (Ideal.span s : Set R) = zeroLocus s :=
  by
  ext x
  exact (Submodule.gi R R).gc s x.as_ideal
#align prime_spectrum.zero_locus_span PrimeSpectrum.zero_locus_span

/-- The vanishing ideal of a set `t` of points of the prime spectrum of a commutative ring `R` is
the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function on the prime spectrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in the quotient ring
`R` modulo the prime ideal `x`. In this manner, `vanishing_ideal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishingIdeal (t : Set (PrimeSpectrum R)) : Ideal R :=
  ⨅ (x : PrimeSpectrum R) (h : x ∈ t), x.asIdeal
#align prime_spectrum.vanishing_ideal PrimeSpectrum.vanishingIdeal

theorem coe_vanishing_ideal (t : Set (PrimeSpectrum R)) :
    (vanishingIdeal t : Set R) = { f : R | ∀ x : PrimeSpectrum R, x ∈ t → f ∈ x.asIdeal } :=
  by
  ext f
  rw [vanishing_ideal, SetLike.mem_coe, Submodule.mem_infi]
  apply forall_congr'; intro x
  rw [Submodule.mem_infi]
#align prime_spectrum.coe_vanishing_ideal PrimeSpectrum.coe_vanishing_ideal

theorem mem_vanishing_ideal (t : Set (PrimeSpectrum R)) (f : R) :
    f ∈ vanishingIdeal t ↔ ∀ x : PrimeSpectrum R, x ∈ t → f ∈ x.asIdeal := by
  rw [← SetLike.mem_coe, coe_vanishing_ideal, Set.mem_setOf_eq]
#align prime_spectrum.mem_vanishing_ideal PrimeSpectrum.mem_vanishing_ideal

@[simp]
theorem vanishing_ideal_singleton (x : PrimeSpectrum R) :
    vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal := by simp [vanishing_ideal]
#align prime_spectrum.vanishing_ideal_singleton PrimeSpectrum.vanishing_ideal_singleton

theorem subset_zero_locus_iff_le_vanishing_ideal (t : Set (PrimeSpectrum R)) (I : Ideal R) :
    t ⊆ zeroLocus I ↔ I ≤ vanishingIdeal t :=
  ⟨fun h f k => (mem_vanishing_ideal _ _).mpr fun x j => (mem_zero_locus _ _).mpr (h j) k, fun h =>
    fun x j =>
    (mem_zero_locus _ _).mpr (le_trans h fun f h => ((mem_vanishing_ideal _ _).mp h) x j)⟩
#align
  prime_spectrum.subset_zero_locus_iff_le_vanishing_ideal PrimeSpectrum.subset_zero_locus_iff_le_vanishing_ideal

section Gc

variable (R)

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc :
    @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => zeroLocus I) fun t =>
      vanishingIdeal t :=
  fun I t => subset_zero_locus_iff_le_vanishing_ideal t I
#align prime_spectrum.gc PrimeSpectrum.gc

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc_set :
    @GaloisConnection (Set R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t =>
      vanishingIdeal t :=
  by
  have ideal_gc : GaloisConnection Ideal.span coe := (Submodule.gi R R).gc
  simpa [zero_locus_span, Function.comp] using ideal_gc.compose (gc R)
#align prime_spectrum.gc_set PrimeSpectrum.gc_set

theorem subset_zero_locus_iff_subset_vanishing_ideal (t : Set (PrimeSpectrum R)) (s : Set R) :
    t ⊆ zeroLocus s ↔ s ⊆ vanishingIdeal t :=
  (gc_set R) s t
#align
  prime_spectrum.subset_zero_locus_iff_subset_vanishing_ideal PrimeSpectrum.subset_zero_locus_iff_subset_vanishing_ideal

end Gc

theorem subset_vanishing_ideal_zero_locus (s : Set R) : s ⊆ vanishingIdeal (zeroLocus s) :=
  (gc_set R).le_u_l s
#align
  prime_spectrum.subset_vanishing_ideal_zero_locus PrimeSpectrum.subset_vanishing_ideal_zero_locus

theorem le_vanishing_ideal_zero_locus (I : Ideal R) : I ≤ vanishingIdeal (zeroLocus I) :=
  (gc R).le_u_l I
#align prime_spectrum.le_vanishing_ideal_zero_locus PrimeSpectrum.le_vanishing_ideal_zero_locus

@[simp]
theorem vanishing_ideal_zero_locus_eq_radical (I : Ideal R) :
    vanishingIdeal (zeroLocus (I : Set R)) = I.radical :=
  Ideal.ext fun f =>
    by
    rw [mem_vanishing_ideal, Ideal.radical_eq_Inf, Submodule.mem_Inf]
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩
#align
  prime_spectrum.vanishing_ideal_zero_locus_eq_radical PrimeSpectrum.vanishing_ideal_zero_locus_eq_radical

@[simp]
theorem zero_locus_radical (I : Ideal R) : zeroLocus (I.radical : Set R) = zeroLocus I :=
  vanishing_ideal_zero_locus_eq_radical I ▸ (gc R).l_u_l_eq_l I
#align prime_spectrum.zero_locus_radical PrimeSpectrum.zero_locus_radical

theorem subset_zero_locus_vanishing_ideal (t : Set (PrimeSpectrum R)) :
    t ⊆ zeroLocus (vanishingIdeal t) :=
  (gc R).l_u_le t
#align
  prime_spectrum.subset_zero_locus_vanishing_ideal PrimeSpectrum.subset_zero_locus_vanishing_ideal

theorem zero_locus_anti_mono {s t : Set R} (h : s ⊆ t) : zeroLocus t ⊆ zeroLocus s :=
  (gc_set R).monotone_l h
#align prime_spectrum.zero_locus_anti_mono PrimeSpectrum.zero_locus_anti_mono

theorem zero_locus_anti_mono_ideal {s t : Ideal R} (h : s ≤ t) :
    zeroLocus (t : Set R) ⊆ zeroLocus (s : Set R) :=
  (gc R).monotone_l h
#align prime_spectrum.zero_locus_anti_mono_ideal PrimeSpectrum.zero_locus_anti_mono_ideal

theorem vanishing_ideal_anti_mono {s t : Set (PrimeSpectrum R)} (h : s ⊆ t) :
    vanishingIdeal t ≤ vanishingIdeal s :=
  (gc R).monotone_u h
#align prime_spectrum.vanishing_ideal_anti_mono PrimeSpectrum.vanishing_ideal_anti_mono

theorem zero_locus_subset_zero_locus_iff (I J : Ideal R) :
    zeroLocus (I : Set R) ⊆ zeroLocus (J : Set R) ↔ J ≤ I.radical :=
  ⟨fun h =>
    Ideal.radical_le_radical_iff.mp
      (vanishing_ideal_zero_locus_eq_radical I ▸
        vanishing_ideal_zero_locus_eq_radical J ▸ vanishing_ideal_anti_mono h),
    fun h => zero_locus_radical I ▸ zero_locus_anti_mono_ideal h⟩
#align
  prime_spectrum.zero_locus_subset_zero_locus_iff PrimeSpectrum.zero_locus_subset_zero_locus_iff

theorem zero_locus_subset_zero_locus_singleton_iff (f g : R) :
    zeroLocus ({f} : Set R) ⊆ zeroLocus {g} ↔ g ∈ (Ideal.span ({f} : Set R)).radical := by
  rw [← zero_locus_span {f}, ← zero_locus_span {g}, zero_locus_subset_zero_locus_iff, Ideal.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe]
#align
  prime_spectrum.zero_locus_subset_zero_locus_singleton_iff PrimeSpectrum.zero_locus_subset_zero_locus_singleton_iff

theorem zero_locus_bot : zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ :=
  (gc R).l_bot
#align prime_spectrum.zero_locus_bot PrimeSpectrum.zero_locus_bot

@[simp]
theorem zero_locus_singleton_zero : zeroLocus ({0} : Set R) = Set.univ :=
  zero_locus_bot
#align prime_spectrum.zero_locus_singleton_zero PrimeSpectrum.zero_locus_singleton_zero

@[simp]
theorem zero_locus_empty : zeroLocus (∅ : Set R) = Set.univ :=
  (gc_set R).l_bot
#align prime_spectrum.zero_locus_empty PrimeSpectrum.zero_locus_empty

@[simp]
theorem vanishing_ideal_univ : vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤ := by
  simpa using (gc R).u_top
#align prime_spectrum.vanishing_ideal_univ PrimeSpectrum.vanishing_ideal_univ

theorem zero_locus_empty_of_one_mem {s : Set R} (h : (1 : R) ∈ s) : zeroLocus s = ∅ :=
  by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x hx
  rw [mem_zero_locus] at hx
  have x_prime : x.as_ideal.is_prime := by infer_instance
  have eq_top : x.as_ideal = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hx h
  apply x_prime.ne_top eq_top
#align prime_spectrum.zero_locus_empty_of_one_mem PrimeSpectrum.zero_locus_empty_of_one_mem

@[simp]
theorem zero_locus_singleton_one : zeroLocus ({1} : Set R) = ∅ :=
  zero_locus_empty_of_one_mem (Set.mem_singleton (1 : R))
#align prime_spectrum.zero_locus_singleton_one PrimeSpectrum.zero_locus_singleton_one

theorem zero_locus_empty_iff_eq_top {I : Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤ :=
  by
  constructor
  · contrapose!
    intro h
    rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
    exact Set.Nonempty.ne_empty ⟨⟨M, hM.is_prime⟩, hIM⟩
  · rintro rfl
    apply zero_locus_empty_of_one_mem
    trivial
#align prime_spectrum.zero_locus_empty_iff_eq_top PrimeSpectrum.zero_locus_empty_iff_eq_top

@[simp]
theorem zero_locus_univ : zeroLocus (Set.univ : Set R) = ∅ :=
  zero_locus_empty_of_one_mem (Set.mem_univ 1)
#align prime_spectrum.zero_locus_univ PrimeSpectrum.zero_locus_univ

theorem vanishing_ideal_eq_top_iff {s : Set (PrimeSpectrum R)} : vanishingIdeal s = ⊤ ↔ s = ∅ := by
  rw [← top_le_iff, ← subset_zero_locus_iff_le_vanishing_ideal, Submodule.top_coe, zero_locus_univ,
    Set.subset_empty_iff]
#align prime_spectrum.vanishing_ideal_eq_top_iff PrimeSpectrum.vanishing_ideal_eq_top_iff

theorem zero_locus_sup (I J : Ideal R) :
    zeroLocus ((I ⊔ J : Ideal R) : Set R) = zeroLocus I ∩ zeroLocus J :=
  (gc R).l_sup
#align prime_spectrum.zero_locus_sup PrimeSpectrum.zero_locus_sup

theorem zero_locus_union (s s' : Set R) : zeroLocus (s ∪ s') = zeroLocus s ∩ zeroLocus s' :=
  (gc_set R).l_sup
#align prime_spectrum.zero_locus_union PrimeSpectrum.zero_locus_union

theorem vanishing_ideal_union (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal (t ∪ t') = vanishingIdeal t ⊓ vanishingIdeal t' :=
  (gc R).u_inf
#align prime_spectrum.vanishing_ideal_union PrimeSpectrum.vanishing_ideal_union

theorem zero_locus_supr {ι : Sort _} (I : ι → Ideal R) :
    zeroLocus ((⨆ i, I i : Ideal R) : Set R) = ⋂ i, zeroLocus (I i) :=
  (gc R).l_supr
#align prime_spectrum.zero_locus_supr PrimeSpectrum.zero_locus_supr

theorem zero_locus_Union {ι : Sort _} (s : ι → Set R) :
    zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i) :=
  (gc_set R).l_supr
#align prime_spectrum.zero_locus_Union PrimeSpectrum.zero_locus_Union

theorem zero_locus_bUnion (s : Set (Set R)) :
    zeroLocus (⋃ s' ∈ s, s' : Set R) = ⋂ s' ∈ s, zeroLocus s' := by simp only [zero_locus_Union]
#align prime_spectrum.zero_locus_bUnion PrimeSpectrum.zero_locus_bUnion

theorem vanishing_ideal_Union {ι : Sort _} (t : ι → Set (PrimeSpectrum R)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  (gc R).u_infi
#align prime_spectrum.vanishing_ideal_Union PrimeSpectrum.vanishing_ideal_Union

theorem zero_locus_inf (I J : Ideal R) :
    zeroLocus ((I ⊓ J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.inf_le
#align prime_spectrum.zero_locus_inf PrimeSpectrum.zero_locus_inf

theorem union_zero_locus (s s' : Set R) :
    zeroLocus s ∪ zeroLocus s' = zeroLocus (Ideal.span s ⊓ Ideal.span s' : Ideal R) :=
  by
  rw [zero_locus_inf]
  simp
#align prime_spectrum.union_zero_locus PrimeSpectrum.union_zero_locus

theorem zero_locus_mul (I J : Ideal R) :
    zeroLocus ((I * J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.mul_le
#align prime_spectrum.zero_locus_mul PrimeSpectrum.zero_locus_mul

theorem zero_locus_singleton_mul (f g : R) :
    zeroLocus ({f * g} : Set R) = zeroLocus {f} ∪ zeroLocus {g} :=
  Set.ext fun x => by simpa using x.2.mul_mem_iff_mem_or_mem
#align prime_spectrum.zero_locus_singleton_mul PrimeSpectrum.zero_locus_singleton_mul

@[simp]
theorem zero_locus_pow (I : Ideal R) {n : ℕ} (hn : 0 < n) :
    zeroLocus ((I ^ n : Ideal R) : Set R) = zeroLocus I :=
  zero_locus_radical (I ^ n) ▸ (I.radical_pow n hn).symm ▸ zero_locus_radical I
#align prime_spectrum.zero_locus_pow PrimeSpectrum.zero_locus_pow

@[simp]
theorem zero_locus_singleton_pow (f : R) (n : ℕ) (hn : 0 < n) :
    zeroLocus ({f ^ n} : Set R) = zeroLocus {f} :=
  Set.ext fun x => by simpa using x.2.pow_mem_iff_mem n hn
#align prime_spectrum.zero_locus_singleton_pow PrimeSpectrum.zero_locus_singleton_pow

theorem sup_vanishing_ideal_le (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal t ⊔ vanishingIdeal t' ≤ vanishingIdeal (t ∩ t') :=
  by
  intro r
  rw [Submodule.mem_sup, mem_vanishing_ideal]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [mem_vanishing_ideal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim
#align prime_spectrum.sup_vanishing_ideal_le PrimeSpectrum.sup_vanishing_ideal_le

theorem mem_compl_zero_locus_iff_not_mem {f : R} {I : PrimeSpectrum R} :
    I ∈ (zeroLocus {f} : Set (PrimeSpectrum R))ᶜ ↔ f ∉ I.asIdeal := by
  rw [Set.mem_compl_iff, mem_zero_locus, Set.singleton_subset_iff] <;> rfl
#align
  prime_spectrum.mem_compl_zero_locus_iff_not_mem PrimeSpectrum.mem_compl_zero_locus_iff_not_mem

/-- The Zariski topology on the prime spectrum of a commutative ring is defined via the closed sets
of the topology: they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariskiTopology : TopologicalSpace (PrimeSpectrum R) :=
  TopologicalSpace.ofClosed (Set.range PrimeSpectrum.zeroLocus) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.interₛ_eq_interᵢ]
      choose f hf using fun i : Zs => h i.Prop
      simp only [← hf]
      exact ⟨_, zero_locus_Union _⟩)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zero_locus s t).symm⟩)
#align prime_spectrum.zariski_topology PrimeSpectrum.zariskiTopology

theorem is_open_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ ∃ s, Uᶜ = zeroLocus s := by
  simp only [@eq_comm _ (Uᶜ)] <;> rfl
#align prime_spectrum.is_open_iff PrimeSpectrum.is_open_iff

theorem is_closed_iff_zero_locus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ∃ s, Z = zeroLocus s :=
  by rw [← is_open_compl_iff, is_open_iff, compl_compl]
#align prime_spectrum.is_closed_iff_zero_locus PrimeSpectrum.is_closed_iff_zero_locus

theorem is_closed_iff_zero_locus_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, Z = zeroLocus I :=
  (is_closed_iff_zero_locus _).trans
    ⟨fun ⟨s, hs⟩ => ⟨_, (zero_locus_span s).substr hs⟩, fun ⟨I, hI⟩ => ⟨I, hI⟩⟩
#align prime_spectrum.is_closed_iff_zero_locus_ideal PrimeSpectrum.is_closed_iff_zero_locus_ideal

theorem is_closed_iff_zero_locus_radical_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, I.IsRadical ∧ Z = zeroLocus I :=
  (is_closed_iff_zero_locus_ideal _).trans
    ⟨fun ⟨I, hI⟩ => ⟨_, I.radical_is_radical, (zero_locus_radical I).substr hI⟩, fun ⟨I, _, hI⟩ =>
      ⟨I, hI⟩⟩
#align
  prime_spectrum.is_closed_iff_zero_locus_radical_ideal PrimeSpectrum.is_closed_iff_zero_locus_radical_ideal

theorem is_closed_zero_locus (s : Set R) : IsClosed (zeroLocus s) :=
  by
  rw [is_closed_iff_zero_locus]
  exact ⟨s, rfl⟩
#align prime_spectrum.is_closed_zero_locus PrimeSpectrum.is_closed_zero_locus

theorem is_closed_singleton_iff_is_maximal (x : PrimeSpectrum R) :
    IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal :=
  by
  refine' (is_closed_iff_zero_locus _).trans ⟨fun h => _, fun h => _⟩
  · obtain ⟨s, hs⟩ := h
    rw [eq_comm, Set.eq_singleton_iff_unique_mem] at hs
    refine'
      ⟨⟨x.2.1, fun I hI =>
          not_not.1
            (mt (Ideal.exists_le_maximal I) <| not_exists.2 fun J => not_and.2 fun hJ hIJ => _)⟩⟩
    exact
      ne_of_lt (lt_of_lt_of_le hI hIJ)
        (symm <|
          congr_arg PrimeSpectrum.asIdeal
            (hs.2 ⟨J, hJ.is_prime⟩ fun r hr => hIJ (le_of_lt hI <| hs.1 hr)))
  · refine' ⟨x.as_ideal.1, _⟩
    rw [eq_comm, Set.eq_singleton_iff_unique_mem]
    refine' ⟨fun _ h => h, fun y hy => PrimeSpectrum.ext _ _ (h.eq_of_le y.2.ne_top hy).symm⟩
#align
  prime_spectrum.is_closed_singleton_iff_is_maximal PrimeSpectrum.is_closed_singleton_iff_is_maximal

theorem zero_locus_vanishing_ideal_eq_closure (t : Set (PrimeSpectrum R)) :
    zeroLocus (vanishingIdeal t : Set R) = closure t :=
  by
  apply Set.Subset.antisymm
  · rintro x hx t' ⟨ht', ht⟩
    obtain ⟨fs, rfl⟩ : ∃ s, t' = zero_locus s := by rwa [is_closed_iff_zero_locus] at ht'
    rw [subset_zero_locus_iff_subset_vanishing_ideal] at ht
    exact Set.Subset.trans ht hx
  · rw [(is_closed_zero_locus _).closure_subset_iff]
    exact subset_zero_locus_vanishing_ideal t
#align
  prime_spectrum.zero_locus_vanishing_ideal_eq_closure PrimeSpectrum.zero_locus_vanishing_ideal_eq_closure

theorem vanishing_ideal_closure (t : Set (PrimeSpectrum R)) :
    vanishingIdeal (closure t) = vanishingIdeal t :=
  zero_locus_vanishing_ideal_eq_closure t ▸ (gc R).u_l_u_eq_u t
#align prime_spectrum.vanishing_ideal_closure PrimeSpectrum.vanishing_ideal_closure

theorem closure_singleton (x) : closure ({x} : Set (PrimeSpectrum R)) = zeroLocus x.asIdeal := by
  rw [← zero_locus_vanishing_ideal_eq_closure, vanishing_ideal_singleton]
#align prime_spectrum.closure_singleton PrimeSpectrum.closure_singleton

theorem is_radical_vanishing_ideal (s : Set (PrimeSpectrum R)) : (vanishingIdeal s).IsRadical :=
  by
  rw [← vanishing_ideal_closure, ← zero_locus_vanishing_ideal_eq_closure,
    vanishing_ideal_zero_locus_eq_radical]
  apply Ideal.radical_is_radical
#align prime_spectrum.is_radical_vanishing_ideal PrimeSpectrum.is_radical_vanishing_ideal

theorem vanishing_ideal_anti_mono_iff {s t : Set (PrimeSpectrum R)} (ht : IsClosed t) :
    s ⊆ t ↔ vanishingIdeal t ≤ vanishingIdeal s :=
  ⟨vanishing_ideal_anti_mono, fun h =>
    by
    rw [← ht.closure_subset_iff, ← ht.closure_eq]
    convert ← zero_locus_anti_mono_ideal h <;> apply zero_locus_vanishing_ideal_eq_closure⟩
#align prime_spectrum.vanishing_ideal_anti_mono_iff PrimeSpectrum.vanishing_ideal_anti_mono_iff

theorem vanishing_ideal_strict_anti_mono_iff {s t : Set (PrimeSpectrum R)} (hs : IsClosed s)
    (ht : IsClosed t) : s ⊂ t ↔ vanishingIdeal t < vanishingIdeal s := by
  rw [Set.ssubset_def, vanishing_ideal_anti_mono_iff hs, vanishing_ideal_anti_mono_iff ht,
    lt_iff_le_not_le]
#align
  prime_spectrum.vanishing_ideal_strict_anti_mono_iff PrimeSpectrum.vanishing_ideal_strict_anti_mono_iff

/-- The antitone order embedding of closed subsets of `Spec R` into ideals of `R`. -/
def closedsEmbedding (R : Type _) [CommRing R] :
    (TopologicalSpace.Closeds <| PrimeSpectrum R)ᵒᵈ ↪o Ideal R :=
  OrderEmbedding.ofMapLeIff (fun s => vanishingIdeal s.ofDual) fun s t =>
    (vanishing_ideal_anti_mono_iff s.2).symm
#align prime_spectrum.closeds_embedding PrimeSpectrum.closedsEmbedding

theorem t1_space_iff_is_field [IsDomain R] : T1Space (PrimeSpectrum R) ↔ IsField R :=
  by
  refine' ⟨_, fun h => _⟩
  · intro h
    have hbot : Ideal.IsPrime (⊥ : Ideal R) := Ideal.botPrime
    exact
      not_not.1
        (mt
          (Ring.ne_bot_of_is_maximal_of_not_is_field <|
            (is_closed_singleton_iff_is_maximal _).1 (T1Space.t1 ⟨⊥, hbot⟩))
          (not_not.2 rfl))
  · refine' ⟨fun x => (is_closed_singleton_iff_is_maximal x).2 _⟩
    by_cases hx : x.as_ideal = ⊥
    · exact hx.symm ▸ @Ideal.botIsMaximal R (@Field.toDivisionRing _ h.to_field)
    · exact absurd h (Ring.not_is_field_iff_exists_prime.2 ⟨x.as_ideal, ⟨hx, x.2⟩⟩)
#align prime_spectrum.t1_space_iff_is_field PrimeSpectrum.t1_space_iff_is_field

-- mathport name: «exprZ( )»
local notation "Z(" a ")" => zeroLocus (a : Set R)

theorem is_irreducible_zero_locus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.IsPrime :=
  by
  rw [Ideal.is_prime_iff, IsIrreducible]
  apply and_congr
  · rw [Set.nonempty_iff_ne_empty, Ne.def, zero_locus_empty_iff_eq_top]
  · trans ∀ x y : Ideal R, Z(I) ⊆ Z(x) ∪ Z(y) → Z(I) ⊆ Z(x) ∨ Z(I) ⊆ Z(y)
    · simp_rw [is_preirreducible_iff_closed_union_closed, is_closed_iff_zero_locus_ideal]
      constructor
      · rintro h x y
        exact h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      · rintro h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact h x y
    · simp_rw [← zero_locus_inf, subset_zero_locus_iff_le_vanishing_ideal,
        vanishing_ideal_zero_locus_eq_radical, hI.radical]
      constructor
      · simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ←
          Ideal.span_singleton_mul_span_singleton]
        refine' fun h x y h' => h _ _ _
        rw [← hI.radical_le_iff] at h'⊢
        simpa only [Ideal.radical_inf, Ideal.radical_mul] using h'
      · simp_rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
        rintro h s t h' ⟨x, hx, hx'⟩ y hy
        exact h (h' ⟨Ideal.mul_mem_right _ _ hx, Ideal.mul_mem_left _ _ hy⟩) hx'
#align
  prime_spectrum.is_irreducible_zero_locus_iff_of_radical PrimeSpectrum.is_irreducible_zero_locus_iff_of_radical

theorem is_irreducible_zero_locus_iff (I : Ideal R) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.radical.IsPrime :=
  zero_locus_radical I ▸ is_irreducible_zero_locus_iff_of_radical _ I.radical_is_radical
#align prime_spectrum.is_irreducible_zero_locus_iff PrimeSpectrum.is_irreducible_zero_locus_iff

theorem is_irreducible_iff_vanishing_ideal_is_prime {s : Set (PrimeSpectrum R)} :
    IsIrreducible s ↔ (vanishingIdeal s).IsPrime := by
  rw [← is_irreducible_iff_closure, ← zero_locus_vanishing_ideal_eq_closure,
    is_irreducible_zero_locus_iff_of_radical _ (is_radical_vanishing_ideal s)]
#align
  prime_spectrum.is_irreducible_iff_vanishing_ideal_is_prime PrimeSpectrum.is_irreducible_iff_vanishing_ideal_is_prime

instance [IsDomain R] : IrreducibleSpace (PrimeSpectrum R) :=
  by
  rw [irreducible_space_def, Set.top_eq_univ, ← zero_locus_bot, is_irreducible_zero_locus_iff]
  simpa using Ideal.botPrime

instance : QuasiSober (PrimeSpectrum R) :=
  ⟨fun S h₁ h₂ =>
    ⟨⟨_, is_irreducible_iff_vanishing_ideal_is_prime.1 h₁⟩, by
      rw [IsGenericPoint, closure_singleton, zero_locus_vanishing_ideal_eq_closure, h₂.closure_eq]⟩⟩

section Comap

variable {S' : Type _} [CommRing S']

theorem preimage_comap_zero_locus_aux (f : R →+* S) (s : Set R) :
    (fun y => ⟨Ideal.comap f y.asIdeal, inferInstance⟩ : PrimeSpectrum S → PrimeSpectrum R) ⁻¹'
        zeroLocus s =
      zeroLocus (f '' s) :=
  by
  ext x
  simp only [mem_zero_locus, Set.image_subset_iff]
  rfl
#align prime_spectrum.preimage_comap_zero_locus_aux PrimeSpectrum.preimage_comap_zero_locus_aux

/-- The function between prime spectra of commutative rings induced by a ring homomorphism.
This function is continuous. -/
def comap (f : R →+* S) : C(PrimeSpectrum S, PrimeSpectrum R)
    where
  toFun y := ⟨Ideal.comap f y.asIdeal, inferInstance⟩
  continuous_to_fun :=
    by
    simp only [continuous_iff_is_closed, is_closed_iff_zero_locus]
    rintro _ ⟨s, rfl⟩
    exact ⟨_, preimage_comap_zero_locus_aux f s⟩
#align prime_spectrum.comap PrimeSpectrum.comap

variable (f : R →+* S)

@[simp]
theorem comap_as_ideal (y : PrimeSpectrum S) : (comap f y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl
#align prime_spectrum.comap_as_ideal PrimeSpectrum.comap_as_ideal

@[simp]
theorem comap_id : comap (RingHom.id R) = ContinuousMap.id _ :=
  by
  ext
  rfl
#align prime_spectrum.comap_id PrimeSpectrum.comap_id

@[simp]
theorem comap_comp (f : R →+* S) (g : S →+* S') : comap (g.comp f) = (comap f).comp (comap g) :=
  rfl
#align prime_spectrum.comap_comp PrimeSpectrum.comap_comp

theorem comap_comp_apply (f : R →+* S) (g : S →+* S') (x : PrimeSpectrum S') :
    PrimeSpectrum.comap (g.comp f) x = (PrimeSpectrum.comap f) (PrimeSpectrum.comap g x) :=
  rfl
#align prime_spectrum.comap_comp_apply PrimeSpectrum.comap_comp_apply

@[simp]
theorem preimage_comap_zero_locus (s : Set R) : comap f ⁻¹' zeroLocus s = zeroLocus (f '' s) :=
  preimage_comap_zero_locus_aux f s
#align prime_spectrum.preimage_comap_zero_locus PrimeSpectrum.preimage_comap_zero_locus

theorem comap_injective_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun x y h =>
  PrimeSpectrum.ext _ _
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (comap f x).asIdeal = (comap f y).asIdeal))
#align prime_spectrum.comap_injective_of_surjective PrimeSpectrum.comap_injective_of_surjective

theorem comap_singleton_is_closed_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  haveI : x.as_ideal.is_maximal := (is_closed_singleton_iff_is_maximal x).1 hx
  (is_closed_singleton_iff_is_maximal _).2 (Ideal.comapIsMaximalOfSurjective f hf)
#align
  prime_spectrum.comap_singleton_is_closed_of_surjective PrimeSpectrum.comap_singleton_is_closed_of_surjective

theorem comap_singleton_is_closed_of_is_integral (f : R →+* S) (hf : f.IsIntegral)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  (is_closed_singleton_iff_is_maximal _).2
    (Ideal.isMaximalComapOfIsIntegralOfIsMaximal' f hf x.asIdeal <|
      (is_closed_singleton_iff_is_maximal x).1 hx)
#align
  prime_spectrum.comap_singleton_is_closed_of_is_integral PrimeSpectrum.comap_singleton_is_closed_of_is_integral

variable (S)

theorem localization_comap_inducing [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Inducing (comap (algebraMap R S)) := by
  constructor
  rw [topological_space_eq_iff]
  intro U
  simp_rw [← is_closed_compl_iff]
  generalize Uᶜ = Z
  simp_rw [is_closed_induced_iff, is_closed_iff_zero_locus]
  constructor
  · rintro ⟨s, rfl⟩
    refine' ⟨_, ⟨algebraMap R S ⁻¹' Ideal.span s, rfl⟩, _⟩
    rw [preimage_comap_zero_locus, ← zero_locus_span, ← zero_locus_span s]
    congr 1
    exact congr_arg Submodule.carrier (IsLocalization.map_comap M S (Ideal.span s))
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    simp
#align prime_spectrum.localization_comap_inducing PrimeSpectrum.localization_comap_inducing

theorem localization_comap_injective [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Function.Injective (comap (algebraMap R S)) :=
  by
  intro p q h
  replace h := congr_arg (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  dsimp only at h
  erw [IsLocalization.map_comap M S, IsLocalization.map_comap M S] at h
  ext1
  exact h
#align prime_spectrum.localization_comap_injective PrimeSpectrum.localization_comap_injective

theorem localization_comap_embedding [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Embedding (comap (algebraMap R S)) :=
  ⟨localization_comap_inducing S M, localization_comap_injective S M⟩
#align prime_spectrum.localization_comap_embedding PrimeSpectrum.localization_comap_embedding

theorem localization_comap_range [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Set.range (comap (algebraMap R S)) = { p | Disjoint (M : Set R) p.asIdeal } :=
  by
  ext x
  constructor
  · simp_rw [disjoint_iff_inf_le]
    rintro ⟨p, rfl⟩ x ⟨hx₁, hx₂⟩
    exact (p.2.1 : ¬_) (p.as_ideal.eq_top_of_is_unit_mem hx₂ (IsLocalization.map_units S ⟨x, hx₁⟩))
  · intro h
    use ⟨x.as_ideal.map (algebraMap R S), IsLocalization.isPrimeOfIsPrimeDisjoint M S _ x.2 h⟩
    ext1
    exact IsLocalization.comap_map_of_is_prime_disjoint M S _ x.2 h
#align prime_spectrum.localization_comap_range PrimeSpectrum.localization_comap_range

section SpecOfSurjective

/-! The comap of a surjective ring homomorphism is a closed embedding between the prime spectra. -/


open Function RingHom

theorem comap_inducing_of_surjective (hf : Surjective f) : Inducing (comap f) :=
  {
    induced :=
      by
      simp_rw [topological_space_eq_iff, ← is_closed_compl_iff, is_closed_induced_iff,
        is_closed_iff_zero_locus]
      refine' fun s =>
        ⟨fun ⟨F, hF⟩ =>
          ⟨zero_locus (f ⁻¹' F), ⟨f ⁻¹' F, rfl⟩, by
            rw [preimage_comap_zero_locus, surjective.image_preimage hf, hF]⟩,
          _⟩
      rintro ⟨-, ⟨F, rfl⟩, hF⟩
      exact ⟨f '' F, hF.symm.trans (preimage_comap_zero_locus f F)⟩ }
#align prime_spectrum.comap_inducing_of_surjective PrimeSpectrum.comap_inducing_of_surjective

theorem image_comap_zero_locus_eq_zero_locus_comap (hf : Surjective f) (I : Ideal S) :
    comap f '' zeroLocus I = zeroLocus (I.comap f) :=
  by
  simp only [Set.ext_iff, Set.mem_image, mem_zero_locus, SetLike.coe_subset_coe]
  refine' fun p => ⟨_, fun h_I_p => _⟩
  · rintro ⟨p, hp, rfl⟩ a ha
    exact hp ha
  · have hp : ker f ≤ p.as_ideal := (Ideal.comap_mono bot_le).trans h_I_p
    refine' ⟨⟨p.as_ideal.map f, Ideal.mapIsPrimeOfSurjective hf hp⟩, fun x hx => _, _⟩
    · obtain ⟨x', rfl⟩ := hf x
      exact Ideal.mem_map_of_mem f (h_I_p hx)
    · ext x
      change f x ∈ p.as_ideal.map f ↔ _
      rw [Ideal.mem_map_iff_of_surjective f hf]
      refine' ⟨_, fun hx => ⟨x, hx, rfl⟩⟩
      rintro ⟨x', hx', heq⟩
      rw [← sub_sub_cancel x' x]
      refine' p.as_ideal.sub_mem hx' (hp _)
      rwa [mem_ker, map_sub, sub_eq_zero]
#align
  prime_spectrum.image_comap_zero_locus_eq_zero_locus_comap PrimeSpectrum.image_comap_zero_locus_eq_zero_locus_comap

theorem range_comap_of_surjective (hf : Surjective f) : Set.range (comap f) = zeroLocus (ker f) :=
  by
  rw [← Set.image_univ]
  convert image_comap_zero_locus_eq_zero_locus_comap _ _ hf _
  rw [zero_locus_bot]
#align prime_spectrum.range_comap_of_surjective PrimeSpectrum.range_comap_of_surjective

theorem is_closed_range_comap_of_surjective (hf : Surjective f) : IsClosed (Set.range (comap f)) :=
  by
  rw [range_comap_of_surjective _ f hf]
  exact is_closed_zero_locus ↑(ker f)
#align
  prime_spectrum.is_closed_range_comap_of_surjective PrimeSpectrum.is_closed_range_comap_of_surjective

theorem closed_embedding_comap_of_surjective (hf : Surjective f) : ClosedEmbedding (comap f) :=
  { induced := (comap_inducing_of_surjective S f hf).induced
    inj := comap_injective_of_surjective f hf
    closed_range := is_closed_range_comap_of_surjective S f hf }
#align
  prime_spectrum.closed_embedding_comap_of_surjective PrimeSpectrum.closed_embedding_comap_of_surjective

end SpecOfSurjective

end Comap

section BasicOpen

/-- `basic_open r` is the open subset containing all prime ideals not containing `r`. -/
def basicOpen (r : R) : TopologicalSpace.Opens (PrimeSpectrum R)
    where
  val := { x | r ∉ x.asIdeal }
  property := ⟨{r}, Set.ext fun x => Set.singleton_subset_iff.trans <| not_not.symm⟩
#align prime_spectrum.basic_open PrimeSpectrum.basicOpen

@[simp]
theorem mem_basic_open (f : R) (x : PrimeSpectrum R) : x ∈ basicOpen f ↔ f ∉ x.asIdeal :=
  Iff.rfl
#align prime_spectrum.mem_basic_open PrimeSpectrum.mem_basic_open

theorem is_open_basic_open {a : R} : IsOpen (basicOpen a : Set (PrimeSpectrum R)) :=
  (basicOpen a).property
#align prime_spectrum.is_open_basic_open PrimeSpectrum.is_open_basic_open

@[simp]
theorem basic_open_eq_zero_locus_compl (r : R) :
    (basicOpen r : Set (PrimeSpectrum R)) = zeroLocus {r}ᶜ :=
  Set.ext fun x => by simpa only [Set.mem_compl_iff, mem_zero_locus, Set.singleton_subset_iff]
#align prime_spectrum.basic_open_eq_zero_locus_compl PrimeSpectrum.basic_open_eq_zero_locus_compl

@[simp]
theorem basic_open_one : basicOpen (1 : R) = ⊤ :=
  TopologicalSpace.Opens.ext <| by simp
#align prime_spectrum.basic_open_one PrimeSpectrum.basic_open_one

@[simp]
theorem basic_open_zero : basicOpen (0 : R) = ⊥ :=
  TopologicalSpace.Opens.ext <| by simp
#align prime_spectrum.basic_open_zero PrimeSpectrum.basic_open_zero

theorem basic_open_le_basic_open_iff (f g : R) :
    basicOpen f ≤ basicOpen g ↔ f ∈ (Ideal.span ({g} : Set R)).radical := by
  rw [TopologicalSpace.Opens.le_def, basic_open_eq_zero_locus_compl, basic_open_eq_zero_locus_compl,
    Set.le_eq_subset, Set.compl_subset_compl, zero_locus_subset_zero_locus_singleton_iff]
#align prime_spectrum.basic_open_le_basic_open_iff PrimeSpectrum.basic_open_le_basic_open_iff

theorem basic_open_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g :=
  TopologicalSpace.Opens.ext <| by simp [zero_locus_singleton_mul]
#align prime_spectrum.basic_open_mul PrimeSpectrum.basic_open_mul

theorem basic_open_mul_le_left (f g : R) : basicOpen (f * g) ≤ basicOpen f :=
  by
  rw [basic_open_mul f g]
  exact inf_le_left
#align prime_spectrum.basic_open_mul_le_left PrimeSpectrum.basic_open_mul_le_left

theorem basic_open_mul_le_right (f g : R) : basicOpen (f * g) ≤ basicOpen g :=
  by
  rw [basic_open_mul f g]
  exact inf_le_right
#align prime_spectrum.basic_open_mul_le_right PrimeSpectrum.basic_open_mul_le_right

@[simp]
theorem basic_open_pow (f : R) (n : ℕ) (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f :=
  TopologicalSpace.Opens.ext <| by simpa using zero_locus_singleton_pow f n hn
#align prime_spectrum.basic_open_pow PrimeSpectrum.basic_open_pow

theorem is_topological_basis_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun r : R => (basicOpen r : Set (PrimeSpectrum R))) :=
  by
  apply TopologicalSpace.is_topological_basis_of_open_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact is_open_basic_open
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U, Set.mem_compl_iff, ← hs, mem_zero_locus, Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine' ⟨basic_open f, ⟨f, rfl⟩, hfp, _⟩
    rw [← Set.compl_subset_compl, ← hs, basic_open_eq_zero_locus_compl, compl_compl]
    exact zero_locus_anti_mono (set.singleton_subset_iff.mpr hfs)
#align
  prime_spectrum.is_topological_basis_basic_opens PrimeSpectrum.is_topological_basis_basic_opens

theorem is_basis_basic_opens : TopologicalSpace.Opens.IsBasis (Set.range (@basicOpen R _)) :=
  by
  unfold TopologicalSpace.Opens.IsBasis
  convert is_topological_basis_basic_opens
  rw [← Set.range_comp]
#align prime_spectrum.is_basis_basic_opens PrimeSpectrum.is_basis_basic_opens

theorem is_compact_basic_open (f : R) : IsCompact (basicOpen f : Set (PrimeSpectrum R)) :=
  is_compact_of_finite_subfamily_closed fun ι Z hZc hZ =>
    by
    let I : ι → Ideal R := fun i => vanishing_ideal (Z i)
    have hI : ∀ i, Z i = zero_locus (I i) := fun i => by
      simpa only [zero_locus_vanishing_ideal_eq_closure] using (hZc i).closure_eq.symm
    rw [basic_open_eq_zero_locus_compl f, Set.inter_comm, ← Set.diff_eq, Set.diff_eq_empty,
      funext hI, ← zero_locus_supr] at hZ
    obtain ⟨n, hn⟩ : f ∈ (⨆ i : ι, I i).radical :=
      by
      rw [← vanishing_ideal_zero_locus_eq_radical]
      apply vanishing_ideal_anti_mono hZ
      exact subset_vanishing_ideal_zero_locus {f} (Set.mem_singleton f)
    rcases Submodule.exists_finset_of_mem_supr I hn with ⟨s, hs⟩
    use s
    -- Using simp_rw here, because `hI` and `zero_locus_supr` need to be applied underneath binders
    simp_rw [basic_open_eq_zero_locus_compl f, Set.inter_comm (zero_locus {f}ᶜ), ← Set.diff_eq,
      Set.diff_eq_empty, hI, ← zero_locus_supr]
    rw [← zero_locus_radical]
    -- this one can't be in `simp_rw` because it would loop
    apply zero_locus_anti_mono
    rw [Set.singleton_subset_iff]
    exact ⟨n, hs⟩
#align prime_spectrum.is_compact_basic_open PrimeSpectrum.is_compact_basic_open

@[simp]
theorem basic_open_eq_bot_iff (f : R) : basicOpen f = ⊥ ↔ IsNilpotent f :=
  by
  rw [← subtype.coe_injective.eq_iff, basic_open_eq_zero_locus_compl]
  simp only [Set.eq_univ_iff_forall, Set.singleton_subset_iff, TopologicalSpace.Opens.coe_bot,
    nilpotent_iff_mem_prime, Set.compl_empty_iff, mem_zero_locus, SetLike.mem_coe]
  exact ⟨fun h I hI => h ⟨I, hI⟩, fun h ⟨I, hI⟩ => h I hI⟩
#align prime_spectrum.basic_open_eq_bot_iff PrimeSpectrum.basic_open_eq_bot_iff

theorem localization_away_comap_range (S : Type v) [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : Set.range (comap (algebraMap R S)) = basicOpen r :=
  by
  rw [localization_comap_range S (Submonoid.powers r)]
  ext
  simp only [mem_zero_locus, basic_open_eq_zero_locus_compl, SetLike.mem_coe, Set.mem_setOf_eq,
    Set.singleton_subset_iff, Set.mem_compl_iff, disjoint_iff_inf_le]
  constructor
  · intro h₁ h₂
    exact h₁ ⟨Submonoid.mem_powers r, h₂⟩
  · rintro h₁ _ ⟨⟨n, rfl⟩, h₃⟩
    exact h₁ (x.2.mem_of_pow_mem _ h₃)
#align prime_spectrum.localization_away_comap_range PrimeSpectrum.localization_away_comap_range

theorem localization_away_open_embedding (S : Type v) [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : OpenEmbedding (comap (algebraMap R S)) :=
  { toEmbedding := localization_comap_embedding S (Submonoid.powers r)
    open_range := by
      rw [localization_away_comap_range S r]
      exact is_open_basic_open }
#align
  prime_spectrum.localization_away_open_embedding PrimeSpectrum.localization_away_open_embedding

end BasicOpen

/-- The prime spectrum of a commutative ring is a compact topological space. -/
instance : CompactSpace (PrimeSpectrum R)
    where is_compact_univ := by
    convert is_compact_basic_open (1 : R)
    rw [basic_open_one]
    rfl

section Order

/-!
## The specialization order

We endow `prime_spectrum R` with a partial order, where `x ≤ y` if and only if `y ∈ closure {x}`.
-/


instance : PartialOrder (PrimeSpectrum R) :=
  PartialOrder.lift asIdeal ext

@[simp]
theorem as_ideal_le_as_ideal (x y : PrimeSpectrum R) : x.asIdeal ≤ y.asIdeal ↔ x ≤ y :=
  Iff.rfl
#align prime_spectrum.as_ideal_le_as_ideal PrimeSpectrum.as_ideal_le_as_ideal

@[simp]
theorem as_ideal_lt_as_ideal (x y : PrimeSpectrum R) : x.asIdeal < y.asIdeal ↔ x < y :=
  Iff.rfl
#align prime_spectrum.as_ideal_lt_as_ideal PrimeSpectrum.as_ideal_lt_as_ideal

theorem le_iff_mem_closure (x y : PrimeSpectrum R) :
    x ≤ y ↔ y ∈ closure ({x} : Set (PrimeSpectrum R)) := by
  rw [← as_ideal_le_as_ideal, ← zero_locus_vanishing_ideal_eq_closure, mem_zero_locus,
    vanishing_ideal_singleton, SetLike.coe_subset_coe]
#align prime_spectrum.le_iff_mem_closure PrimeSpectrum.le_iff_mem_closure

theorem le_iff_specializes (x y : PrimeSpectrum R) : x ≤ y ↔ x ⤳ y :=
  (le_iff_mem_closure x y).trans specializes_iff_mem_closure.symm
#align prime_spectrum.le_iff_specializes PrimeSpectrum.le_iff_specializes

/-- `nhds` as an order embedding. -/
@[simps (config := { fullyApplied := true })]
def nhdsOrderEmbedding : PrimeSpectrum R ↪o Filter (PrimeSpectrum R) :=
  (OrderEmbedding.ofMapLeIff nhds) fun a b => (le_iff_specializes a b).symm
#align prime_spectrum.nhds_order_embedding PrimeSpectrum.nhdsOrderEmbedding

instance : T0Space (PrimeSpectrum R) :=
  ⟨nhdsOrderEmbedding.Injective⟩

end Order

/-- If `x` specializes to `y`, then there is a natural map from the localization of `y` to the
localization of `x`. -/
def localizationMapOfSpecializes {x y : PrimeSpectrum R} (h : x ⤳ y) :
    Localization.AtPrime y.asIdeal →+* Localization.AtPrime x.asIdeal :=
  @IsLocalization.lift _ _ _ _ _ _ _ _ Localization.is_localization
    (algebraMap R (Localization.AtPrime x.asIdeal))
    (by
      rintro ⟨a, ha⟩
      rw [← PrimeSpectrum.le_iff_specializes, ← as_ideal_le_as_ideal, ← SetLike.coe_subset_coe, ←
        Set.compl_subset_compl] at h
      exact (IsLocalization.map_units _ ⟨a, show a ∈ x.as_ideal.prime_compl from h ha⟩ : _))
#align prime_spectrum.localization_map_of_specializes PrimeSpectrum.localizationMapOfSpecializes

end PrimeSpectrum

namespace LocalRing

variable [LocalRing R]

/-- The closed point in the prime spectrum of a local ring. -/
def closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.isMaximal R).IsPrime⟩
#align local_ring.closed_point LocalRing.closedPoint

variable {R}

theorem is_local_ring_hom_iff_comap_closed_point {S : Type v} [CommRing S] [LocalRing S]
    (f : R →+* S) : IsLocalRingHom f ↔ PrimeSpectrum.comap f (closedPoint S) = closedPoint R :=
  by
  rw [(local_hom_tfae f).out 0 4, PrimeSpectrum.ext_iff]
  rfl
#align
  local_ring.is_local_ring_hom_iff_comap_closed_point LocalRing.is_local_ring_hom_iff_comap_closed_point

@[simp]
theorem comap_closed_point {S : Type v} [CommRing S] [LocalRing S] (f : R →+* S)
    [IsLocalRingHom f] : PrimeSpectrum.comap f (closedPoint S) = closedPoint R :=
  (is_local_ring_hom_iff_comap_closed_point f).mp inferInstance
#align local_ring.comap_closed_point LocalRing.comap_closed_point

end LocalRing

