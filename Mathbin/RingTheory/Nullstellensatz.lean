/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma

! This file was ported from Lean 3 source module ring_theory.nullstellensatz
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Jacobson
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.FieldTheory.MvPolynomial
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Basic

/-!
# Nullstellensatz
This file establishes a version of Hilbert's classical Nullstellensatz for `mv_polynomial`s.
The main statement of the theorem is `vanishing_ideal_zero_locus_eq_radical`.

The statement is in terms of new definitions `vanishing_ideal` and `zero_locus`.
Mathlib already has versions of these in terms of the prime spectrum of a ring,
  but those are not well-suited for expressing this result.
Suggestions for better ways to state this theorem or organize things are welcome.

The machinery around `vanishing_ideal` and `zero_locus` is also minimal, I only added lemmas
  directly needed in this proof, since I'm not sure if they are the right approach.
-/


open Ideal

noncomputable section

namespace MvPolynomial

open MvPolynomial

variable {k : Type _} [Field k]

variable {σ : Type _}

/-- Set of points that are zeroes of all polynomials in an ideal -/
def zeroLocus (I : Ideal (MvPolynomial σ k)) : Set (σ → k) :=
  { x : σ → k | ∀ p ∈ I, eval x p = 0 }
#align mv_polynomial.zero_locus MvPolynomial.zeroLocus

@[simp]
theorem mem_zeroLocus_iff {I : Ideal (MvPolynomial σ k)} {x : σ → k} :
    x ∈ zeroLocus I ↔ ∀ p ∈ I, eval x p = 0 :=
  Iff.rfl
#align mv_polynomial.mem_zero_locus_iff MvPolynomial.mem_zeroLocus_iff

theorem zeroLocus_anti_mono {I J : Ideal (MvPolynomial σ k)} (h : I ≤ J) :
    zeroLocus J ≤ zeroLocus I := fun x hx p hp => hx p <| h hp
#align mv_polynomial.zero_locus_anti_mono MvPolynomial.zeroLocus_anti_mono

theorem zeroLocus_bot : zeroLocus (⊥ : Ideal (MvPolynomial σ k)) = ⊤ :=
  eq_top_iff.2 fun x hx p hp => trans (congr_arg (eval x) (mem_bot.1 hp)) (eval x).map_zero
#align mv_polynomial.zero_locus_bot MvPolynomial.zeroLocus_bot

theorem zeroLocus_top : zeroLocus (⊤ : Ideal (MvPolynomial σ k)) = ⊥ :=
  eq_bot_iff.2 fun x hx => one_neZero ((eval x).map_one ▸ hx 1 Submodule.mem_top : (1 : k) = 0)
#align mv_polynomial.zero_locus_top MvPolynomial.zeroLocus_top

/-- Ideal of polynomials with common zeroes at all elements of a set -/
def vanishingIdeal (V : Set (σ → k)) : Ideal (MvPolynomial σ k)
    where
  carrier := { p | ∀ x ∈ V, eval x p = 0 }
  zero_mem' x hx := RingHom.map_zero _
  add_mem' p q hp hq x hx := by simp only [hq x hx, hp x hx, add_zero, RingHom.map_add]
  smul_mem' p q hq x hx := by simp only [hq x hx, Algebra.id.smul_eq_mul, mul_zero, RingHom.map_mul]
#align mv_polynomial.vanishing_ideal MvPolynomial.vanishingIdeal

@[simp]
theorem mem_vanishingIdeal_iff {V : Set (σ → k)} {p : MvPolynomial σ k} :
    p ∈ vanishingIdeal V ↔ ∀ x ∈ V, eval x p = 0 :=
  Iff.rfl
#align mv_polynomial.mem_vanishing_ideal_iff MvPolynomial.mem_vanishingIdeal_iff

theorem vanishingIdeal_anti_mono {A B : Set (σ → k)} (h : A ≤ B) :
    vanishingIdeal B ≤ vanishingIdeal A := fun p hp x hx => hp x <| h hx
#align mv_polynomial.vanishing_ideal_anti_mono MvPolynomial.vanishingIdeal_anti_mono

theorem vanishingIdeal_empty : vanishingIdeal (∅ : Set (σ → k)) = ⊤ :=
  le_antisymm le_top fun p hp x hx => absurd hx (Set.not_mem_empty x)
#align mv_polynomial.vanishing_ideal_empty MvPolynomial.vanishingIdeal_empty

theorem le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    I ≤ vanishingIdeal (zeroLocus I) := fun p hp x hx => hx p hp
#align mv_polynomial.le_vanishing_ideal_zero_locus MvPolynomial.le_vanishingIdeal_zeroLocus

theorem zeroLocus_vanishingIdeal_le (V : Set (σ → k)) : V ≤ zeroLocus (vanishingIdeal V) :=
  fun V hV p hp => hp V hV
#align mv_polynomial.zero_locus_vanishing_ideal_le MvPolynomial.zeroLocus_vanishingIdeal_le

theorem zeroLocus_vanishingIdeal_galoisConnection :
    @GaloisConnection (Ideal (MvPolynomial σ k)) (Set (σ → k))ᵒᵈ _ _ zeroLocus vanishingIdeal :=
  fun I V =>
  ⟨fun h => le_trans (le_vanishingIdeal_zeroLocus I) (vanishingIdeal_anti_mono h), fun h =>
    le_trans (zeroLocus_anti_mono h) (zeroLocus_vanishingIdeal_le V)⟩
#align mv_polynomial.zero_locus_vanishing_ideal_galois_connection MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection

theorem mem_vanishingIdeal_singleton_iff (x : σ → k) (p : MvPolynomial σ k) :
    p ∈ (vanishingIdeal {x} : Ideal (MvPolynomial σ k)) ↔ eval x p = 0 :=
  ⟨fun h => h x rfl, fun hpx y hy => hy.symm ▸ hpx⟩
#align mv_polynomial.mem_vanishing_ideal_singleton_iff MvPolynomial.mem_vanishingIdeal_singleton_iff

instance vanishingIdealSingletonIsMaximal {x : σ → k} :
    (vanishingIdeal {x} : Ideal (MvPolynomial σ k)).IsMaximal :=
  by
  have : MvPolynomial σ k ⧸ vanishing_ideal {x} ≃+* k :=
    RingEquiv.ofBijective
      (Ideal.Quotient.lift _ (eval x) fun p h => (mem_vanishing_ideal_singleton_iff x p).mp h)
      (by
        refine'
          ⟨(injective_iff_map_eq_zero _).mpr fun p hp => _, fun z =>
            ⟨(Ideal.Quotient.mk (vanishing_ideal {x} : Ideal (MvPolynomial σ k))) (C z), by simp⟩⟩
        obtain ⟨q, rfl⟩ := quotient.mk_surjective p
        rwa [Ideal.Quotient.lift_mk, ← mem_vanishing_ideal_singleton_iff, ←
          quotient.eq_zero_iff_mem] at hp)
  rw [← bot_quotient_is_maximal_iff, ring_equiv.bot_maximal_iff this]
  exact bot_is_maximal
#align mv_polynomial.vanishing_ideal_singleton_is_maximal MvPolynomial.vanishingIdealSingletonIsMaximal

theorem radical_le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    I.radical ≤ vanishingIdeal (zeroLocus I) :=
  by
  intro p hp x hx
  rw [← mem_vanishing_ideal_singleton_iff]
  rw [radical_eq_Inf] at hp
  refine'
    (mem_Inf.mp hp)
      ⟨le_trans (le_vanishing_ideal_zero_locus I)
          (vanishing_ideal_anti_mono fun y hy => hy.symm ▸ hx),
        is_maximal.is_prime' _⟩
#align mv_polynomial.radical_le_vanishing_ideal_zero_locus MvPolynomial.radical_le_vanishingIdeal_zeroLocus

/-- The point in the prime spectrum assosiated to a given point -/
def pointToPoint (x : σ → k) : PrimeSpectrum (MvPolynomial σ k) :=
  ⟨(vanishingIdeal {x} : Ideal (MvPolynomial σ k)), by infer_instance⟩
#align mv_polynomial.point_to_point MvPolynomial.pointToPoint

@[simp]
theorem vanishingIdeal_pointToPoint (V : Set (σ → k)) :
    PrimeSpectrum.vanishingIdeal (point_to_point '' V) = MvPolynomial.vanishingIdeal V :=
  le_antisymm
    (fun p hp x hx =>
      (((PrimeSpectrum.mem_vanishingIdeal _ _).1 hp) ⟨vanishingIdeal {x}, by infer_instance⟩
          ⟨x, ⟨hx, rfl⟩⟩)
        x rfl)
    fun p hp =>
    (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun I hI =>
      let ⟨x, hx⟩ := hI
      hx.2 ▸ fun x' hx' => (Set.mem_singleton_iff.1 hx').symm ▸ hp x hx.1
#align mv_polynomial.vanishing_ideal_point_to_point MvPolynomial.vanishingIdeal_pointToPoint

theorem pointToPoint_zeroLocus_le (I : Ideal (MvPolynomial σ k)) :
    point_to_point '' MvPolynomial.zeroLocus I ≤ PrimeSpectrum.zeroLocus ↑I := fun J hJ =>
  let ⟨x, hx⟩ := hJ
  (le_trans (le_vanishingIdeal_zeroLocus I)
      (hx.2 ▸ vanishingIdeal_anti_mono (Set.singleton_subset_iff.2 hx.1)) :
    I ≤ J.asIdeal)
#align mv_polynomial.point_to_point_zero_locus_le MvPolynomial.pointToPoint_zeroLocus_le

variable [IsAlgClosed k] [Finite σ]

theorem isMaximal_iff_eq_vanishingIdeal_singleton (I : Ideal (MvPolynomial σ k)) :
    I.IsMaximal ↔ ∃ x : σ → k, I = vanishingIdeal {x} :=
  by
  cases nonempty_fintype σ
  refine'
    ⟨fun hI => _, fun h =>
      let ⟨x, hx⟩ := h
      hx.symm ▸ MvPolynomial.vanishingIdealSingletonIsMaximal⟩
  letI : I.is_maximal := hI
  letI : Field (MvPolynomial σ k ⧸ I) := quotient.field I
  let ϕ : k →+* MvPolynomial σ k ⧸ I := (Ideal.Quotient.mk I).comp C
  have hϕ : Function.Bijective ϕ :=
    ⟨quotient_mk_comp_C_injective _ _ I hI.ne_top,
      IsAlgClosed.algebra_map_surjective_of_is_integral' ϕ
        (mv_polynomial.comp_C_integral_of_surjective_of_jacobson _ quotient.mk_surjective)⟩
  obtain ⟨φ, hφ⟩ := Function.Surjective.hasRightInverse hϕ.2
  let x : σ → k := fun s => φ ((Ideal.Quotient.mk I) (X s))
  have hx : ∀ s : σ, ϕ (x s) = (Ideal.Quotient.mk I) (X s) := fun s =>
    hφ ((Ideal.Quotient.mk I) (X s))
  refine' ⟨x, (is_maximal.eq_of_le (by infer_instance) hI.ne_top _).symm⟩
  intro p hp
  rw [← quotient.eq_zero_iff_mem, map_mv_polynomial_eq_eval₂ (Ideal.Quotient.mk I) p, eval₂_eq']
  rw [mem_vanishing_ideal_singleton_iff, eval_eq'] at hp
  simpa only [ϕ.map_sum, ϕ.map_mul, ϕ.map_prod, ϕ.map_pow, ϕ.map_zero, hx] using congr_arg ϕ hp
#align mv_polynomial.is_maximal_iff_eq_vanishing_ideal_singleton MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton

/-- Main statement of the Nullstellensatz -/
@[simp]
theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal (MvPolynomial σ k)) :
    vanishingIdeal (zeroLocus I) = I.radical :=
  by
  rw [I.radical_eq_jacobson]
  refine' le_antisymm (le_infₛ _) fun p hp x hx => _
  · rintro J ⟨hJI, hJ⟩
    obtain ⟨x, hx⟩ := (is_maximal_iff_eq_vanishing_ideal_singleton J).1 hJ
    refine' hx.symm ▸ vanishing_ideal_anti_mono fun y hy p hp => _
    rw [← mem_vanishing_ideal_singleton_iff, Set.mem_singleton_iff.1 hy, ← hx]
    refine' hJI hp
  · rw [← mem_vanishing_ideal_singleton_iff x p]
    refine'
      (mem_Inf.mp hp)
        ⟨le_trans (le_vanishing_ideal_zero_locus I)
            (vanishing_ideal_anti_mono fun y hy => hy.symm ▸ hx),
          MvPolynomial.vanishingIdealSingletonIsMaximal⟩
#align mv_polynomial.vanishing_ideal_zero_locus_eq_radical MvPolynomial.vanishingIdeal_zeroLocus_eq_radical

@[simp]
theorem IsPrime.vanishingIdeal_zeroLocus (P : Ideal (MvPolynomial σ k)) [h : P.IsPrime] :
    vanishingIdeal (zeroLocus P) = P :=
  trans (vanishingIdeal_zeroLocus_eq_radical P) h.radical
#align mv_polynomial.is_prime.vanishing_ideal_zero_locus MvPolynomial.IsPrime.vanishingIdeal_zeroLocus

end MvPolynomial

