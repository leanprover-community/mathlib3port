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

noncomputable theory

namespace MvPolynomial

open MvPolynomial

variable{k : Type _}[Field k]

variable{σ : Type _}

/-- Set of points that are zeroes of all polynomials in an ideal -/
def zero_locus (I : Ideal (MvPolynomial σ k)) : Set (σ → k) :=
  { x:σ → k | ∀ p (_ : p ∈ I), eval x p = 0 }

@[simp]
theorem mem_zero_locus_iff {I : Ideal (MvPolynomial σ k)} {x : σ → k} :
  x ∈ zero_locus I ↔ ∀ p (_ : p ∈ I), eval x p = 0 :=
  Iff.rfl

theorem zero_locus_anti_mono {I J : Ideal (MvPolynomial σ k)} (h : I ≤ J) : zero_locus J ≤ zero_locus I :=
  fun x hx p hp => hx p$ h hp

theorem zero_locus_bot : zero_locus (⊥ : Ideal (MvPolynomial σ k)) = ⊤ :=
  eq_top_iff.2 fun x hx p hp => trans (congr_argₓ (eval x) (mem_bot.1 hp)) (eval x).map_zero

theorem zero_locus_top : zero_locus (⊤ : Ideal (MvPolynomial σ k)) = ⊥ :=
  eq_bot_iff.2$ fun x hx => one_ne_zero ((eval x).map_one ▸ hx 1 Submodule.mem_top : (1 : k) = 0)

/-- Ideal of polynomials with common zeroes at all elements of a set -/
def vanishing_ideal (V : Set (σ → k)) : Ideal (MvPolynomial σ k) :=
  { Carrier := { p | ∀ x (_ : x ∈ V), eval x p = 0 }, zero_mem' := fun x hx => RingHom.map_zero _,
    add_mem' :=
      fun p q hp hq x hx =>
        by 
          simp only [hq x hx, hp x hx, add_zeroₓ, RingHom.map_add],
    smul_mem' :=
      fun p q hq x hx =>
        by 
          simp only [hq x hx, Algebra.id.smul_eq_mul, mul_zero, RingHom.map_mul] }

@[simp]
theorem mem_vanishing_ideal_iff {V : Set (σ → k)} {p : MvPolynomial σ k} :
  p ∈ vanishing_ideal V ↔ ∀ x (_ : x ∈ V), eval x p = 0 :=
  Iff.rfl

theorem vanishing_ideal_anti_mono {A B : Set (σ → k)} (h : A ≤ B) : vanishing_ideal B ≤ vanishing_ideal A :=
  fun p hp x hx => hp x$ h hx

theorem vanishing_ideal_empty : vanishing_ideal (∅ : Set (σ → k)) = ⊤ :=
  le_antisymmₓ le_top fun p hp x hx => absurd hx (Set.not_mem_empty x)

theorem le_vanishing_ideal_zero_locus (I : Ideal (MvPolynomial σ k)) : I ≤ vanishing_ideal (zero_locus I) :=
  fun p hp x hx => hx p hp

theorem zero_locus_vanishing_ideal_le (V : Set (σ → k)) : V ≤ zero_locus (vanishing_ideal V) :=
  fun V hV p hp => hp V hV

theorem zero_locus_vanishing_ideal_galois_connection :
  @GaloisConnection (Ideal (MvPolynomial σ k)) (OrderDual (Set (σ → k))) _ _ zero_locus vanishing_ideal :=
  fun I V =>
    ⟨fun h => le_transₓ (le_vanishing_ideal_zero_locus I) (vanishing_ideal_anti_mono h),
      fun h => le_transₓ (zero_locus_anti_mono h) (zero_locus_vanishing_ideal_le V)⟩

theorem mem_vanishing_ideal_singleton_iff (x : σ → k) (p : MvPolynomial σ k) :
  p ∈ (vanishing_ideal {x} : Ideal (MvPolynomial σ k)) ↔ eval x p = 0 :=
  ⟨fun h => h x rfl, fun hpx y hy => hy.symm ▸ hpx⟩

-- error in RingTheory.Nullstellensatz: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance vanishing_ideal_singleton_is_maximal
{x : σ → k} : (vanishing_ideal {x} : ideal (mv_polynomial σ k)).is_maximal :=
begin
  have [] [":", expr «expr ≃+* »((vanishing_ideal {x} : ideal (mv_polynomial σ k)).quotient, k)] [":=", expr ring_equiv.of_bijective (ideal.quotient.lift _ (eval x) (λ
     p
     h, (mem_vanishing_ideal_singleton_iff x p).mp h)) (begin
      refine [expr ⟨(ring_hom.injective_iff _).mpr (λ
         p
         hp, _), λ
        z, ⟨ideal.quotient.mk (vanishing_ideal {x} : ideal (mv_polynomial σ k)) (C z), by simp [] [] [] [] [] []⟩⟩],
      obtain ["⟨", ident q, ",", ident rfl, "⟩", ":=", expr quotient.mk_surjective p],
      rwa ["[", expr ideal.quotient.lift_mk, ",", "<-", expr mem_vanishing_ideal_singleton_iff, ",", "<-", expr quotient.eq_zero_iff_mem, "]"] ["at", ident hp]
    end)],
  rw ["[", "<-", expr bot_quotient_is_maximal_iff, ",", expr ring_equiv.bot_maximal_iff this, "]"] [],
  exact [expr bot_is_maximal]
end

theorem radical_le_vanishing_ideal_zero_locus (I : Ideal (MvPolynomial σ k)) :
  I.radical ≤ vanishing_ideal (zero_locus I) :=
  by 
    intro p hp x hx 
    rw [←mem_vanishing_ideal_singleton_iff]
    rw [radical_eq_Inf] at hp 
    refine'
      (mem_Inf.mp hp)
        ⟨le_transₓ (le_vanishing_ideal_zero_locus I) (vanishing_ideal_anti_mono fun y hy => hy.symm ▸ hx),
          is_maximal.is_prime' _⟩

/-- The point in the prime spectrum assosiated to a given point -/
def point_to_point (x : σ → k) : PrimeSpectrum (MvPolynomial σ k) :=
  ⟨(vanishing_ideal {x} : Ideal (MvPolynomial σ k)),
    by 
      infer_instance⟩

@[simp]
theorem vanishing_ideal_point_to_point (V : Set (σ → k)) :
  PrimeSpectrum.vanishingIdeal (point_to_point '' V) = MvPolynomial.vanishingIdeal V :=
  le_antisymmₓ
    (fun p hp x hx =>
      (((PrimeSpectrum.mem_vanishing_ideal _ _).1 hp)
          ⟨vanishing_ideal {x},
            by 
              infer_instance⟩
          ⟨x, ⟨hx, rfl⟩⟩)
        x rfl)
    fun p hp =>
      (PrimeSpectrum.mem_vanishing_ideal _ _).2
        fun I hI =>
          let ⟨x, hx⟩ := hI 
          hx.2 ▸ fun x' hx' => (Set.mem_singleton_iff.1 hx').symm ▸ hp x hx.1

theorem point_to_point_zero_locus_le (I : Ideal (MvPolynomial σ k)) :
  point_to_point '' MvPolynomial.ZeroLocus I ≤ PrimeSpectrum.ZeroLocus («expr↑ » I) :=
  fun J hJ =>
    let ⟨x, hx⟩ := hJ
    (le_transₓ (le_vanishing_ideal_zero_locus I) (hx.2 ▸ vanishing_ideal_anti_mono (Set.singleton_subset_iff.2 hx.1)) :
    I ≤ J.as_ideal)

variable[IsAlgClosed k][Fintype σ]

-- error in RingTheory.Nullstellensatz: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_maximal_iff_eq_vanishing_ideal_singleton
(I : ideal (mv_polynomial σ k)) : «expr ↔ »(I.is_maximal, «expr∃ , »((x : σ → k), «expr = »(I, vanishing_ideal {x}))) :=
begin
  refine [expr ⟨λ hI, _, λ h, let ⟨x, hx⟩ := h in
    «expr ▸ »(hx.symm, mv_polynomial.vanishing_ideal_singleton_is_maximal)⟩],
  letI [] [":", expr I.is_maximal] [":=", expr hI],
  letI [] [":", expr field I.quotient] [":=", expr quotient.field I],
  let [ident ϕ] [":", expr «expr →+* »(k, I.quotient)] [":=", expr (ideal.quotient.mk I).comp C],
  have [ident hϕ] [":", expr function.bijective ϕ] [":=", expr ⟨quotient_mk_comp_C_injective _ _ I hI.ne_top, is_alg_closed.algebra_map_surjective_of_is_integral' ϕ (mv_polynomial.comp_C_integral_of_surjective_of_jacobson _ quotient.mk_surjective)⟩],
  obtain ["⟨", ident φ, ",", ident hφ, "⟩", ":=", expr function.surjective.has_right_inverse hϕ.2],
  let [ident x] [":", expr σ → k] [":=", expr λ s, φ (ideal.quotient.mk I (X s))],
  have [ident hx] [":", expr ∀
   s : σ, «expr = »(ϕ (x s), ideal.quotient.mk I (X s))] [":=", expr λ s, hφ (ideal.quotient.mk I (X s))],
  refine [expr ⟨x, (is_maximal.eq_of_le (by apply_instance) hI.ne_top _).symm⟩],
  intros [ident p, ident hp],
  rw ["[", "<-", expr quotient.eq_zero_iff_mem, ",", expr map_mv_polynomial_eq_eval₂ (ideal.quotient.mk I) p, ",", expr eval₂_eq', "]"] [],
  rw ["[", expr mem_vanishing_ideal_singleton_iff, ",", expr eval_eq', "]"] ["at", ident hp],
  convert [] [expr trans (congr_arg ϕ hp) ϕ.map_zero] [],
  simp [] [] ["only"] ["[", expr ϕ.map_sum, ",", expr ϕ.map_mul, ",", expr ϕ.map_prod, ",", expr ϕ.map_pow, ",", expr hx, "]"] [] []
end

/-- Main statement of the Nullstellensatz -/
@[simp]
theorem vanishing_ideal_zero_locus_eq_radical (I : Ideal (MvPolynomial σ k)) :
  vanishing_ideal (zero_locus I) = I.radical :=
  by 
    rw [I.radical_eq_jacobson]
    refine' le_antisymmₓ (le_Inf _) fun p hp x hx => _
    ·
      rintro J ⟨hJI, hJ⟩
      obtain ⟨x, hx⟩ := (is_maximal_iff_eq_vanishing_ideal_singleton J).1 hJ 
      refine' hx.symm ▸ vanishing_ideal_anti_mono fun y hy p hp => _ 
      rw [←mem_vanishing_ideal_singleton_iff, Set.mem_singleton_iff.1 hy, ←hx]
      refine' hJI hp
    ·
      rw [←mem_vanishing_ideal_singleton_iff x p]
      refine'
        (mem_Inf.mp hp)
          ⟨le_transₓ (le_vanishing_ideal_zero_locus I) (vanishing_ideal_anti_mono fun y hy => hy.symm ▸ hx),
            MvPolynomial.vanishing_ideal_singleton_is_maximal⟩

@[simp]
theorem is_prime.vanishing_ideal_zero_locus (P : Ideal (MvPolynomial σ k)) [h : P.is_prime] :
  vanishing_ideal (zero_locus P) = P :=
  trans (vanishing_ideal_zero_locus_eq_radical P) h.radical

end MvPolynomial

