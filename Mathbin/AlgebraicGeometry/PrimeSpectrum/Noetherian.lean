/-
Copyright (c) 2020 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.prime_spectrum.noetherian
! leanprover-community/mathlib commit 052f6013363326d50cb99c6939814a4b8eb7b301
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathbin.Topology.NoetherianSpace

/-!
This file proves additional properties of the prime spectrum a ring is Noetherian.
-/


universe u v

namespace PrimeSpectrum

open Submodule

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/- warning: prime_spectrum.exists_prime_spectrum_prod_le -> PrimeSpectrum.exists_primeSpectrum_prod_le is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] [_inst_2 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] (I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))), Exists.{succ u1} (Multiset.{u1} (PrimeSpectrum.{u1} R _inst_1)) (fun (Z : Multiset.{u1} (PrimeSpectrum.{u1} R _inst_1)) => LE.le.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Preorder.toHasLe.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (Multiset.prod.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (CommSemiring.toCommMonoid.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (IdemCommSemiring.toCommSemiring.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.idemCommSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (Multiset.map.{u1, u1} (PrimeSpectrum.{u1} R _inst_1) (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (PrimeSpectrum.asIdeal.{u1} R _inst_1) Z)) I)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] [_inst_2 : IsNoetherianRing.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] (I : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))), Exists.{succ u1} (Multiset.{u1} (PrimeSpectrum.{u1} R _inst_1)) (fun (Z : Multiset.{u1} (PrimeSpectrum.{u1} R _inst_1)) => LE.le.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Preorder.toLE.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))))) (Multiset.prod.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (CommSemiring.toCommMonoid.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemCommSemiring.toCommSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (Multiset.map.{u1, u1} (PrimeSpectrum.{u1} R _inst_1) (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (PrimeSpectrum.asIdeal.{u1} R _inst_1) Z)) I)
Case conversion may be inaccurate. Consider using '#align prime_spectrum.exists_prime_spectrum_prod_le PrimeSpectrum.exists_primeSpectrum_prod_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (z «expr ∉ » M) -/
/-- In a noetherian ring, every ideal contains a product of prime ideals
([samuel, § 3.3, Lemma 3])-/
theorem exists_primeSpectrum_prod_le (I : Ideal R) :
    ∃ Z : Multiset (PrimeSpectrum R), Multiset.prod (Z.map asIdeal) ≤ I :=
  by
  refine' IsNoetherian.induction (fun (M : Ideal R) hgt => _) I
  by_cases h_prM : M.is_prime
  · use {⟨M, h_prM⟩}
    rw [Multiset.map_singleton, Multiset.prod_singleton]
    exact le_rfl
  by_cases htop : M = ⊤
  · rw [htop]
    exact ⟨0, le_top⟩
  have lt_add : ∀ (z) (_ : z ∉ M), M < M + span R {z} :=
    by
    intro z hz
    refine' lt_of_le_of_ne le_sup_left fun m_eq => hz _
    rw [m_eq]
    exact Ideal.mem_sup_right (mem_span_singleton_self z)
  obtain ⟨x, hx, y, hy, hxy⟩ := (ideal.not_is_prime_iff.mp h_prM).resolve_left htop
  obtain ⟨Wx, h_Wx⟩ := hgt (M + span R {x}) (lt_add _ hx)
  obtain ⟨Wy, h_Wy⟩ := hgt (M + span R {y}) (lt_add _ hy)
  use Wx + Wy
  rw [Multiset.map_add, Multiset.prod_add]
  apply le_trans (Submodule.mul_le_mul h_Wx h_Wy)
  rw [add_mul]
  apply sup_le (show M * (M + span R {y}) ≤ M from Ideal.mul_le_right)
  rw [mul_add]
  apply sup_le (show span R {x} * M ≤ M from Ideal.mul_le_left)
  rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]
#align prime_spectrum.exists_prime_spectrum_prod_le PrimeSpectrum.exists_primeSpectrum_prod_le

/- warning: prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain -> PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_3 : CommRing.{u1} A] [_inst_4 : IsDomain.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))] [_inst_5 : IsNoetherianRing.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))], (Not (IsField.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3)))) -> (forall {I : Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))}, (Ne.{succ u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) I (Bot.bot.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (Submodule.hasBot.{u1, u1} A A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))))) (Semiring.toModule.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3)))))) -> (Exists.{succ u1} (Multiset.{u1} (PrimeSpectrum.{u1} A _inst_3)) (fun (Z : Multiset.{u1} (PrimeSpectrum.{u1} A _inst_3)) => And (LE.le.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (Preorder.toHasLe.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) A (Submodule.setLike.{u1, u1} A A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))))) (Semiring.toModule.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))))))) (Multiset.prod.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (CommSemiring.toCommMonoid.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (IdemCommSemiring.toCommSemiring.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (Ideal.idemCommSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)))) (Multiset.map.{u1, u1} (PrimeSpectrum.{u1} A _inst_3) (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (PrimeSpectrum.asIdeal.{u1} A _inst_3) Z)) I) (Ne.{succ u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (Multiset.prod.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (CommSemiring.toCommMonoid.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (IdemCommSemiring.toCommSemiring.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (Ideal.idemCommSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)))) (Multiset.map.{u1, u1} (PrimeSpectrum.{u1} A _inst_3) (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (PrimeSpectrum.asIdeal.{u1} A _inst_3) Z)) (Bot.bot.{u1} (Ideal.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))) (Submodule.hasBot.{u1, u1} A A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))))) (Semiring.toModule.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3)))))))))
but is expected to have type
  forall {A : Type.{u1}} [_inst_3 : CommRing.{u1} A] [_inst_4 : IsDomain.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))] [_inst_5 : IsNoetherianRing.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))], (Not (IsField.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)))) -> (forall {I : Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))}, (Ne.{succ u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) I (Bot.bot.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (Submodule.instBotSubmodule.{u1, u1} A A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))))) (Semiring.toModule.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)))))) -> (Exists.{succ u1} (Multiset.{u1} (PrimeSpectrum.{u1} A _inst_3)) (fun (Z : Multiset.{u1} (PrimeSpectrum.{u1} A _inst_3)) => And (LE.le.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (Preorder.toLE.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (Submodule.completeLattice.{u1, u1} A A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))))) (Semiring.toModule.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)))))))) (Multiset.prod.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (CommSemiring.toCommMonoid.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (IdemCommSemiring.toCommSemiring.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)))) (Multiset.map.{u1, u1} (PrimeSpectrum.{u1} A _inst_3) (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (PrimeSpectrum.asIdeal.{u1} A _inst_3) Z)) I) (Ne.{succ u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (Multiset.prod.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (CommSemiring.toCommMonoid.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (IdemCommSemiring.toCommSemiring.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)))) (Multiset.map.{u1, u1} (PrimeSpectrum.{u1} A _inst_3) (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (PrimeSpectrum.asIdeal.{u1} A _inst_3) Z)) (Bot.bot.{u1} (Ideal.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))) (Submodule.instBotSubmodule.{u1, u1} A A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3))))) (Semiring.toModule.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3)))))))))
Case conversion may be inaccurate. Consider using '#align prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domainₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (z «expr ∉ » M) -/
/-- In a noetherian integral domain which is not a field, every non-zero ideal contains a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal containing only 0 as
  product or prime ideals ([samuel, § 3.3, Lemma 3]) -/
theorem exists_primeSpectrum_prod_le_and_ne_bot_of_domain (h_fA : ¬IsField A) {I : Ideal A}
    (h_nzI : I ≠ ⊥) :
    ∃ Z : Multiset (PrimeSpectrum A),
      Multiset.prod (Z.map asIdeal) ≤ I ∧ Multiset.prod (Z.map asIdeal) ≠ ⊥ :=
  by
  revert h_nzI
  refine' IsNoetherian.induction (fun (M : Ideal A) hgt => _) I
  intro h_nzM
  have hA_nont : Nontrivial A
  apply IsDomain.to_nontrivial A
  by_cases h_topM : M = ⊤
  · rcases h_topM with rfl
    obtain ⟨p_id, h_nzp, h_pp⟩ : ∃ p : Ideal A, p ≠ ⊥ ∧ p.IsPrime := by
      apply ring.not_is_field_iff_exists_prime.mp h_fA
    use ({⟨p_id, h_pp⟩} : Multiset (PrimeSpectrum A)), le_top
    rwa [Multiset.map_singleton, Multiset.prod_singleton]
  by_cases h_prM : M.is_prime
  · use ({⟨M, h_prM⟩} : Multiset (PrimeSpectrum A))
    rw [Multiset.map_singleton, Multiset.prod_singleton]
    exact ⟨le_rfl, h_nzM⟩
  obtain ⟨x, hx, y, hy, h_xy⟩ := (ideal.not_is_prime_iff.mp h_prM).resolve_left h_topM
  have lt_add : ∀ (z) (_ : z ∉ M), M < M + span A {z} :=
    by
    intro z hz
    refine' lt_of_le_of_ne le_sup_left fun m_eq => hz _
    rw [m_eq]
    exact mem_sup_right (mem_span_singleton_self z)
  obtain ⟨Wx, h_Wx_le, h_Wx_ne⟩ := hgt (M + span A {x}) (lt_add _ hx) (ne_bot_of_gt (lt_add _ hx))
  obtain ⟨Wy, h_Wy_le, h_Wx_ne⟩ := hgt (M + span A {y}) (lt_add _ hy) (ne_bot_of_gt (lt_add _ hy))
  use Wx + Wy
  rw [Multiset.map_add, Multiset.prod_add]
  refine' ⟨le_trans (Submodule.mul_le_mul h_Wx_le h_Wy_le) _, mt ideal.mul_eq_bot.mp _⟩
  · rw [add_mul]
    apply sup_le (show M * (M + span A {y}) ≤ M from Ideal.mul_le_right)
    rw [mul_add]
    apply sup_le (show span A {x} * M ≤ M from Ideal.mul_le_left)
    rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]
  · rintro (hx | hy) <;> contradiction
#align prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain

open TopologicalSpace

instance : NoetherianSpace (PrimeSpectrum R) :=
  by
  rw [(noetherian_space_tfae <| PrimeSpectrum R).out 0 1]
  have H := ‹IsNoetherianRing R›
  rw [isNoetherianRing_iff, isNoetherian_iff_wellFounded] at H
  exact (closeds_embedding R).dual.WellFounded H

end PrimeSpectrum

