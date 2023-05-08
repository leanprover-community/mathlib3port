/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.ideal.associated_prime
! leanprover-community/mathlib commit b5ad141426bb005414324f89719c77c0aa3ec612
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Span
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.RingTheory.Ideal.QuotientOperations
import Mathbin.RingTheory.Noetherian

/-!

# Associated primes of a module

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide the definition and related lemmas about associated primes of modules.

## Main definition
- `is_associated_prime`: `is_associated_prime I M` if the prime ideal `I` is the
  annihilator of some `x : M`.
- `associated_primes`: The set of associated primes of a module.

## Main results
- `exists_le_is_associated_prime_of_is_noetherian_ring`: In a noetherian ring, any `ann(x)` is
  contained in an associated prime for `x ≠ 0`.
- `associated_primes.eq_singleton_of_is_primary`: In a noetherian ring, `I.radical` is the only
  associated prime of `R ⧸ I` when `I` is primary.

## Todo

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

-/


variable {R : Type _} [CommRing R] (I J : Ideal R) (M : Type _) [AddCommGroup M] [Module R M]

#print IsAssociatedPrime /-
/-- `is_associated_prime I M` if the prime ideal `I` is the annihilator of some `x : M`. -/
def IsAssociatedPrime : Prop :=
  I.IsPrime ∧ ∃ x : M, I = (R ∙ x).annihilator
#align is_associated_prime IsAssociatedPrime
-/

variable (R)

#print associatedPrimes /-
/-- The set of associated primes of a module. -/
def associatedPrimes : Set (Ideal R) :=
  { I | IsAssociatedPrime I M }
#align associated_primes associatedPrimes
-/

variable {I J M R} (h : IsAssociatedPrime I M)

variable {M' : Type _} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')

/- warning: associate_primes.mem_iff -> AssociatePrimes.mem_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)], Iff (Membership.Mem.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Set.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Set.hasMem.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) I (associatedPrimes.{u1, u2} R _inst_1 M _inst_2 _inst_3)) (IsAssociatedPrime.{u1, u2} R _inst_1 I M _inst_2 _inst_3)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {I : Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))} {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)], Iff (Membership.mem.{u2, u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Set.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))) (Set.instMembershipSet.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))) I (associatedPrimes.{u2, u1} R _inst_1 M _inst_2 _inst_3)) (IsAssociatedPrime.{u2, u1} R _inst_1 I M _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align associate_primes.mem_iff AssociatePrimes.mem_iffₓ'. -/
theorem AssociatePrimes.mem_iff : I ∈ associatedPrimes R M ↔ IsAssociatedPrime I M :=
  Iff.rfl
#align associate_primes.mem_iff AssociatePrimes.mem_iff

/- warning: is_associated_prime.is_prime -> IsAssociatedPrime.isPrime is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)], (IsAssociatedPrime.{u1, u2} R _inst_1 I M _inst_2 _inst_3) -> (Ideal.IsPrime.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) I)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {I : Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))} {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)], (IsAssociatedPrime.{u2, u1} R _inst_1 I M _inst_2 _inst_3) -> (Ideal.IsPrime.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) I)
Case conversion may be inaccurate. Consider using '#align is_associated_prime.is_prime IsAssociatedPrime.isPrimeₓ'. -/
theorem IsAssociatedPrime.isPrime : I.IsPrime :=
  h.1
#align is_associated_prime.is_prime IsAssociatedPrime.isPrime

/- warning: is_associated_prime.map_of_injective -> IsAssociatedPrime.map_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {M' : Type.{u3}} [_inst_4 : AddCommGroup.{u3} M'] [_inst_5 : Module.{u1, u3} R M' (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4)] (f : LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5), (IsAssociatedPrime.{u1, u2} R _inst_1 I M _inst_2 _inst_3) -> (Function.Injective.{succ u2, succ u3} M M' (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5) (fun (_x : LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5) => M -> M') (LinearMap.hasCoeToFun.{u1, u1, u2, u3} R R M M' (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) f)) -> (IsAssociatedPrime.{u1, u3} R _inst_1 I M' _inst_4 _inst_5)
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommRing.{u3} R] {I : Ideal.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))} {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u3, u2} R M (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {M' : Type.{u1}} [_inst_4 : AddCommGroup.{u1} M'] [_inst_5 : Module.{u3, u1} R M' (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M' _inst_4)] (f : LinearMap.{u3, u3, u2, u1} R R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M' _inst_4) _inst_3 _inst_5), (IsAssociatedPrime.{u3, u2} R _inst_1 I M _inst_2 _inst_3) -> (Function.Injective.{succ u2, succ u1} M M' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LinearMap.{u3, u3, u2, u1} R R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M' _inst_4) _inst_3 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => M') _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u2, u1} R R M M' (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M' _inst_4) _inst_3 _inst_5 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))))) f)) -> (IsAssociatedPrime.{u3, u1} R _inst_1 I M' _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align is_associated_prime.map_of_injective IsAssociatedPrime.map_of_injectiveₓ'. -/
theorem IsAssociatedPrime.map_of_injective (h : IsAssociatedPrime I M) (hf : Function.Injective f) :
    IsAssociatedPrime I M' := by
  obtain ⟨x, rfl⟩ := h.2
  refine' ⟨h.1, ⟨f x, _⟩⟩
  ext r
  rw [Submodule.mem_annihilator_span_singleton, Submodule.mem_annihilator_span_singleton, ←
    map_smul, ← f.map_zero, hf.eq_iff]
#align is_associated_prime.map_of_injective IsAssociatedPrime.map_of_injective

/- warning: linear_equiv.is_associated_prime_iff -> LinearEquiv.isAssociatedPrime_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {M' : Type.{u3}} [_inst_4 : AddCommGroup.{u3} M'] [_inst_5 : Module.{u1, u3} R M' (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4)], (LinearEquiv.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5) -> (Iff (IsAssociatedPrime.{u1, u2} R _inst_1 I M _inst_2 _inst_3) (IsAssociatedPrime.{u1, u3} R _inst_1 I M' _inst_4 _inst_5))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommRing.{u3} R] {I : Ideal.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))} {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u3, u2} R M (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {M' : Type.{u1}} [_inst_4 : AddCommGroup.{u1} M'] [_inst_5 : Module.{u3, u1} R M' (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M' _inst_4)], (LinearEquiv.{u3, u3, u2, u1} R R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) (RingHomInvPair.ids.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))) (RingHomInvPair.ids.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M' _inst_4) _inst_3 _inst_5) -> (Iff (IsAssociatedPrime.{u3, u2} R _inst_1 I M _inst_2 _inst_3) (IsAssociatedPrime.{u3, u1} R _inst_1 I M' _inst_4 _inst_5))
Case conversion may be inaccurate. Consider using '#align linear_equiv.is_associated_prime_iff LinearEquiv.isAssociatedPrime_iffₓ'. -/
theorem LinearEquiv.isAssociatedPrime_iff (l : M ≃ₗ[R] M') :
    IsAssociatedPrime I M ↔ IsAssociatedPrime I M' :=
  ⟨fun h => h.map_of_injective l l.Injective, fun h => h.map_of_injective l.symm l.symm.Injective⟩
#align linear_equiv.is_associated_prime_iff LinearEquiv.isAssociatedPrime_iff

#print not_isAssociatedPrime_of_subsingleton /-
theorem not_isAssociatedPrime_of_subsingleton [Subsingleton M] : ¬IsAssociatedPrime I M :=
  by
  rintro ⟨hI, x, hx⟩
  apply hI.ne_top
  rwa [Subsingleton.elim x 0, submodule.span_singleton_eq_bot.mpr rfl, Submodule.annihilator_bot] at
    hx
#align not_is_associated_prime_of_subsingleton not_isAssociatedPrime_of_subsingleton
-/

variable (R)

/- warning: exists_le_is_associated_prime_of_is_noetherian_ring -> exists_le_isAssociatedPrime_of_isNoetherianRing is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [H : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] (x : M), (Ne.{succ u2} M x (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))))))))) -> (Exists.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (fun (P : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) => And (IsAssociatedPrime.{u1, u2} R _inst_1 P M _inst_2 _inst_3) (LE.le.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Preorder.toLE.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) (Submodule.annihilator.{u1, u2} R M (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 (Submodule.span.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 (Singleton.singleton.{u2, u2} M (Set.{u2} M) (Set.hasSingleton.{u2} M) x))) P)))
but is expected to have type
  forall (R : Type.{u2}) [_inst_1 : CommRing.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [H : IsNoetherianRing.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))] (x : M), (Ne.{succ u1} M x (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (NegZeroClass.toZero.{u1} M (SubNegZeroMonoid.toNegZeroClass.{u1} M (SubtractionMonoid.toSubNegZeroMonoid.{u1} M (SubtractionCommMonoid.toSubtractionMonoid.{u1} M (AddCommGroup.toDivisionAddCommMonoid.{u1} M _inst_2)))))))) -> (Exists.{succ u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (fun (P : Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) => And (IsAssociatedPrime.{u2, u1} R _inst_1 P M _inst_2 _inst_3) (LE.le.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Preorder.toLE.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (PartialOrder.toPreorder.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Submodule.completeLattice.{u2, u2} R R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))))) (Submodule.annihilator.{u2, u1} R M (CommRing.toCommSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 (Submodule.span.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) x))) P)))
Case conversion may be inaccurate. Consider using '#align exists_le_is_associated_prime_of_is_noetherian_ring exists_le_isAssociatedPrime_of_isNoetherianRingₓ'. -/
theorem exists_le_isAssociatedPrime_of_isNoetherianRing [H : IsNoetherianRing R] (x : M)
    (hx : x ≠ 0) : ∃ P : Ideal R, IsAssociatedPrime P M ∧ (R ∙ x).annihilator ≤ P :=
  by
  have : (R ∙ x).annihilator ≠ ⊤ := by
    rwa [Ne.def, Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul]
  obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ :=
    set_has_maximal_iff_noetherian.mpr H
      { P | (R ∙ x).annihilator ≤ P ∧ P ≠ ⊤ ∧ ∃ y : M, P = (R ∙ y).annihilator }
      ⟨(R ∙ x).annihilator, rfl.le, this, x, rfl⟩
  refine' ⟨_, ⟨⟨h₁, _⟩, y, rfl⟩, l⟩
  intro a b hab
  rw [or_iff_not_imp_left]
  intro ha
  rw [Submodule.mem_annihilator_span_singleton] at ha hab
  have H₁ : (R ∙ y).annihilator ≤ (R ∙ a • y).annihilator :=
    by
    intro c hc
    rw [Submodule.mem_annihilator_span_singleton] at hc⊢
    rw [smul_comm, hc, smul_zero]
  have H₂ : (Submodule.span R {a • y}).annihilator ≠ ⊤ := by
    rwa [Ne.def, Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot]
  rwa [H₁.eq_of_not_lt (h₃ (R ∙ a • y).annihilator ⟨l.trans H₁, H₂, _, rfl⟩),
    Submodule.mem_annihilator_span_singleton, smul_comm, smul_smul]
#align exists_le_is_associated_prime_of_is_noetherian_ring exists_le_isAssociatedPrime_of_isNoetherianRing

variable {R}

/- warning: associated_primes.subset_of_injective -> associatedPrimes.subset_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {M' : Type.{u3}} [_inst_4 : AddCommGroup.{u3} M'] [_inst_5 : Module.{u1, u3} R M' (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4)] (f : LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5), (Function.Injective.{succ u2, succ u3} M M' (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5) (fun (_x : LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5) => M -> M') (LinearMap.hasCoeToFun.{u1, u1, u2, u3} R R M M' (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) f)) -> (HasSubset.Subset.{u1} (Set.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Set.hasSubset.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (associatedPrimes.{u1, u2} R _inst_1 M _inst_2 _inst_3) (associatedPrimes.{u1, u3} R _inst_1 M' _inst_4 _inst_5))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M : Type.{u3}} [_inst_2 : AddCommGroup.{u3} M] [_inst_3 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2)] {M' : Type.{u2}} [_inst_4 : AddCommGroup.{u2} M'] [_inst_5 : Module.{u1, u2} R M' (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M' _inst_4)] (f : LinearMap.{u1, u1, u3, u2} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M' _inst_4) _inst_3 _inst_5), (Function.Injective.{succ u3, succ u2} M M' (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (LinearMap.{u1, u1, u3, u2} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M' _inst_4) _inst_3 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => M') _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u3, u2} R R M M' (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M' _inst_4) _inst_3 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) f)) -> (HasSubset.Subset.{u1} (Set.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (Set.instHasSubsetSet.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (associatedPrimes.{u1, u3} R _inst_1 M _inst_2 _inst_3) (associatedPrimes.{u1, u2} R _inst_1 M' _inst_4 _inst_5))
Case conversion may be inaccurate. Consider using '#align associated_primes.subset_of_injective associatedPrimes.subset_of_injectiveₓ'. -/
theorem associatedPrimes.subset_of_injective (hf : Function.Injective f) :
    associatedPrimes R M ⊆ associatedPrimes R M' := fun I h => h.map_of_injective f hf
#align associated_primes.subset_of_injective associatedPrimes.subset_of_injective

/- warning: linear_equiv.associated_primes.eq -> LinearEquiv.AssociatedPrimes.eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {M' : Type.{u3}} [_inst_4 : AddCommGroup.{u3} M'] [_inst_5 : Module.{u1, u3} R M' (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4)], (LinearEquiv.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} M' _inst_4) _inst_3 _inst_5) -> (Eq.{succ u1} (Set.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (associatedPrimes.{u1, u2} R _inst_1 M _inst_2 _inst_3) (associatedPrimes.{u1, u3} R _inst_1 M' _inst_4 _inst_5))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommRing.{u3} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u3, u2} R M (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {M' : Type.{u1}} [_inst_4 : AddCommGroup.{u1} M'] [_inst_5 : Module.{u3, u1} R M' (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M' _inst_4)], (LinearEquiv.{u3, u3, u2, u1} R R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) (RingHomInvPair.ids.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))) (RingHomInvPair.ids.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M' _inst_4) _inst_3 _inst_5) -> (Eq.{succ u3} (Set.{u3} (Ideal.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) (associatedPrimes.{u3, u2} R _inst_1 M _inst_2 _inst_3) (associatedPrimes.{u3, u1} R _inst_1 M' _inst_4 _inst_5))
Case conversion may be inaccurate. Consider using '#align linear_equiv.associated_primes.eq LinearEquiv.AssociatedPrimes.eqₓ'. -/
theorem LinearEquiv.AssociatedPrimes.eq (l : M ≃ₗ[R] M') :
    associatedPrimes R M = associatedPrimes R M' :=
  le_antisymm (associatedPrimes.subset_of_injective l l.Injective)
    (associatedPrimes.subset_of_injective l.symm l.symm.Injective)
#align linear_equiv.associated_primes.eq LinearEquiv.AssociatedPrimes.eq

#print associatedPrimes.eq_empty_of_subsingleton /-
theorem associatedPrimes.eq_empty_of_subsingleton [Subsingleton M] : associatedPrimes R M = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false_iff];
  apply not_isAssociatedPrime_of_subsingleton
#align associated_primes.eq_empty_of_subsingleton associatedPrimes.eq_empty_of_subsingleton
-/

variable (R M)

/- warning: associated_primes.nonempty -> associatedPrimes.nonempty is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (M : Type.{u2}) [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_6 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_7 : Nontrivial.{u2} M], Set.Nonempty.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (associatedPrimes.{u1, u2} R _inst_1 M _inst_2 _inst_3)
but is expected to have type
  forall (R : Type.{u2}) [_inst_1 : CommRing.{u2} R] (M : Type.{u1}) [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [_inst_6 : IsNoetherianRing.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))] [_inst_7 : Nontrivial.{u1} M], Set.Nonempty.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (associatedPrimes.{u2, u1} R _inst_1 M _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align associated_primes.nonempty associatedPrimes.nonemptyₓ'. -/
theorem associatedPrimes.nonempty [IsNoetherianRing R] [Nontrivial M] :
    (associatedPrimes R M).Nonempty :=
  by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨P, hP, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  exact ⟨P, hP⟩
#align associated_primes.nonempty associatedPrimes.nonempty

variable {R M}

/- warning: is_associated_prime.annihilator_le -> IsAssociatedPrime.annihilator_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)], (IsAssociatedPrime.{u1, u2} R _inst_1 I M _inst_2 _inst_3) -> (LE.le.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Preorder.toLE.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) (Submodule.annihilator.{u1, u2} R M (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasTop.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))) I)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {I : Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))} {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)], (IsAssociatedPrime.{u2, u1} R _inst_1 I M _inst_2 _inst_3) -> (LE.le.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Preorder.toLE.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (PartialOrder.toPreorder.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Submodule.completeLattice.{u2, u2} R R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))))) (Submodule.annihilator.{u2, u1} R M (CommRing.toCommSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 (Top.top.{u1} (Submodule.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.instTopSubmodule.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3))) I)
Case conversion may be inaccurate. Consider using '#align is_associated_prime.annihilator_le IsAssociatedPrime.annihilator_leₓ'. -/
theorem IsAssociatedPrime.annihilator_le (h : IsAssociatedPrime I M) :
    (⊤ : Submodule R M).annihilator ≤ I :=
  by
  obtain ⟨hI, x, rfl⟩ := h
  exact Submodule.annihilator_mono le_top
#align is_associated_prime.annihilator_le IsAssociatedPrime.annihilator_le

#print IsAssociatedPrime.eq_radical /-
theorem IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I)) :
    J = I.radical := by
  obtain ⟨hJ, x, e⟩ := h
  have : x ≠ 0 := by
    rintro rfl
    apply hJ.1
    rwa [submodule.span_singleton_eq_bot.mpr rfl, Submodule.annihilator_bot] at e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  replace e : ∀ {y}, y ∈ J ↔ x * y ∈ I
  · intro y
    rw [e, Submodule.mem_annihilator_span_singleton, ← map_smul, smul_eq_mul, mul_comm,
      Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_eq_zero]
  apply le_antisymm
  · intro y hy
    exact (hI.2 <| e.mp hy).resolve_left ((Submodule.Quotient.mk_eq_zero I).Not.mp this)
  · rw [hJ.radical_le_iff]
    intro y hy
    exact e.mpr (I.mul_mem_left x hy)
#align is_associated_prime.eq_radical IsAssociatedPrime.eq_radical
-/

#print associatedPrimes.eq_singleton_of_isPrimary /-
theorem associatedPrimes.eq_singleton_of_isPrimary [IsNoetherianRing R] (hI : I.IsPrimary) :
    associatedPrimes R (R ⧸ I) = {I.radical} :=
  by
  ext J
  rw [Set.mem_singleton_iff]
  refine' ⟨IsAssociatedPrime.eq_radical hI, _⟩
  rintro rfl
  haveI : Nontrivial (R ⧸ I) := ⟨⟨(I.Quotient.mk : _) 1, (I.Quotient.mk : _) 0, _⟩⟩
  obtain ⟨a, ha⟩ := associatedPrimes.nonempty R (R ⧸ I)
  exact ha.eq_radical hI ▸ ha
  rw [Ne.def, Ideal.Quotient.eq, sub_zero, ← Ideal.eq_top_iff_one]
  exact hI.1
#align associated_primes.eq_singleton_of_is_primary associatedPrimes.eq_singleton_of_isPrimary
-/

