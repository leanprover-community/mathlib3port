/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

! This file was ported from Lean 3 source module data.nat.prime_fin
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Factors
import Mathbin.Data.Set.Finite

/-!
# Prime numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results about prime numbers which depend on finiteness of sets.
-/


namespace Nat

#print Nat.infinite_setOf_prime /-
/-- A version of `nat.exists_infinite_primes` using the `set.infinite` predicate. -/
theorem infinite_setOf_prime : { p | Prime p }.Infinite :=
  Set.infinite_of_not_bddAbove not_bddAbove_setOf_prime
#align nat.infinite_set_of_prime Nat.infinite_setOf_prime
-/

/- warning: nat.factors_mul_to_finset -> Nat.factors_mul_toFinset is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {b : Nat}, (Ne.{1} Nat a (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Ne.{1} Nat b (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) a b))) (Union.union.{0} (Finset.{0} Nat) (Finset.hasUnion.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors a)) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors b))))
but is expected to have type
  forall {a : Nat} {b : Nat}, (Ne.{1} Nat a (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Ne.{1} Nat b (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) a b))) (Union.union.{0} (Finset.{0} Nat) (Finset.instUnionFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors a)) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors b))))
Case conversion may be inaccurate. Consider using '#align nat.factors_mul_to_finset Nat.factors_mul_toFinsetₓ'. -/
/-- If `a`, `b` are positive, the prime divisors of `a * b` are the union of those of `a` and `b` -/
theorem factors_mul_toFinset {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factors.toFinset = a.factors.toFinset ∪ b.factors.toFinset :=
  (List.toFinset.ext fun x => (mem_factors_mul ha hb).trans List.mem_union.symm).trans <|
    List.toFinset_union _ _
#align nat.factors_mul_to_finset Nat.factors_mul_toFinset

/- warning: nat.pow_succ_factors_to_finset -> Nat.pow_succ_factors_toFinset is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (k : Nat), Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors n))
but is expected to have type
  forall (n : Nat) (k : Nat), Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors n))
Case conversion may be inaccurate. Consider using '#align nat.pow_succ_factors_to_finset Nat.pow_succ_factors_toFinsetₓ'. -/
theorem pow_succ_factors_toFinset (n k : ℕ) : (n ^ (k + 1)).factors.toFinset = n.factors.toFinset :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  induction' k with k ih
  · simp
  rw [pow_succ, factors_mul_to_finset hn (pow_ne_zero _ hn), ih, Finset.union_idempotent]
#align nat.pow_succ_factors_to_finset Nat.pow_succ_factors_toFinset

/- warning: nat.pow_factors_to_finset -> Nat.pow_factors_toFinset is a dubious translation:
lean 3 declaration is
  forall (n : Nat) {k : Nat}, (Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) n k))) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors n)))
but is expected to have type
  forall (n : Nat) {k : Nat}, (Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) n k))) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors n)))
Case conversion may be inaccurate. Consider using '#align nat.pow_factors_to_finset Nat.pow_factors_toFinsetₓ'. -/
theorem pow_factors_toFinset (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    (n ^ k).factors.toFinset = n.factors.toFinset :=
  by
  cases k
  · simpa using hk
  rw [pow_succ_factors_to_finset]
#align nat.pow_factors_to_finset Nat.pow_factors_toFinset

/- warning: nat.prime_pow_prime_divisor -> Nat.prime_pow_prime_divisor is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {k : Nat}, (Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Nat.Prime p) -> (Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p k))) (Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (Finset.hasSingleton.{0} Nat) p))
but is expected to have type
  forall {p : Nat} {k : Nat}, (Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Nat.Prime p) -> (Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p k))) (Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (Finset.instSingletonFinset.{0} Nat) p))
Case conversion may be inaccurate. Consider using '#align nat.prime_pow_prime_divisor Nat.prime_pow_prime_divisorₓ'. -/
/-- The only prime divisor of positive prime power `p^k` is `p` itself -/
theorem prime_pow_prime_divisor {p k : ℕ} (hk : k ≠ 0) (hp : Prime p) :
    (p ^ k).factors.toFinset = {p} := by simp [pow_factors_to_finset p hk, factors_prime hp]
#align nat.prime_pow_prime_divisor Nat.prime_pow_prime_divisor

/- warning: nat.factors_mul_to_finset_of_coprime -> Nat.factors_mul_toFinset_of_coprime is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {b : Nat}, (Nat.coprime a b) -> (Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) a b))) (Union.union.{0} (Finset.{0} Nat) (Finset.hasUnion.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors a)) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Nat.factors b))))
but is expected to have type
  forall {a : Nat} {b : Nat}, (Nat.coprime a b) -> (Eq.{1} (Finset.{0} Nat) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) a b))) (Union.union.{0} (Finset.{0} Nat) (Finset.instUnionFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors a)) (List.toFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Nat.factors b))))
Case conversion may be inaccurate. Consider using '#align nat.factors_mul_to_finset_of_coprime Nat.factors_mul_toFinset_of_coprimeₓ'. -/
theorem factors_mul_toFinset_of_coprime {a b : ℕ} (hab : coprime a b) :
    (a * b).factors.toFinset = a.factors.toFinset ∪ b.factors.toFinset :=
  (List.toFinset.ext <| mem_factors_mul_of_coprime hab).trans <| List.toFinset_union _ _
#align nat.factors_mul_to_finset_of_coprime Nat.factors_mul_toFinset_of_coprime

end Nat

