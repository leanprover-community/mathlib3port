/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Data.Nat.Factors
import Data.Set.Finite

#align_import data.nat.prime_fin from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# Prime numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results about prime numbers which depend on finiteness of sets.
-/


namespace Nat

#print Nat.infinite_setOf_prime /-
/-- A version of `nat.exists_infinite_primes` using the `set.infinite` predicate. -/
theorem infinite_setOf_prime : {p | Prime p}.Infinite :=
  Set.infinite_of_not_bddAbove not_bddAbove_setOf_prime
#align nat.infinite_set_of_prime Nat.infinite_setOf_prime
-/

#print Nat.primeFactors_mul /-
/-- If `a`, `b` are positive, the prime divisors of `a * b` are the union of those of `a` and `b` -/
theorem primeFactors_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactorsList.toFinset = a.primeFactorsList.toFinset ∪ b.primeFactorsList.toFinset :=
  (List.toFinset.ext fun x =>
        (mem_primeFactorsList_mul ha hb).trans List.mem_union_iff.symm).trans <|
    List.toFinset_union _ _
#align nat.factors_mul_to_finset Nat.primeFactors_mul
-/

#print Nat.primeFactors_pow_succ /-
theorem primeFactors_pow_succ (n k : ℕ) :
    (n ^ (k + 1)).primeFactorsList.toFinset = n.primeFactorsList.toFinset :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  induction' k with k ih
  · simp
  rw [pow_succ', factors_mul_to_finset hn (pow_ne_zero _ hn), ih, Finset.union_idempotent]
#align nat.pow_succ_factors_to_finset Nat.primeFactors_pow_succ
-/

#print Nat.primeFactors_pow /-
theorem primeFactors_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    (n ^ k).primeFactorsList.toFinset = n.primeFactorsList.toFinset :=
  by
  cases k
  · simpa using hk
  rw [pow_succ_factors_to_finset]
#align nat.pow_factors_to_finset Nat.primeFactors_pow
-/

#print Nat.primeFactors_prime_pow /-
/-- The only prime divisor of positive prime power `p^k` is `p` itself -/
theorem primeFactors_prime_pow {p k : ℕ} (hk : k ≠ 0) (hp : Prime p) :
    (p ^ k).primeFactorsList.toFinset = {p} := by
  simp [pow_factors_to_finset p hk, factors_prime hp]
#align nat.prime_pow_prime_divisor Nat.primeFactors_prime_pow
-/

#print Nat.Coprime.primeFactors_mul /-
theorem Nat.Coprime.primeFactors_mul {a b : ℕ} (hab : Coprime a b) :
    (a * b).primeFactorsList.toFinset = a.primeFactorsList.toFinset ∪ b.primeFactorsList.toFinset :=
  (List.toFinset.ext <| mem_primeFactorsList_mul_of_coprime hab).trans <| List.toFinset_union _ _
#align nat.factors_mul_to_finset_of_coprime Nat.Coprime.primeFactors_mul
-/

end Nat

