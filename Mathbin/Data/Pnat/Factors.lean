/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

! This file was ported from Lean 3 source module data.pnat.factors
! leanprover-community/mathlib commit 50832daea47b195a48b5b33b1c8b2162c48c3afc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Multiset.Basic
import Mathbin.Data.Pnat.Prime
import Mathbin.Data.Nat.Factors
import Mathbin.Data.Multiset.Sort

/-!
# Prime factors of nonzero naturals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the factorization of a nonzero natural number `n` as a multiset of primes,
the multiplicity of `p` in this factors multiset being the p-adic valuation of `n`.

## Main declarations

* `prime_multiset`: Type of multisets of prime numbers.
* `factor_multiset n`: Multiset of prime factors of `n`.
-/


#print PrimeMultiset /-
/-- The type of multisets of prime numbers.  Unique factorization
 gives an equivalence between this set and ℕ+, as we will formalize
 below. -/
def PrimeMultiset :=
  Multiset Nat.Primes deriving Inhabited, CanonicallyOrderedAddMonoid, DistribLattice,
  SemilatticeSup, OrderBot, Sub, OrderedSub
#align prime_multiset PrimeMultiset
-/

namespace PrimeMultiset

-- `@[derive]` doesn't work for `meta` instances
unsafe instance : Repr PrimeMultiset := by delta PrimeMultiset <;> infer_instance

#print PrimeMultiset.ofPrime /-
/-- The multiset consisting of a single prime -/
def ofPrime (p : Nat.Primes) : PrimeMultiset :=
  ({p} : Multiset Nat.Primes)
#align prime_multiset.of_prime PrimeMultiset.ofPrime
-/

/- warning: prime_multiset.card_of_prime -> PrimeMultiset.card_ofPrime is a dubious translation:
lean 3 declaration is
  forall (p : Nat.Primes), Eq.{1} Nat (coeFn.{1, 1} (AddMonoidHom.{0, 0} (Multiset.{0} Nat.Primes) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat.Primes) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat.Primes) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat.Primes) (Multiset.orderedCancelAddCommMonoid.{0} Nat.Primes)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{0, 0} (Multiset.{0} Nat.Primes) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat.Primes) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat.Primes) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat.Primes) (Multiset.orderedCancelAddCommMonoid.{0} Nat.Primes)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{0} Nat.Primes) -> Nat) (AddMonoidHom.hasCoeToFun.{0, 0} (Multiset.{0} Nat.Primes) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat.Primes) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat.Primes) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat.Primes) (Multiset.orderedCancelAddCommMonoid.{0} Nat.Primes)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{0} Nat.Primes) (PrimeMultiset.ofPrime p)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall (p : Nat.Primes), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} Nat.Primes) => Nat) (PrimeMultiset.ofPrime p)) (FunLike.coe.{1, 1, 1} (AddMonoidHom.{0, 0} (Multiset.{0} Nat.Primes) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat.Primes) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat.Primes) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat.Primes) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat.Primes)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} Nat.Primes) (fun (_x : Multiset.{0} Nat.Primes) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} Nat.Primes) => Nat) _x) (AddHomClass.toFunLike.{0, 0, 0} (AddMonoidHom.{0, 0} (Multiset.{0} Nat.Primes) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat.Primes) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat.Primes) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat.Primes) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat.Primes)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} Nat.Primes) Nat (AddZeroClass.toAdd.{0} (Multiset.{0} Nat.Primes) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat.Primes) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat.Primes) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat.Primes) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat.Primes))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{0, 0, 0} (AddMonoidHom.{0, 0} (Multiset.{0} Nat.Primes) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat.Primes) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat.Primes) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat.Primes) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat.Primes)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} Nat.Primes) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat.Primes) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat.Primes) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat.Primes) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat.Primes)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{0, 0} (Multiset.{0} Nat.Primes) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat.Primes) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat.Primes) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat.Primes) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat.Primes) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat.Primes)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{0} Nat.Primes) (PrimeMultiset.ofPrime p)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} Nat.Primes) => Nat) (PrimeMultiset.ofPrime p)) 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align prime_multiset.card_of_prime PrimeMultiset.card_ofPrimeₓ'. -/
theorem card_ofPrime (p : Nat.Primes) : Multiset.card (ofPrime p) = 1 :=
  rfl
#align prime_multiset.card_of_prime PrimeMultiset.card_ofPrime

#print PrimeMultiset.toNatMultiset /-
/-- We can forget the primality property and regard a multiset
 of primes as just a multiset of positive integers, or a multiset
 of natural numbers.  In the opposite direction, if we have a
 multiset of positive integers or natural numbers, together with
 a proof that all the elements are prime, then we can regard it
 as a multiset of primes.  The next block of results records
 obvious properties of these coercions.
-/
def toNatMultiset : PrimeMultiset → Multiset ℕ := fun v => v.map fun p => (p : ℕ)
#align prime_multiset.to_nat_multiset PrimeMultiset.toNatMultiset
-/

#print PrimeMultiset.coeNat /-
instance coeNat : Coe PrimeMultiset (Multiset ℕ) :=
  ⟨toNatMultiset⟩
#align prime_multiset.coe_nat PrimeMultiset.coeNat
-/

/- warning: prime_multiset.coe_nat_monoid_hom -> PrimeMultiset.coeNatMonoidHom is a dubious translation:
lean 3 declaration is
  AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat))))))
but is expected to have type
  AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat))))))
Case conversion may be inaccurate. Consider using '#align prime_multiset.coe_nat_monoid_hom PrimeMultiset.coeNatMonoidHomₓ'. -/
/-- `prime_multiset.coe`, the coercion from a multiset of primes to a multiset of
naturals, promoted to an `add_monoid_hom`. -/
def coeNatMonoidHom : PrimeMultiset →+ Multiset ℕ :=
  { Multiset.mapAddMonoidHom coe with toFun := coe }
#align prime_multiset.coe_nat_monoid_hom PrimeMultiset.coeNatMonoidHom

/- warning: prime_multiset.coe_coe_nat_monoid_hom -> PrimeMultiset.coe_coeNatMonoidHom is a dubious translation:
lean 3 declaration is
  Eq.{1} ((fun (_x : AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat))))))) => PrimeMultiset -> (Multiset.{0} Nat)) PrimeMultiset.coeNatMonoidHom) (coeFn.{1, 1} (AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat))))))) (fun (_x : AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat))))))) => PrimeMultiset -> (Multiset.{0} Nat)) (AddMonoidHom.hasCoeToFun.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat))))))) PrimeMultiset.coeNatMonoidHom) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PrimeMultiset (Multiset.{0} Nat) (HasLiftT.mk.{1, 1} PrimeMultiset (Multiset.{0} Nat) (CoeTCₓ.coe.{1, 1} PrimeMultiset (Multiset.{0} Nat) (coeBase.{1, 1} PrimeMultiset (Multiset.{0} Nat) PrimeMultiset.coeNat))))
but is expected to have type
  Eq.{1} (forall (a : PrimeMultiset), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : PrimeMultiset) => Multiset.{0} Nat) a) (FunLike.coe.{1, 1, 1} (AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat))))))) PrimeMultiset (fun (_x : PrimeMultiset) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : PrimeMultiset) => Multiset.{0} Nat) _x) (AddHomClass.toFunLike.{0, 0, 0} (AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat))))))) PrimeMultiset (Multiset.{0} Nat) (AddZeroClass.toAdd.{0} PrimeMultiset (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid))))) (AddZeroClass.toAdd.{0} (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat))))))) (AddMonoidHomClass.toAddHomClass.{0, 0, 0} (AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat))))))) PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoidHom.addMonoidHomClass.{0, 0} PrimeMultiset (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat))))))))) PrimeMultiset.coeNatMonoidHom) (Coe.coe.{1, 1} PrimeMultiset (Multiset.{0} Nat) PrimeMultiset.coeNat)
Case conversion may be inaccurate. Consider using '#align prime_multiset.coe_coe_nat_monoid_hom PrimeMultiset.coe_coeNatMonoidHomₓ'. -/
@[simp]
theorem coe_coeNatMonoidHom : (coeNatMonoidHom : PrimeMultiset → Multiset ℕ) = coe :=
  rfl
#align prime_multiset.coe_coe_nat_monoid_hom PrimeMultiset.coe_coeNatMonoidHom

#print PrimeMultiset.coeNat_injective /-
theorem coeNat_injective : Function.Injective (coe : PrimeMultiset → Multiset ℕ) :=
  Multiset.map_injective Nat.Primes.coe_nat_injective
#align prime_multiset.coe_nat_injective PrimeMultiset.coeNat_injective
-/

#print PrimeMultiset.coeNat_ofPrime /-
theorem coeNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ) = {p} :=
  rfl
#align prime_multiset.coe_nat_of_prime PrimeMultiset.coeNat_ofPrime
-/

#print PrimeMultiset.coeNat_prime /-
theorem coeNat_prime (v : PrimeMultiset) (p : ℕ) (h : p ∈ (v : Multiset ℕ)) : p.Prime :=
  by
  rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
  exact h_eq ▸ hp'
#align prime_multiset.coe_nat_prime PrimeMultiset.coeNat_prime
-/

#print PrimeMultiset.toPNatMultiset /-
/-- Converts a `prime_multiset` to a `multiset ℕ+`. -/
def toPNatMultiset : PrimeMultiset → Multiset ℕ+ := fun v => v.map fun p => (p : ℕ+)
#align prime_multiset.to_pnat_multiset PrimeMultiset.toPNatMultiset
-/

#print PrimeMultiset.coePNat /-
instance coePNat : Coe PrimeMultiset (Multiset ℕ+) :=
  ⟨toPNatMultiset⟩
#align prime_multiset.coe_pnat PrimeMultiset.coePNat
-/

/- warning: prime_multiset.coe_pnat_monoid_hom -> PrimeMultiset.coePNatMonoidHom is a dubious translation:
lean 3 declaration is
  AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.orderedCancelAddCommMonoid.{0} PNat))))))
but is expected to have type
  AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} PNat))))))
Case conversion may be inaccurate. Consider using '#align prime_multiset.coe_pnat_monoid_hom PrimeMultiset.coePNatMonoidHomₓ'. -/
/-- `coe_pnat`, the coercion from a multiset of primes to a multiset of positive
naturals, regarded as an `add_monoid_hom`. -/
def coePNatMonoidHom : PrimeMultiset →+ Multiset ℕ+ :=
  { Multiset.mapAddMonoidHom coe with toFun := coe }
#align prime_multiset.coe_pnat_monoid_hom PrimeMultiset.coePNatMonoidHom

/- warning: prime_multiset.coe_coe_pnat_monoid_hom -> PrimeMultiset.coe_coePNatMonoidHom is a dubious translation:
lean 3 declaration is
  Eq.{1} ((fun (_x : AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.orderedCancelAddCommMonoid.{0} PNat))))))) => PrimeMultiset -> (Multiset.{0} PNat)) PrimeMultiset.coePNatMonoidHom) (coeFn.{1, 1} (AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.orderedCancelAddCommMonoid.{0} PNat))))))) (fun (_x : AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.orderedCancelAddCommMonoid.{0} PNat))))))) => PrimeMultiset -> (Multiset.{0} PNat)) (AddMonoidHom.hasCoeToFun.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.orderedCancelAddCommMonoid.{0} PNat))))))) PrimeMultiset.coePNatMonoidHom) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PrimeMultiset (Multiset.{0} PNat) (HasLiftT.mk.{1, 1} PrimeMultiset (Multiset.{0} PNat) (CoeTCₓ.coe.{1, 1} PrimeMultiset (Multiset.{0} PNat) (coeBase.{1, 1} PrimeMultiset (Multiset.{0} PNat) PrimeMultiset.coePNat))))
but is expected to have type
  Eq.{1} (forall (a : PrimeMultiset), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : PrimeMultiset) => Multiset.{0} PNat) a) (FunLike.coe.{1, 1, 1} (AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} PNat))))))) PrimeMultiset (fun (_x : PrimeMultiset) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : PrimeMultiset) => Multiset.{0} PNat) _x) (AddHomClass.toFunLike.{0, 0, 0} (AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} PNat))))))) PrimeMultiset (Multiset.{0} PNat) (AddZeroClass.toAdd.{0} PrimeMultiset (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid))))) (AddZeroClass.toAdd.{0} (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} PNat))))))) (AddMonoidHomClass.toAddHomClass.{0, 0, 0} (AddMonoidHom.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} PNat))))))) PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} PNat)))))) (AddMonoidHom.addMonoidHomClass.{0, 0} PrimeMultiset (Multiset.{0} PNat) (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} PNat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} PNat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} PNat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} PNat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} PNat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} PNat))))))))) PrimeMultiset.coePNatMonoidHom) (Coe.coe.{1, 1} PrimeMultiset (Multiset.{0} PNat) PrimeMultiset.coePNat)
Case conversion may be inaccurate. Consider using '#align prime_multiset.coe_coe_pnat_monoid_hom PrimeMultiset.coe_coePNatMonoidHomₓ'. -/
@[simp]
theorem coe_coePNatMonoidHom : (coePNatMonoidHom : PrimeMultiset → Multiset ℕ+) = coe :=
  rfl
#align prime_multiset.coe_coe_pnat_monoid_hom PrimeMultiset.coe_coePNatMonoidHom

#print PrimeMultiset.coePNat_injective /-
theorem coePNat_injective : Function.Injective (coe : PrimeMultiset → Multiset ℕ+) :=
  Multiset.map_injective Nat.Primes.coe_pnat_injective
#align prime_multiset.coe_pnat_injective PrimeMultiset.coePNat_injective
-/

#print PrimeMultiset.coePNat_ofPrime /-
theorem coePNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ+) = {(p : ℕ+)} :=
  rfl
#align prime_multiset.coe_pnat_of_prime PrimeMultiset.coePNat_ofPrime
-/

#print PrimeMultiset.coePNat_prime /-
theorem coePNat_prime (v : PrimeMultiset) (p : ℕ+) (h : p ∈ (v : Multiset ℕ+)) : p.Prime :=
  by
  rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
  exact h_eq ▸ hp'
#align prime_multiset.coe_pnat_prime PrimeMultiset.coePNat_prime
-/

#print PrimeMultiset.coeMultisetPNatNat /-
instance coeMultisetPNatNat : Coe (Multiset ℕ+) (Multiset ℕ) :=
  ⟨fun v => v.map fun n => (n : ℕ)⟩
#align prime_multiset.coe_multiset_pnat_nat PrimeMultiset.coeMultisetPNatNat
-/

#print PrimeMultiset.coePNat_nat /-
theorem coePNat_nat (v : PrimeMultiset) : ((v : Multiset ℕ+) : Multiset ℕ) = (v : Multiset ℕ) :=
  by
  change (v.map (coe : Nat.Primes → ℕ+)).map Subtype.val = v.map Subtype.val
  rw [Multiset.map_map]
  congr
#align prime_multiset.coe_pnat_nat PrimeMultiset.coePNat_nat
-/

#print PrimeMultiset.prod /-
/-- The product of a `prime_multiset`, as a `ℕ+`. -/
def prod (v : PrimeMultiset) : ℕ+ :=
  (v : Multiset PNat).Prod
#align prime_multiset.prod PrimeMultiset.prod
-/

#print PrimeMultiset.coe_prod /-
theorem coe_prod (v : PrimeMultiset) : (v.Prod : ℕ) = (v : Multiset ℕ).Prod :=
  by
  let h : (v.prod : ℕ) = ((v.map coe).map coe).Prod :=
    pnat.coe_monoid_hom.map_multiset_prod v.to_pnat_multiset
  rw [Multiset.map_map] at h
  have : (coe : ℕ+ → ℕ) ∘ (coe : Nat.Primes → ℕ+) = coe := funext fun p => rfl
  rw [this] at h; exact h
#align prime_multiset.coe_prod PrimeMultiset.coe_prod
-/

#print PrimeMultiset.prod_ofPrime /-
theorem prod_ofPrime (p : Nat.Primes) : (ofPrime p).Prod = (p : ℕ+) :=
  Multiset.prod_singleton _
#align prime_multiset.prod_of_prime PrimeMultiset.prod_ofPrime
-/

#print PrimeMultiset.ofNatMultiset /-
/-- If a `multiset ℕ` consists only of primes, it can be recast as a `prime_multiset`. -/
def ofNatMultiset (v : Multiset ℕ) (h : ∀ p : ℕ, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h
#align prime_multiset.of_nat_multiset PrimeMultiset.ofNatMultiset
-/

#print PrimeMultiset.to_ofNatMultiset /-
theorem to_ofNatMultiset (v : Multiset ℕ) (h) : (ofNatMultiset v h : Multiset ℕ) = v :=
  by
  unfold_coes
  dsimp [of_nat_multiset, to_nat_multiset]
  have : (fun (p : ℕ) (h : p.Prime) => ((⟨p, h⟩ : Nat.Primes) : ℕ)) = fun p h => id p :=
    by
    funext p h
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]
#align prime_multiset.to_of_nat_multiset PrimeMultiset.to_ofNatMultiset
-/

#print PrimeMultiset.prod_ofNatMultiset /-
theorem prod_ofNatMultiset (v : Multiset ℕ) (h) : ((ofNatMultiset v h).Prod : ℕ) = (v.Prod : ℕ) :=
  by rw [coe_prod, to_of_nat_multiset]
#align prime_multiset.prod_of_nat_multiset PrimeMultiset.prod_ofNatMultiset
-/

#print PrimeMultiset.ofPNatMultiset /-
/-- If a `multiset ℕ+` consists only of primes, it can be recast as a `prime_multiset`. -/
def ofPNatMultiset (v : Multiset ℕ+) (h : ∀ p : ℕ+, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ+ Nat.Primes PNat.Prime (fun p hp => ⟨(p : ℕ), hp⟩) v h
#align prime_multiset.of_pnat_multiset PrimeMultiset.ofPNatMultiset
-/

#print PrimeMultiset.to_ofPNatMultiset /-
theorem to_ofPNatMultiset (v : Multiset ℕ+) (h) : (ofPNatMultiset v h : Multiset ℕ+) = v :=
  by
  unfold_coes; dsimp [of_pnat_multiset, to_pnat_multiset]
  have : (fun (p : ℕ+) (h : p.Prime) => (coe : Nat.Primes → ℕ+) ⟨p, h⟩) = fun p h => id p :=
    by
    funext p h
    apply Subtype.eq
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]
#align prime_multiset.to_of_pnat_multiset PrimeMultiset.to_ofPNatMultiset
-/

#print PrimeMultiset.prod_ofPNatMultiset /-
theorem prod_ofPNatMultiset (v : Multiset ℕ+) (h) : ((ofPNatMultiset v h).Prod : ℕ+) = v.Prod :=
  by
  dsimp [Prod]
  rw [to_of_pnat_multiset]
#align prime_multiset.prod_of_pnat_multiset PrimeMultiset.prod_ofPNatMultiset
-/

#print PrimeMultiset.ofNatList /-
/-- Lists can be coerced to multisets; here we have some results
about how this interacts with our constructions on multisets. -/
def ofNatList (l : List ℕ) (h : ∀ p : ℕ, p ∈ l → p.Prime) : PrimeMultiset :=
  ofNatMultiset (l : Multiset ℕ) h
#align prime_multiset.of_nat_list PrimeMultiset.ofNatList
-/

#print PrimeMultiset.prod_ofNatList /-
theorem prod_ofNatList (l : List ℕ) (h) : ((ofNatList l h).Prod : ℕ) = l.Prod :=
  by
  have := prod_of_nat_multiset (l : Multiset ℕ) h
  rw [Multiset.coe_prod] at this
  exact this
#align prime_multiset.prod_of_nat_list PrimeMultiset.prod_ofNatList
-/

#print PrimeMultiset.ofPNatList /-
/-- If a `list ℕ+` consists only of primes, it can be recast as a `prime_multiset` with
the coercion from lists to multisets. -/
def ofPNatList (l : List ℕ+) (h : ∀ p : ℕ+, p ∈ l → p.Prime) : PrimeMultiset :=
  ofPNatMultiset (l : Multiset ℕ+) h
#align prime_multiset.of_pnat_list PrimeMultiset.ofPNatList
-/

/- warning: prime_multiset.prod_of_pnat_list -> PrimeMultiset.prod_ofPNatList is a dubious translation:
lean 3 declaration is
  forall (l : List.{0} PNat) (h : forall (p : PNat), (Membership.Mem.{0, 0} PNat (List.{0} PNat) (List.hasMem.{0} PNat) p l) -> (PNat.Prime p)), Eq.{1} PNat (PrimeMultiset.prod (PrimeMultiset.ofPNatList l h)) (List.prod.{0} PNat PNat.hasMul PNat.hasOne l)
but is expected to have type
  forall (l : List.{0} PNat) (h : forall (p : PNat), (Membership.mem.{0, 0} PNat (List.{0} PNat) (List.instMembershipList.{0} PNat) p l) -> (PNat.Prime p)), Eq.{1} PNat (PrimeMultiset.prod (PrimeMultiset.ofPNatList l h)) (List.prod.{0} PNat instPNatMul instOnePNat l)
Case conversion may be inaccurate. Consider using '#align prime_multiset.prod_of_pnat_list PrimeMultiset.prod_ofPNatListₓ'. -/
theorem prod_ofPNatList (l : List ℕ+) (h) : (ofPNatList l h).Prod = l.Prod :=
  by
  have := prod_of_pnat_multiset (l : Multiset ℕ+) h
  rw [Multiset.coe_prod] at this
  exact this
#align prime_multiset.prod_of_pnat_list PrimeMultiset.prod_ofPNatList

/- warning: prime_multiset.prod_zero -> PrimeMultiset.prod_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} PNat (PrimeMultiset.prod (OfNat.ofNat.{0} PrimeMultiset 0 (OfNat.mk.{0} PrimeMultiset 0 (Zero.zero.{0} PrimeMultiset (AddZeroClass.toHasZero.{0} PrimeMultiset (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid))))))))) (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))
but is expected to have type
  Eq.{1} PNat (PrimeMultiset.prod (OfNat.ofNat.{0} PrimeMultiset 0 (Zero.toOfNat0.{0} PrimeMultiset (AddMonoid.toZero.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid))))))) (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
Case conversion may be inaccurate. Consider using '#align prime_multiset.prod_zero PrimeMultiset.prod_zeroₓ'. -/
/-- The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+. -/
theorem prod_zero : (0 : PrimeMultiset).Prod = 1 :=
  by
  dsimp [Prod]
  exact Multiset.prod_zero
#align prime_multiset.prod_zero PrimeMultiset.prod_zero

/- warning: prime_multiset.prod_add -> PrimeMultiset.prod_add is a dubious translation:
lean 3 declaration is
  forall (u : PrimeMultiset) (v : PrimeMultiset), Eq.{1} PNat (PrimeMultiset.prod (HAdd.hAdd.{0, 0, 0} PrimeMultiset PrimeMultiset PrimeMultiset (instHAdd.{0} PrimeMultiset (AddZeroClass.toHasAdd.{0} PrimeMultiset (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))))) u v)) (HMul.hMul.{0, 0, 0} PNat PNat PNat (instHMul.{0} PNat PNat.hasMul) (PrimeMultiset.prod u) (PrimeMultiset.prod v))
but is expected to have type
  forall (u : PrimeMultiset) (v : PrimeMultiset), Eq.{1} PNat (PrimeMultiset.prod (HAdd.hAdd.{0, 0, 0} PrimeMultiset PrimeMultiset PrimeMultiset (instHAdd.{0} PrimeMultiset (AddZeroClass.toAdd.{0} PrimeMultiset (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))))) u v)) (HMul.hMul.{0, 0, 0} PNat PNat PNat (instHMul.{0} PNat instPNatMul) (PrimeMultiset.prod u) (PrimeMultiset.prod v))
Case conversion may be inaccurate. Consider using '#align prime_multiset.prod_add PrimeMultiset.prod_addₓ'. -/
theorem prod_add (u v : PrimeMultiset) : (u + v).Prod = u.Prod * v.Prod :=
  by
  change (coe_pnat_monoid_hom (u + v)).Prod = _
  rw [coe_pnat_monoid_hom.map_add]
  exact Multiset.prod_add _ _
#align prime_multiset.prod_add PrimeMultiset.prod_add

/- warning: prime_multiset.prod_smul -> PrimeMultiset.prod_smul is a dubious translation:
lean 3 declaration is
  forall (d : Nat) (u : PrimeMultiset), Eq.{1} PNat (PrimeMultiset.prod (SMul.smul.{0, 0} Nat PrimeMultiset (AddMonoid.SMul.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) d u)) (HPow.hPow.{0, 0, 0} PNat Nat PNat (instHPow.{0, 0} PNat Nat (Monoid.Pow.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) (PrimeMultiset.prod u) d)
but is expected to have type
  forall (d : Nat) (u : PrimeMultiset), Eq.{1} PNat (PrimeMultiset.prod (HSMul.hSMul.{0, 0, 0} Nat PrimeMultiset PrimeMultiset (instHSMul.{0, 0} Nat PrimeMultiset (AddMonoid.SMul.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid))))) d u)) (Pow.pow.{0, 0} PNat Nat (Monoid.Pow.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) (PrimeMultiset.prod u) d)
Case conversion may be inaccurate. Consider using '#align prime_multiset.prod_smul PrimeMultiset.prod_smulₓ'. -/
theorem prod_smul (d : ℕ) (u : PrimeMultiset) : (d • u).Prod = u.Prod ^ d :=
  by
  induction' d with d ih
  rfl
  rw [succ_nsmul, prod_add, ih, Nat.succ_eq_add_one, pow_succ, mul_comm]
#align prime_multiset.prod_smul PrimeMultiset.prod_smul

end PrimeMultiset

namespace PNat

#print PNat.factorMultiset /-
/-- The prime factors of n, regarded as a multiset -/
def factorMultiset (n : ℕ+) : PrimeMultiset :=
  PrimeMultiset.ofNatList (Nat.factors n) (@Nat.prime_of_mem_factors n)
#align pnat.factor_multiset PNat.factorMultiset
-/

#print PNat.prod_factorMultiset /-
/-- The product of the factors is the original number -/
theorem prod_factorMultiset (n : ℕ+) : (factorMultiset n).Prod = n :=
  eq <| by
    dsimp [factor_multiset]
    rw [PrimeMultiset.prod_ofNatList]
    exact Nat.prod_factors n.ne_zero
#align pnat.prod_factor_multiset PNat.prod_factorMultiset
-/

#print PNat.coeNat_factorMultiset /-
theorem coeNat_factorMultiset (n : ℕ+) :
    (factorMultiset n : Multiset ℕ) = (Nat.factors n : Multiset ℕ) :=
  PrimeMultiset.to_ofNatMultiset (Nat.factors n) (@Nat.prime_of_mem_factors n)
#align pnat.coe_nat_factor_multiset PNat.coeNat_factorMultiset
-/

end PNat

namespace PrimeMultiset

#print PrimeMultiset.factorMultiset_prod /-
/-- If we start with a multiset of primes, take the product and
 then factor it, we get back the original multiset. -/
theorem factorMultiset_prod (v : PrimeMultiset) : v.Prod.factorMultiset = v :=
  by
  apply PrimeMultiset.coeNat_injective
  rw [v.prod.coe_nat_factor_multiset, PrimeMultiset.coe_prod]
  rcases v with ⟨l⟩
  unfold_coes
  dsimp [PrimeMultiset.toNatMultiset]
  rw [Multiset.coe_prod]
  let l' := l.map (coe : Nat.Primes → ℕ)
  have : ∀ p : ℕ, p ∈ l' → p.Prime := fun p hp =>
    by
    rcases list.mem_map.mp hp with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
    exact h_eq ▸ hp'
  exact multiset.coe_eq_coe.mpr (@Nat.factors_unique _ l' rfl this).symm
#align prime_multiset.factor_multiset_prod PrimeMultiset.factorMultiset_prod
-/

end PrimeMultiset

namespace PNat

#print PNat.factorMultisetEquiv /-
/-- Positive integers biject with multisets of primes. -/
def factorMultisetEquiv : ℕ+ ≃ PrimeMultiset
    where
  toFun := factorMultiset
  invFun := PrimeMultiset.prod
  left_inv := prod_factorMultiset
  right_inv := PrimeMultiset.factorMultiset_prod
#align pnat.factor_multiset_equiv PNat.factorMultisetEquiv
-/

/- warning: pnat.factor_multiset_one -> PNat.factorMultiset_one is a dubious translation:
lean 3 declaration is
  Eq.{1} PrimeMultiset (PNat.factorMultiset (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) (OfNat.ofNat.{0} PrimeMultiset 0 (OfNat.mk.{0} PrimeMultiset 0 (Zero.zero.{0} PrimeMultiset (AddZeroClass.toHasZero.{0} PrimeMultiset (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid))))))))
but is expected to have type
  Eq.{1} PrimeMultiset (PNat.factorMultiset (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (OfNat.ofNat.{0} PrimeMultiset 0 (Zero.toOfNat0.{0} PrimeMultiset (AddMonoid.toZero.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid))))))
Case conversion may be inaccurate. Consider using '#align pnat.factor_multiset_one PNat.factorMultiset_oneₓ'. -/
/-- Factoring gives a homomorphism from the multiplicative
 monoid ℕ+ to the additive monoid of multisets. -/
theorem factorMultiset_one : factorMultiset 1 = 0 := by
  simp [factor_multiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset]
#align pnat.factor_multiset_one PNat.factorMultiset_one

/- warning: pnat.factor_multiset_mul -> PNat.factorMultiset_mul is a dubious translation:
lean 3 declaration is
  forall (n : PNat) (m : PNat), Eq.{1} PrimeMultiset (PNat.factorMultiset (HMul.hMul.{0, 0, 0} PNat PNat PNat (instHMul.{0} PNat PNat.hasMul) n m)) (HAdd.hAdd.{0, 0, 0} PrimeMultiset PrimeMultiset PrimeMultiset (instHAdd.{0} PrimeMultiset (AddZeroClass.toHasAdd.{0} PrimeMultiset (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))))) (PNat.factorMultiset n) (PNat.factorMultiset m))
but is expected to have type
  forall (n : PNat) (m : PNat), Eq.{1} PrimeMultiset (PNat.factorMultiset (HMul.hMul.{0, 0, 0} PNat PNat PNat (instHMul.{0} PNat instPNatMul) n m)) (HAdd.hAdd.{0, 0, 0} PrimeMultiset PrimeMultiset PrimeMultiset (instHAdd.{0} PrimeMultiset (AddZeroClass.toAdd.{0} PrimeMultiset (AddMonoid.toAddZeroClass.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))))) (PNat.factorMultiset n) (PNat.factorMultiset m))
Case conversion may be inaccurate. Consider using '#align pnat.factor_multiset_mul PNat.factorMultiset_mulₓ'. -/
theorem factorMultiset_mul (n m : ℕ+) :
    factorMultiset (n * m) = factorMultiset n + factorMultiset m :=
  by
  let u := factor_multiset n
  let v := factor_multiset m
  have : n = u.prod := (prod_factor_multiset n).symm; rw [this]
  have : m = v.prod := (prod_factor_multiset m).symm; rw [this]
  rw [← PrimeMultiset.prod_add]
  repeat' rw [PrimeMultiset.factorMultiset_prod]
#align pnat.factor_multiset_mul PNat.factorMultiset_mul

/- warning: pnat.factor_multiset_pow -> PNat.factorMultiset_pow is a dubious translation:
lean 3 declaration is
  forall (n : PNat) (m : Nat), Eq.{1} PrimeMultiset (PNat.factorMultiset (HPow.hPow.{0, 0, 0} PNat Nat PNat (instHPow.{0, 0} PNat Nat (Monoid.Pow.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) n m)) (SMul.smul.{0, 0} Nat PrimeMultiset (AddMonoid.SMul.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) m (PNat.factorMultiset n))
but is expected to have type
  forall (n : PNat) (m : Nat), Eq.{1} PrimeMultiset (PNat.factorMultiset (Pow.pow.{0, 0} PNat Nat (Monoid.Pow.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) n m)) (HSMul.hSMul.{0, 0, 0} Nat PrimeMultiset PrimeMultiset (instHSMul.{0, 0} Nat PrimeMultiset (AddMonoid.SMul.{0} PrimeMultiset (AddCommMonoid.toAddMonoid.{0} PrimeMultiset (OrderedAddCommMonoid.toAddCommMonoid.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid))))) m (PNat.factorMultiset n))
Case conversion may be inaccurate. Consider using '#align pnat.factor_multiset_pow PNat.factorMultiset_powₓ'. -/
theorem factorMultiset_pow (n : ℕ+) (m : ℕ) : factorMultiset (n ^ m) = m • factorMultiset n :=
  by
  let u := factor_multiset n
  have : n = u.prod := (prod_factor_multiset n).symm
  rw [this, ← PrimeMultiset.prod_smul]
  repeat' rw [PrimeMultiset.factorMultiset_prod]
#align pnat.factor_multiset_pow PNat.factorMultiset_pow

#print PNat.factorMultiset_ofPrime /-
/-- Factoring a prime gives the corresponding one-element multiset. -/
theorem factorMultiset_ofPrime (p : Nat.Primes) :
    (p : ℕ+).factorMultiset = PrimeMultiset.ofPrime p :=
  by
  apply factor_multiset_equiv.symm.injective
  change (p : ℕ+).factorMultiset.Prod = (PrimeMultiset.ofPrime p).Prod
  rw [(p : ℕ+).prod_factorMultiset, PrimeMultiset.prod_ofPrime]
#align pnat.factor_multiset_of_prime PNat.factorMultiset_ofPrime
-/

/- warning: pnat.factor_multiset_le_iff -> PNat.factorMultiset_le_iff is a dubious translation:
lean 3 declaration is
  forall {m : PNat} {n : PNat}, Iff (LE.le.{0} PrimeMultiset (Preorder.toLE.{0} PrimeMultiset (PartialOrder.toPreorder.{0} PrimeMultiset (OrderedAddCommMonoid.toPartialOrder.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (PNat.factorMultiset m) (PNat.factorMultiset n)) (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) m n)
but is expected to have type
  forall {m : PNat} {n : PNat}, Iff (LE.le.{0} PrimeMultiset (Preorder.toLE.{0} PrimeMultiset (PartialOrder.toPreorder.{0} PrimeMultiset (OrderedAddCommMonoid.toPartialOrder.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (PNat.factorMultiset m) (PNat.factorMultiset n)) (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) m n)
Case conversion may be inaccurate. Consider using '#align pnat.factor_multiset_le_iff PNat.factorMultiset_le_iffₓ'. -/
/-- We now have four different results that all encode the
 idea that inequality of multisets corresponds to divisibility
 of positive integers. -/
theorem factorMultiset_le_iff {m n : ℕ+} : factorMultiset m ≤ factorMultiset n ↔ m ∣ n :=
  by
  constructor
  · intro h
    rw [← prod_factor_multiset m, ← prod_factor_multiset m]
    apply Dvd.intro (n.factor_multiset - m.factor_multiset).Prod
    rw [← PrimeMultiset.prod_add, PrimeMultiset.factorMultiset_prod, add_tsub_cancel_of_le h,
      prod_factor_multiset]
  · intro h
    rw [← mul_div_exact h, factor_multiset_mul]
    exact le_self_add
#align pnat.factor_multiset_le_iff PNat.factorMultiset_le_iff

/- warning: pnat.factor_multiset_le_iff' -> PNat.factorMultiset_le_iff' is a dubious translation:
lean 3 declaration is
  forall {m : PNat} {v : PrimeMultiset}, Iff (LE.le.{0} PrimeMultiset (Preorder.toLE.{0} PrimeMultiset (PartialOrder.toPreorder.{0} PrimeMultiset (OrderedAddCommMonoid.toPartialOrder.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) (PNat.factorMultiset m) v) (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) m (PrimeMultiset.prod v))
but is expected to have type
  forall {m : PNat} {v : PrimeMultiset}, Iff (LE.le.{0} PrimeMultiset (Preorder.toLE.{0} PrimeMultiset (PartialOrder.toPreorder.{0} PrimeMultiset (OrderedAddCommMonoid.toPartialOrder.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) (PNat.factorMultiset m) v) (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) m (PrimeMultiset.prod v))
Case conversion may be inaccurate. Consider using '#align pnat.factor_multiset_le_iff' PNat.factorMultiset_le_iff'ₓ'. -/
theorem factorMultiset_le_iff' {m : ℕ+} {v : PrimeMultiset} : factorMultiset m ≤ v ↔ m ∣ v.Prod :=
  by
  let h := @factor_multiset_le_iff m v.prod
  rw [v.factor_multiset_prod] at h
  exact h
#align pnat.factor_multiset_le_iff' PNat.factorMultiset_le_iff'

end PNat

namespace PrimeMultiset

/- warning: prime_multiset.prod_dvd_iff -> PrimeMultiset.prod_dvd_iff is a dubious translation:
lean 3 declaration is
  forall {u : PrimeMultiset} {v : PrimeMultiset}, Iff (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) (PrimeMultiset.prod u) (PrimeMultiset.prod v)) (LE.le.{0} PrimeMultiset (Preorder.toLE.{0} PrimeMultiset (PartialOrder.toPreorder.{0} PrimeMultiset (OrderedAddCommMonoid.toPartialOrder.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) u v)
but is expected to have type
  forall {u : PrimeMultiset} {v : PrimeMultiset}, Iff (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) (PrimeMultiset.prod u) (PrimeMultiset.prod v)) (LE.le.{0} PrimeMultiset (Preorder.toLE.{0} PrimeMultiset (PartialOrder.toPreorder.{0} PrimeMultiset (OrderedAddCommMonoid.toPartialOrder.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) u v)
Case conversion may be inaccurate. Consider using '#align prime_multiset.prod_dvd_iff PrimeMultiset.prod_dvd_iffₓ'. -/
theorem prod_dvd_iff {u v : PrimeMultiset} : u.Prod ∣ v.Prod ↔ u ≤ v :=
  by
  let h := @PNat.factorMultiset_le_iff' u.prod v
  rw [u.factor_multiset_prod] at h
  exact h.symm
#align prime_multiset.prod_dvd_iff PrimeMultiset.prod_dvd_iff

/- warning: prime_multiset.prod_dvd_iff' -> PrimeMultiset.prod_dvd_iff' is a dubious translation:
lean 3 declaration is
  forall {u : PrimeMultiset} {n : PNat}, Iff (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) (PrimeMultiset.prod u) n) (LE.le.{0} PrimeMultiset (Preorder.toLE.{0} PrimeMultiset (PartialOrder.toPreorder.{0} PrimeMultiset (OrderedAddCommMonoid.toPartialOrder.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset PrimeMultiset.canonicallyOrderedAddMonoid)))) u (PNat.factorMultiset n))
but is expected to have type
  forall {u : PrimeMultiset} {n : PNat}, Iff (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) (PrimeMultiset.prod u) n) (LE.le.{0} PrimeMultiset (Preorder.toLE.{0} PrimeMultiset (PartialOrder.toPreorder.{0} PrimeMultiset (OrderedAddCommMonoid.toPartialOrder.{0} PrimeMultiset (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{0} PrimeMultiset instPrimeMultisetCanonicallyOrderedAddMonoid)))) u (PNat.factorMultiset n))
Case conversion may be inaccurate. Consider using '#align prime_multiset.prod_dvd_iff' PrimeMultiset.prod_dvd_iff'ₓ'. -/
theorem prod_dvd_iff' {u : PrimeMultiset} {n : ℕ+} : u.Prod ∣ n ↔ u ≤ n.factorMultiset :=
  by
  let h := @prod_dvd_iff u n.factor_multiset
  rw [n.prod_factor_multiset] at h
  exact h
#align prime_multiset.prod_dvd_iff' PrimeMultiset.prod_dvd_iff'

end PrimeMultiset

namespace PNat

/- warning: pnat.factor_multiset_gcd -> PNat.factorMultiset_gcd is a dubious translation:
lean 3 declaration is
  forall (m : PNat) (n : PNat), Eq.{1} PrimeMultiset (PNat.factorMultiset (PNat.gcd m n)) (Inf.inf.{0} PrimeMultiset (SemilatticeInf.toHasInf.{0} PrimeMultiset (Lattice.toSemilatticeInf.{0} PrimeMultiset (DistribLattice.toLattice.{0} PrimeMultiset PrimeMultiset.distribLattice))) (PNat.factorMultiset m) (PNat.factorMultiset n))
but is expected to have type
  forall (m : PNat) (n : PNat), Eq.{1} PrimeMultiset (PNat.factorMultiset (PNat.gcd m n)) (Inf.inf.{0} PrimeMultiset (Lattice.toInf.{0} PrimeMultiset (DistribLattice.toLattice.{0} PrimeMultiset instPrimeMultisetDistribLattice)) (PNat.factorMultiset m) (PNat.factorMultiset n))
Case conversion may be inaccurate. Consider using '#align pnat.factor_multiset_gcd PNat.factorMultiset_gcdₓ'. -/
/-- The gcd and lcm operations on positive integers correspond
 to the inf and sup operations on multisets. -/
theorem factorMultiset_gcd (m n : ℕ+) :
    factorMultiset (gcd m n) = factorMultiset m ⊓ factorMultiset n :=
  by
  apply le_antisymm
  · apply le_inf_iff.mpr <;> constructor <;> apply factor_multiset_le_iff.mpr
    exact gcd_dvd_left m n
    exact gcd_dvd_right m n
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factor_multiset]
    apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
    exact inf_le_left
    exact inf_le_right
#align pnat.factor_multiset_gcd PNat.factorMultiset_gcd

/- warning: pnat.factor_multiset_lcm -> PNat.factorMultiset_lcm is a dubious translation:
lean 3 declaration is
  forall (m : PNat) (n : PNat), Eq.{1} PrimeMultiset (PNat.factorMultiset (PNat.lcm m n)) (Sup.sup.{0} PrimeMultiset (SemilatticeSup.toHasSup.{0} PrimeMultiset PrimeMultiset.semilatticeSup) (PNat.factorMultiset m) (PNat.factorMultiset n))
but is expected to have type
  forall (m : PNat) (n : PNat), Eq.{1} PrimeMultiset (PNat.factorMultiset (PNat.lcm m n)) (Sup.sup.{0} PrimeMultiset (SemilatticeSup.toSup.{0} PrimeMultiset instPrimeMultisetSemilatticeSup) (PNat.factorMultiset m) (PNat.factorMultiset n))
Case conversion may be inaccurate. Consider using '#align pnat.factor_multiset_lcm PNat.factorMultiset_lcmₓ'. -/
theorem factorMultiset_lcm (m n : ℕ+) :
    factorMultiset (lcm m n) = factorMultiset m ⊔ factorMultiset n :=
  by
  apply le_antisymm
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factor_multiset]
    apply lcm_dvd <;> rw [← factor_multiset_le_iff']
    exact le_sup_left
    exact le_sup_right
  · apply sup_le_iff.mpr <;> constructor <;> apply factor_multiset_le_iff.mpr
    exact dvd_lcm_left m n
    exact dvd_lcm_right m n
#align pnat.factor_multiset_lcm PNat.factorMultiset_lcm

/- warning: pnat.count_factor_multiset -> PNat.count_factorMultiset is a dubious translation:
lean 3 declaration is
  forall (m : PNat) (p : Nat.Primes) (k : Nat), Iff (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) (HPow.hPow.{0, 0, 0} PNat Nat PNat (instHPow.{0, 0} PNat Nat (Monoid.Pow.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat.Primes PNat (HasLiftT.mk.{1, 1} Nat.Primes PNat (CoeTCₓ.coe.{1, 1} Nat.Primes PNat (coeBase.{1, 1} Nat.Primes PNat Nat.Primes.coePNat))) p) k) m) (LE.le.{0} Nat Nat.hasLe k (Multiset.count.{0} Nat.Primes (fun (a : Nat.Primes) (b : Nat.Primes) => Subtype.decidableEq.{0} Nat (fun (x : Nat) => Nat.Prime x) (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) a b) p (PNat.factorMultiset m)))
but is expected to have type
  forall (m : PNat) (p : Nat.Primes) (k : Nat), Iff (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) (Pow.pow.{0, 0} PNat Nat (Monoid.Pow.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) (Nat.Primes.toPNat p) k) m) (LE.le.{0} Nat instLENat k (Multiset.count.{0} Nat.Primes (fun (a : Nat.Primes) (b : Nat.Primes) => Nat.instPrimesDecidableEq a b) p (PNat.factorMultiset m)))
Case conversion may be inaccurate. Consider using '#align pnat.count_factor_multiset PNat.count_factorMultisetₓ'. -/
/-- The number of occurrences of p in the factor multiset of m
 is the same as the p-adic valuation of m. -/
theorem count_factorMultiset (m : ℕ+) (p : Nat.Primes) (k : ℕ) :
    (p : ℕ+) ^ k ∣ m ↔ k ≤ m.factorMultiset.count p :=
  by
  intros
  rw [Multiset.le_count_iff_replicate_le]
  rw [← factor_multiset_le_iff, factor_multiset_pow, factor_multiset_of_prime]
  congr 2
  apply multiset.eq_replicate.mpr
  constructor
  · rw [Multiset.card_nsmul, PrimeMultiset.card_ofPrime, mul_one]
  · intro q h
    rw [PrimeMultiset.ofPrime, Multiset.nsmul_singleton _ k] at h
    exact Multiset.eq_of_mem_replicate h
#align pnat.count_factor_multiset PNat.count_factorMultiset

end PNat

namespace PrimeMultiset

/- warning: prime_multiset.prod_inf -> PrimeMultiset.prod_inf is a dubious translation:
lean 3 declaration is
  forall (u : PrimeMultiset) (v : PrimeMultiset), Eq.{1} PNat (PrimeMultiset.prod (Inf.inf.{0} PrimeMultiset (SemilatticeInf.toHasInf.{0} PrimeMultiset (Lattice.toSemilatticeInf.{0} PrimeMultiset (DistribLattice.toLattice.{0} PrimeMultiset PrimeMultiset.distribLattice))) u v)) (PNat.gcd (PrimeMultiset.prod u) (PrimeMultiset.prod v))
but is expected to have type
  forall (u : PrimeMultiset) (v : PrimeMultiset), Eq.{1} PNat (PrimeMultiset.prod (Inf.inf.{0} PrimeMultiset (Lattice.toInf.{0} PrimeMultiset (DistribLattice.toLattice.{0} PrimeMultiset instPrimeMultisetDistribLattice)) u v)) (PNat.gcd (PrimeMultiset.prod u) (PrimeMultiset.prod v))
Case conversion may be inaccurate. Consider using '#align prime_multiset.prod_inf PrimeMultiset.prod_infₓ'. -/
theorem prod_inf (u v : PrimeMultiset) : (u ⊓ v).Prod = PNat.gcd u.Prod v.Prod :=
  by
  let n := u.prod
  let m := v.prod
  change (u ⊓ v).Prod = PNat.gcd n m
  have : u = n.factor_multiset := u.factor_multiset_prod.symm; rw [this]
  have : v = m.factor_multiset := v.factor_multiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_gcd n m, PNat.prod_factorMultiset]
#align prime_multiset.prod_inf PrimeMultiset.prod_inf

/- warning: prime_multiset.prod_sup -> PrimeMultiset.prod_sup is a dubious translation:
lean 3 declaration is
  forall (u : PrimeMultiset) (v : PrimeMultiset), Eq.{1} PNat (PrimeMultiset.prod (Sup.sup.{0} PrimeMultiset (SemilatticeSup.toHasSup.{0} PrimeMultiset PrimeMultiset.semilatticeSup) u v)) (PNat.lcm (PrimeMultiset.prod u) (PrimeMultiset.prod v))
but is expected to have type
  forall (u : PrimeMultiset) (v : PrimeMultiset), Eq.{1} PNat (PrimeMultiset.prod (Sup.sup.{0} PrimeMultiset (SemilatticeSup.toSup.{0} PrimeMultiset instPrimeMultisetSemilatticeSup) u v)) (PNat.lcm (PrimeMultiset.prod u) (PrimeMultiset.prod v))
Case conversion may be inaccurate. Consider using '#align prime_multiset.prod_sup PrimeMultiset.prod_supₓ'. -/
theorem prod_sup (u v : PrimeMultiset) : (u ⊔ v).Prod = PNat.lcm u.Prod v.Prod :=
  by
  let n := u.prod
  let m := v.prod
  change (u ⊔ v).Prod = PNat.lcm n m
  have : u = n.factor_multiset := u.factor_multiset_prod.symm; rw [this]
  have : v = m.factor_multiset := v.factor_multiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_lcm n m, PNat.prod_factorMultiset]
#align prime_multiset.prod_sup PrimeMultiset.prod_sup

end PrimeMultiset

