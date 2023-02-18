/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey

! This file was ported from Lean 3 source module data.nat.periodic
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Periodic
import Mathbin.Data.Nat.Count
import Mathbin.Data.Nat.Interval

/-!
# Periodic Functions on ℕ

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file identifies a few functions on `ℕ` which are periodic, and also proves a lemma about
periodic predicates which helps determine their cardinality when filtering intervals over them.
-/


namespace Nat

open Nat Function

#print Nat.periodic_gcd /-
theorem periodic_gcd (a : ℕ) : Periodic (gcd a) a := by
  simp only [forall_const, gcd_add_self_right, eq_self_iff_true, periodic]
#align nat.periodic_gcd Nat.periodic_gcd
-/

#print Nat.periodic_coprime /-
theorem periodic_coprime (a : ℕ) : Periodic (coprime a) a := by
  simp only [coprime_add_self_right, forall_const, iff_self_iff, eq_iff_iff, periodic]
#align nat.periodic_coprime Nat.periodic_coprime
-/

#print Nat.periodic_mod /-
theorem periodic_mod (a : ℕ) : Periodic (fun n => n % a) a := by
  simp only [forall_const, eq_self_iff_true, add_mod_right, periodic]
#align nat.periodic_mod Nat.periodic_mod
-/

#print Nat.Function.Periodic.map_mod_nat /-
theorem Nat.Function.Periodic.map_mod_nat {α : Type _} {f : ℕ → α} {a : ℕ} (hf : Periodic f a) :
    ∀ n, f (n % a) = f n := fun n => by
  conv_rhs => rw [← Nat.mod_add_div n a, mul_comm, ← Nat.nsmul_eq_mul, hf.nsmul]
#align function.periodic.map_mod_nat Nat.Function.Periodic.map_mod_nat
-/

section Multiset

open Multiset

/- warning: nat.filter_multiset_Ico_card_eq_of_periodic -> Nat.filter_multiset_Ico_card_eq_of_periodic is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (a : Nat) (p : Nat -> Prop) [_inst_1 : DecidablePred.{1} Nat p], (Function.Periodic.{0, 0} Nat Prop Nat.hasAdd p a) -> (Eq.{1} Nat (coeFn.{1, 1} (AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{0} Nat) -> Nat) (AddMonoidHom.hasCoeToFun.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{0} Nat) (Multiset.filter.{0} Nat p (fun (a : Nat) => _inst_1 a) (Multiset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n a)))) (Nat.count p (fun (a : Nat) => _inst_1 a) a))
but is expected to have type
  forall (n : Nat) (a : Nat) (p : Nat -> Prop) [_inst_1 : DecidablePred.{1} Nat p], (Function.Periodic.{0, 0} Nat Prop instAddNat p a) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} Nat) => Nat) (Multiset.filter.{0} Nat p (fun (a : Nat) => _inst_1 a) (Multiset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n a)))) (FunLike.coe.{1, 1, 1} (AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} Nat) (fun (_x : Multiset.{0} Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} Nat) => Nat) _x) (AddHomClass.toFunLike.{0, 0, 0} (AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} Nat) Nat (AddZeroClass.toAdd.{0} (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{0, 0, 0} (AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{0} Nat) (Multiset.filter.{0} Nat p (fun (a : Nat) => _inst_1 a) (Multiset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n a)))) (Nat.count p (fun (a : Nat) => _inst_1 a) a))
Case conversion may be inaccurate. Consider using '#align nat.filter_multiset_Ico_card_eq_of_periodic Nat.filter_multiset_Ico_card_eq_of_periodicₓ'. -/
/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
theorem filter_multiset_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (pp : Periodic p a) : (filter p (Ico n (n + a))).card = a.count p :=
  by
  rw [count_eq_card_filter_range, Finset.card, Finset.filter_val, Finset.range_val, ←
    multiset_Ico_map_mod n, ← map_count_true_eq_filter_card, ← map_count_true_eq_filter_card,
    map_map, Function.comp]
  simp only [pp.map_mod_nat]
#align nat.filter_multiset_Ico_card_eq_of_periodic Nat.filter_multiset_Ico_card_eq_of_periodic

end Multiset

section Finset

open Finset

#print Nat.filter_Ico_card_eq_of_periodic /-
/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
theorem filter_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (pp : Periodic p a) : ((Ico n (n + a)).filterₓ p).card = a.count p :=
  filter_multiset_Ico_card_eq_of_periodic n a p pp
#align nat.filter_Ico_card_eq_of_periodic Nat.filter_Ico_card_eq_of_periodic
-/

end Finset

end Nat

