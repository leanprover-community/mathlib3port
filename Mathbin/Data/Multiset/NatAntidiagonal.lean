/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.multiset.nat_antidiagonal
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Nodup
import Mathbin.Data.List.NatAntidiagonal

/-!
# Antidiagonals in ℕ × ℕ as multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the antidiagonals of ℕ × ℕ as multisets: the `n`-th antidiagonal is the multiset
of pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines file `data.list.nat_antidiagonal` and is further refined by file
`data.finset.nat_antidiagonal`.
-/


namespace Multiset

namespace Nat

#print Multiset.Nat.antidiagonal /-
/-- The antidiagonal of a natural number `n` is
    the multiset of pairs `(i, j)` such that `i + j = n`. -/
def antidiagonal (n : ℕ) : Multiset (ℕ × ℕ) :=
  List.Nat.antidiagonal n
#align multiset.nat.antidiagonal Multiset.Nat.antidiagonal
-/

#print Multiset.Nat.mem_antidiagonal /-
/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp]
theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ antidiagonal n ↔ x.1 + x.2 = n := by
  rw [antidiagonal, mem_coe, List.Nat.mem_antidiagonal]
#align multiset.nat.mem_antidiagonal Multiset.Nat.mem_antidiagonal
-/

/- warning: multiset.nat.card_antidiagonal -> Multiset.Nat.card_antidiagonal is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Nat (coeFn.{1, 1} (AddMonoidHom.{0, 0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (Multiset.orderedCancelAddCommMonoid.{0} (Prod.{0, 0} Nat Nat))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{0, 0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (Multiset.orderedCancelAddCommMonoid.{0} (Prod.{0, 0} Nat Nat))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{0} (Prod.{0, 0} Nat Nat)) -> Nat) (AddMonoidHom.hasCoeToFun.{0, 0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (Multiset.orderedCancelAddCommMonoid.{0} (Prod.{0, 0} Nat Nat))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{0} (Prod.{0, 0} Nat Nat)) (Multiset.Nat.antidiagonal n)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall (n : Nat), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} (Prod.{0, 0} Nat Nat)) => Nat) (Multiset.Nat.antidiagonal n)) (FunLike.coe.{1, 1, 1} (AddMonoidHom.{0, 0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} (Prod.{0, 0} Nat Nat))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} (Prod.{0, 0} Nat Nat)) (fun (_x : Multiset.{0} (Prod.{0, 0} Nat Nat)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} (Prod.{0, 0} Nat Nat)) => Nat) _x) (AddHomClass.toFunLike.{0, 0, 0} (AddMonoidHom.{0, 0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} (Prod.{0, 0} Nat Nat))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} (Prod.{0, 0} Nat Nat)) Nat (AddZeroClass.toAdd.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} (Prod.{0, 0} Nat Nat)))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{0, 0, 0} (AddMonoidHom.{0, 0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} (Prod.{0, 0} Nat Nat))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} (Prod.{0, 0} Nat Nat)) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} (Prod.{0, 0} Nat Nat))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{0, 0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} (Prod.{0, 0} Nat Nat))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{0} (Prod.{0, 0} Nat Nat)) (Multiset.Nat.antidiagonal n)) (HAdd.hAdd.{0, 0, 0} Nat ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} (Prod.{0, 0} Nat Nat)) => Nat) (Multiset.Nat.antidiagonal n)) Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} (Prod.{0, 0} Nat Nat)) => Nat) (Multiset.Nat.antidiagonal n)) 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align multiset.nat.card_antidiagonal Multiset.Nat.card_antidiagonalₓ'. -/
/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp]
theorem card_antidiagonal (n : ℕ) : (antidiagonal n).card = n + 1 := by
  rw [antidiagonal, coe_card, List.Nat.length_antidiagonal]
#align multiset.nat.card_antidiagonal Multiset.Nat.card_antidiagonal

#print Multiset.Nat.antidiagonal_zero /-
/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
  rfl
#align multiset.nat.antidiagonal_zero Multiset.Nat.antidiagonal_zero
-/

#print Multiset.Nat.nodup_antidiagonal /-
/-- The antidiagonal of `n` does not contain duplicate entries. -/
@[simp]
theorem nodup_antidiagonal (n : ℕ) : Nodup (antidiagonal n) :=
  coe_nodup.2 <| List.Nat.nodup_antidiagonal n
#align multiset.nat.nodup_antidiagonal Multiset.Nat.nodup_antidiagonal
-/

#print Multiset.Nat.antidiagonal_succ /-
@[simp]
theorem antidiagonal_succ {n : ℕ} :
    antidiagonal (n + 1) = (0, n + 1) ::ₘ (antidiagonal n).map (Prod.map Nat.succ id) := by
  simp only [antidiagonal, List.Nat.antidiagonal_succ, coe_map, cons_coe]
#align multiset.nat.antidiagonal_succ Multiset.Nat.antidiagonal_succ
-/

#print Multiset.Nat.antidiagonal_succ' /-
theorem antidiagonal_succ' {n : ℕ} :
    antidiagonal (n + 1) = (n + 1, 0) ::ₘ (antidiagonal n).map (Prod.map id Nat.succ) := by
  rw [antidiagonal, List.Nat.antidiagonal_succ', ← coe_add, add_comm, antidiagonal, coe_map,
    coe_add, List.singleton_append, cons_coe]
#align multiset.nat.antidiagonal_succ' Multiset.Nat.antidiagonal_succ'
-/

#print Multiset.Nat.antidiagonal_succ_succ' /-
theorem antidiagonal_succ_succ' {n : ℕ} :
    antidiagonal (n + 2) =
      (0, n + 2) ::ₘ (n + 2, 0) ::ₘ (antidiagonal n).map (Prod.map Nat.succ Nat.succ) :=
  by
  rw [antidiagonal_succ, antidiagonal_succ', map_cons, map_map, Prod_map]
  rfl
#align multiset.nat.antidiagonal_succ_succ' Multiset.Nat.antidiagonal_succ_succ'
-/

#print Multiset.Nat.map_swap_antidiagonal /-
theorem map_swap_antidiagonal {n : ℕ} : (antidiagonal n).map Prod.swap = antidiagonal n := by
  rw [antidiagonal, coe_map, List.Nat.map_swap_antidiagonal, coe_reverse]
#align multiset.nat.map_swap_antidiagonal Multiset.Nat.map_swap_antidiagonal
-/

end Nat

end Multiset

