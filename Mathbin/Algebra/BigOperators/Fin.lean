/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen

! This file was ported from Lean 3 source module algebra.big_operators.fin
! leanprover-community/mathlib commit cc5dd6244981976cc9da7afc4eee5682b037a013
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Data.Fintype.Fin
import Mathbin.Data.List.FinRange
import Mathbin.Logic.Equiv.Fin

/-!
# Big operators and `fin`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Some results about products and sums over the type `fin`.

The most important results are the induction formulas `fin.prod_univ_cast_succ`
and `fin.prod_univ_succ`, and the formula `fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

## Main declarations

* `fin_function_fin_equiv`: An explicit equivalence between `fin n → fin m` and `fin (m ^ n)`.
-/


open BigOperators

open Finset

variable {α : Type _} {β : Type _}

namespace Finset

#print Finset.prod_range /-
@[to_additive]
theorem prod_range [CommMonoid β] {n : ℕ} (f : ℕ → β) :
    (∏ i in Finset.range n, f i) = ∏ i : Fin n, f i :=
  prod_bij' (fun k w => ⟨k, mem_range.mp w⟩) (fun a ha => mem_univ _)
    (fun a ha => congr_arg _ (Fin.val_mk _).symm) (fun a m => a) (fun a m => mem_range.mpr a.Prop)
    (fun a ha => Fin.val_mk _) fun a ha => Fin.eta _ _
#align finset.prod_range Finset.prod_range
#align finset.sum_range Finset.sum_range
-/

end Finset

namespace Fin

/- warning: fin.prod_univ_def -> Fin.prod_univ_def is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (f : (Fin n) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f i)) (List.prod.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (List.map.{0, u1} (Fin n) β f (List.finRange n)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (f : (Fin n) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f i)) (List.prod.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (List.map.{0, u1} (Fin n) β f (List.finRange n)))
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_def Fin.prod_univ_defₓ'. -/
@[to_additive]
theorem prod_univ_def [CommMonoid β] {n : ℕ} (f : Fin n → β) :
    (∏ i, f i) = ((List.finRange n).map f).Prod := by simp [univ_def]
#align fin.prod_univ_def Fin.prod_univ_def
#align fin.sum_univ_def Fin.sum_univ_def

/- warning: fin.prod_of_fn -> Fin.prod_ofFn is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (f : (Fin n) -> β), Eq.{succ u1} β (List.prod.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (List.ofFn.{u1} β n f)) (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f i))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (f : (Fin n) -> β), Eq.{succ u1} β (List.prod.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (List.ofFn.{u1} β n f)) (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f i))
Case conversion may be inaccurate. Consider using '#align fin.prod_of_fn Fin.prod_ofFnₓ'. -/
@[to_additive]
theorem prod_ofFn [CommMonoid β] {n : ℕ} (f : Fin n → β) : (List.ofFn f).Prod = ∏ i, f i := by
  rw [List.ofFn_eq_map, prod_univ_def]
#align fin.prod_of_fn Fin.prod_ofFn
#align fin.sum_of_fn Fin.sum_ofFn

/- warning: fin.prod_univ_zero -> Fin.prod_univ_zero is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Fin.fintype (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => f i)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Fin.fintype (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => f i)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_zero Fin.prod_univ_zeroₓ'. -/
/-- A product of a function `f : fin 0 → β` is `1` because `fin 0` is empty -/
@[to_additive "A sum of a function `f : fin 0 → β` is `0` because `fin 0` is empty"]
theorem prod_univ_zero [CommMonoid β] (f : Fin 0 → β) : (∏ i, f i) = 1 :=
  rfl
#align fin.prod_univ_zero Fin.prod_univ_zero
#align fin.sum_univ_zero Fin.sum_univ_zero

/- warning: fin.prod_univ_succ_above -> Fin.prod_univ_succAbove is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_succ_above Fin.prod_univ_succAboveₓ'. -/
/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f x`, for some `x : fin (n + 1)` times the remaining product -/
@[to_additive
      "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of `f x`,\nfor some `x : fin (n + 1)` plus the remaining product"]
theorem prod_univ_succAbove [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) (x : Fin (n + 1)) :
    (∏ i, f i) = f x * ∏ i : Fin n, f (x.succAbove i) := by
  rw [univ_succ_above, prod_cons, Finset.prod_map, RelEmbedding.coe_toEmbedding]
#align fin.prod_univ_succ_above Fin.prod_univ_succAbove
#align fin.sum_univ_succ_above Fin.sum_univ_succAbove

/- warning: fin.prod_univ_succ -> Fin.prod_univ_succ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) _inst_1 (Finset.univ.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f (Fin.succ n i))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _inst_1 (Finset.univ.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f (Fin.succ n i))))
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_succ Fin.prod_univ_succₓ'. -/
/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive
      "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of `f 0`\nplus the remaining product"]
theorem prod_univ_succ [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    (∏ i, f i) = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0
#align fin.prod_univ_succ Fin.prod_univ_succ
#align fin.sum_univ_succ Fin.sum_univ_succ

/- warning: fin.prod_univ_cast_succ -> Fin.prod_univ_castSucc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_cast_succ Fin.prod_univ_castSuccₓ'. -/
/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f (fin.last n)` plus the remaining product -/
@[to_additive
      "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of\n`f (fin.last n)` plus the remaining sum"]
theorem prod_univ_castSucc [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    (∏ i, f i) = (∏ i : Fin n, f i.cast_succ) * f (last n) := by
  simpa [mul_comm] using prod_univ_succ_above f (last n)
#align fin.prod_univ_cast_succ Fin.prod_univ_castSucc
#align fin.sum_univ_cast_succ Fin.sum_univ_castSucc

/- warning: fin.prod_cons -> Fin.prod_cons is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (x : β) (f : (Fin n) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (Nat.succ n)) _inst_1 (Finset.univ.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n))) (fun (i : Fin (Nat.succ n)) => Fin.cons.{u1} n (fun (ᾰ : Fin (Nat.succ n)) => β) x f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) x (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f i)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (x : β) (f : (Fin n) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (Nat.succ n)) _inst_1 (Finset.univ.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n))) (fun (i : Fin (Nat.succ n)) => Fin.cons.{u1} n (fun (ᾰ : Fin (Nat.succ n)) => β) x f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) x (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f i)))
Case conversion may be inaccurate. Consider using '#align fin.prod_cons Fin.prod_consₓ'. -/
@[to_additive]
theorem prod_cons [CommMonoid β] {n : ℕ} (x : β) (f : Fin n → β) :
    (∏ i : Fin n.succ, (cons x f : Fin n.succ → β) i) = x * ∏ i : Fin n, f i := by
  simp_rw [prod_univ_succ, cons_zero, cons_succ]
#align fin.prod_cons Fin.prod_cons
#align fin.sum_cons Fin.sum_cons

/- warning: fin.prod_univ_one -> Fin.prod_univ_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Fin.fintype (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) => f i)) (f (OfNat.ofNat.{0} (Fin (One.one.{0} Nat Nat.hasOne)) 0 (OfNat.mk.{0} (Fin (One.one.{0} Nat Nat.hasOne)) 0 (Zero.zero.{0} (Fin (One.one.{0} Nat Nat.hasOne)) (Fin.hasZeroOfNeZero (One.one.{0} Nat Nat.hasOne) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fin.fintype (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => f i)) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_one Fin.prod_univ_oneₓ'. -/
@[to_additive sum_univ_one]
theorem prod_univ_one [CommMonoid β] (f : Fin 1 → β) : (∏ i, f i) = f 0 := by simp
#align fin.prod_univ_one Fin.prod_univ_one
#align fin.sum_univ_one Fin.sum_univ_one

/- warning: fin.prod_univ_two -> Fin.prod_univ_two is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (f (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_two Fin.prod_univ_twoₓ'. -/
@[simp, to_additive]
theorem prod_univ_two [CommMonoid β] (f : Fin 2 → β) : (∏ i, f i) = f 0 * f 1 := by
  simp [prod_univ_succ]
#align fin.prod_univ_two Fin.prod_univ_two
#align fin.sum_univ_two Fin.sum_univ_two

/- warning: fin.prod_univ_three -> Fin.prod_univ_three is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin.fintype (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))) (f (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))))) (f (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (bit0.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (Fin.fintype (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))) (fun (i : Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 2 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 2 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_three Fin.prod_univ_threeₓ'. -/
@[to_additive]
theorem prod_univ_three [CommMonoid β] (f : Fin 3 → β) : (∏ i, f i) = f 0 * f 1 * f 2 :=
  by
  rw [prod_univ_cast_succ, prod_univ_two]
  rfl
#align fin.prod_univ_three Fin.prod_univ_three
#align fin.sum_univ_three Fin.sum_univ_three

/- warning: fin.prod_univ_four -> Fin.prod_univ_four is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 4 (OfNat.mk.{0} Nat 4 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 4 (OfNat.mk.{0} Nat 4 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 4 (OfNat.mk.{0} Nat 4 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (Fin.fintype (OfNat.ofNat.{0} Nat 4 (OfNat.mk.{0} Nat 4 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 4 (OfNat.mk.{0} Nat 4 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (ZeroLEOneClass.NeZero.four.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))) (f (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (ZeroLEOneClass.NeZero.four.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))))) (f (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 2 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 2 (bit0.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (ZeroLEOneClass.NeZero.four.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))))) (f (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 3 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 3 (bit1.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (ZeroLEOneClass.NeZero.four.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))) (Fin.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (ZeroLEOneClass.NeZero.four.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) (Fin.fintype (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))) (fun (i : Fin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) 2 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)) 2 (NeZero.succ (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) 3 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)) 3 (NeZero.succ (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))))))
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_four Fin.prod_univ_fourₓ'. -/
@[to_additive]
theorem prod_univ_four [CommMonoid β] (f : Fin 4 → β) : (∏ i, f i) = f 0 * f 1 * f 2 * f 3 :=
  by
  rw [prod_univ_cast_succ, prod_univ_three]
  rfl
#align fin.prod_univ_four Fin.prod_univ_four
#align fin.sum_univ_four Fin.sum_univ_four

/- warning: fin.prod_univ_five -> Fin.prod_univ_five is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 5 (OfNat.mk.{0} Nat 5 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 5 (OfNat.mk.{0} Nat 5 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 5 (OfNat.mk.{0} Nat 5 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (Fin.fintype (OfNat.ofNat.{0} Nat 5 (OfNat.mk.{0} Nat 5 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 5 (OfNat.mk.{0} Nat 5 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 0 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 0 (Zero.zero.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasZeroOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NeZero.succ (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))) (f (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 1 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 1 (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NeZero.succ (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))))) (f (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 2 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 2 (bit0.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NeZero.succ (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (f (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 3 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 3 (bit1.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NeZero.succ (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NeZero.succ (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (f (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 4 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 4 (bit0.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (bit0.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NeZero.succ (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : (Fin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) _inst_1 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) (Fin.fintype (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))) (fun (i : Fin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) 2 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)) 2 (NeZero.succ (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) 3 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)) 3 (NeZero.succ (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) 4 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)) 4 (NeZero.succ (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))))))
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_five Fin.prod_univ_fiveₓ'. -/
@[to_additive]
theorem prod_univ_five [CommMonoid β] (f : Fin 5 → β) : (∏ i, f i) = f 0 * f 1 * f 2 * f 3 * f 4 :=
  by
  rw [prod_univ_cast_succ, prod_univ_four]
  rfl
#align fin.prod_univ_five Fin.prod_univ_five
#align fin.sum_univ_five Fin.sum_univ_five

/- warning: fin.prod_univ_six -> Fin.prod_univ_six is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_six Fin.prod_univ_sixₓ'. -/
@[to_additive]
theorem prod_univ_six [CommMonoid β] (f : Fin 6 → β) :
    (∏ i, f i) = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 :=
  by
  rw [prod_univ_cast_succ, prod_univ_five]
  rfl
#align fin.prod_univ_six Fin.prod_univ_six
#align fin.sum_univ_six Fin.sum_univ_six

/- warning: fin.prod_univ_seven -> Fin.prod_univ_seven is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_seven Fin.prod_univ_sevenₓ'. -/
@[to_additive]
theorem prod_univ_seven [CommMonoid β] (f : Fin 7 → β) :
    (∏ i, f i) = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 :=
  by
  rw [prod_univ_cast_succ, prod_univ_six]
  rfl
#align fin.prod_univ_seven Fin.prod_univ_seven
#align fin.sum_univ_seven Fin.sum_univ_seven

/- warning: fin.prod_univ_eight -> Fin.prod_univ_eight is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_eight Fin.prod_univ_eightₓ'. -/
@[to_additive]
theorem prod_univ_eight [CommMonoid β] (f : Fin 8 → β) :
    (∏ i, f i) = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 :=
  by
  rw [prod_univ_cast_succ, prod_univ_seven]
  rfl
#align fin.prod_univ_eight Fin.prod_univ_eight
#align fin.sum_univ_eight Fin.sum_univ_eight

/- warning: fin.sum_pow_mul_eq_add_pow -> Fin.sum_pow_mul_eq_add_pow is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (a : R) (b : R), Eq.{succ u1} R (Finset.sum.{u1, 0} R (Finset.{0} (Fin n)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Finset.univ.{0} (Finset.{0} (Fin n)) (Finset.fintype.{0} (Fin n) (Fin.fintype n))) (fun (s : Finset.{0} (Fin n)) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) a (Finset.card.{0} (Fin n) s)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) b (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (Finset.card.{0} (Fin n) s))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) a b) n)
but is expected to have type
  forall {n : Nat} {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (a : R) (b : R), Eq.{succ u1} R (Finset.sum.{u1, 0} R (Finset.{0} (Fin n)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Finset.univ.{0} (Finset.{0} (Fin n)) (Finset.fintype.{0} (Fin n) (Fin.fintype n))) (fun (s : Finset.{0} (Fin n)) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) a (Finset.card.{0} (Fin n) s)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) b (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (Finset.card.{0} (Fin n) s))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) a b) n)
Case conversion may be inaccurate. Consider using '#align fin.sum_pow_mul_eq_add_pow Fin.sum_pow_mul_eq_add_powₓ'. -/
theorem sum_pow_mul_eq_add_pow {n : ℕ} {R : Type _} [CommSemiring R] (a b : R) :
    (∑ s : Finset (Fin n), a ^ s.card * b ^ (n - s.card)) = (a + b) ^ n := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin n) a b
#align fin.sum_pow_mul_eq_add_pow Fin.sum_pow_mul_eq_add_pow

#print Fin.prod_const /-
theorem prod_const [CommMonoid α] (n : ℕ) (x : α) : (∏ i : Fin n, x) = x ^ n := by simp
#align fin.prod_const Fin.prod_const
-/

#print Fin.sum_const /-
theorem sum_const [AddCommMonoid α] (n : ℕ) (x : α) : (∑ i : Fin n, x) = n • x := by simp
#align fin.sum_const Fin.sum_const
-/

/- warning: fin.prod_Ioi_zero -> Fin.prod_Ioi_zero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {n : Nat} {v : (Fin (Nat.succ n)) -> M}, Eq.{succ u1} M (Finset.prod.{u1, 0} M (Fin (Nat.succ n)) _inst_1 (Finset.Ioi.{0} (Fin (Nat.succ n)) (PartialOrder.toPreorder.{0} (Fin (Nat.succ n)) (Fin.partialOrder (Nat.succ n))) (Fin.locallyFiniteOrderTop (Nat.succ n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))) (fun (i : Fin (Nat.succ n)) => v i)) (Finset.prod.{u1, 0} M (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (j : Fin n) => v (Fin.succ n j)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {n : Nat} {v : (Fin (Nat.succ n)) -> M}, Eq.{succ u1} M (Finset.prod.{u1, 0} M (Fin (Nat.succ n)) _inst_1 (Finset.Ioi.{0} (Fin (Nat.succ n)) (PartialOrder.toPreorder.{0} (Fin (Nat.succ n)) (Fin.instPartialOrderFin (Nat.succ n))) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin (Nat.succ n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))) (fun (i : Fin (Nat.succ n)) => v i)) (Finset.prod.{u1, 0} M (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (j : Fin n) => v (Fin.succ n j)))
Case conversion may be inaccurate. Consider using '#align fin.prod_Ioi_zero Fin.prod_Ioi_zeroₓ'. -/
@[to_additive]
theorem prod_Ioi_zero {M : Type _} [CommMonoid M] {n : ℕ} {v : Fin n.succ → M} :
    (∏ i in Ioi 0, v i) = ∏ j : Fin n, v j.succ := by
  rw [Ioi_zero_eq_map, Finset.prod_map, RelEmbedding.coe_toEmbedding, coe_succ_embedding]
#align fin.prod_Ioi_zero Fin.prod_Ioi_zero
#align fin.sum_Ioi_zero Fin.sum_Ioi_zero

/- warning: fin.prod_Ioi_succ -> Fin.prod_Ioi_succ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {n : Nat} (i : Fin n) (v : (Fin (Nat.succ n)) -> M), Eq.{succ u1} M (Finset.prod.{u1, 0} M (Fin (Nat.succ n)) _inst_1 (Finset.Ioi.{0} (Fin (Nat.succ n)) (PartialOrder.toPreorder.{0} (Fin (Nat.succ n)) (Fin.partialOrder (Nat.succ n))) (Fin.locallyFiniteOrderTop (Nat.succ n)) (Fin.succ n i)) (fun (j : Fin (Nat.succ n)) => v j)) (Finset.prod.{u1, 0} M (Fin n) _inst_1 (Finset.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderTop n) i) (fun (j : Fin n) => v (Fin.succ n j)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {n : Nat} (i : Fin n) (v : (Fin (Nat.succ n)) -> M), Eq.{succ u1} M (Finset.prod.{u1, 0} M (Fin (Nat.succ n)) _inst_1 (Finset.Ioi.{0} (Fin (Nat.succ n)) (PartialOrder.toPreorder.{0} (Fin (Nat.succ n)) (Fin.instPartialOrderFin (Nat.succ n))) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin (Nat.succ n)) (Fin.succ n i)) (fun (j : Fin (Nat.succ n)) => v j)) (Finset.prod.{u1, 0} M (Fin n) _inst_1 (Finset.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin n) i) (fun (j : Fin n) => v (Fin.succ n j)))
Case conversion may be inaccurate. Consider using '#align fin.prod_Ioi_succ Fin.prod_Ioi_succₓ'. -/
@[to_additive]
theorem prod_Ioi_succ {M : Type _} [CommMonoid M] {n : ℕ} (i : Fin n) (v : Fin n.succ → M) :
    (∏ j in Ioi i.succ, v j) = ∏ j in Ioi i, v j.succ := by
  rw [Ioi_succ, Finset.prod_map, RelEmbedding.coe_toEmbedding, coe_succ_embedding]
#align fin.prod_Ioi_succ Fin.prod_Ioi_succ
#align fin.sum_Ioi_succ Fin.sum_Ioi_succ

/- warning: fin.prod_congr' -> Fin.prod_congr' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {a : Nat} {b : Nat} (f : (Fin b) -> M) (h : Eq.{1} Nat a b), Eq.{succ u1} M (Finset.prod.{u1, 0} M (Fin a) _inst_1 (Finset.univ.{0} (Fin a) (Fin.fintype a)) (fun (i : Fin a) => f (coeFn.{1, 1} (OrderIso.{0, 0} (Fin a) (Fin b) (Fin.hasLe a) (Fin.hasLe b)) (fun (_x : RelIso.{0, 0} (Fin a) (Fin b) (LE.le.{0} (Fin a) (Fin.hasLe a)) (LE.le.{0} (Fin b) (Fin.hasLe b))) => (Fin a) -> (Fin b)) (RelIso.hasCoeToFun.{0, 0} (Fin a) (Fin b) (LE.le.{0} (Fin a) (Fin.hasLe a)) (LE.le.{0} (Fin b) (Fin.hasLe b))) (Fin.cast a b h) i))) (Finset.prod.{u1, 0} M (Fin b) _inst_1 (Finset.univ.{0} (Fin b) (Fin.fintype b)) (fun (i : Fin b) => f i))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {a : Nat} {b : Nat} (f : (Fin b) -> M) (h : Eq.{1} Nat a b), Eq.{succ u1} M (Finset.prod.{u1, 0} M (Fin a) _inst_1 (Finset.univ.{0} (Fin a) (Fin.fintype a)) (fun (i : Fin a) => f (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} (Fin a) (Fin b) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin a) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin a) => LE.le.{0} (Fin a) (instLEFin a) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin b) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin b) => LE.le.{0} (Fin b) (instLEFin b) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (Fin a) (fun (_x : Fin a) => Fin b) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} (Fin a) (Fin b) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin a) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin a) => LE.le.{0} (Fin a) (instLEFin a) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin b) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin b) => LE.le.{0} (Fin b) (instLEFin b) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (Fin a) (Fin b) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin a) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin a) => LE.le.{0} (Fin a) (instLEFin a) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin b) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin b) => LE.le.{0} (Fin b) (instLEFin b) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{0, 0} (Fin a) (Fin b) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin a) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin a) => LE.le.{0} (Fin a) (instLEFin a) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin b) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin b) => LE.le.{0} (Fin b) (instLEFin b) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) (Fin.cast a b h) i))) (Finset.prod.{u1, 0} M (Fin b) _inst_1 (Finset.univ.{0} (Fin b) (Fin.fintype b)) (fun (i : Fin b) => f i))
Case conversion may be inaccurate. Consider using '#align fin.prod_congr' Fin.prod_congr'ₓ'. -/
@[to_additive]
theorem prod_congr' {M : Type _} [CommMonoid M] {a b : ℕ} (f : Fin b → M) (h : a = b) :
    (∏ i : Fin a, f (cast h i)) = ∏ i : Fin b, f i :=
  by
  subst h
  congr
  ext
  congr
  ext
  rw [coe_cast]
#align fin.prod_congr' Fin.prod_congr'
#align fin.sum_congr' Fin.sum_congr'

/- warning: fin.prod_univ_add -> Fin.prod_univ_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.prod_univ_add Fin.prod_univ_addₓ'. -/
@[to_additive]
theorem prod_univ_add {M : Type _} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M) :
    (∏ i : Fin (a + b), f i) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i) :=
  by
  rw [Fintype.prod_equiv fin_sum_fin_equiv.symm f fun i => f (fin_sum_fin_equiv.to_fun i)]; swap
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]
  apply Fintype.prod_sum_type
#align fin.prod_univ_add Fin.prod_univ_add
#align fin.sum_univ_add Fin.sum_univ_add

/- warning: fin.prod_trunc -> Fin.prod_trunc is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {a : Nat} {b : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) -> M), (forall (j : Fin b), Eq.{succ u1} M (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin b) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Fin.hasLe b) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b))) (fun (_x : RelEmbedding.{0, 0} (Fin b) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (LE.le.{0} (Fin b) (Fin.hasLe b)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)))) => (Fin b) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin b) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (LE.le.{0} (Fin b) (Fin.hasLe b)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)))) (Fin.natAdd a b) j)) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))))) -> (Eq.{succ u1} M (Finset.prod.{u1, 0} M (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) _inst_1 (Finset.univ.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) => f i)) (Finset.prod.{u1, 0} M (Fin a) _inst_1 (Finset.univ.{0} (Fin a) (Fin.fintype a)) (fun (i : Fin a) => f (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin a) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Fin.hasLe a) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b))) (fun (_x : RelEmbedding.{0, 0} (Fin a) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (LE.le.{0} (Fin a) (Fin.hasLe a)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)))) => (Fin a) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin a) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (LE.le.{0} (Fin a) (Fin.hasLe a)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)))) (Fin.castLE a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b) (Nat.le.intro a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b) b (rfl.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)))) i))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {a : Nat} {b : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) -> M), (forall (j : Fin b), Eq.{succ u1} M (f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin b) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (instLEFin b) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b))) (Fin b) (fun (_x : Fin b) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin b) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin b) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (instLEFin b) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b))) (Fin b) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin b) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin b) => LE.le.{0} (Fin b) (instLEFin b) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin b) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin b) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin b) => LE.le.{0} (Fin b) (instLEFin b) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.natAdd a b) j)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))) -> (Eq.{succ u1} M (Finset.prod.{u1, 0} M (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) _inst_1 (Finset.univ.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) => f i)) (Finset.prod.{u1, 0} M (Fin a) _inst_1 (Finset.univ.{0} (Fin a) (Fin.fintype a)) (fun (i : Fin a) => f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin a) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (instLEFin a) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b))) (Fin a) (fun (_x : Fin a) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin a) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin a) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (instLEFin a) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b))) (Fin a) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin a) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin a) => LE.le.{0} (Fin a) (instLEFin a) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin a) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin a) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin a) => LE.le.{0} (Fin a) (instLEFin a) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castLE a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b) (Nat.le.intro a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b) b (rfl.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)))) i))))
Case conversion may be inaccurate. Consider using '#align fin.prod_trunc Fin.prod_truncₓ'. -/
@[to_additive]
theorem prod_trunc {M : Type _} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M)
    (hf : ∀ j : Fin b, f (natAdd a j) = 1) :
    (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (castLE (Nat.le.intro rfl) i) := by
  simpa only [prod_univ_add, Fintype.prod_eq_one _ hf, mul_one]
#align fin.prod_trunc Fin.prod_trunc
#align fin.sum_trunc Fin.sum_trunc

section PartialProd

variable [Monoid α] {n : ℕ}

#print Fin.partialProd /-
/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_prod f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive
      "For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_sum f` is\n`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`."]
def partialProd (f : Fin n → α) (i : Fin (n + 1)) : α :=
  ((List.ofFn f).take i).Prod
#align fin.partial_prod Fin.partialProd
#align fin.partial_sum Fin.partialSum
-/

/- warning: fin.partial_prod_zero -> Fin.partialProd_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} (f : (Fin n) -> α), Eq.{succ u1} α (Fin.partialProd.{u1} α _inst_1 n f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} (f : (Fin n) -> α), Eq.{succ u1} α (Fin.partialProd.{u1} α _inst_1 n f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align fin.partial_prod_zero Fin.partialProd_zeroₓ'. -/
@[simp, to_additive]
theorem partialProd_zero (f : Fin n → α) : partialProd f 0 = 1 := by simp [partial_prod]
#align fin.partial_prod_zero Fin.partialProd_zero
#align fin.partial_sum_zero Fin.partialSum_zero

/- warning: fin.partial_prod_succ -> Fin.partialProd_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} (f : (Fin n) -> α) (j : Fin n), Eq.{succ u1} α (Fin.partialProd.{u1} α _inst_1 n f (Fin.succ n j)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Fin.partialProd.{u1} α _inst_1 n f (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) j)) (f j))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} (f : (Fin n) -> α) (j : Fin n), Eq.{succ u1} α (Fin.partialProd.{u1} α _inst_1 n f (Fin.succ n j)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Fin.partialProd.{u1} α _inst_1 n f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.castSucc n) j)) (f j))
Case conversion may be inaccurate. Consider using '#align fin.partial_prod_succ Fin.partialProd_succₓ'. -/
@[to_additive]
theorem partialProd_succ (f : Fin n → α) (j : Fin n) :
    partialProd f j.succ = partialProd f j.cast_succ * f j := by
  simp [partial_prod, List.take_succ, List.ofFnNthVal, dif_pos j.is_lt, ← Option.coe_def]
#align fin.partial_prod_succ Fin.partialProd_succ
#align fin.partial_sum_succ Fin.partialSum_succ

/- warning: fin.partial_prod_succ' -> Fin.partialProd_succ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> α) (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Eq.{succ u1} α (Fin.partialProd.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) f (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) j)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Fin.partialProd.{u1} α _inst_1 n (Fin.tail.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α) f) j))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> α) (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Eq.{succ u1} α (Fin.partialProd.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) f (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) j)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (Fin.partialProd.{u1} α _inst_1 n (Fin.tail.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α) f) j))
Case conversion may be inaccurate. Consider using '#align fin.partial_prod_succ' Fin.partialProd_succ'ₓ'. -/
@[to_additive]
theorem partialProd_succ' (f : Fin (n + 1) → α) (j : Fin (n + 1)) :
    partialProd f j.succ = f 0 * partialProd (Fin.tail f) j := by simpa [partial_prod]
#align fin.partial_prod_succ' Fin.partialProd_succ'
#align fin.partial_sum_succ' Fin.partialSum_succ'

/- warning: fin.partial_prod_left_inv -> Fin.partialProd_left_inv is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {G : Type.{u1}} [_inst_2 : Group.{u1} G] (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> G), Eq.{succ u1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> G) (SMul.smul.{u1, u1} G ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> G) (Function.hasSMul.{0, u1, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) G G (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Fin.partialProd.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) n (fun (i : Fin n) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (coeTrans.{1, 1, 1} (Fin n) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))) (Fin.coeToNat n)))) i))) (f (Fin.succ n i))))) f
but is expected to have type
  forall {n : Nat} {G : Type.{u1}} [_inst_2 : Group.{u1} G] (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> G), Eq.{succ u1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> G) (HSMul.hSMul.{u1, u1, u1} G ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> G) ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> G) (instHSMul.{u1, u1} G ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> G) (Pi.instSMul.{0, u1, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) G (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => G) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (Fin.partialProd.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) n (fun (i : Fin n) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) (f (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) (Fin.val n i)))) (f (Fin.succ n i))))) f
Case conversion may be inaccurate. Consider using '#align fin.partial_prod_left_inv Fin.partialProd_left_invₓ'. -/
@[to_additive]
theorem partialProd_left_inv {G : Type _} [Group G] (f : Fin (n + 1) → G) :
    (f 0 • partialProd fun i : Fin n => (f i)⁻¹ * f i.succ) = f :=
  funext fun x =>
    Fin.inductionOn x (by simp) fun x hx =>
      by
      simp only [coe_eq_cast_succ, Pi.smul_apply, smul_eq_mul] at hx⊢
      rw [partial_prod_succ, ← mul_assoc, hx, mul_inv_cancel_left]
#align fin.partial_prod_left_inv Fin.partialProd_left_inv
#align fin.partial_sum_left_neg Fin.partialSum_left_neg

/- warning: fin.partial_prod_right_inv -> Fin.partialProd_right_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.partial_prod_right_inv Fin.partialProd_right_invₓ'. -/
@[to_additive]
theorem partialProd_right_inv {G : Type _} [Group G] (f : Fin n → G) (i : Fin n) :
    (partialProd f i.cast_succ)⁻¹ * partialProd f i.succ = f i :=
  by
  cases' i with i hn
  induction' i with i hi generalizing hn
  · simp [-Fin.succ_mk, partial_prod_succ]
  · specialize hi (lt_trans (Nat.lt_succ_self i) hn)
    simp only [Fin.coe_eq_castSucc, Fin.succ_mk, Fin.castSucc_mk] at hi⊢
    rw [← Fin.succ_mk _ _ (lt_trans (Nat.lt_succ_self _) hn), ← Fin.succ_mk]
    simp only [partial_prod_succ, mul_inv_rev, Fin.castSucc_mk]
    assoc_rw [hi, inv_mul_cancel_left]
#align fin.partial_prod_right_inv Fin.partialProd_right_inv
#align fin.partial_sum_right_neg Fin.partialSum_right_neg

/- warning: fin.inv_partial_prod_mul_eq_contract_nth -> Fin.inv_partialProd_mul_eq_contractNth is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.inv_partial_prod_mul_eq_contract_nth Fin.inv_partialProd_mul_eq_contractNthₓ'. -/
/-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
Then if `k < j`, this says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ = gₖ`.
If `k = j`, it says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ₊₁ = gₖgₖ₊₁`.
If `k > j`, it says `(g₀g₁...gₖ)⁻¹ * g₀g₁...gₖ₊₁ = gₖ₊₁.`
Useful for defining group cohomology. -/
@[to_additive
      "Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.\nThen if `k < j`, this says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ) = gₖ`.\nIf `k = j`, it says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ + gₖ₊₁`.\nIf `k > j`, it says `-(g₀ + g₁ + ... + gₖ) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ₊₁.`\nUseful for defining group cohomology."]
theorem inv_partialProd_mul_eq_contractNth {G : Type _} [Group G] (g : Fin (n + 1) → G)
    (j : Fin (n + 1)) (k : Fin n) :
    (partialProd g (j.succ.succAbove k.cast_succ))⁻¹ * partialProd g (j.succAbove k).succ =
      j.contractNth Mul.mul g k :=
  by
  rcases lt_trichotomy (k : ℕ) j with (h | h | h)
  · rwa [succ_above_below, succ_above_below, partial_prod_right_inv, contract_nth_apply_of_lt]
    · assumption
    · rw [cast_succ_lt_iff_succ_le, succ_le_succ_iff, le_iff_coe_le_coe]
      exact le_of_lt h
  · rwa [succ_above_below, succ_above_above, partial_prod_succ, cast_succ_fin_succ, ← mul_assoc,
      partial_prod_right_inv, contract_nth_apply_of_eq]
    · simpa only [le_iff_coe_le_coe, ← h]
    · rw [cast_succ_lt_iff_succ_le, succ_le_succ_iff, le_iff_coe_le_coe]
      exact le_of_eq h
  · rwa [succ_above_above, succ_above_above, partial_prod_succ, partial_prod_succ,
      cast_succ_fin_succ, partial_prod_succ, inv_mul_cancel_left, contract_nth_apply_of_gt]
    · exact le_iff_coe_le_coe.2 (le_of_lt h)
    · rw [le_iff_coe_le_coe, coe_succ]
      exact Nat.succ_le_of_lt h
#align fin.inv_partial_prod_mul_eq_contract_nth Fin.inv_partialProd_mul_eq_contractNth
#align fin.neg_partial_sum_add_eq_contract_nth Fin.neg_partialSum_add_eq_contractNth

end PartialProd

end Fin

#print finFunctionFinEquiv /-
/-- Equivalence between `fin n → fin m` and `fin (m ^ n)`. -/
@[simps]
def finFunctionFinEquiv {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  Equiv.ofRightInverseOfCardLe (le_of_eq <| by simp_rw [Fintype.card_fun, Fintype.card_fin])
    (fun f =>
      ⟨∑ i, f i * m ^ (i : ℕ), by
        induction' n with n ih generalizing f
        · simp
        cases m
        · exact isEmptyElim (f <| Fin.last _)
        simp_rw [Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last]
        refine' (add_lt_add_of_lt_of_le (ih _) <| mul_le_mul_right' (Fin.is_le _) _).trans_eq _
        rw [← one_add_mul, add_comm, pow_succ]⟩)
    (fun a b =>
      ⟨a / m ^ (b : ℕ) % m, by
        cases n
        · exact b.elim0
        cases m
        · rw [zero_pow n.succ_pos] at a
          exact a.elim0
        · exact Nat.mod_lt _ m.succ_pos⟩)
    fun a => by
    dsimp
    induction' n with n ih generalizing a
    · haveI : Subsingleton (Fin (m ^ 0)) := (Fin.cast <| pow_zero _).toEquiv.Subsingleton
      exact Subsingleton.elim _ _
    simp_rw [Fin.forall_iff, Fin.ext_iff, Fin.val_mk] at ih
    ext
    simp_rw [Fin.val_mk, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one,
      mul_one, pow_succ, ← Nat.div_div_eq_div_mul, mul_left_comm _ m, ← mul_sum]
    rw [ih _ (Nat.div_lt_of_lt_mul a.is_lt), Nat.mod_add_div]
#align fin_function_fin_equiv finFunctionFinEquiv
-/

#print finFunctionFinEquiv_apply /-
theorem finFunctionFinEquiv_apply {m n : ℕ} (f : Fin n → Fin m) :
    (finFunctionFinEquiv f : ℕ) = ∑ i : Fin n, ↑(f i) * m ^ (i : ℕ) :=
  rfl
#align fin_function_fin_equiv_apply finFunctionFinEquiv_apply
-/

#print finFunctionFinEquiv_single /-
theorem finFunctionFinEquiv_single {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) :
    (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) :=
  by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero, MulZeroClass.zero_mul]
#align fin_function_fin_equiv_single finFunctionFinEquiv_single
-/

#print finPiFinEquiv /-
/-- Equivalence between `Π i : fin m, fin (n i)` and `fin (∏ i : fin m, n i)`. -/
def finPiFinEquiv {m : ℕ} {n : Fin m → ℕ} : (∀ i : Fin m, Fin (n i)) ≃ Fin (∏ i : Fin m, n i) :=
  Equiv.ofRightInverseOfCardLe (le_of_eq <| by simp_rw [Fintype.card_pi, Fintype.card_fin])
    (fun f =>
      ⟨∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j),
        by
        induction' m with m ih generalizing f
        · simp
        rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
        suffices
          ∀ (n : Fin m → ℕ) (nn : ℕ) (f : ∀ i : Fin m, Fin (n i)) (fn : Fin nn),
            ((∑ i : Fin m, ↑(f i) * ∏ j : Fin i, n (Fin.castLE i.prop.le j)) + ↑fn * ∏ j, n j) <
              (∏ i : Fin m, n i) * nn
          by
          replace this := this (Fin.init n) (n (Fin.last _)) (Fin.init f) (f (Fin.last _))
          rw [← Fin.snoc_init_self f]
          simp (config := { singlePass := true }) only [← Fin.snoc_init_self n]
          simp_rw [Fin.snoc_castSucc, Fin.init_snoc, Fin.snoc_last, Fin.snoc_init_self n]
          exact this
        intro n nn f fn
        cases nn
        · exact isEmptyElim fn
        refine' (add_lt_add_of_lt_of_le (ih _) <| mul_le_mul_right' (Fin.is_le _) _).trans_eq _
        rw [← one_add_mul, mul_comm, add_comm]⟩)
    (fun a b =>
      ⟨(a / ∏ j : Fin b, n (Fin.castLE b.is_lt.le j)) % n b,
        by
        cases m
        · exact b.elim0
        cases' h : n b with nb
        · rw [prod_eq_zero (Finset.mem_univ _) h] at a
          exact isEmptyElim a
        exact Nat.mod_lt _ nb.succ_pos⟩)
    (by
      intro a; revert a; dsimp only [Fin.val_mk]
      refine' Fin.consInduction _ _ n
      · intro a
        haveI : Subsingleton (Fin (∏ i : Fin 0, i.elim0ₓ)) :=
          (Fin.cast <| prod_empty).toEquiv.Subsingleton
        exact Subsingleton.elim _ _
      · intro n x xs ih a
        simp_rw [Fin.forall_iff, Fin.ext_iff, Fin.val_mk] at ih
        ext
        simp_rw [Fin.val_mk, Fin.sum_univ_succ, Fin.cons_succ]
        have := fun i : Fin n =>
          Fintype.prod_equiv (Fin.cast <| Fin.val_succ i).toEquiv
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Fin.is_lt _).le j))
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Nat.succ_le_succ (Fin.is_lt _).le) j))
            fun j => rfl
        simp_rw [this]
        clear this
        dsimp only [Fin.val_zero]
        simp_rw [Fintype.prod_empty, Nat.div_one, mul_one, Fin.cons_zero, Fin.prod_univ_succ]
        change (_ + ∑ y : _, _ / (x * _) % _ * (x * _)) = _
        simp_rw [← Nat.div_div_eq_div_mul, mul_left_comm (_ % _ : ℕ), ← mul_sum]
        convert Nat.mod_add_div _ _
        refine' Eq.trans _ (ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq _))
        swap
        · convert Fin.prod_univ_succ (Fin.cons x xs : ∀ _, ℕ)
          simp_rw [Fin.cons_succ]
        congr with i
        congr with j
        · cases j
          rfl
        · cases j
          rfl)
#align fin_pi_fin_equiv finPiFinEquiv
-/

#print finPiFinEquiv_apply /-
theorem finPiFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (f : ∀ i : Fin m, Fin (n i)) :
    (finPiFinEquiv f : ℕ) = ∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j) :=
  rfl
#align fin_pi_fin_equiv_apply finPiFinEquiv_apply
-/

#print finPiFinEquiv_single /-
theorem finPiFinEquiv_single {m : ℕ} {n : Fin m → ℕ} [∀ i, NeZero (n i)] (i : Fin m)
    (j : Fin (n i)) :
    (finPiFinEquiv (Pi.single i j : ∀ i : Fin m, Fin (n i)) : ℕ) =
      j * ∏ j, n (Fin.castLE i.is_lt.le j) :=
  by
  rw [finPiFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero, MulZeroClass.zero_mul]
#align fin_pi_fin_equiv_single finPiFinEquiv_single
-/

namespace List

section CommMonoid

variable [CommMonoid α]

/- warning: list.prod_take_of_fn -> List.prod_take_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {n : Nat} (f : (Fin n) -> α) (i : Nat), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.take.{u1} α i (List.ofFn.{u1} α n f))) (Finset.prod.{u1, 0} α (Fin n) _inst_1 (Finset.filter.{0} (Fin n) (fun (j : Fin n) => LT.lt.{0} Nat Nat.hasLt (Fin.val n j) i) (fun (a : Fin n) => Nat.decidableLt (Fin.val n a) i) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (fun (j : Fin n) => f j))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {n : Nat} (f : (Fin n) -> α) (i : Nat), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (List.take.{u1} α i (List.ofFn.{u1} α n f))) (Finset.prod.{u1, 0} α (Fin n) _inst_1 (Finset.filter.{0} (Fin n) (fun (j : Fin n) => LT.lt.{0} Nat instLTNat (Fin.val n j) i) (fun (a : Fin n) => Nat.decLt (Fin.val n a) i) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (fun (j : Fin n) => f j))
Case conversion may be inaccurate. Consider using '#align list.prod_take_of_fn List.prod_take_ofFnₓ'. -/
@[to_additive]
theorem prod_take_ofFn {n : ℕ} (f : Fin n → α) (i : ℕ) :
    ((ofFn f).take i).Prod = ∏ j in Finset.univ.filterₓ fun j : Fin n => j.val < i, f j :=
  by
  have A : ∀ j : Fin n, ¬(j : ℕ) < 0 := fun j => not_lt_bot
  induction' i with i IH; · simp [A]
  by_cases h : i < n
  · have : i < length (of_fn f) := by rwa [length_of_fn f]
    rw [prod_take_succ _ _ this]
    have A :
      ((Finset.univ : Finset (Fin n)).filterₓ fun j => j.val < i + 1) =
        ((Finset.univ : Finset (Fin n)).filterₓ fun j => j.val < i) ∪ {(⟨i, h⟩ : Fin n)} :=
      by
      ext ⟨_, _⟩
      simp [Nat.lt_succ_iff_lt_or_eq]
    have B :
      _root_.disjoint (Finset.filter (fun j : Fin n => j.val < i) Finset.univ)
        (singleton (⟨i, h⟩ : Fin n)) :=
      by simp
    rw [A, Finset.prod_union B, IH]
    simp
  · have A : (of_fn f).take i = (of_fn f).take i.succ :=
      by
      rw [← length_of_fn f] at h
      have : length (of_fn f) ≤ i := not_lt.mp h
      rw [take_all_of_le this, take_all_of_le (le_trans this (Nat.le_succ _))]
    have B : ∀ j : Fin n, ((j : ℕ) < i.succ) = ((j : ℕ) < i) :=
      by
      intro j
      have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h)
      simp [this, lt_trans this (Nat.lt_succ_self _)]
    simp [← A, B, IH]
#align list.prod_take_of_fn List.prod_take_ofFn
#align list.sum_take_of_fn List.sum_take_ofFn

/- warning: list.prod_of_fn -> List.prod_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {n : Nat} {f : (Fin n) -> α}, Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.ofFn.{u1} α n f)) (Finset.prod.{u1, 0} α (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {n : Nat} {f : (Fin n) -> α}, Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (List.ofFn.{u1} α n f)) (Finset.prod.{u1, 0} α (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => f i))
Case conversion may be inaccurate. Consider using '#align list.prod_of_fn List.prod_ofFnₓ'. -/
@[to_additive]
theorem prod_ofFn {n : ℕ} {f : Fin n → α} : (ofFn f).Prod = ∏ i, f i :=
  by
  convert prod_take_of_fn f n
  · rw [take_all_of_le (le_of_eq (length_of_fn f))]
  · have : ∀ j : Fin n, (j : ℕ) < n := fun j => j.is_lt
    simp [this]
#align list.prod_of_fn List.prod_ofFn
#align list.sum_of_fn List.sum_ofFn

end CommMonoid

/- warning: list.alternating_sum_eq_finset_sum -> List.alternatingSum_eq_finset_sum is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : AddCommGroup.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (List.alternatingSum.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))))) (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))))) (SubNegMonoid.toHasNeg.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))) L) (Finset.sum.{u1, 0} G (Fin (List.length.{u1} G L)) (AddCommGroup.toAddCommMonoid.{u1} G _inst_1) (Finset.univ.{0} (Fin (List.length.{u1} G L)) (Fin.fintype (List.length.{u1} G L))) (fun (i : Fin (List.length.{u1} G L)) => SMul.smul.{0, u1} Int G (SubNegMonoid.SMulInt.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} G L)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} G L)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} G L)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} G L)) Nat (Fin.coeToNat (List.length.{u1} G L))))) i)) (List.nthLe.{u1} G L ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} G L)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} G L)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} G L)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} G L)) Nat (Fin.coeToNat (List.length.{u1} G L))))) i) (Fin.is_lt (List.length.{u1} G L) i))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : AddCommGroup.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (List.alternatingSum.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G _inst_1))))) (AddZeroClass.toAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))))) (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G _inst_1))))) L) (Finset.sum.{u1, 0} G (Fin (List.length.{u1} G L)) (AddCommGroup.toAddCommMonoid.{u1} G _inst_1) (Finset.univ.{0} (Fin (List.length.{u1} G L)) (Fin.fintype (List.length.{u1} G L))) (fun (i : Fin (List.length.{u1} G L)) => HSMul.hSMul.{0, u1, u1} Int G G (instHSMul.{0, u1} Int G (SubNegMonoid.SMulInt.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)))) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (Fin.val (List.length.{u1} G L) i)) (List.get.{u1} G L i)))
Case conversion may be inaccurate. Consider using '#align list.alternating_sum_eq_finset_sum List.alternatingSum_eq_finset_sumₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem alternatingSum_eq_finset_sum {G : Type _} [AddCommGroup G] :
    ∀ L : List G, alternatingSum L = ∑ i : Fin L.length, (-1 : ℤ) ^ (i : ℕ) • L.nthLe i i.is_lt
  | [] => by
    rw [alternating_sum, Finset.sum_eq_zero]
    rintro ⟨i, ⟨⟩⟩
  | g::[] => by simp
  | g::h::L =>
    calc
      g + -h + L.alternatingSum = g + -h + ∑ i : Fin L.length, (-1 : ℤ) ^ (i : ℕ) • L.nthLe i i.2 :=
        congr_arg _ (alternating_sum_eq_finset_sum _)
      _ = ∑ i : Fin (L.length + 2), (-1 : ℤ) ^ (i : ℕ) • List.nthLe (g::h::L) i _ :=
        by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, add_assoc]
        unfold_coes
        simp [Nat.succ_eq_add_one, pow_add]
        rfl
      
#align list.alternating_sum_eq_finset_sum List.alternatingSum_eq_finset_sum

/- warning: list.alternating_prod_eq_finset_prod -> List.alternatingProd_eq_finset_prod is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (List.alternatingProd.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) L) (Finset.prod.{u1, 0} G (Fin (List.length.{u1} G L)) (CommGroup.toCommMonoid.{u1} G _inst_1) (Finset.univ.{0} (Fin (List.length.{u1} G L)) (Fin.fintype (List.length.{u1} G L))) (fun (i : Fin (List.length.{u1} G L)) => HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (List.nthLe.{u1} G L ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} G L)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} G L)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} G L)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} G L)) Nat (Fin.coeToNat (List.length.{u1} G L))))) i) (Fin.property (List.length.{u1} G L) i)) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} G L)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} G L)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} G L)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} G L)) Nat (Fin.coeToNat (List.length.{u1} G L))))) i))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (List.alternatingProd.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) L) (Finset.prod.{u1, 0} G (Fin (List.length.{u1} G L)) (CommGroup.toCommMonoid.{u1} G _inst_1) (Finset.univ.{0} (Fin (List.length.{u1} G L)) (Fin.fintype (List.length.{u1} G L))) (fun (i : Fin (List.length.{u1} G L)) => HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (List.get.{u1} G L i) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (Fin.val (List.length.{u1} G L) i))))
Case conversion may be inaccurate. Consider using '#align list.alternating_prod_eq_finset_prod List.alternatingProd_eq_finset_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem alternatingProd_eq_finset_prod {G : Type _} [CommGroup G] :
    ∀ L : List G, alternatingProd L = ∏ i : Fin L.length, L.nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ)
  | [] => by
    rw [alternating_prod, Finset.prod_eq_one]
    rintro ⟨i, ⟨⟩⟩
  | g::[] => by
    show g = ∏ i : Fin 1, [g].nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ)
    rw [Fin.prod_univ_succ]; simp
  | g::h::L =>
    calc
      g * h⁻¹ * L.alternatingProd =
          g * h⁻¹ * ∏ i : Fin L.length, L.nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ) :=
        congr_arg _ (alternating_prod_eq_finset_prod _)
      _ = ∏ i : Fin (L.length + 2), List.nthLe (g::h::L) i _ ^ (-1 : ℤ) ^ (i : ℕ) :=
        by
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
        unfold_coes
        simp [Nat.succ_eq_add_one, pow_add]
        rfl
      
#align list.alternating_prod_eq_finset_prod List.alternatingProd_eq_finset_prod
#align list.alternating_sum_eq_finset_sum List.alternatingSum_eq_finset_sum

end List

