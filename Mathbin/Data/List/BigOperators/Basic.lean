/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best

! This file was ported from Lean 3 source module data.list.big_operators.basic
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Forall2

/-!
# Sums and products from lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides basic results about `list.prod`, `list.sum`, which calculate the product and sum
of elements of a list and `list.alternating_prod`, `list.alternating_sum`, their alternating
counterparts. These are defined in [`data.list.defs`](./defs).
-/


variable {ι α M N P M₀ G R : Type _}

namespace List

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

/- warning: list.prod_nil -> List.prod_nil is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.nil.{u1} M)) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.nil.{u1} M)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align list.prod_nil List.prod_nilₓ'. -/
@[simp, to_additive]
theorem prod_nil : ([] : List M).Prod = 1 :=
  rfl
#align list.prod_nil List.prod_nil
#align list.sum_nil List.sum_nil

/- warning: list.prod_singleton -> List.prod_singleton is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.cons.{u1} M a (List.nil.{u1} M))) a
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.cons.{u1} M a (List.nil.{u1} M))) a
Case conversion may be inaccurate. Consider using '#align list.prod_singleton List.prod_singletonₓ'. -/
@[to_additive]
theorem prod_singleton : [a].Prod = a :=
  one_mul a
#align list.prod_singleton List.prod_singleton
#align list.sum_singleton List.sum_singleton

/- warning: list.prod_cons -> List.prod_cons is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M} {a : M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.cons.{u1} M a l)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M} {a : M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.cons.{u1} M a l)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l))
Case conversion may be inaccurate. Consider using '#align list.prod_cons List.prod_consₓ'. -/
@[simp, to_additive]
theorem prod_cons : (a :: l).Prod = a * l.Prod :=
  calc
    (a :: l).Prod = foldl (· * ·) (a * 1) l := by
      simp only [List.prod, foldl_cons, one_mul, mul_one]
    _ = _ := foldl_assoc
    
#align list.prod_cons List.prod_cons
#align list.sum_cons List.sum_cons

/- warning: list.prod_append -> List.prod_append is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Append.append.{u1} (List.{u1} M) (List.hasAppend.{u1} M) l₁ l₂)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l₁) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l₂))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (HAppend.hAppend.{u1, u1, u1} (List.{u1} M) (List.{u1} M) (List.{u1} M) (instHAppend.{u1} (List.{u1} M) (List.instAppendList.{u1} M)) l₁ l₂)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l₁) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l₂))
Case conversion may be inaccurate. Consider using '#align list.prod_append List.prod_appendₓ'. -/
@[simp, to_additive]
theorem prod_append : (l₁ ++ l₂).Prod = l₁.Prod * l₂.Prod :=
  calc
    (l₁ ++ l₂).Prod = foldl (· * ·) (foldl (· * ·) 1 l₁ * 1) l₂ := by simp [List.prod]
    _ = l₁.Prod * l₂.Prod := foldl_assoc
    
#align list.prod_append List.prod_append
#align list.sum_append List.sum_append

/- warning: list.prod_concat -> List.prod_concat is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M} {a : M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.concat.{u1} M l a)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) a)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M} {a : M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.concat.{u1} M l a)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) a)
Case conversion may be inaccurate. Consider using '#align list.prod_concat List.prod_concatₓ'. -/
@[to_additive]
theorem prod_concat : (l.concat a).Prod = l.Prod * a := by
  rw [concat_eq_append, prod_append, prod_singleton]
#align list.prod_concat List.prod_concat
#align list.sum_concat List.sum_concat

/- warning: list.prod_join -> List.prod_join is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} (List.{u1} M)}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.join.{u1} M l)) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.map.{u1, u1} (List.{u1} M) M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} (List.{u1} M)}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.join.{u1} M l)) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.map.{u1, u1} (List.{u1} M) M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1)) l))
Case conversion may be inaccurate. Consider using '#align list.prod_join List.prod_joinₓ'. -/
@[simp, to_additive]
theorem prod_join {l : List (List M)} : l.join.Prod = (l.map List.prod).Prod := by
  induction l <;> [rfl, simp only [*, List.join, map, prod_append, prod_cons]]
#align list.prod_join List.prod_join
#align list.sum_join List.sum_join

/- warning: list.prod_eq_foldr -> List.prod_eq_foldr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) (List.foldr.{u1, u1} M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) l)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M}, Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) (List.foldr.{u1, u1} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.516 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.518 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.516 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.518) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))) l)
Case conversion may be inaccurate. Consider using '#align list.prod_eq_foldr List.prod_eq_foldrₓ'. -/
@[to_additive]
theorem prod_eq_foldr : l.Prod = foldr (· * ·) 1 l :=
  List.recOn l rfl fun a l ihl => by rw [prod_cons, foldr_cons, ihl]
#align list.prod_eq_foldr List.prod_eq_foldr
#align list.sum_eq_foldr List.sum_eq_foldr

/- warning: list.prod_replicate -> List.prod_replicate is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (n : Nat) (a : M), Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.replicate.{u1} M n a)) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a n)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (n : Nat) (a : M), Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.replicate.{u1} M n a)) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a n)
Case conversion may be inaccurate. Consider using '#align list.prod_replicate List.prod_replicateₓ'. -/
@[simp, to_additive]
theorem prod_replicate (n : ℕ) (a : M) : (replicate n a).Prod = a ^ n :=
  by
  induction' n with n ih
  · rw [pow_zero]
    rfl
  · rw [List.replicate_succ, List.prod_cons, ih, pow_succ]
#align list.prod_replicate List.prod_replicate
#align list.sum_replicate List.sum_replicate

/- warning: list.prod_eq_pow_card -> List.prod_eq_pow_card is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M) (m : M), (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Eq.{succ u1} M x m)) -> (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) m (List.length.{u1} M l)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M) (m : M), (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Eq.{succ u1} M x m)) -> (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) m (List.length.{u1} M l)))
Case conversion may be inaccurate. Consider using '#align list.prod_eq_pow_card List.prod_eq_pow_cardₓ'. -/
@[to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card (l : List M) (m : M) (h : ∀ x ∈ l, x = m) : l.Prod = m ^ l.length := by
  rw [← prod_replicate, ← eq_replicate_length.2 h]
#align list.prod_eq_pow_card List.prod_eq_pow_card
#align list.sum_eq_card_nsmul List.sum_eq_card_nsmul

/- warning: list.prod_hom_rel -> List.prod_hom_rel is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u3} N] (l : List.{u1} ι) {r : M -> N -> Prop} {f : ι -> M} {g : ι -> N}, (r (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (OfNat.ofNat.{u3} N 1 (OfNat.mk.{u3} N 1 (One.one.{u3} N (MulOneClass.toHasOne.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)))))) -> (forall {{i : ι}} {{a : M}} {{b : N}}, (r a b) -> (r (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) (f i) a) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2))) (g i) b))) -> (r (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M f l)) (List.prod.{u3} N (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (MulOneClass.toHasOne.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (List.map.{u1, u3} ι N g l)))
but is expected to have type
  forall {ι : Type.{u3}} {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] (l : List.{u3} ι) {r : M -> N -> Prop} {f : ι -> M} {g : ι -> N}, (r (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N _inst_2)))) -> (forall {{i : ι}} {{a : M}} {{b : N}}, (r a b) -> (r (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) (f i) a) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) (g i) b))) -> (r (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u3, u2} ι M f l)) (List.prod.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (Monoid.toOne.{u1} N _inst_2) (List.map.{u3, u1} ι N g l)))
Case conversion may be inaccurate. Consider using '#align list.prod_hom_rel List.prod_hom_relₓ'. -/
@[to_additive]
theorem prod_hom_rel (l : List ι) {r : M → N → Prop} {f : ι → M} {g : ι → N} (h₁ : r 1 1)
    (h₂ : ∀ ⦃i a b⦄, r a b → r (f i * a) (g i * b)) : r (l.map f).Prod (l.map g).Prod :=
  List.recOn l h₁ fun a l hl => by simp only [map_cons, prod_cons, h₂ hl]
#align list.prod_hom_rel List.prod_hom_rel
#align list.sum_hom_rel List.sum_hom_rel

/- warning: list.prod_hom -> List.prod_hom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] (l : List.{u1} M) {F : Type.{u3}} [_inst_4 : MonoidHomClass.{u3, u1, u2} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)] (f : F), Eq.{succ u2} N (List.prod.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (List.map.{u1, u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) _inst_4))) f) l)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) _inst_4))) f (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u1}} [_inst_1 : Monoid.{u3} M] [_inst_2 : Monoid.{u1} N] (l : List.{u3} M) {F : Type.{u2}} [_inst_4 : MonoidHomClass.{u2, u3, u1} F M N (Monoid.toMulOneClass.{u3} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)] (f : F), Eq.{succ u1} N (List.prod.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (Monoid.toOne.{u1} N _inst_2) (List.map.{u3, u1} M N (FunLike.coe.{succ u2, succ u3, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u2, u3, u1} F M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{u2, u3, u1} F M N (Monoid.toMulOneClass.{u3} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) _inst_4)) f) l)) (FunLike.coe.{succ u2, succ u3, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u2, u3, u1} F M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{u2, u3, u1} F M N (Monoid.toMulOneClass.{u3} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) _inst_4)) f (List.prod.{u3} M (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_1)) (Monoid.toOne.{u3} M _inst_1) l))
Case conversion may be inaccurate. Consider using '#align list.prod_hom List.prod_homₓ'. -/
@[to_additive]
theorem prod_hom (l : List M) {F : Type _} [MonoidHomClass F M N] (f : F) :
    (l.map f).Prod = f l.Prod :=
  by
  simp only [Prod, foldl_map, ← map_one f]
  exact l.foldl_hom _ _ _ 1 (map_mul f)
#align list.prod_hom List.prod_hom
#align list.sum_hom List.sum_hom

/- warning: list.prod_hom₂ -> List.prod_hom₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} {P : Type.{u4}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u3} N] [_inst_3 : Monoid.{u4} P] (l : List.{u1} ι) (f : M -> N -> P), (forall (a : M) (b : M) (c : N) (d : N), Eq.{succ u4} P (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) a b) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2))) c d)) (HMul.hMul.{u4, u4, u4} P P P (instHMul.{u4} P (MulOneClass.toHasMul.{u4} P (Monoid.toMulOneClass.{u4} P _inst_3))) (f a c) (f b d))) -> (Eq.{succ u4} P (f (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (OfNat.ofNat.{u3} N 1 (OfNat.mk.{u3} N 1 (One.one.{u3} N (MulOneClass.toHasOne.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)))))) (OfNat.ofNat.{u4} P 1 (OfNat.mk.{u4} P 1 (One.one.{u4} P (MulOneClass.toHasOne.{u4} P (Monoid.toMulOneClass.{u4} P _inst_3)))))) -> (forall (f₁ : ι -> M) (f₂ : ι -> N), Eq.{succ u4} P (List.prod.{u4} P (MulOneClass.toHasMul.{u4} P (Monoid.toMulOneClass.{u4} P _inst_3)) (MulOneClass.toHasOne.{u4} P (Monoid.toMulOneClass.{u4} P _inst_3)) (List.map.{u1, u4} ι P (fun (i : ι) => f (f₁ i) (f₂ i)) l)) (f (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M f₁ l)) (List.prod.{u3} N (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (MulOneClass.toHasOne.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (List.map.{u1, u3} ι N f₂ l))))
but is expected to have type
  forall {ι : Type.{u4}} {M : Type.{u2}} {N : Type.{u1}} {P : Type.{u3}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] [_inst_3 : Monoid.{u3} P] (l : List.{u4} ι) (f : M -> N -> P), (forall (a : M) (b : M) (c : N) (d : N), Eq.{succ u3} P (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) a b) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) c d)) (HMul.hMul.{u3, u3, u3} P P P (instHMul.{u3} P (MulOneClass.toMul.{u3} P (Monoid.toMulOneClass.{u3} P _inst_3))) (f a c) (f b d))) -> (Eq.{succ u3} P (f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N _inst_2)))) (OfNat.ofNat.{u3} P 1 (One.toOfNat1.{u3} P (Monoid.toOne.{u3} P _inst_3)))) -> (forall (f₁ : ι -> M) (f₂ : ι -> N), Eq.{succ u3} P (List.prod.{u3} P (MulOneClass.toMul.{u3} P (Monoid.toMulOneClass.{u3} P _inst_3)) (Monoid.toOne.{u3} P _inst_3) (List.map.{u4, u3} ι P (fun (i : ι) => f (f₁ i) (f₂ i)) l)) (f (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u4, u2} ι M f₁ l)) (List.prod.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (Monoid.toOne.{u1} N _inst_2) (List.map.{u4, u1} ι N f₂ l))))
Case conversion may be inaccurate. Consider using '#align list.prod_hom₂ List.prod_hom₂ₓ'. -/
@[to_additive]
theorem prod_hom₂ (l : List ι) (f : M → N → P) (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d)
    (hf' : f 1 1 = 1) (f₁ : ι → M) (f₂ : ι → N) :
    (l.map fun i => f (f₁ i) (f₂ i)).Prod = f (l.map f₁).Prod (l.map f₂).Prod :=
  by
  simp only [Prod, foldl_map]
  convert l.foldl_hom₂ (fun a b => f a b) _ _ _ _ _ fun a b i => _
  · exact hf'.symm
  · exact hf _ _ _ _
#align list.prod_hom₂ List.prod_hom₂
#align list.sum_hom₂ List.sum_hom₂

/- warning: list.prod_map_mul -> List.prod_map_mul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_4 : CommMonoid.{u2} α] {l : List.{u1} ι} {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (List.prod.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4))) (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4))) (List.map.{u1, u2} ι α (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4)))) (f i) (g i)) l)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4)))) (List.prod.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4))) (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4))) (List.map.{u1, u2} ι α f l)) (List.prod.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4))) (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4))) (List.map.{u1, u2} ι α g l)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_4 : CommMonoid.{u2} α] {l : List.{u1} ι} {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (List.prod.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4))) (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4)) (List.map.{u1, u2} ι α (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4)))) (f i) (g i)) l)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4)))) (List.prod.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4))) (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4)) (List.map.{u1, u2} ι α f l)) (List.prod.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4))) (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_4)) (List.map.{u1, u2} ι α g l)))
Case conversion may be inaccurate. Consider using '#align list.prod_map_mul List.prod_map_mulₓ'. -/
@[simp, to_additive]
theorem prod_map_mul {α : Type _} [CommMonoid α] {l : List ι} {f g : ι → α} :
    (l.map fun i => f i * g i).Prod = (l.map f).Prod * (l.map g).Prod :=
  l.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _
#align list.prod_map_mul List.prod_map_mul
#align list.sum_map_add List.sum_map_add

/- warning: list.prod_map_neg -> List.prod_map_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : CommMonoid.{u1} α] [_inst_5 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4)))] (l : List.{u1} α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) (List.map.{u1, u1} α α (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) _inst_5))) l)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) _inst_5)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))))))) (List.length.{u1} α l)) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : CommMonoid.{u1} α] [_inst_5 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4)))] (l : List.{u1} α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4)) (List.map.{u1, u1} α α (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) _inst_5))) l)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) _inst_5)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))))) (List.length.{u1} α l)) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4)) l))
Case conversion may be inaccurate. Consider using '#align list.prod_map_neg List.prod_map_negₓ'. -/
@[simp]
theorem prod_map_neg {α} [CommMonoid α] [HasDistribNeg α] (l : List α) :
    (l.map Neg.neg).Prod = (-1) ^ l.length * l.Prod := by
  simpa only [id, neg_mul, one_mul, map_const', prod_replicate, map_id] using
    @prod_map_mul α α _ l (fun _ => -1) id
#align list.prod_map_neg List.prod_map_neg

/- warning: list.prod_map_hom -> List.prod_map_hom is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u3} N] (L : List.{u1} ι) (f : ι -> M) {G : Type.{u4}} [_inst_4 : MonoidHomClass.{u4, u2, u3} G M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u3} N _inst_2)] (g : G), Eq.{succ u3} N (List.prod.{u3} N (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (MulOneClass.toHasOne.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (List.map.{u1, u3} ι N (Function.comp.{succ u1, succ u2, succ u3} ι M N (coeFn.{succ u4, max (succ u2) (succ u3)} G (fun (_x : G) => M -> N) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} G M (fun (_x : M) => N) (MulHomClass.toFunLike.{u4, u2, u3} G M N (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (MonoidHomClass.toMulHomClass.{u4, u2, u3} G M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u3} N _inst_2) _inst_4))) g) f) L)) (coeFn.{succ u4, max (succ u2) (succ u3)} G (fun (_x : G) => M -> N) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} G M (fun (_x : M) => N) (MulHomClass.toFunLike.{u4, u2, u3} G M N (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (MonoidHomClass.toMulHomClass.{u4, u2, u3} G M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u3} N _inst_2) _inst_4))) g (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M f L)))
but is expected to have type
  forall {ι : Type.{u4}} {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] (L : List.{u4} ι) (f : ι -> M) {G : Type.{u3}} [_inst_4 : MonoidHomClass.{u3, u2, u1} G M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)] (g : G), Eq.{succ u1} N (List.prod.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (Monoid.toOne.{u1} N _inst_2) (List.map.{u4, u1} ι N (Function.comp.{succ u4, succ u2, succ u1} ι M N (FunLike.coe.{succ u3, succ u2, succ u1} G M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} G M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u2, u1} G M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) _inst_4)) g) f) L)) (FunLike.coe.{succ u3, succ u2, succ u1} G M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} G M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u2, u1} G M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) _inst_4)) g (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u4, u2} ι M f L)))
Case conversion may be inaccurate. Consider using '#align list.prod_map_hom List.prod_map_homₓ'. -/
@[to_additive]
theorem prod_map_hom (L : List ι) (f : ι → M) {G : Type _} [MonoidHomClass G M N] (g : G) :
    (L.map (g ∘ f)).Prod = g (L.map f).Prod := by rw [← prod_hom, map_map]
#align list.prod_map_hom List.prod_map_hom
#align list.sum_map_hom List.sum_map_hom

/- warning: list.prod_is_unit -> List.prod_isUnit is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {L : List.{u1} M}, (forall (m : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) m L) -> (IsUnit.{u1} M _inst_1 m)) -> (IsUnit.{u1} M _inst_1 (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) L))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {L : List.{u1} M}, (forall (m : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) m L) -> (IsUnit.{u1} M _inst_1 m)) -> (IsUnit.{u1} M _inst_1 (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) L))
Case conversion may be inaccurate. Consider using '#align list.prod_is_unit List.prod_isUnitₓ'. -/
@[to_additive]
theorem prod_isUnit : ∀ {L : List M} (u : ∀ m ∈ L, IsUnit m), IsUnit L.Prod
  | [], _ => by simp
  | h :: t, u => by
    simp only [List.prod_cons]
    exact IsUnit.mul (u h (mem_cons_self h t)) (prod_is_unit fun m mt => u m (mem_cons_of_mem h mt))
#align list.prod_is_unit List.prod_isUnit

/- warning: list.prod_is_unit_iff -> List.prod_isUnit_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : CommMonoid.{u1} α] {L : List.{u1} α}, Iff (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) L)) (forall (m : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) m L) -> (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4) m))
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : CommMonoid.{u1} α] {L : List.{u1} α}, Iff (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4)) L)) (forall (m : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) m L) -> (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_4) m))
Case conversion may be inaccurate. Consider using '#align list.prod_is_unit_iff List.prod_isUnit_iffₓ'. -/
@[to_additive]
theorem prod_isUnit_iff {α : Type _} [CommMonoid α] {L : List α} :
    IsUnit L.Prod ↔ ∀ m ∈ L, IsUnit m :=
  by
  refine' ⟨fun h => _, prod_is_unit⟩
  induction' L with m L ih
  · exact fun m' h' => False.elim (not_mem_nil m' h')
  rw [prod_cons, IsUnit.mul_iff] at h
  exact fun m' h' => Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H
#align list.prod_is_unit_iff List.prod_isUnit_iff

/- warning: list.prod_take_mul_prod_drop -> List.prod_take_mul_prod_drop is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (L : List.{u1} M) (i : Nat), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.take.{u1} M i L)) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.drop.{u1} M i L))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) L)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (L : List.{u1} M) (i : Nat), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.take.{u1} M i L)) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.drop.{u1} M i L))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) L)
Case conversion may be inaccurate. Consider using '#align list.prod_take_mul_prod_drop List.prod_take_mul_prod_dropₓ'. -/
@[simp, to_additive]
theorem prod_take_mul_prod_drop : ∀ (L : List M) (i : ℕ), (L.take i).Prod * (L.drop i).Prod = L.Prod
  | [], i => by simp [Nat.zero_le]
  | L, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    rw [prod_cons, prod_cons, mul_assoc, prod_take_mul_prod_drop]
#align list.prod_take_mul_prod_drop List.prod_take_mul_prod_drop
#align list.sum_take_add_sum_drop List.sum_take_add_sum_drop

/- warning: list.prod_take_succ -> List.prod_take_succ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (L : List.{u1} M) (i : Nat) (p : LT.lt.{0} Nat Nat.hasLt i (List.length.{u1} M L)), Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.take.{u1} M (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) L)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.take.{u1} M i L)) (List.nthLe.{u1} M L i p))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (L : List.{u1} M) (i : Nat) (p : LT.lt.{0} Nat instLTNat i (List.length.{u1} M L)), Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.take.{u1} M (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) L)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.take.{u1} M i L)) (List.nthLe.{u1} M L i p))
Case conversion may be inaccurate. Consider using '#align list.prod_take_succ List.prod_take_succₓ'. -/
@[simp, to_additive]
theorem prod_take_succ :
    ∀ (L : List M) (i : ℕ) (p), (L.take (i + 1)).Prod = (L.take i).Prod * L.nthLe i p
  | [], i, p => by cases p
  | h :: t, 0, _ => by simp
  | h :: t, n + 1, _ => by
    dsimp
    rw [prod_cons, prod_cons, prod_take_succ, mul_assoc]
#align list.prod_take_succ List.prod_take_succ
#align list.sum_take_succ List.sum_take_succ

/- warning: list.length_pos_of_prod_ne_one -> List.length_pos_of_prod_ne_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (L : List.{u1} M), (Ne.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) L) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (List.length.{u1} M L))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (L : List.{u1} M), (Ne.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) L) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (List.length.{u1} M L))
Case conversion may be inaccurate. Consider using '#align list.length_pos_of_prod_ne_one List.length_pos_of_prod_ne_oneₓ'. -/
/-- A list with product not one must have positive length. -/
@[to_additive "A list with sum not zero must have positive length."]
theorem length_pos_of_prod_ne_one (L : List M) (h : L.Prod ≠ 1) : 0 < L.length :=
  by
  cases L
  · contrapose h
    simp
  · simp
#align list.length_pos_of_prod_ne_one List.length_pos_of_prod_ne_one
#align list.length_pos_of_sum_ne_zero List.length_pos_of_sum_ne_zero

/- warning: list.length_pos_of_one_lt_prod -> List.length_pos_of_one_lt_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] (L : List.{u1} M), (LT.lt.{u1} M (Preorder.toLT.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) L)) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (List.length.{u1} M L))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] (L : List.{u1} M), (LT.lt.{u1} M (Preorder.toLT.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) L)) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (List.length.{u1} M L))
Case conversion may be inaccurate. Consider using '#align list.length_pos_of_one_lt_prod List.length_pos_of_one_lt_prodₓ'. -/
/-- A list with product greater than one must have positive length. -/
@[to_additive length_pos_of_sum_pos "A list with positive sum must have positive length."]
theorem length_pos_of_one_lt_prod [Preorder M] (L : List M) (h : 1 < L.Prod) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne'
#align list.length_pos_of_one_lt_prod List.length_pos_of_one_lt_prod
#align list.length_pos_of_sum_pos List.length_pos_of_sum_pos

/- warning: list.length_pos_of_prod_lt_one -> List.length_pos_of_prod_lt_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] (L : List.{u1} M), (LT.lt.{u1} M (Preorder.toLT.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) L) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (List.length.{u1} M L))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] (L : List.{u1} M), (LT.lt.{u1} M (Preorder.toLT.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) L) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (List.length.{u1} M L))
Case conversion may be inaccurate. Consider using '#align list.length_pos_of_prod_lt_one List.length_pos_of_prod_lt_oneₓ'. -/
/-- A list with product less than one must have positive length. -/
@[to_additive "A list with negative sum must have positive length."]
theorem length_pos_of_prod_lt_one [Preorder M] (L : List M) (h : L.Prod < 1) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.Ne
#align list.length_pos_of_prod_lt_one List.length_pos_of_prod_lt_one
#align list.length_pos_of_sum_neg List.length_pos_of_sum_neg

/- warning: list.prod_update_nth -> List.prod_set is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (L : List.{u1} M) (n : Nat) (a : M), Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.set.{u1} M L n a)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.take.{u1} M n L)) (ite.{succ u1} M (LT.lt.{0} Nat Nat.hasLt n (List.length.{u1} M L)) (Nat.decidableLt n (List.length.{u1} M L)) a (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.drop.{u1} M (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) L)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (L : List.{u1} M) (n : Nat) (a : M), Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.set.{u1} M L n a)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.take.{u1} M n L)) (ite.{succ u1} M (LT.lt.{0} Nat instLTNat n (List.length.{u1} M L)) (Nat.decLt n (List.length.{u1} M L)) a (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.drop.{u1} M (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) L)))
Case conversion may be inaccurate. Consider using '#align list.prod_update_nth List.prod_setₓ'. -/
@[to_additive]
theorem prod_set :
    ∀ (L : List M) (n : ℕ) (a : M),
      (L.updateNth n a).Prod =
        ((L.take n).Prod * if n < L.length then a else 1) * (L.drop (n + 1)).Prod
  | x :: xs, 0, a => by simp [update_nth]
  | x :: xs, i + 1, a => by simp [update_nth, prod_update_nth xs i a, mul_assoc]
  | [], _, _ => by simp [update_nth, (Nat.zero_le _).not_lt, Nat.zero_le]
#align list.prod_update_nth List.prod_set
#align list.sum_update_nth List.sum_set

open MulOpposite

/- warning: list.nth_zero_mul_tail_prod -> List.get?_zero_mul_tail_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Option.getD.{u1} M (List.get?.{u1} M l (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.tail.{u1} M l))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Option.getD.{u1} M (List.get?.{u1} M l (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.tail.{u1} M l))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l)
Case conversion may be inaccurate. Consider using '#align list.nth_zero_mul_tail_prod List.get?_zero_mul_tail_prodₓ'. -/
/-- We'd like to state this as `L.head * L.tail.prod = L.prod`, but because `L.head` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `(L.nth 0).get_or_else 1`.
-/
@[to_additive
      "We'd like to state this as `L.head + L.tail.sum = L.sum`, but because `L.head`\nrelies on an inhabited instance to return a garbage value on the empty list, this is not possible.\nInstead, we write the statement in terms of `(L.nth 0).get_or_else 0`."]
theorem get?_zero_mul_tail_prod (l : List M) : (l.nth 0).getOrElse 1 * l.tail.Prod = l.Prod := by
  cases l <;> simp
#align list.nth_zero_mul_tail_prod List.get?_zero_mul_tail_prod
#align list.nth_zero_add_tail_sum List.get?_zero_add_tail_sum

/- warning: list.head_mul_tail_prod_of_ne_nil -> List.headI_mul_tail_prod_of_ne_nil is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Inhabited.{succ u1} M] (l : List.{u1} M), (Ne.{succ u1} (List.{u1} M) l (List.nil.{u1} M)) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.headI.{u1} M _inst_4 l) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.tail.{u1} M l))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Inhabited.{succ u1} M] (l : List.{u1} M), (Ne.{succ u1} (List.{u1} M) l (List.nil.{u1} M)) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.headI.{u1} M _inst_4 l) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.tail.{u1} M l))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l))
Case conversion may be inaccurate. Consider using '#align list.head_mul_tail_prod_of_ne_nil List.headI_mul_tail_prod_of_ne_nilₓ'. -/
/-- Same as `nth_zero_mul_tail_prod`, but avoiding the `list.head` garbage complication by requiring
the list to be nonempty. -/
@[to_additive
      "Same as `nth_zero_add_tail_sum`, but avoiding the `list.head` garbage complication\nby requiring the list to be nonempty."]
theorem headI_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l ≠ []) :
    l.head * l.tail.Prod = l.Prod := by cases l <;> [contradiction, simp]
#align list.head_mul_tail_prod_of_ne_nil List.headI_mul_tail_prod_of_ne_nil
#align list.head_add_tail_sum_of_ne_nil List.headI_add_tail_sum_of_ne_nil

/- warning: commute.list_prod_right -> Commute.list_prod_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M) (y : M), (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) y x)) -> (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) y (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M) (y : M), (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) y x)) -> (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) y (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l))
Case conversion may be inaccurate. Consider using '#align commute.list_prod_right Commute.list_prod_rightₓ'. -/
@[to_additive]
theorem Commute.list_prod_right (l : List M) (y : M) (h : ∀ x ∈ l, Commute y x) :
    Commute y l.Prod := by
  induction' l with z l IH
  · simp
  · rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)
#align commute.list_prod_right Commute.list_prod_right
#align add_commute.list_sum_right AddCommute.list_sum_right

/- warning: commute.list_prod_left -> Commute.list_prod_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M) (y : M), (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) x y)) -> (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) y)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M) (y : M), (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) x y)) -> (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) y)
Case conversion may be inaccurate. Consider using '#align commute.list_prod_left Commute.list_prod_leftₓ'. -/
@[to_additive]
theorem Commute.list_prod_left (l : List M) (y : M) (h : ∀ x ∈ l, Commute x y) : Commute l.Prod y :=
  (Commute.list_prod_right _ _ fun x hx => (h _ hx).symm).symm
#align commute.list_prod_left Commute.list_prod_left
#align add_commute.list_sum_left AddCommute.list_sum_left

/- warning: list.forall₂.prod_le_prod' -> List.Forall₂.prod_le_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4))] [_inst_6 : CovariantClass.{u1, u1} M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4))] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, (List.Forall₂.{u1, u1} M M (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4)) l₁ l₂) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l₁) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l₂))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2748 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2750 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2748 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2750)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2763 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2765 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2763 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2765)] [_inst_6 : CovariantClass.{u1, u1} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2782 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2784 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2782 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2784) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2797 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2799 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2797 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2799)] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, (List.Forall₂.{u1, u1} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2817 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2819 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2817 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2819) l₁ l₂) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l₁) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l₂))
Case conversion may be inaccurate. Consider using '#align list.forall₂.prod_le_prod' List.Forall₂.prod_le_prod'ₓ'. -/
@[to_additive sum_le_sum]
theorem Forall₂.prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l₁ l₂ : List M} (h : Forall₂ (· ≤ ·) l₁ l₂) :
    l₁.Prod ≤ l₂.Prod := by
  induction' h with a b la lb hab ih ih'
  · rfl
  · simpa only [prod_cons] using mul_le_mul' hab ih'
#align list.forall₂.prod_le_prod' List.Forall₂.prod_le_prod'
#align list.forall₂.sum_le_sum List.Forall₂.sum_le_sum

/- warning: list.sublist.prod_le_prod' -> List.Sublist.prod_le_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4))] [_inst_6 : CovariantClass.{u1, u1} M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4))] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, (List.Sublist.{u1} M l₁ l₂) -> (forall (a : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) a l₂) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) a)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l₁) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l₂))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2901 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2903 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2901 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2903)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2916 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2918 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2916 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2918)] [_inst_6 : CovariantClass.{u1, u1} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2935 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2937 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2935 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2937) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2950 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2952 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2950 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.2952)] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, (List.Sublist.{u1} M l₁ l₂) -> (forall (a : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) a l₂) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))) a)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l₁) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l₂))
Case conversion may be inaccurate. Consider using '#align list.sublist.prod_le_prod' List.Sublist.prod_le_prod'ₓ'. -/
/-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are greater than or equal to one, then
`l₁.prod ≤ l₂.prod`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 1 ≤ a` instead
of `∀ a ∈ l₂, 1 ≤ a` but this lemma is not yet in `mathlib`. -/
@[to_additive sum_le_sum
      "If `l₁` is a sublist of `l₂` and all elements of `l₂` are nonnegative,\nthen `l₁.sum ≤ l₂.sum`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 0 ≤ a` instead\nof `∀ a ∈ l₂, 0 ≤ a` but this lemma is not yet in `mathlib`."]
theorem Sublist.prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l₁ l₂ : List M} (h : l₁ <+ l₂)
    (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) : l₁.Prod ≤ l₂.Prod :=
  by
  induction h; · rfl
  case cons l₁ l₂ a ih ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  case cons2 l₁ l₂ a ih ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁⊢
    exact mul_le_mul_left' (ih' h₁.2) _
#align list.sublist.prod_le_prod' List.Sublist.prod_le_prod'
#align list.sublist.sum_le_sum List.Sublist.sum_le_sum

/- warning: list.sublist_forall₂.prod_le_prod' -> List.SublistForall₂.prod_le_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4))] [_inst_6 : CovariantClass.{u1, u1} M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4))] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, (List.SublistForall₂.{u1, u1} M M (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4)) l₁ l₂) -> (forall (a : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) a l₂) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) a)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l₁) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l₂))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3090 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3092 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3090 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3092)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3105 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3107 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3105 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3107)] [_inst_6 : CovariantClass.{u1, u1} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3124 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3126 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3124 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3126) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3139 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3141 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3139 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3141)] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, (List.SublistForall₂.{u1, u1} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3159 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3161 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3159 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3161) l₁ l₂) -> (forall (a : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) a l₂) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))) a)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l₁) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l₂))
Case conversion may be inaccurate. Consider using '#align list.sublist_forall₂.prod_le_prod' List.SublistForall₂.prod_le_prod'ₓ'. -/
@[to_additive sum_le_sum]
theorem SublistForall₂.prod_le_prod' [Preorder M]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] [CovariantClass M M (· * ·) (· ≤ ·)]
    {l₁ l₂ : List M} (h : SublistForall₂ (· ≤ ·) l₁ l₂) (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) :
    l₁.Prod ≤ l₂.Prod :=
  let ⟨l, hall, hsub⟩ := sublistForall₂_iff.1 h
  hall.prod_le_prod'.trans <| hsub.prod_le_prod' h₁
#align list.sublist_forall₂.prod_le_prod' List.SublistForall₂.prod_le_prod'
#align list.sublist_forall₂.sum_le_sum List.SublistForall₂.sum_le_sum

/- warning: list.prod_le_prod' -> List.prod_le_prod' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : Preorder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4))] [_inst_6 : CovariantClass.{u2, u2} M M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4))] {l : List.{u1} ι} {f : ι -> M} {g : ι -> M}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) (f i) (g i))) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M g l)))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : Preorder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3272 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3274 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3272 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3274)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3287 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3289 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3287 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3289)] [_inst_6 : CovariantClass.{u2, u2} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3306 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3308 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3306 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3308) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3321 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3323 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3321 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3323)] {l : List.{u1} ι} {f : ι -> M} {g : ι -> M}, (forall (i : ι), (Membership.mem.{u1, u1} ι (List.{u1} ι) (List.instMembershipList.{u1} ι) i l) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) (f i) (g i))) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M g l)))
Case conversion may be inaccurate. Consider using '#align list.prod_le_prod' List.prod_le_prod'ₓ'. -/
@[to_additive sum_le_sum]
theorem prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l : List ι} {f g : ι → M} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).Prod ≤ (l.map g).Prod :=
  forall₂.prod_le_prod' <| by simpa
#align list.prod_le_prod' List.prod_le_prod'
#align list.sum_le_sum List.sum_le_sum

/- warning: list.prod_lt_prod' -> List.prod_lt_prod' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : Preorder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4))] [_inst_6 : CovariantClass.{u2, u2} M M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4))] [_inst_7 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4))] [_inst_8 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4))] {l : List.{u1} ι} (f : ι -> M) (g : ι -> M), (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) (f i) (g i))) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) (fun (H : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) (f i) (g i)))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M g l)))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : Preorder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3417 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3419 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3417 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3419) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3432 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3434 : M) => LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3432 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3434)] [_inst_6 : CovariantClass.{u2, u2} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3451 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3453 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3451 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3453) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3466 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3468 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3466 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3468)] [_inst_7 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3488 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3490 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3488 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3490)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3503 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3505 : M) => LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3503 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3505)] [_inst_8 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3525 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3527 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3525 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3527)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3540 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3542 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3540 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3542)] {l : List.{u1} ι} (f : ι -> M) (g : ι -> M), (forall (i : ι), (Membership.mem.{u1, u1} ι (List.{u1} ι) (List.instMembershipList.{u1} ι) i l) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) (f i) (g i))) -> (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (List.{u1} ι) (List.instMembershipList.{u1} ι) i l) (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) (f i) (g i)))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M g l)))
Case conversion may be inaccurate. Consider using '#align list.prod_lt_prod' List.prod_lt_prod'ₓ'. -/
@[to_additive sum_lt_sum]
theorem prod_lt_prod' [Preorder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (f g : ι → M)
    (h₁ : ∀ i ∈ l, f i ≤ g i) (h₂ : ∃ i ∈ l, f i < g i) : (l.map f).Prod < (l.map g).Prod :=
  by
  induction' l with i l ihl; · rcases h₂ with ⟨_, ⟨⟩, _⟩
  simp only [ball_cons, bex_cons, map_cons, prod_cons] at h₁ h₂⊢
  cases h₂
  exacts[mul_lt_mul_of_lt_of_le h₂ (prod_le_prod' h₁.2), mul_lt_mul_of_le_of_lt h₁.1 <| ihl h₁.2 h₂]
#align list.prod_lt_prod' List.prod_lt_prod'
#align list.sum_lt_sum List.sum_lt_sum

/- warning: list.prod_lt_prod_of_ne_nil -> List.prod_lt_prod_of_ne_nil is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : Preorder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4))] [_inst_6 : CovariantClass.{u2, u2} M M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4))] [_inst_7 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4))] [_inst_8 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4))] {l : List.{u1} ι}, (Ne.{succ u1} (List.{u1} ι) l (List.nil.{u1} ι)) -> (forall (f : ι -> M) (g : ι -> M), (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) (f i) (g i))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M g l))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : Preorder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3716 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3718 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3716 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3718) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3731 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3733 : M) => LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3731 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3733)] [_inst_6 : CovariantClass.{u2, u2} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3750 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3752 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3750 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3752) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3765 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3767 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3765 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3767)] [_inst_7 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3787 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3789 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3787 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3789)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3802 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3804 : M) => LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3802 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3804)] [_inst_8 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3824 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3826 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3824 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3826)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3839 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3841 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3839 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3841)] {l : List.{u1} ι}, (Ne.{succ u1} (List.{u1} ι) l (List.nil.{u1} ι)) -> (forall (f : ι -> M) (g : ι -> M), (forall (i : ι), (Membership.mem.{u1, u1} ι (List.{u1} ι) (List.instMembershipList.{u1} ι) i l) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) (f i) (g i))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M _inst_4) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M g l))))
Case conversion may be inaccurate. Consider using '#align list.prod_lt_prod_of_ne_nil List.prod_lt_prod_of_ne_nilₓ'. -/
@[to_additive]
theorem prod_lt_prod_of_ne_nil [Preorder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (hlt : ∀ i ∈ l, f i < g i) : (l.map f).Prod < (l.map g).Prod :=
  (prod_lt_prod' f g fun i hi => (hlt i hi).le) <|
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩
#align list.prod_lt_prod_of_ne_nil List.prod_lt_prod_of_ne_nil
#align list.sum_lt_sum_of_ne_nil List.sum_lt_sum_of_ne_nil

/- warning: list.prod_le_pow_card -> List.prod_le_pow_card is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4))] [_inst_6 : CovariantClass.{u1, u1} M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4))] (l : List.{u1} M) (n : M), (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x n)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n (List.length.{u1} M l)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3972 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3974 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3972 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3974)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3987 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3989 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3987 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.3989)] [_inst_6 : CovariantClass.{u1, u1} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4006 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4008 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4006 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4008) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4021 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4023 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4021 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4023)] (l : List.{u1} M) (n : M), (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x n)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n (List.length.{u1} M l)))
Case conversion may be inaccurate. Consider using '#align list.prod_le_pow_card List.prod_le_pow_cardₓ'. -/
@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] (l : List M) (n : M) (h : ∀ x ∈ l, x ≤ n) :
    l.Prod ≤ n ^ l.length := by
  simpa only [map_id'', map_const, prod_replicate] using prod_le_prod' h
#align list.prod_le_pow_card List.prod_le_pow_card
#align list.sum_le_card_nsmul List.sum_le_card_nsmul

/- warning: list.exists_lt_of_prod_lt' -> List.exists_lt_of_prod_lt' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : LinearOrder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))))] [_inst_6 : CovariantClass.{u2, u2} M M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))))] {l : List.{u1} ι} (f : ι -> M) (g : ι -> M), (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M g l))) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) (fun (H : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))) (f i) (g i))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : LinearOrder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4109 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4111 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4109 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4111)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4124 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4126 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4124 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4126)] [_inst_6 : CovariantClass.{u2, u2} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4143 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4145 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4143 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4145) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4158 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4160 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4158 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4160)] {l : List.{u1} ι} (f : ι -> M) (g : ι -> M), (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M g l))) -> (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (List.{u1} ι) (List.instMembershipList.{u1} ι) i l) (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) (f i) (g i))))
Case conversion may be inaccurate. Consider using '#align list.exists_lt_of_prod_lt' List.exists_lt_of_prod_lt'ₓ'. -/
@[to_additive exists_lt_of_sum_lt]
theorem exists_lt_of_prod_lt' [LinearOrder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l : List ι} (f g : ι → M)
    (h : (l.map f).Prod < (l.map g).Prod) : ∃ i ∈ l, f i < g i :=
  by
  contrapose! h
  exact prod_le_prod' h
#align list.exists_lt_of_prod_lt' List.exists_lt_of_prod_lt'
#align list.exists_lt_of_sum_lt List.exists_lt_of_sum_lt

/- warning: list.exists_le_of_prod_le' -> List.exists_le_of_prod_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : LinearOrder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))))] [_inst_6 : CovariantClass.{u2, u2} M M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))))] [_inst_7 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))))] [_inst_8 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))))) (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))))] {l : List.{u1} ι}, (Ne.{succ u1} (List.{u1} ι) l (List.nil.{u1} ι)) -> (forall (f : ι -> M) (g : ι -> M), (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (List.map.{u1, u2} ι M g l))) -> (Exists.{succ u1} ι (fun (x : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) x l) (fun (H : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) x l) => LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (LinearOrder.toLattice.{u2} M _inst_4))))) (f x) (g x)))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] [_inst_4 : LinearOrder.{u2} M] [_inst_5 : CovariantClass.{u2, u2} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4276 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4278 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4276 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4278) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4291 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4293 : M) => LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4291 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4293)] [_inst_6 : CovariantClass.{u2, u2} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4310 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4312 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4310 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4312) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4325 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4327 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4325 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4327)] [_inst_7 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4347 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4349 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4347 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4349)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4362 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4364 : M) => LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4362 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4364)] [_inst_8 : CovariantClass.{u2, u2} M M (Function.swap.{succ u2, succ u2, succ u2} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4384 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4386 : M) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4384 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4386)) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4399 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4401 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4399 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4401)] {l : List.{u1} ι}, (Ne.{succ u1} (List.{u1} ι) l (List.nil.{u1} ι)) -> (forall (f : ι -> M) (g : ι -> M), (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M f l)) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u1, u2} ι M g l))) -> (Exists.{succ u1} ι (fun (x : ι) => And (Membership.mem.{u1, u1} ι (List.{u1} ι) (List.instMembershipList.{u1} ι) x l) (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (SemilatticeInf.toPartialOrder.{u2} M (Lattice.toSemilatticeInf.{u2} M (DistribLattice.toLattice.{u2} M (instDistribLattice.{u2} M _inst_4)))))) (f x) (g x)))))
Case conversion may be inaccurate. Consider using '#align list.exists_le_of_prod_le' List.exists_le_of_prod_le'ₓ'. -/
@[to_additive exists_le_of_sum_le]
theorem exists_le_of_prod_le' [LinearOrder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (h : (l.map f).Prod ≤ (l.map g).Prod) : ∃ x ∈ l, f x ≤ g x :=
  by
  contrapose! h
  exact prod_lt_prod_of_ne_nil hl _ _ h
#align list.exists_le_of_prod_le' List.exists_le_of_prod_le'
#align list.exists_le_of_sum_le List.exists_le_of_sum_le

/- warning: list.one_le_prod_of_one_le -> List.one_le_prod_of_one_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4))] {l : List.{u1} M}, (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) x)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_4 : Preorder.{u1} M] [_inst_5 : CovariantClass.{u1, u1} M M (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4527 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4529 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4527 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4529) (fun (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4542 : M) (x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4544 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4542 x._@.Mathlib.Data.List.BigOperators.Basic._hyg.4544)] {l : List.{u1} M}, (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))) x)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_4) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l))
Case conversion may be inaccurate. Consider using '#align list.one_le_prod_of_one_le List.one_le_prod_of_one_leₓ'. -/
@[to_additive sum_nonneg]
theorem one_le_prod_of_one_le [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) : 1 ≤ l.Prod :=
  by
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [covariant_class M M (function.swap (*)) (≤)]
  induction' l with hd tl ih;
  · rfl
  rw [prod_cons]
  exact one_le_mul (hl₁ hd (mem_cons_self hd tl)) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))
#align list.one_le_prod_of_one_le List.one_le_prod_of_one_le
#align list.sum_nonneg List.sum_nonneg

end Monoid

section MonoidWithZero

variable [MonoidWithZero M₀]

/- warning: list.prod_eq_zero -> List.prod_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] {L : List.{u1} M₀}, (Membership.Mem.{u1, u1} M₀ (List.{u1} M₀) (List.hasMem.{u1} M₀) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))) L) -> (Eq.{succ u1} M₀ (List.prod.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) L) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] {L : List.{u1} M₀}, (Membership.mem.{u1, u1} M₀ (List.{u1} M₀) (List.instMembershipList.{u1} M₀) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))) L) -> (Eq.{succ u1} M₀ (List.prod.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) L) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align list.prod_eq_zero List.prod_eq_zeroₓ'. -/
/-- If zero is an element of a list `L`, then `list.prod L = 0`. If the domain is a nontrivial
monoid with zero with no divisors, then this implication becomes an `iff`, see
`list.prod_eq_zero_iff`. -/
theorem prod_eq_zero {L : List M₀} (h : (0 : M₀) ∈ L) : L.Prod = 0 :=
  by
  induction' L with a L ihL
  · exact absurd h (not_mem_nil _)
  · rw [prod_cons]
    cases' (mem_cons_iff _ _ _).1 h with ha hL
    exacts[mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (ihL hL)]
#align list.prod_eq_zero List.prod_eq_zero

/- warning: list.prod_eq_zero_iff -> List.prod_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] [_inst_3 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))] {L : List.{u1} M₀}, Iff (Eq.{succ u1} M₀ (List.prod.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) L) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))) (Membership.Mem.{u1, u1} M₀ (List.{u1} M₀) (List.hasMem.{u1} M₀) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))) L)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] [_inst_3 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (MonoidWithZero.toZero.{u1} M₀ _inst_1)] {L : List.{u1} M₀}, Iff (Eq.{succ u1} M₀ (List.prod.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) L) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))) (Membership.mem.{u1, u1} M₀ (List.{u1} M₀) (List.instMembershipList.{u1} M₀) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))) L)
Case conversion may be inaccurate. Consider using '#align list.prod_eq_zero_iff List.prod_eq_zero_iffₓ'. -/
/-- Product of elements of a list `L` equals zero if and only if `0 ∈ L`. See also
`list.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
@[simp]
theorem prod_eq_zero_iff [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} :
    L.Prod = 0 ↔ (0 : M₀) ∈ L := by
  induction' L with a L ihL
  · simp
  · rw [prod_cons, mul_eq_zero, ihL, mem_cons_iff, eq_comm]
#align list.prod_eq_zero_iff List.prod_eq_zero_iff

/- warning: list.prod_ne_zero -> List.prod_ne_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] [_inst_3 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))] {L : List.{u1} M₀}, (Not (Membership.Mem.{u1, u1} M₀ (List.{u1} M₀) (List.hasMem.{u1} M₀) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))) L)) -> (Ne.{succ u1} M₀ (List.prod.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) L) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] [_inst_3 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (MonoidWithZero.toZero.{u1} M₀ _inst_1)] {L : List.{u1} M₀}, (Not (Membership.mem.{u1, u1} M₀ (List.{u1} M₀) (List.instMembershipList.{u1} M₀) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))) L)) -> (Ne.{succ u1} M₀ (List.prod.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))) (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) L) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align list.prod_ne_zero List.prod_ne_zeroₓ'. -/
theorem prod_ne_zero [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} (hL : (0 : M₀) ∉ L) :
    L.Prod ≠ 0 :=
  mt prod_eq_zero_iff.1 hL
#align list.prod_ne_zero List.prod_ne_zero

end MonoidWithZero

section Group

variable [Group G]

/- warning: list.prod_inv_reverse -> List.prod_inv_reverse is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) L)) (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (List.reverse.{u1} G (List.map.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) x) L)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) L)) (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (List.reverse.{u1} G (List.map.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) x) L)))
Case conversion may be inaccurate. Consider using '#align list.prod_inv_reverse List.prod_inv_reverseₓ'. -/
/-- This is the `list.prod` version of `mul_inv_rev` -/
@[to_additive "This is the `list.sum` version of `add_neg_rev`"]
theorem prod_inv_reverse : ∀ L : List G, L.Prod⁻¹ = (L.map fun x => x⁻¹).reverse.Prod
  | [] => by simp
  | x :: xs => by simp [prod_inv_reverse xs]
#align list.prod_inv_reverse List.prod_inv_reverse
#align list.sum_neg_reverse List.sum_neg_reverse

/- warning: list.prod_reverse_noncomm -> List.prod_reverse_noncomm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (List.reverse.{u1} G L)) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (List.map.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) x) L)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (List.reverse.{u1} G L)) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (List.map.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) x) L)))
Case conversion may be inaccurate. Consider using '#align list.prod_reverse_noncomm List.prod_reverse_noncommₓ'. -/
/-- A non-commutative variant of `list.prod_reverse` -/
@[to_additive "A non-commutative variant of `list.sum_reverse`"]
theorem prod_reverse_noncomm : ∀ L : List G, L.reverse.Prod = (L.map fun x => x⁻¹).Prod⁻¹ := by
  simp [prod_inv_reverse]
#align list.prod_reverse_noncomm List.prod_reverse_noncomm
#align list.sum_reverse_noncomm List.sum_reverse_noncomm

/- warning: list.prod_drop_succ -> List.prod_drop_succ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (L : List.{u1} G) (i : Nat) (p : LT.lt.{0} Nat Nat.hasLt i (List.length.{u1} G L)), Eq.{succ u1} G (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (List.drop.{u1} G (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) L)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (List.nthLe.{u1} G L i p)) (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (List.drop.{u1} G i L)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (L : List.{u1} G) (i : Nat) (p : LT.lt.{0} Nat instLTNat i (List.length.{u1} G L)), Eq.{succ u1} G (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (List.drop.{u1} G (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) L)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (List.nthLe.{u1} G L i p)) (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (List.drop.{u1} G i L)))
Case conversion may be inaccurate. Consider using '#align list.prod_drop_succ List.prod_drop_succₓ'. -/
/-- Counterpart to `list.prod_take_succ` when we have an inverse operation -/
@[simp, to_additive "Counterpart to `list.sum_take_succ` when we have an negation operation"]
theorem prod_drop_succ :
    ∀ (L : List G) (i : ℕ) (p), (L.drop (i + 1)).Prod = (L.nthLe i p)⁻¹ * (L.drop i).Prod
  | [], i, p => False.elim (Nat.not_lt_zero _ p)
  | x :: xs, 0, p => by simp
  | x :: xs, i + 1, p => prod_drop_succ xs i _
#align list.prod_drop_succ List.prod_drop_succ
#align list.sum_drop_succ List.sum_drop_succ

end Group

section CommGroup

variable [CommGroup G]

/- warning: list.prod_inv -> List.prod_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) L)) (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (List.map.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) x) L))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (L : List.{u1} G), Eq.{succ u1} G (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) L)) (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) (List.map.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) x) L))
Case conversion may be inaccurate. Consider using '#align list.prod_inv List.prod_invₓ'. -/
/-- This is the `list.prod` version of `mul_inv` -/
@[to_additive "This is the `list.sum` version of `add_neg`"]
theorem prod_inv : ∀ L : List G, L.Prod⁻¹ = (L.map fun x => x⁻¹).Prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv xs]
#align list.prod_inv List.prod_inv
#align list.sum_neg List.sum_neg

/- warning: list.prod_update_nth' -> List.prod_set' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (L : List.{u1} G) (n : Nat) (a : G), Eq.{succ u1} G (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (List.set.{u1} G L n a)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) L) (dite.{succ u1} G (LT.lt.{0} Nat Nat.hasLt n (List.length.{u1} G L)) (Nat.decidableLt n (List.length.{u1} G L)) (fun (hn : LT.lt.{0} Nat Nat.hasLt n (List.length.{u1} G L)) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) (List.nthLe.{u1} G L n hn)) a) (fun (hn : Not (LT.lt.{0} Nat Nat.hasLt n (List.length.{u1} G L))) => OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (L : List.{u1} G) (n : Nat) (a : G), Eq.{succ u1} G (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) (List.set.{u1} G L n a)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) L) (dite.{succ u1} G (LT.lt.{0} Nat instLTNat n (List.length.{u1} G L)) (Nat.decLt n (List.length.{u1} G L)) (fun (hn : LT.lt.{0} Nat instLTNat n (List.length.{u1} G L)) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) (List.nthLe.{u1} G L n hn)) a) (fun (hn : Not (LT.lt.{0} Nat instLTNat n (List.length.{u1} G L))) => OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align list.prod_update_nth' List.prod_set'ₓ'. -/
/-- Alternative version of `list.prod_update_nth` when the list is over a group -/
@[to_additive "Alternative version of `list.sum_update_nth` when the list is over a group"]
theorem prod_set' (L : List G) (n : ℕ) (a : G) :
    (L.updateNth n a).Prod = L.Prod * if hn : n < L.length then (L.nthLe n hn)⁻¹ * a else 1 :=
  by
  refine' (prod_update_nth L n a).trans _
  split_ifs with hn hn
  ·
    rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).Prod, ←
      mul_assoc (take n L).Prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  ·
    simp only [take_all_of_le (le_of_not_lt hn), prod_nil, mul_one,
      drop_eq_nil_of_le ((le_of_not_lt hn).trans n.le_succ)]
#align list.prod_update_nth' List.prod_set'

end CommGroup

/- warning: list.eq_of_prod_take_eq -> List.eq_of_prod_take_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : LeftCancelMonoid.{u1} M] {L : List.{u1} M} {L' : List.{u1} M}, (Eq.{1} Nat (List.length.{u1} M L) (List.length.{u1} M L')) -> (forall (i : Nat), (LE.le.{0} Nat Nat.hasLe i (List.length.{u1} M L)) -> (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1))) (List.take.{u1} M i L)) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1))) (List.take.{u1} M i L')))) -> (Eq.{succ u1} (List.{u1} M) L L')
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : LeftCancelMonoid.{u1} M] {L : List.{u1} M} {L' : List.{u1} M}, (Eq.{1} Nat (List.length.{u1} M L) (List.length.{u1} M L')) -> (forall (i : Nat), (LE.le.{0} Nat instLENat i (List.length.{u1} M L)) -> (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1))) (LeftCancelMonoid.toOne.{u1} M _inst_1) (List.take.{u1} M i L)) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1))) (LeftCancelMonoid.toOne.{u1} M _inst_1) (List.take.{u1} M i L')))) -> (Eq.{succ u1} (List.{u1} M) L L')
Case conversion may be inaccurate. Consider using '#align list.eq_of_prod_take_eq List.eq_of_prod_take_eqₓ'. -/
@[to_additive]
theorem eq_of_prod_take_eq [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
    (h' : ∀ i ≤ L.length, (L.take i).Prod = (L'.take i).Prod) : L = L' :=
  by
  apply ext_le h fun i h₁ h₂ => _
  have : (L.take (i + 1)).Prod = (L'.take (i + 1)).Prod := h' _ (Nat.succ_le_of_lt h₁)
  rw [prod_take_succ L i h₁, prod_take_succ L' i h₂, h' i (le_of_lt h₁)] at this
  convert mul_left_cancel this
#align list.eq_of_prod_take_eq List.eq_of_prod_take_eq
#align list.eq_of_sum_take_eq List.eq_of_sum_take_eq

/- warning: list.monotone_prod_take -> List.monotone_prod_take is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] (L : List.{u1} M), Monotone.{0, u1} Nat M (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))) (fun (i : Nat) => List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))) (List.take.{u1} M i L))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] (L : List.{u1} M), Monotone.{0, u1} Nat M (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))) (fun (i : Nat) => List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) (List.take.{u1} M i L))
Case conversion may be inaccurate. Consider using '#align list.monotone_prod_take List.monotone_prod_takeₓ'. -/
@[to_additive]
theorem monotone_prod_take [CanonicallyOrderedMonoid M] (L : List M) :
    Monotone fun i => (L.take i).Prod :=
  by
  apply monotone_nat_of_le_succ fun n => _
  cases' lt_or_le n L.length with h h
  · rw [prod_take_succ _ _ h]
    exact le_self_mul
  · simp [take_all_of_le h, take_all_of_le (le_trans h (Nat.le_succ _))]
#align list.monotone_prod_take List.monotone_prod_take
#align list.monotone_sum_take List.monotone_sum_take

/- warning: list.one_lt_prod_of_one_lt -> List.one_lt_prod_of_one_lt is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} M] (l : List.{u1} M), (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))))))) x)) -> (Ne.{succ u1} (List.{u1} M) l (List.nil.{u1} M)) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))))))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} M] (l : List.{u1} M), (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))))) x)) -> (Ne.{succ u1} (List.{u1} M) l (List.nil.{u1} M)) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))) l))
Case conversion may be inaccurate. Consider using '#align list.one_lt_prod_of_one_lt List.one_lt_prod_of_one_ltₓ'. -/
@[to_additive sum_pos]
theorem one_lt_prod_of_one_lt [OrderedCommMonoid M] :
    ∀ (l : List M) (hl : ∀ x ∈ l, (1 : M) < x) (hl₂ : l ≠ []), 1 < l.Prod
  | [], _, h => (h rfl).elim
  | [b], h, _ => by simpa using h
  | a :: b :: l, hl₁, hl₂ =>
    by
    simp only [forall_eq_or_imp, List.mem_cons _ a] at hl₁
    rw [List.prod_cons]
    apply one_lt_mul_of_lt_of_le' hl₁.1
    apply le_of_lt ((b :: l).one_lt_prod_of_one_lt hl₁.2 (l.cons_ne_nil b))
#align list.one_lt_prod_of_one_lt List.one_lt_prod_of_one_lt
#align list.sum_pos List.sum_pos

/- warning: list.single_le_prod -> List.single_le_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} M] {l : List.{u1} M}, (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))))))) x)) -> (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) x (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))) l)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} M] {l : List.{u1} M}, (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))))) x)) -> (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) x (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))) l)))
Case conversion may be inaccurate. Consider using '#align list.single_le_prod List.single_le_prodₓ'. -/
@[to_additive]
theorem single_le_prod [OrderedCommMonoid M] {l : List M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) :
    ∀ x ∈ l, x ≤ l.Prod := by
  induction l
  · simp
  simp_rw [prod_cons, forall_mem_cons] at hl₁⊢
  constructor
  · exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
  · exact fun x H => le_mul_of_one_le_of_le hl₁.1 (l_ih hl₁.right x H)
#align list.single_le_prod List.single_le_prod
#align list.single_le_sum List.single_le_sum

/- warning: list.all_one_of_le_one_le_of_prod_eq_one -> List.all_one_of_le_one_le_of_prod_eq_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} M] {l : List.{u1} M}, (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))))))) x)) -> (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))) l) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))))))) -> (forall {x : M}, (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} M] {l : List.{u1} M}, (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))))) x)) -> (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1))) l) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))))) -> (forall {x : M}, (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align list.all_one_of_le_one_le_of_prod_eq_one List.all_one_of_le_one_le_of_prod_eq_oneₓ'. -/
@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
theorem all_one_of_le_one_le_of_prod_eq_one [OrderedCommMonoid M] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) (hl₂ : l.Prod = 1) {x : M} (hx : x ∈ l) : x = 1 :=
  le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)
#align list.all_one_of_le_one_le_of_prod_eq_one List.all_one_of_le_one_le_of_prod_eq_one
#align list.all_zero_of_le_zero_le_of_sum_eq_zero List.all_zero_of_le_zero_le_of_sum_eq_zero

/- warning: list.prod_eq_one -> List.prod_eq_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M}, (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))))) -> (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M}, (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))))) -> (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align list.prod_eq_one List.prod_eq_oneₓ'. -/
/-- Slightly more general version of `list.prod_eq_one_iff` for a non-ordered `monoid` -/
@[to_additive
      "Slightly more general version of `list.sum_eq_zero_iff`\n  for a non-ordered `add_monoid`"]
theorem prod_eq_one [Monoid M] {l : List M} (hl : ∀ x ∈ l, x = (1 : M)) : l.Prod = 1 :=
  by
  induction' l with i l hil
  · rfl
  rw [List.prod_cons, hil fun x hx => hl _ (mem_cons_of_mem i hx), hl _ (mem_cons_self i l),
    one_mul]
#align list.prod_eq_one List.prod_eq_one
#align list.sum_eq_zero List.sum_eq_zero

/- warning: list.exists_mem_ne_one_of_prod_ne_one -> List.exists_mem_ne_one_of_prod_ne_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M}, (Ne.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (Exists.{succ u1} M (fun (x : M) => Exists.{0} (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) (fun (H : Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) => Ne.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {l : List.{u1} M}, (Ne.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (Exists.{succ u1} M (fun (x : M) => And (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) (Ne.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align list.exists_mem_ne_one_of_prod_ne_one List.exists_mem_ne_one_of_prod_ne_oneₓ'. -/
@[to_additive]
theorem exists_mem_ne_one_of_prod_ne_one [Monoid M] {l : List M} (h : l.Prod ≠ 1) :
    ∃ x ∈ l, x ≠ (1 : M) := by simpa only [not_forall] using mt prod_eq_one h
#align list.exists_mem_ne_one_of_prod_ne_one List.exists_mem_ne_one_of_prod_ne_one
#align list.exists_mem_ne_zero_of_sum_ne_zero List.exists_mem_ne_zero_of_sum_ne_zero

/- warning: list.sum_le_foldr_max -> List.sum_le_foldr_max is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : AddMonoid.{u1} M] [_inst_2 : AddMonoid.{u2} N] [_inst_3 : LinearOrder.{u2} N] (f : M -> N), (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3))))) (f (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u2} N 0 (OfNat.mk.{u2} N 0 (Zero.zero.{u2} N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))))) -> (forall (x : M) (y : M), LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3))))) (f (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1))) x y)) (LinearOrder.max.{u2} N _inst_3 (f x) (f y))) -> (forall (l : List.{u1} M), LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3))))) (f (List.sum.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)) (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)) l)) (List.foldr.{u2, u2} N N (LinearOrder.max.{u2} N _inst_3) (OfNat.ofNat.{u2} N 0 (OfNat.mk.{u2} N 0 (Zero.zero.{u2} N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))))) (List.map.{u1, u2} M N f l)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : AddMonoid.{u2} M] [_inst_2 : AddMonoid.{u1} N] [_inst_3 : LinearOrder.{u1} N] (f : M -> N), (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (SemilatticeInf.toPartialOrder.{u1} N (Lattice.toSemilatticeInf.{u1} N (DistribLattice.toLattice.{u1} N (instDistribLattice.{u1} N _inst_3)))))) (f (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M _inst_1)))) (OfNat.ofNat.{u1} N 0 (Zero.toOfNat0.{u1} N (AddMonoid.toZero.{u1} N _inst_2)))) -> (forall (x : M) (y : M), LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (SemilatticeInf.toPartialOrder.{u1} N (Lattice.toSemilatticeInf.{u1} N (DistribLattice.toLattice.{u1} N (instDistribLattice.{u1} N _inst_3)))))) (f (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_1))) x y)) (Max.max.{u1} N (LinearOrder.toMax.{u1} N _inst_3) (f x) (f y))) -> (forall (l : List.{u2} M), LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (SemilatticeInf.toPartialOrder.{u1} N (Lattice.toSemilatticeInf.{u1} N (DistribLattice.toLattice.{u1} N (instDistribLattice.{u1} N _inst_3)))))) (f (List.sum.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_1)) (AddMonoid.toZero.{u2} M _inst_1) l)) (List.foldr.{u1, u1} N N (Max.max.{u1} N (LinearOrder.toMax.{u1} N _inst_3)) (OfNat.ofNat.{u1} N 0 (Zero.toOfNat0.{u1} N (AddMonoid.toZero.{u1} N _inst_2))) (List.map.{u2, u1} M N f l)))
Case conversion may be inaccurate. Consider using '#align list.sum_le_foldr_max List.sum_le_foldr_maxₓ'. -/
-- TODO: develop theory of tropical rings
theorem sum_le_foldr_max [AddMonoid M] [AddMonoid N] [LinearOrder N] (f : M → N) (h0 : f 0 ≤ 0)
    (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : List M) : f l.Sum ≤ (l.map f).foldr max 0 :=
  by
  induction' l with hd tl IH
  · simpa using h0
  simp only [List.sum_cons, List.foldr_map, List.foldr] at IH⊢
  exact (hadd _ _).trans (max_le_max le_rfl IH)
#align list.sum_le_foldr_max List.sum_le_foldr_max

/- warning: list.prod_erase -> List.prod_erase is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} M] [_inst_2 : CommMonoid.{u1} M] {a : M} {l : List.{u1} M}, (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) a l) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) a (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (List.eraseₓ.{u1} M (fun (a : M) (b : M) => _inst_1 a b) l a))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} M] [_inst_2 : CommMonoid.{u1} M] {a : M} {l : List.{u1} M}, (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) a l) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) a (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) (List.erase.{u1} M (instBEq.{u1} M (fun (a : M) (b : M) => _inst_1 a b)) l a))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) l))
Case conversion may be inaccurate. Consider using '#align list.prod_erase List.prod_eraseₓ'. -/
@[simp, to_additive]
theorem prod_erase [DecidableEq M] [CommMonoid M] {a} :
    ∀ {l : List M}, a ∈ l → a * (l.erase a).Prod = l.Prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := Decidable.List.eq_or_ne_mem_of_mem h
    · simp only [List.erase, if_pos, prod_cons]
    · simp only [List.erase, if_neg (mt Eq.symm Ne), prod_cons, prod_erase h, mul_left_comm a b]
#align list.prod_erase List.prod_erase
#align list.sum_erase List.sum_erase

/- warning: list.prod_map_erase -> List.prod_map_erase is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : CommMonoid.{u2} M] (f : ι -> M) {a : ι} {l : List.{u1} ι}, (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) a l) -> (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))) (f a) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) (List.map.{u1, u2} ι M f (List.eraseₓ.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b) l a)))) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) (List.map.{u1, u2} ι M f l)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : CommMonoid.{u1} M] (f : ι -> M) {a : ι} {l : List.{u2} ι}, (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) a l) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) (f a) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) (List.map.{u2, u1} ι M f (List.erase.{u2} ι (instBEq.{u2} ι (fun (a : ι) (b : ι) => _inst_1 a b)) l a)))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) (List.map.{u2, u1} ι M f l)))
Case conversion may be inaccurate. Consider using '#align list.prod_map_erase List.prod_map_eraseₓ'. -/
@[simp, to_additive]
theorem prod_map_erase [DecidableEq ι] [CommMonoid M] (f : ι → M) {a} :
    ∀ {l : List ι}, a ∈ l → f a * ((l.erase a).map f).Prod = (l.map f).Prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := Decidable.List.eq_or_ne_mem_of_mem h
    · simp only [map, erase_cons_head, prod_cons]
    ·
      simp only [map, erase_cons_tail _ Ne.symm, prod_cons, prod_map_erase h,
        mul_left_comm (f a) (f b)]
#align list.prod_map_erase List.prod_map_erase
#align list.sum_map_erase List.sum_map_erase

#print List.sum_const_nat /-
theorem sum_const_nat (m n : ℕ) : sum (replicate m n) = m * n := by rw [sum_replicate, smul_eq_mul]
#align list.sum_const_nat List.sum_const_nat
-/

/- warning: list.prod_pos -> List.prod_pos is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedSemiring.{u1} R] (l : List.{u1} R), (forall (a : R), (Membership.Mem.{u1, u1} R (List.{u1} R) (List.hasMem.{u1} R) a l) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedCancelAddCommMonoid.toPartialOrder.{u1} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1)))))))) a)) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedCancelAddCommMonoid.toPartialOrder.{u1} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1)))))))) (List.prod.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1))))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1))))) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedSemiring.{u1} R] (l : List.{u1} R), (forall (a : R), (Membership.mem.{u1, u1} R (List.{u1} R) (List.instMembershipList.{u1} R) a l) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedSemiring.toPartialOrder.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1))))) a)) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedSemiring.toPartialOrder.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1))))) (List.prod.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toOne.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1)) l))
Case conversion may be inaccurate. Consider using '#align list.prod_pos List.prod_posₓ'. -/
/-- The product of a list of positive natural numbers is positive,
and likewise for any nontrivial ordered semiring. -/
theorem prod_pos [StrictOrderedSemiring R] (l : List R) (h : ∀ a ∈ l, (0 : R) < a) : 0 < l.Prod :=
  by
  induction' l with a l ih
  · simp
  · rw [prod_cons]
    exact mul_pos (h _ <| mem_cons_self _ _) (ih fun a ha => h a <| mem_cons_of_mem _ ha)
#align list.prod_pos List.prod_pos

/-!
Several lemmas about sum/head/tail for `list ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default = 0`.
-/


#print List.headI_add_tail_sum /-
/-- This relies on `default ℕ = 0`. -/
theorem headI_add_tail_sum (L : List ℕ) : L.head + L.tail.Sum = L.Sum :=
  by
  cases L
  · simp
    rfl
  · simp
#align list.head_add_tail_sum List.headI_add_tail_sum
-/

#print List.headI_le_sum /-
/-- This relies on `default ℕ = 0`. -/
theorem headI_le_sum (L : List ℕ) : L.head ≤ L.Sum :=
  Nat.le.intro (headI_add_tail_sum L)
#align list.head_le_sum List.headI_le_sum
-/

#print List.tail_sum /-
/-- This relies on `default ℕ = 0`. -/
theorem tail_sum (L : List ℕ) : L.tail.Sum = L.Sum - L.head := by
  rw [← head_add_tail_sum L, add_comm, add_tsub_cancel_right]
#align list.tail_sum List.tail_sum
-/

section Alternating

section

variable [One α] [Mul α] [Inv α]

#print List.alternatingProd_nil /-
@[simp, to_additive]
theorem alternatingProd_nil : alternatingProd ([] : List α) = 1 :=
  rfl
#align list.alternating_prod_nil List.alternatingProd_nil
-/

#print List.alternatingProd_singleton /-
@[simp, to_additive]
theorem alternatingProd_singleton (a : α) : alternatingProd [a] = a :=
  rfl
#align list.alternating_prod_singleton List.alternatingProd_singleton
-/

#print List.alternatingProd_cons_cons' /-
@[to_additive]
theorem alternatingProd_cons_cons' (a b : α) (l : List α) :
    alternatingProd (a :: b :: l) = a * b⁻¹ * alternatingProd l :=
  rfl
#align list.alternating_prod_cons_cons' List.alternatingProd_cons_cons'
-/

end

/- warning: list.alternating_prod_cons_cons -> List.alternatingProd_cons_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} α] (a : α) (b : α) (l : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1))) (DivInvMonoid.toHasInv.{u1} α _inst_1) (List.cons.{u1} α a (List.cons.{u1} α b l))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α _inst_1)) a b) (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1))) (DivInvMonoid.toHasInv.{u1} α _inst_1) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} α] (a : α) (b : α) (l : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1))) (DivInvMonoid.toInv.{u1} α _inst_1) (List.cons.{u1} α a (List.cons.{u1} α b l))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α _inst_1)) a b) (List.alternatingProd.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α _inst_1))) (DivInvMonoid.toInv.{u1} α _inst_1) l))
Case conversion may be inaccurate. Consider using '#align list.alternating_prod_cons_cons List.alternatingProd_cons_consₓ'. -/
@[to_additive]
theorem alternatingProd_cons_cons [DivInvMonoid α] (a b : α) (l : List α) :
    alternatingProd (a :: b :: l) = a / b * alternatingProd l := by
  rw [div_eq_mul_inv, alternating_prod_cons_cons']
#align list.alternating_prod_cons_cons List.alternatingProd_cons_cons

variable [CommGroup α]

/- warning: list.alternating_prod_cons' -> List.alternatingProd_cons' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (a : α) (l : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) (List.cons.{u1} α a l)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (a : α) (l : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (List.cons.{u1} α a l)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (List.alternatingProd.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) l)))
Case conversion may be inaccurate. Consider using '#align list.alternating_prod_cons' List.alternatingProd_cons'ₓ'. -/
@[to_additive]
theorem alternatingProd_cons' :
    ∀ (a : α) (l : List α), alternatingProd (a :: l) = a * (alternatingProd l)⁻¹
  | a, [] => by rw [alternating_prod_nil, inv_one, mul_one, alternating_prod_singleton]
  | a, b :: l => by
    rw [alternating_prod_cons_cons', alternating_prod_cons' b l, mul_inv, inv_inv, mul_assoc]
#align list.alternating_prod_cons' List.alternatingProd_cons'

/- warning: list.alternating_prod_cons -> List.alternatingProd_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (a : α) (l : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) (List.cons.{u1} α a l)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (a : α) (l : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (List.cons.{u1} α a l)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a (List.alternatingProd.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) l))
Case conversion may be inaccurate. Consider using '#align list.alternating_prod_cons List.alternatingProd_consₓ'. -/
@[simp, to_additive]
theorem alternatingProd_cons (a : α) (l : List α) :
    alternatingProd (a :: l) = a / alternatingProd l := by
  rw [div_eq_mul_inv, alternating_prod_cons']
#align list.alternating_prod_cons List.alternatingProd_cons

end Alternating

end List

section MonoidHom

variable [Monoid M] [Monoid N]

/- warning: map_list_prod -> map_list_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] {F : Type.{u3}} [_inst_3 : MonoidHomClass.{u3, u1, u2} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)] (f : F) (l : List.{u1} M), Eq.{succ u2} N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) _inst_3))) f (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l)) (List.prod.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (List.map.{u1, u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) _inst_3))) f) l))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] {F : Type.{u3}} [_inst_3 : MonoidHomClass.{u3, u2, u1} F M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)] (f : F) (l : List.{u2} M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) l)) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) _inst_3)) f (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) l)) (List.prod.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (Monoid.toOne.{u1} N _inst_2) (List.map.{u2, u1} M N (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) _inst_3)) f) l))
Case conversion may be inaccurate. Consider using '#align map_list_prod map_list_prodₓ'. -/
@[to_additive]
theorem map_list_prod {F : Type _} [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.Prod = (l.map f).Prod :=
  (l.prod_hom f).symm
#align map_list_prod map_list_prod
#align map_list_sum map_list_sum

namespace MonoidHom

/- warning: monoid_hom.map_list_prod -> MonoidHom.map_list_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (l : List.{u1} M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) f (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l)) (List.prod.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (List.map.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) f) l))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] (f : MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) (l : List.{u2} M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) l)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)))) f (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) l)) (List.prod.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (Monoid.toOne.{u1} N _inst_2) (List.map.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)))) f) l))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_list_prod MonoidHom.map_list_prodₓ'. -/
/-- Deprecated, use `_root_.map_list_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_list_sum` instead."]
protected theorem map_list_prod (f : M →* N) (l : List M) : f l.Prod = (l.map f).Prod :=
  map_list_prod f l
#align monoid_hom.map_list_prod MonoidHom.map_list_prod
#align add_monoid_hom.map_list_sum AddMonoidHom.map_list_sum

end MonoidHom

end MonoidHom

