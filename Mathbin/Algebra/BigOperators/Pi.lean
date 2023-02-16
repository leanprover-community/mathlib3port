/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

! This file was ported from Lean 3 source module algebra.big_operators.pi
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Ring.Pi

/-!
# Big operators for Pi Types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains theorems relevant to big operators in binary and arbitrary product
of monoids and groups
-/


open BigOperators

namespace Pi

/- warning: pi.list_prod_apply -> Pi.list_prod_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : forall (a : α), Monoid.{u2} (β a)] (a : α) (l : List.{max u1 u2} (forall (a : α), β a)), Eq.{succ u2} (β a) (List.prod.{max u1 u2} (forall (a : α), β a) (Pi.instMul.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => MulOneClass.toHasMul.{u2} (β i) (Monoid.toMulOneClass.{u2} (β i) (_inst_1 i)))) (Pi.instOne.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => MulOneClass.toHasOne.{u2} (β i) (Monoid.toMulOneClass.{u2} (β i) (_inst_1 i)))) l a) (List.prod.{u2} (β a) (MulOneClass.toHasMul.{u2} (β a) (Monoid.toMulOneClass.{u2} (β a) (_inst_1 a))) (MulOneClass.toHasOne.{u2} (β a) (Monoid.toMulOneClass.{u2} (β a) (_inst_1 a))) (List.map.{max u1 u2, u2} (forall (a : α), β a) (β a) (fun (f : forall (a : α), β a) => f a) l))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : forall (a : α), Monoid.{u1} (β a)] (a : α) (l : List.{max u2 u1} (forall (a : α), β a)), Eq.{succ u1} (β a) (List.prod.{max u2 u1} (forall (a : α), β a) (Pi.instMul.{u2, u1} α (fun (a : α) => β a) (fun (i : α) => MulOneClass.toMul.{u1} (β i) (Monoid.toMulOneClass.{u1} (β i) (_inst_1 i)))) (Pi.instOne.{u2, u1} α (fun (a : α) => β a) (fun (i : α) => Monoid.toOne.{u1} (β i) (_inst_1 i))) l a) (List.prod.{u1} (β a) (MulOneClass.toMul.{u1} (β a) (Monoid.toMulOneClass.{u1} (β a) (_inst_1 a))) (Monoid.toOne.{u1} (β a) (_inst_1 a)) (List.map.{max u2 u1, u1} (forall (a : α), β a) (β a) (fun (f : forall (a : α), β a) => f a) l))
Case conversion may be inaccurate. Consider using '#align pi.list_prod_apply Pi.list_prod_applyₓ'. -/
@[to_additive]
theorem list_prod_apply {α : Type _} {β : α → Type _} [∀ a, Monoid (β a)] (a : α)
    (l : List (∀ a, β a)) : l.Prod a = (l.map fun f : ∀ a, β a => f a).Prod :=
  (evalMonoidHom β a).map_list_prod _
#align pi.list_prod_apply Pi.list_prod_apply
#align pi.list_sum_apply Pi.list_sum_apply

/- warning: pi.multiset_prod_apply -> Pi.multiset_prod_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : forall (a : α), CommMonoid.{u2} (β a)] (a : α) (s : Multiset.{max u1 u2} (forall (a : α), β a)), Eq.{succ u2} (β a) (Multiset.prod.{max u1 u2} (forall (a : α), β a) (Pi.commMonoid.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (Multiset.prod.{u2} (β a) (_inst_1 a) (Multiset.map.{max u1 u2, u2} (forall (a : α), β a) (β a) (fun (f : forall (a : α), β a) => f a) s))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : forall (a : α), CommMonoid.{u1} (β a)] (a : α) (s : Multiset.{max u2 u1} (forall (a : α), β a)), Eq.{succ u1} (β a) (Multiset.prod.{max u2 u1} (forall (a : α), β a) (Pi.commMonoid.{u2, u1} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (Multiset.prod.{u1} (β a) (_inst_1 a) (Multiset.map.{max u2 u1, u1} (forall (a : α), β a) (β a) (fun (f : forall (a : α), β a) => f a) s))
Case conversion may be inaccurate. Consider using '#align pi.multiset_prod_apply Pi.multiset_prod_applyₓ'. -/
@[to_additive]
theorem multiset_prod_apply {α : Type _} {β : α → Type _} [∀ a, CommMonoid (β a)] (a : α)
    (s : Multiset (∀ a, β a)) : s.Prod a = (s.map fun f : ∀ a, β a => f a).Prod :=
  (evalMonoidHom β a).map_multiset_prod _
#align pi.multiset_prod_apply Pi.multiset_prod_apply
#align pi.multiset_sum_apply Pi.multiset_sum_apply

end Pi

/- warning: finset.prod_apply -> Finset.prod_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {γ : Type.{u3}} [_inst_1 : forall (a : α), CommMonoid.{u2} (β a)] (a : α) (s : Finset.{u3} γ) (g : γ -> (forall (a : α), β a)), Eq.{succ u2} (β a) (Finset.prod.{max u1 u2, u3} (forall (a : α), β a) γ (Pi.commMonoid.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s (fun (c : γ) => g c) a) (Finset.prod.{u2, u3} (β a) γ (_inst_1 a) s (fun (c : γ) => g c a))
but is expected to have type
  forall {α : Type.{u3}} {β : α -> Type.{u2}} {γ : Type.{u1}} [_inst_1 : forall (a : α), CommMonoid.{u2} (β a)] (a : α) (s : Finset.{u1} γ) (g : γ -> (forall (a : α), β a)), Eq.{succ u2} (β a) (Finset.prod.{max u3 u2, u1} (forall (a : α), β a) γ (Pi.commMonoid.{u3, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s (fun (c : γ) => g c) a) (Finset.prod.{u2, u1} (β a) γ (_inst_1 a) s (fun (c : γ) => g c a))
Case conversion may be inaccurate. Consider using '#align finset.prod_apply Finset.prod_applyₓ'. -/
@[simp, to_additive]
theorem Finset.prod_apply {α : Type _} {β : α → Type _} {γ} [∀ a, CommMonoid (β a)] (a : α)
    (s : Finset γ) (g : γ → ∀ a, β a) : (∏ c in s, g c) a = ∏ c in s, g c a :=
  (Pi.evalMonoidHom β a).map_prod _ _
#align finset.prod_apply Finset.prod_apply
#align finset.sum_apply Finset.sum_apply

/- warning: finset.prod_fn -> Finset.prod_fn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {γ : Type.{u3}} [_inst_1 : forall (a : α), CommMonoid.{u2} (β a)] (s : Finset.{u3} γ) (g : γ -> (forall (a : α), β a)), Eq.{succ (max u1 u2)} (forall (a : α), β a) (Finset.prod.{max u1 u2, u3} (forall (a : α), β a) γ (Pi.commMonoid.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s (fun (c : γ) => g c)) (fun (a : α) => Finset.prod.{u2, u3} (β a) γ (_inst_1 a) s (fun (c : γ) => g c a))
but is expected to have type
  forall {α : Type.{u3}} {β : α -> Type.{u2}} {γ : Type.{u1}} [_inst_1 : forall (a : α), CommMonoid.{u2} (β a)] (s : Finset.{u1} γ) (g : γ -> (forall (a : α), β a)), Eq.{max (succ u3) (succ u2)} (forall (a : α), β a) (Finset.prod.{max u3 u2, u1} (forall (a : α), β a) γ (Pi.commMonoid.{u3, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s (fun (c : γ) => g c)) (fun (a : α) => Finset.prod.{u2, u1} (β a) γ (_inst_1 a) s (fun (c : γ) => g c a))
Case conversion may be inaccurate. Consider using '#align finset.prod_fn Finset.prod_fnₓ'. -/
/-- An 'unapplied' analogue of `finset.prod_apply`. -/
@[to_additive "An 'unapplied' analogue of `finset.sum_apply`."]
theorem Finset.prod_fn {α : Type _} {β : α → Type _} {γ} [∀ a, CommMonoid (β a)] (s : Finset γ)
    (g : γ → ∀ a, β a) : (∏ c in s, g c) = fun a => ∏ c in s, g c a :=
  funext fun a => Finset.prod_apply _ _ _
#align finset.prod_fn Finset.prod_fn
#align finset.sum_fn Finset.sum_fn

/- warning: fintype.prod_apply -> Fintype.prod_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {γ : Type.{u3}} [_inst_1 : Fintype.{u3} γ] [_inst_2 : forall (a : α), CommMonoid.{u2} (β a)] (a : α) (g : γ -> (forall (a : α), β a)), Eq.{succ u2} (β a) (Finset.prod.{max u1 u2, u3} (forall (a : α), β a) γ (Pi.commMonoid.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_2 i)) (Finset.univ.{u3} γ _inst_1) (fun (c : γ) => g c) a) (Finset.prod.{u2, u3} (β a) γ (_inst_2 a) (Finset.univ.{u3} γ _inst_1) (fun (c : γ) => g c a))
but is expected to have type
  forall {α : Type.{u3}} {β : α -> Type.{u2}} {γ : Type.{u1}} [_inst_1 : Fintype.{u1} γ] [_inst_2 : forall (a : α), CommMonoid.{u2} (β a)] (a : α) (g : γ -> (forall (a : α), β a)), Eq.{succ u2} (β a) (Finset.prod.{max u3 u2, u1} (forall (a : α), β a) γ (Pi.commMonoid.{u3, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_2 i)) (Finset.univ.{u1} γ _inst_1) (fun (c : γ) => g c) a) (Finset.prod.{u2, u1} (β a) γ (_inst_2 a) (Finset.univ.{u1} γ _inst_1) (fun (c : γ) => g c a))
Case conversion may be inaccurate. Consider using '#align fintype.prod_apply Fintype.prod_applyₓ'. -/
@[simp, to_additive]
theorem Fintype.prod_apply {α : Type _} {β : α → Type _} {γ : Type _} [Fintype γ]
    [∀ a, CommMonoid (β a)] (a : α) (g : γ → ∀ a, β a) : (∏ c, g c) a = ∏ c, g c a :=
  Finset.prod_apply a Finset.univ g
#align fintype.prod_apply Fintype.prod_apply
#align fintype.sum_apply Fintype.sum_apply

/- warning: prod_mk_prod -> prod_mk_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u2} β] (s : Finset.{u3} γ) (f : γ -> α) (g : γ -> β), Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β (Finset.prod.{u1, u3} α γ _inst_1 s (fun (x : γ) => f x)) (Finset.prod.{u2, u3} β γ _inst_2 s (fun (x : γ) => g x))) (Finset.prod.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.commMonoid.{u1, u2} α β _inst_1 _inst_2) s (fun (x : γ) => Prod.mk.{u1, u2} α β (f x) (g x)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : CommMonoid.{u3} α] [_inst_2 : CommMonoid.{u2} β] (s : Finset.{u1} γ) (f : γ -> α) (g : γ -> β), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} α β) (Prod.mk.{u3, u2} α β (Finset.prod.{u3, u1} α γ _inst_1 s (fun (x : γ) => f x)) (Finset.prod.{u2, u1} β γ _inst_2 s (fun (x : γ) => g x))) (Finset.prod.{max u2 u3, u1} (Prod.{u3, u2} α β) γ (Prod.instCommMonoidProd.{u3, u2} α β _inst_1 _inst_2) s (fun (x : γ) => Prod.mk.{u3, u2} α β (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align prod_mk_prod prod_mk_prodₓ'. -/
@[to_additive prod_mk_sum]
theorem prod_mk_prod {α β γ : Type _} [CommMonoid α] [CommMonoid β] (s : Finset γ) (f : γ → α)
    (g : γ → β) : (∏ x in s, f x, ∏ x in s, g x) = ∏ x in s, (f x, g x) :=
  haveI := Classical.decEq γ
  Finset.induction_on s rfl (by simp (config := { contextual := true }) [Prod.ext_iff])
#align prod_mk_prod prod_mk_prod
#align prod_mk_sum prod_mk_sum

section Single

variable {I : Type _} [DecidableEq I] {Z : I → Type _}

variable [∀ i, AddCommMonoid (Z i)]

/- warning: finset.univ_sum_single -> Finset.univ_sum_single is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} I] {Z : I -> Type.{u2}} [_inst_2 : forall (i : I), AddCommMonoid.{u2} (Z i)] [_inst_3 : Fintype.{u1} I] (f : forall (i : I), Z i), Eq.{succ (max u1 u2)} (forall (i : I), Z i) (Finset.sum.{max u1 u2, u1} (forall (i : I), Z i) I (Pi.addCommMonoid.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => _inst_2 i)) (Finset.univ.{u1} I _inst_3) (fun (i : I) => Pi.single.{u1, u2} I (fun (i : I) => Z i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddZeroClass.toHasZero.{u2} (Z i) (AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) i (f i))) f
but is expected to have type
  forall {I : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} I] {Z : I -> Type.{u1}} [_inst_2 : forall (i : I), AddCommMonoid.{u1} (Z i)] [_inst_3 : Fintype.{u2} I] (f : forall (i : I), Z i), Eq.{max (succ u2) (succ u1)} (forall (i : I), Z i) (Finset.sum.{max u1 u2, u2} (forall (i : I), Z i) I (Pi.addCommMonoid.{u2, u1} I (fun (i : I) => Z i) (fun (i : I) => _inst_2 i)) (Finset.univ.{u2} I _inst_3) (fun (i : I) => Pi.single.{u2, u1} I (fun (i : I) => Z i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddMonoid.toZero.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))) i (f i))) f
Case conversion may be inaccurate. Consider using '#align finset.univ_sum_single Finset.univ_sum_singleₓ'. -/
-- As we only defined `single` into `add_monoid`, we only prove the `finset.sum` version here.
theorem Finset.univ_sum_single [Fintype I] (f : ∀ i, Z i) : (∑ i, Pi.single i (f i)) = f :=
  by
  ext a
  simp
#align finset.univ_sum_single Finset.univ_sum_single

/- warning: add_monoid_hom.functions_ext -> AddMonoidHom.functions_ext is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} I] {Z : I -> Type.{u2}} [_inst_2 : forall (i : I), AddCommMonoid.{u2} (Z i)] [_inst_3 : Finite.{succ u1} I] (G : Type.{u3}) [_inst_4 : AddCommMonoid.{u3} G] (g : AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) G (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} G (AddCommMonoid.toAddMonoid.{u3} G _inst_4))) (h : AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) G (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} G (AddCommMonoid.toAddMonoid.{u3} G _inst_4))), (forall (i : I) (x : Z i), Eq.{succ u3} G (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u3)} (AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) G (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} G (AddCommMonoid.toAddMonoid.{u3} G _inst_4))) (fun (_x : AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) G (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} G (AddCommMonoid.toAddMonoid.{u3} G _inst_4))) => (forall (i : I), Z i) -> G) (AddMonoidHom.hasCoeToFun.{max u1 u2, u3} (forall (i : I), Z i) G (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} G (AddCommMonoid.toAddMonoid.{u3} G _inst_4))) g (Pi.single.{u1, u2} I (fun (i : I) => Z i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddZeroClass.toHasZero.{u2} (Z i) (AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) i x)) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u3)} (AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) G (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} G (AddCommMonoid.toAddMonoid.{u3} G _inst_4))) (fun (_x : AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) G (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} G (AddCommMonoid.toAddMonoid.{u3} G _inst_4))) => (forall (i : I), Z i) -> G) (AddMonoidHom.hasCoeToFun.{max u1 u2, u3} (forall (i : I), Z i) G (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} G (AddCommMonoid.toAddMonoid.{u3} G _inst_4))) h (Pi.single.{u1, u2} I (fun (i : I) => Z i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddZeroClass.toHasZero.{u2} (Z i) (AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) i x))) -> (Eq.{max (succ u3) (succ (max u1 u2))} (AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) G (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} G (AddCommMonoid.toAddMonoid.{u3} G _inst_4))) g h)
but is expected to have type
  forall {I : Type.{u3}} [_inst_1 : DecidableEq.{succ u3} I] {Z : I -> Type.{u1}} [_inst_2 : forall (i : I), AddCommMonoid.{u1} (Z i)] [_inst_3 : Finite.{succ u3} I] (G : Type.{u2}) [_inst_4 : AddCommMonoid.{u2} G] (g : AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) (h : AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))), (forall (i : I) (x : Z i), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : forall (i : I), Z i) => G) (Pi.single.{u3, u1} I (fun (i : I) => Z i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddMonoid.toZero.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))) i x)) (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), max (succ u3) (succ u1), succ u2} (AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) (forall (i : I), Z i) (fun (_x : forall (i : I), Z i) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : forall (i : I), Z i) => G) _x) (AddHomClass.toFunLike.{max (max u3 u1) u2, max u3 u1, u2} (AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) (forall (i : I), Z i) G (AddZeroClass.toAdd.{max u3 u1} (forall (i : I), Z i) (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))))) (AddZeroClass.toAdd.{u2} G (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) (AddMonoidHomClass.toAddHomClass.{max (max u3 u1) u2, max u3 u1, u2} (AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4)) (AddMonoidHom.addMonoidHomClass.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))))) g (Pi.single.{u3, u1} I (fun (i : I) => Z i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddMonoid.toZero.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))) i x)) (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), max (succ u3) (succ u1), succ u2} (AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) (forall (i : I), Z i) (fun (_x : forall (i : I), Z i) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : forall (i : I), Z i) => G) _x) (AddHomClass.toFunLike.{max (max u3 u1) u2, max u3 u1, u2} (AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) (forall (i : I), Z i) G (AddZeroClass.toAdd.{max u3 u1} (forall (i : I), Z i) (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))))) (AddZeroClass.toAdd.{u2} G (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) (AddMonoidHomClass.toAddHomClass.{max (max u3 u1) u2, max u3 u1, u2} (AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4)) (AddMonoidHom.addMonoidHomClass.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))))) h (Pi.single.{u3, u1} I (fun (i : I) => Z i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddMonoid.toZero.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))) i x))) -> (Eq.{max (max (succ u3) (succ u1)) (succ u2)} (AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) G (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} G (AddCommMonoid.toAddMonoid.{u2} G _inst_4))) g h)
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.functions_ext AddMonoidHom.functions_extₓ'. -/
theorem AddMonoidHom.functions_ext [Finite I] (G : Type _) [AddCommMonoid G] (g h : (∀ i, Z i) →+ G)
    (H : ∀ i x, g (Pi.single i x) = h (Pi.single i x)) : g = h :=
  by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_sum_single k, g.map_sum, h.map_sum]
  simp only [H]
#align add_monoid_hom.functions_ext AddMonoidHom.functions_ext

/- warning: add_monoid_hom.functions_ext' -> AddMonoidHom.functions_ext' is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} I] {Z : I -> Type.{u2}} [_inst_2 : forall (i : I), AddCommMonoid.{u2} (Z i)] [_inst_3 : Finite.{succ u1} I] (M : Type.{u3}) [_inst_4 : AddCommMonoid.{u3} M] (g : AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) M (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (h : AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) M (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))), (forall (i : I), Eq.{max (succ u3) (succ u2)} (AddMonoidHom.{u2, u3} (Z i) M (AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i))) (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (AddMonoidHom.comp.{u2, max u1 u2, u3} (Z i) (forall (i : I), Z i) M (AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i))) (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) g (AddMonoidHom.single.{u1, u2} I Z (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i))) i)) (AddMonoidHom.comp.{u2, max u1 u2, u3} (Z i) (forall (i : I), Z i) M (AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i))) (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) h (AddMonoidHom.single.{u1, u2} I Z (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i))) i))) -> (Eq.{max (succ u3) (succ (max u1 u2))} (AddMonoidHom.{max u1 u2, u3} (forall (i : I), Z i) M (Pi.addZeroClass.{u1, u2} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u2} (Z i) (AddCommMonoid.toAddMonoid.{u2} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) g h)
but is expected to have type
  forall {I : Type.{u3}} [_inst_1 : DecidableEq.{succ u3} I] {Z : I -> Type.{u1}} [_inst_2 : forall (i : I), AddCommMonoid.{u1} (Z i)] [_inst_3 : Finite.{succ u3} I] (M : Type.{u2}) [_inst_4 : AddCommMonoid.{u2} M] (g : AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) M (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))) (h : AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) M (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))), (forall (i : I), Eq.{max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (Z i) M (AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))) (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))) (AddMonoidHom.comp.{u1, max u3 u1, u2} (Z i) (forall (i : I), Z i) M (AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))) (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) g (AddMonoidHom.single.{u3, u1} I Z (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))) i)) (AddMonoidHom.comp.{u1, max u3 u1, u2} (Z i) (forall (i : I), Z i) M (AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))) (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) h (AddMonoidHom.single.{u3, u1} I Z (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i))) i))) -> (Eq.{max (max (succ u3) (succ u1)) (succ u2)} (AddMonoidHom.{max u3 u1, u2} (forall (i : I), Z i) M (Pi.addZeroClass.{u3, u1} I (fun (i : I) => Z i) (fun (i : I) => AddMonoid.toAddZeroClass.{u1} (Z i) (AddCommMonoid.toAddMonoid.{u1} (Z i) (_inst_2 i)))) (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))) g h)
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.functions_ext' AddMonoidHom.functions_ext'ₓ'. -/
/-- This is used as the ext lemma instead of `add_monoid_hom.functions_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
theorem AddMonoidHom.functions_ext' [Finite I] (M : Type _) [AddCommMonoid M]
    (g h : (∀ i, Z i) →+ M)
    (H : ∀ i, g.comp (AddMonoidHom.single Z i) = h.comp (AddMonoidHom.single Z i)) : g = h :=
  have := fun i => AddMonoidHom.congr_fun (H i)
  -- elab without an expected type
      g.functions_ext
    M h this
#align add_monoid_hom.functions_ext' AddMonoidHom.functions_ext'

end Single

section RingHom

open Pi

variable {I : Type _} [DecidableEq I] {f : I → Type _}

variable [∀ i, NonAssocSemiring (f i)]

/- warning: ring_hom.functions_ext -> RingHom.functions_ext is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} I] {f : I -> Type.{u2}} [_inst_2 : forall (i : I), NonAssocSemiring.{u2} (f i)] [_inst_3 : Finite.{succ u1} I] (G : Type.{u3}) [_inst_4 : NonAssocSemiring.{u3} G] (g : RingHom.{max u1 u2, u3} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (h : RingHom.{max u1 u2, u3} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4), (forall (i : I) (x : f i), Eq.{succ u3} G (coeFn.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u2)) (succ u3)} (RingHom.{max u1 u2, u3} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (fun (_x : RingHom.{max u1 u2, u3} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) => (forall (i : I), f i) -> G) (RingHom.hasCoeToFun.{max u1 u2, u3} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) g (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroClass.toHasZero.{u2} (f i) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (f i) (_inst_2 i)))) i x)) (coeFn.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u2)) (succ u3)} (RingHom.{max u1 u2, u3} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (fun (_x : RingHom.{max u1 u2, u3} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) => (forall (i : I), f i) -> G) (RingHom.hasCoeToFun.{max u1 u2, u3} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) h (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroClass.toHasZero.{u2} (f i) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (f i) (_inst_2 i)))) i x))) -> (Eq.{max (succ (max u1 u2)) (succ u3)} (RingHom.{max u1 u2, u3} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) g h)
but is expected to have type
  forall {I : Type.{u3}} [_inst_1 : DecidableEq.{succ u3} I] {f : I -> Type.{u1}} [_inst_2 : forall (i : I), NonAssocSemiring.{u1} (f i)] [_inst_3 : Finite.{succ u3} I] (G : Type.{u2}) [_inst_4 : NonAssocSemiring.{u2} G] (g : RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (h : RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4), (forall (i : I) (x : f i), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : forall (i : I), f i) => G) (Pi.single.{u3, u1} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroOneClass.toZero.{u1} (f i) (NonAssocSemiring.toMulZeroOneClass.{u1} (f i) (_inst_2 i))) i x)) (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), max (succ u3) (succ u1), succ u2} (RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (forall (i : I), f i) (fun (_x : forall (i : I), f i) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : forall (i : I), f i) => G) _x) (MulHomClass.toFunLike.{max (max u3 u1) u2, max u3 u1, u2} (RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (forall (i : I), f i) G (NonUnitalNonAssocSemiring.toMul.{max u3 u1} (forall (i : I), f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (forall (i : I), f i) (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)))) (NonUnitalNonAssocSemiring.toMul.{u2} G (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} G _inst_4)) (NonUnitalRingHomClass.toMulHomClass.{max (max u3 u1) u2, max u3 u1, u2} (RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (forall (i : I), f i) G (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (forall (i : I), f i) (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} G _inst_4) (RingHomClass.toNonUnitalRingHomClass.{max (max u3 u1) u2, max u3 u1, u2} (RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4 (RingHom.instRingHomClassRingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4)))) g (Pi.single.{u3, u1} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroOneClass.toZero.{u1} (f i) (NonAssocSemiring.toMulZeroOneClass.{u1} (f i) (_inst_2 i))) i x)) (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), max (succ u3) (succ u1), succ u2} (RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (forall (i : I), f i) (fun (_x : forall (i : I), f i) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : forall (i : I), f i) => G) _x) (MulHomClass.toFunLike.{max (max u3 u1) u2, max u3 u1, u2} (RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (forall (i : I), f i) G (NonUnitalNonAssocSemiring.toMul.{max u3 u1} (forall (i : I), f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (forall (i : I), f i) (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)))) (NonUnitalNonAssocSemiring.toMul.{u2} G (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} G _inst_4)) (NonUnitalRingHomClass.toMulHomClass.{max (max u3 u1) u2, max u3 u1, u2} (RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (forall (i : I), f i) G (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (forall (i : I), f i) (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} G _inst_4) (RingHomClass.toNonUnitalRingHomClass.{max (max u3 u1) u2, max u3 u1, u2} (RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4 (RingHom.instRingHomClassRingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4)))) h (Pi.single.{u3, u1} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroOneClass.toZero.{u1} (f i) (NonAssocSemiring.toMulZeroOneClass.{u1} (f i) (_inst_2 i))) i x))) -> (Eq.{max (max (succ u3) (succ u1)) (succ u2)} (RingHom.{max u3 u1, u2} (forall (i : I), f i) G (Pi.nonAssocSemiring.{u3, u1} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) _inst_4) g h)
Case conversion may be inaccurate. Consider using '#align ring_hom.functions_ext RingHom.functions_extₓ'. -/
@[ext]
theorem RingHom.functions_ext [Finite I] (G : Type _) [NonAssocSemiring G] (g h : (∀ i, f i) →+* G)
    (H : ∀ (i : I) (x : f i), g (single i x) = h (single i x)) : g = h :=
  RingHom.coe_addMonoidHom_injective <|
    @AddMonoidHom.functions_ext I _ f _ _ G _ (g : (∀ i, f i) →+ G) h H
#align ring_hom.functions_ext RingHom.functions_ext

end RingHom

namespace Prod

variable {α β γ : Type _} [CommMonoid α] [CommMonoid β] {s : Finset γ} {f : γ → α × β}

/- warning: prod.fst_prod -> Prod.fst_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u2} β] {s : Finset.{u3} γ} {f : γ -> (Prod.{u1, u2} α β)}, Eq.{succ u1} α (Prod.fst.{u1, u2} α β (Finset.prod.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.commMonoid.{u1, u2} α β _inst_1 _inst_2) s (fun (c : γ) => f c))) (Finset.prod.{u1, u3} α γ _inst_1 s (fun (c : γ) => Prod.fst.{u1, u2} α β (f c)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : CommMonoid.{u3} α] [_inst_2 : CommMonoid.{u2} β] {s : Finset.{u1} γ} {f : γ -> (Prod.{u3, u2} α β)}, Eq.{succ u3} α (Prod.fst.{u3, u2} α β (Finset.prod.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (Prod.instCommMonoidProd.{u3, u2} α β _inst_1 _inst_2) s (fun (c : γ) => f c))) (Finset.prod.{u3, u1} α γ _inst_1 s (fun (c : γ) => Prod.fst.{u3, u2} α β (f c)))
Case conversion may be inaccurate. Consider using '#align prod.fst_prod Prod.fst_prodₓ'. -/
@[to_additive]
theorem fst_prod : (∏ c in s, f c).1 = ∏ c in s, (f c).1 :=
  (MonoidHom.fst α β).map_prod f s
#align prod.fst_prod Prod.fst_prod
#align prod.fst_sum Prod.fst_sum

/- warning: prod.snd_prod -> Prod.snd_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u2} β] {s : Finset.{u3} γ} {f : γ -> (Prod.{u1, u2} α β)}, Eq.{succ u2} β (Prod.snd.{u1, u2} α β (Finset.prod.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.commMonoid.{u1, u2} α β _inst_1 _inst_2) s (fun (c : γ) => f c))) (Finset.prod.{u2, u3} β γ _inst_2 s (fun (c : γ) => Prod.snd.{u1, u2} α β (f c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u3} β] {s : Finset.{u1} γ} {f : γ -> (Prod.{u2, u3} α β)}, Eq.{succ u3} β (Prod.snd.{u2, u3} α β (Finset.prod.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (Prod.instCommMonoidProd.{u2, u3} α β _inst_1 _inst_2) s (fun (c : γ) => f c))) (Finset.prod.{u3, u1} β γ _inst_2 s (fun (c : γ) => Prod.snd.{u2, u3} α β (f c)))
Case conversion may be inaccurate. Consider using '#align prod.snd_prod Prod.snd_prodₓ'. -/
@[to_additive]
theorem snd_prod : (∏ c in s, f c).2 = ∏ c in s, (f c).2 :=
  (MonoidHom.snd α β).map_prod f s
#align prod.snd_prod Prod.snd_prod
#align prod.snd_sum Prod.snd_sum

end Prod

