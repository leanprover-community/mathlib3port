/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.antidiagonal
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Powerset

/-!
# The antidiagonal on a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/


namespace Multiset

open List

variable {α β : Type _}

#print Multiset.antidiagonal /-
/-- The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities. -/
def antidiagonal (s : Multiset α) : Multiset (Multiset α × Multiset α) :=
  Quot.liftOn s (fun l => (revzip (powersetAux l) : Multiset (Multiset α × Multiset α)))
    fun l₁ l₂ h => Quot.sound (revzip_powersetAux_perm h)
#align multiset.antidiagonal Multiset.antidiagonal
-/

#print Multiset.antidiagonal_coe /-
theorem antidiagonal_coe (l : List α) : @antidiagonal α l = revzip (powersetAux l) :=
  rfl
#align multiset.antidiagonal_coe Multiset.antidiagonal_coe
-/

#print Multiset.antidiagonal_coe' /-
@[simp]
theorem antidiagonal_coe' (l : List α) : @antidiagonal α l = revzip (powersetAux' l) :=
  Quot.sound revzip_powersetAux_perm_aux'
#align multiset.antidiagonal_coe' Multiset.antidiagonal_coe'
-/

#print Multiset.mem_antidiagonal /-
/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp]
theorem mem_antidiagonal {s : Multiset α} {x : Multiset α × Multiset α} :
    x ∈ antidiagonal s ↔ x.1 + x.2 = s :=
  Quotient.inductionOn s fun l => by
    simp [antidiagonal_coe]; refine' ⟨fun h => revzip_powerset_aux h, fun h => _⟩
    haveI := Classical.decEq α
    simp [revzip_powerset_aux_lemma l revzip_powerset_aux, h.symm]
    cases' x with x₁ x₂
    dsimp only
    exact ⟨x₁, le_add_right _ _, by rw [add_tsub_cancel_left x₁ x₂]⟩
#align multiset.mem_antidiagonal Multiset.mem_antidiagonal
-/

#print Multiset.antidiagonal_map_fst /-
@[simp]
theorem antidiagonal_map_fst (s : Multiset α) : (antidiagonal s).map Prod.fst = powerset s :=
  Quotient.inductionOn s fun l => by simp [powerset_aux']
#align multiset.antidiagonal_map_fst Multiset.antidiagonal_map_fst
-/

#print Multiset.antidiagonal_map_snd /-
@[simp]
theorem antidiagonal_map_snd (s : Multiset α) : (antidiagonal s).map Prod.snd = powerset s :=
  Quotient.inductionOn s fun l => by simp [powerset_aux']
#align multiset.antidiagonal_map_snd Multiset.antidiagonal_map_snd
-/

#print Multiset.antidiagonal_zero /-
@[simp]
theorem antidiagonal_zero : @antidiagonal α 0 = {(0, 0)} :=
  rfl
#align multiset.antidiagonal_zero Multiset.antidiagonal_zero
-/

#print Multiset.antidiagonal_cons /-
@[simp]
theorem antidiagonal_cons (a : α) (s) :
    antidiagonal (a ::ₘ s) =
      map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a) id) (antidiagonal s) :=
  Quotient.inductionOn s fun l =>
    by
    simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powerset_aux'_cons, cons_coe,
      coe_map, antidiagonal_coe', coe_add]
    rw [← zip_map, ← zip_map, zip_append, (_ : _ ++ _ = _)]
    · congr <;> simp; · simp
#align multiset.antidiagonal_cons Multiset.antidiagonal_cons
-/

#print Multiset.antidiagonal_eq_map_powerset /-
theorem antidiagonal_eq_map_powerset [DecidableEq α] (s : Multiset α) :
    s.antidiagonal = s.powerset.map fun t => (s - t, t) :=
  by
  induction' s using Multiset.induction_on with a s hs
  · simp only [antidiagonal_zero, powerset_zero, zero_tsub, map_singleton]
  · simp_rw [antidiagonal_cons, powerset_cons, map_add, hs, map_map, Function.comp, Prod.map_mk,
      id.def, sub_cons, erase_cons_head]
    rw [add_comm]
    congr 1
    refine' Multiset.map_congr rfl fun x hx => _
    rw [cons_sub_of_le _ (mem_powerset.mp hx)]
#align multiset.antidiagonal_eq_map_powerset Multiset.antidiagonal_eq_map_powerset
-/

/- warning: multiset.card_antidiagonal -> Multiset.card_antidiagonal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.orderedCancelAddCommMonoid.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.orderedCancelAddCommMonoid.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.orderedCancelAddCommMonoid.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.antidiagonal.{u1} α s)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) => Nat) (Multiset.antidiagonal.{u1} α s)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (fun (_x : Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) (Multiset.antidiagonal.{u1} α s)) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) => Nat) (Multiset.antidiagonal.{u1} α s)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) => Nat) (Multiset.antidiagonal.{u1} α s)) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) => Nat) (Multiset.antidiagonal.{u1} α s)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instPowNat) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α))) => Nat) (Multiset.antidiagonal.{u1} α s)) 2 (instOfNatNat 2)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align multiset.card_antidiagonal Multiset.card_antidiagonalₓ'. -/
@[simp]
theorem card_antidiagonal (s : Multiset α) : card (antidiagonal s) = 2 ^ card s := by
  have := card_powerset s <;> rwa [← antidiagonal_map_fst, card_map] at this
#align multiset.card_antidiagonal Multiset.card_antidiagonal

/- warning: multiset.prod_map_add -> Multiset.prod_map_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommSemiring.{u2} β] {s : Multiset.{u1} α} {f : α -> β} {g : α -> β}, Eq.{succ u2} β (Multiset.prod.{u2} β (CommSemiring.toCommMonoid.{u2} β _inst_1) (Multiset.map.{u1, u2} α β (fun (a : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))))) (f a) (g a)) s)) (Multiset.sum.{u2} β (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))) (Multiset.map.{u1, u2} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)) β (fun (p : Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))))) (Multiset.prod.{u2} β (CommSemiring.toCommMonoid.{u2} β _inst_1) (Multiset.map.{u1, u2} α β f (Prod.fst.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) p))) (Multiset.prod.{u2} β (CommSemiring.toCommMonoid.{u2} β _inst_1) (Multiset.map.{u1, u2} α β g (Prod.snd.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) p)))) (Multiset.antidiagonal.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommSemiring.{u2} β] {s : Multiset.{u1} α} {f : α -> β} {g : α -> β}, Eq.{succ u2} β (Multiset.prod.{u2} β (CommSemiring.toCommMonoid.{u2} β _inst_1) (Multiset.map.{u1, u2} α β (fun (a : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (Distrib.toAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))))) (f a) (g a)) s)) (Multiset.sum.{u2} β (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))) (Multiset.map.{u1, u2} (Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)) β (fun (p : Prod.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α)) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1))))) (Multiset.prod.{u2} β (CommSemiring.toCommMonoid.{u2} β _inst_1) (Multiset.map.{u1, u2} α β f (Prod.fst.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) p))) (Multiset.prod.{u2} β (CommSemiring.toCommMonoid.{u2} β _inst_1) (Multiset.map.{u1, u2} α β g (Prod.snd.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) p)))) (Multiset.antidiagonal.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_add Multiset.prod_map_addₓ'. -/
theorem prod_map_add [CommSemiring β] {s : Multiset α} {f g : α → β} :
    prod (s.map fun a => f a + g a) =
      sum ((antidiagonal s).map fun p => (p.1.map f).Prod * (p.2.map g).Prod) :=
  by
  refine' s.induction_on _ _
  · simp
  · intro a s ih
    have := @sum_map_mul_left α β _
    simp [ih, add_mul, mul_comm, mul_left_comm (f a), mul_left_comm (g a), mul_assoc,
      sum_map_mul_left.symm]
    cc
#align multiset.prod_map_add Multiset.prod_map_add

end Multiset

