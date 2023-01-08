/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Floris van Doorn

! This file was ported from Lean 3 source module data.pnat.find
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pnat.Basic

/-!
# Explicit least witnesses to existentials on positive natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Implemented via calling out to `nat.find`.

-/


namespace PNat

variable {p q : ℕ+ → Prop} [DecidablePred p] [DecidablePred q] (h : ∃ n, p n)

#print PNat.decidablePredExistsNat /-
instance decidablePredExistsNat : DecidablePred fun n' : ℕ => ∃ (n : ℕ+)(hn : n' = n), p n :=
  fun n' =>
  decidable_of_iff' (∃ h : 0 < n', p ⟨n', h⟩) <|
    Subtype.exists.trans <| by
      simp_rw [Subtype.coe_mk, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']
#align pnat.decidable_pred_exists_nat PNat.decidablePredExistsNat
-/

include h

/- warning: pnat.find_x -> PNat.findX is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p], (Exists.{1} PNat (fun (n : PNat) => p n)) -> (Subtype.{1} PNat (fun (n : PNat) => And (p n) (forall (m : PNat), (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n) -> (Not (p m)))))
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p], (Exists.{1} PNat (fun (n : PNat) => p n)) -> (Subtype.{1} PNat (fun (n : PNat) => And (p n) (forall (m : PNat), (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m n) -> (Not (p m)))))
Case conversion may be inaccurate. Consider using '#align pnat.find_x PNat.findXₓ'. -/
/-- The `pnat` version of `nat.find_x` -/
protected def findX : { n // p n ∧ ∀ m : ℕ+, m < n → ¬p m } :=
  by
  have : ∃ (n' : ℕ)(n : ℕ+)(hn' : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine' ⟨⟨n, _⟩, _, fun m hm pm => _⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [hn', Subtype.coe_eta] using pn'
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩
#align pnat.find_x PNat.findX

#print PNat.find /-
/-- If `p` is a (decidable) predicate on `ℕ+` and `hp : ∃ (n : ℕ+), p n` is a proof that
there exists some positive natural number satisfying `p`, then `pnat.find hp` is the
smallest positive natural number satisfying `p`. Note that `pnat.find` is protected,
meaning that you can't just write `find`, even if the `pnat` namespace is open.

The API for `pnat.find` is:

* `pnat.find_spec` is the proof that `pnat.find hp` satisfies `p`.
* `pnat.find_min` is the proof that if `m < pnat.find hp` then `m` does not satisfy `p`.
* `pnat.find_min'` is the proof that if `m` does satisfy `p` then `pnat.find hp ≤ m`.
-/
protected def find : ℕ+ :=
  PNat.findX h
#align pnat.find PNat.find
-/

#print PNat.find_spec /-
protected theorem find_spec : p (PNat.find h) :=
  (PNat.findX h).Prop.left
#align pnat.find_spec PNat.find_spec
-/

/- warning: pnat.find_min -> PNat.find_min is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) {m : PNat}, (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h)) -> (Not (p m))
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) {m : PNat}, (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h)) -> (Not (p m))
Case conversion may be inaccurate. Consider using '#align pnat.find_min PNat.find_minₓ'. -/
protected theorem find_min : ∀ {m : ℕ+}, m < PNat.find h → ¬p m :=
  (PNat.findX h).Prop.right
#align pnat.find_min PNat.find_min

/- warning: pnat.find_min' -> PNat.find_min' is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) {m : PNat}, (p m) -> (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) m)
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) {m : PNat}, (p m) -> (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) m)
Case conversion may be inaccurate. Consider using '#align pnat.find_min' PNat.find_min'ₓ'. -/
protected theorem find_min' {m : ℕ+} (hm : p m) : PNat.find h ≤ m :=
  le_of_not_lt fun l => PNat.find_min h l hm
#align pnat.find_min' PNat.find_min'

variable {n m : ℕ+}

/- warning: pnat.find_eq_iff -> PNat.find_eq_iff is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) {m : PNat}, Iff (Eq.{1} PNat (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) m) (And (p m) (forall (n : PNat), (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) n m) -> (Not (p n))))
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) {m : PNat}, Iff (Eq.{1} PNat (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) m) (And (p m) (forall (n : PNat), (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) n m) -> (Not (p n))))
Case conversion may be inaccurate. Consider using '#align pnat.find_eq_iff PNat.find_eq_iffₓ'. -/
theorem find_eq_iff : PNat.find h = m ↔ p m ∧ ∀ n < m, ¬p n :=
  by
  constructor
  · rintro rfl
    exact ⟨PNat.find_spec h, fun _ => PNat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (PNat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| PNat.find_spec h)
#align pnat.find_eq_iff PNat.find_eq_iff

/- warning: pnat.find_lt_iff -> PNat.find_lt_iff is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (n : PNat), Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) n) (Exists.{1} PNat (fun (m : PNat) => Exists.{0} (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n) (fun (H : LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n) => p m)))
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (n : PNat), Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) n) (Exists.{1} PNat (fun (m : PNat) => And (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m n) (p m)))
Case conversion may be inaccurate. Consider using '#align pnat.find_lt_iff PNat.find_lt_iffₓ'. -/
@[simp]
theorem find_lt_iff (n : ℕ+) : PNat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 => ⟨PNat.find h, h2, PNat.find_spec h⟩, fun ⟨m, hmn, hm⟩ =>
    (PNat.find_min' h hm).trans_lt hmn⟩
#align pnat.find_lt_iff PNat.find_lt_iff

/- warning: pnat.find_le_iff -> PNat.find_le_iff is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (n : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) n) (Exists.{1} PNat (fun (m : PNat) => Exists.{0} (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n) (fun (H : LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n) => p m)))
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (n : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) n) (Exists.{1} PNat (fun (m : PNat) => And (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m n) (p m)))
Case conversion may be inaccurate. Consider using '#align pnat.find_le_iff PNat.find_le_iffₓ'. -/
@[simp]
theorem find_le_iff (n : ℕ+) : PNat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [exists_prop, ← lt_add_one_iff, find_lt_iff]
#align pnat.find_le_iff PNat.find_le_iff

/- warning: pnat.le_find_iff -> PNat.le_find_iff is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (n : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) n (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h)) (forall (m : PNat), (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n) -> (Not (p m)))
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (n : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) n (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h)) (forall (m : PNat), (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m n) -> (Not (p m)))
Case conversion may be inaccurate. Consider using '#align pnat.le_find_iff PNat.le_find_iffₓ'. -/
@[simp]
theorem le_find_iff (n : ℕ+) : n ≤ PNat.find h ↔ ∀ m < n, ¬p m := by
  simp_rw [← not_lt, find_lt_iff, not_exists]
#align pnat.le_find_iff PNat.le_find_iff

/- warning: pnat.lt_find_iff -> PNat.lt_find_iff is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (n : PNat), Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) n (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h)) (forall (m : PNat), (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n) -> (Not (p m)))
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (n : PNat), Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) n (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h)) (forall (m : PNat), (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m n) -> (Not (p m)))
Case conversion may be inaccurate. Consider using '#align pnat.lt_find_iff PNat.lt_find_iffₓ'. -/
@[simp]
theorem lt_find_iff (n : ℕ+) : n < PNat.find h ↔ ∀ m ≤ n, ¬p m := by
  simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]
#align pnat.lt_find_iff PNat.lt_find_iff

#print PNat.find_eq_one /-
@[simp]
theorem find_eq_one : PNat.find h = 1 ↔ p 1 := by simp [find_eq_iff]
#align pnat.find_eq_one PNat.find_eq_one
-/

/- warning: pnat.one_le_find -> PNat.one_le_find is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)), Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h)) (Not (p (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))))
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)), Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h)) (Not (p (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align pnat.one_le_find PNat.one_le_findₓ'. -/
@[simp]
theorem one_le_find : 1 < PNat.find h ↔ ¬p 1 :=
  not_iff_not.mp <| by simp
#align pnat.one_le_find PNat.one_le_find

/- warning: pnat.find_mono -> PNat.find_mono is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} {q : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] [_inst_2 : DecidablePred.{1} PNat q], (forall (n : PNat), (q n) -> (p n)) -> (forall {hp : Exists.{1} PNat (fun (n : PNat) => p n)} {hq : Exists.{1} PNat (fun (n : PNat) => q n)}, LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) hp) (PNat.find (fun (n : PNat) => q n) (fun (a : PNat) => _inst_2 a) hq))
but is expected to have type
  forall {p : PNat -> Prop} {q : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] [_inst_2 : DecidablePred.{1} PNat q], (forall (n : PNat), (q n) -> (p n)) -> (forall {hp : Exists.{1} PNat (fun (n : PNat) => p n)} {hq : Exists.{1} PNat (fun (n : PNat) => q n)}, LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) hp) (PNat.find (fun (n : PNat) => q n) (fun (a : PNat) => _inst_2 a) hq))
Case conversion may be inaccurate. Consider using '#align pnat.find_mono PNat.find_monoₓ'. -/
theorem find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} :
    PNat.find hp ≤ PNat.find hq :=
  PNat.find_min' _ (h _ (PNat.find_spec hq))
#align pnat.find_mono PNat.find_mono

/- warning: pnat.find_le -> PNat.find_le is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] {n : PNat} {h : Exists.{1} PNat (fun (n : PNat) => p n)}, (p n) -> (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) n)
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] {n : PNat} {h : Exists.{1} PNat (fun (n : PNat) => p n)}, (p n) -> (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) n)
Case conversion may be inaccurate. Consider using '#align pnat.find_le PNat.find_leₓ'. -/
theorem find_le {h : ∃ n, p n} (hn : p n) : PNat.find h ≤ n :=
  (PNat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩
#align pnat.find_le PNat.find_le

/- warning: pnat.find_comp_succ -> PNat.find_comp_succ is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (h₂ : Exists.{1} PNat (fun (n : PNat) => p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))))), (Not (p (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))))) -> (Eq.{1} PNat (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) (PNat.find (fun (n : PNat) => p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))))) (fun (a : PNat) => _inst_1 (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) a (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))))) h₂) (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))))
but is expected to have type
  forall {p : PNat -> Prop} [_inst_1 : DecidablePred.{1} PNat p] (h : Exists.{1} PNat (fun (n : PNat) => p n)) (h₂ : Exists.{1} PNat (fun (n : PNat) => p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))), (Not (p (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) -> (Eq.{1} PNat (PNat.find (fun (n : PNat) => p n) (fun (a : PNat) => _inst_1 a) h) (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) (PNat.find (fun (n : PNat) => p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (fun (a : PNat) => _inst_1 (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) a (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) h₂) (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align pnat.find_comp_succ PNat.find_comp_succₓ'. -/
theorem find_comp_succ (h : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h1 : ¬p 1) :
    PNat.find h = PNat.find h₂ + 1 :=
  by
  refine' (find_eq_iff _).2 ⟨PNat.find_spec h₂, fun n => PNat.recOn n _ _⟩
  · simp [h1]
  intro m IH hm
  simp only [add_lt_add_iff_right, lt_find_iff] at hm
  exact hm _ le_rfl
#align pnat.find_comp_succ PNat.find_comp_succ

end PNat

