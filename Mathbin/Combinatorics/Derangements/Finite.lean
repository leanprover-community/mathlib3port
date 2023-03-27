/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson

! This file was ported from Lean 3 source module combinatorics.derangements.finite
! leanprover-community/mathlib commit c3019c79074b0619edb4b27553a91b2e82242395
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Derangements.Basic
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Tactic.DeltaInstance
import Mathbin.Tactic.Ring

/-!
# Derangements on fintypes

This file contains lemmas that describe the cardinality of `derangements α` when `α` is a fintype.

# Main definitions

* `card_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.
* `num_derangements n`: The number of derangements on an n-element set, defined in a computation-
    friendly way.
* `card_derangements_eq_num_derangements`: Proof that `num_derangements` really does compute the
    number of derangements.
* `num_derangements_sum`: A lemma giving an expression for `num_derangements n` in terms of
    factorials.
-/


open derangements Equiv Fintype

open BigOperators

variable {α : Type _} [DecidableEq α] [Fintype α]

instance : DecidablePred (derangements α) := fun _ => Fintype.decidableForallFintype

instance : Fintype (derangements α) := by delta_instance derangements

/- warning: card_derangements_invariant -> card_derangements_invariant is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Fintype.{u1} α] [_inst_4 : DecidableEq.{succ u1} α] [_inst_5 : Fintype.{u2} β] [_inst_6 : DecidableEq.{succ u2} β], (Eq.{1} Nat (Fintype.card.{u1} α _inst_3) (Fintype.card.{u2} β _inst_5)) -> (Eq.{1} Nat (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Equiv.Perm.{succ u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Equiv.Perm.{succ u1} α)) (derangements.{u1} α)) (derangements.fintype.{u1} α (fun (a : α) (b : α) => _inst_4 a b) _inst_3)) (Fintype.card.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} (Equiv.Perm.{succ u2} β)) Type.{u2} (Set.hasCoeToSort.{u2} (Equiv.Perm.{succ u2} β)) (derangements.{u2} β)) (derangements.fintype.{u2} β (fun (a : β) (b : β) => _inst_6 a b) _inst_5)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Fintype.{u2} α] [_inst_4 : DecidableEq.{succ u2} α] [_inst_5 : Fintype.{u1} β] [_inst_6 : DecidableEq.{succ u1} β], (Eq.{1} Nat (Fintype.card.{u2} α _inst_3) (Fintype.card.{u1} β _inst_5)) -> (Eq.{1} Nat (Fintype.card.{u2} (Set.Elem.{u2} (Equiv.Perm.{succ u2} α) (derangements.{u2} α)) (instFintypeElemPermDerangements.{u2} α (fun (a : α) (b : α) => _inst_4 a b) _inst_3)) (Fintype.card.{u1} (Set.Elem.{u1} (Equiv.Perm.{succ u1} β) (derangements.{u1} β)) (instFintypeElemPermDerangements.{u1} β (fun (a : β) (b : β) => _inst_6 a b) _inst_5)))
Case conversion may be inaccurate. Consider using '#align card_derangements_invariant card_derangements_invariantₓ'. -/
theorem card_derangements_invariant {α β : Type _} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (h : card α = card β) : card (derangements α) = card (derangements β) :=
  Fintype.card_congr (Equiv.derangementsCongr <| equivOfCardEq h)
#align card_derangements_invariant card_derangements_invariant

/- warning: card_derangements_fin_add_two -> card_derangements_fin_add_two is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Equiv.Perm.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))) Type (Set.hasCoeToSort.{0} (Equiv.Perm.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))) (derangements.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))) (derangements.fintype.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) a b) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Equiv.Perm.{1} (Fin n))) Type (Set.hasCoeToSort.{0} (Equiv.Perm.{1} (Fin n))) (derangements.{0} (Fin n))) (derangements.fintype.{0} (Fin n) (fun (a : Fin n) (b : Fin n) => Fin.decidableEq n a b) (Fin.fintype n)))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Equiv.Perm.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) Type (Set.hasCoeToSort.{0} (Equiv.Perm.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (derangements.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (derangements.fintype.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))))
but is expected to have type
  forall (n : Nat), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Equiv.Perm.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (derangements.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (instFintypeElemPermDerangements.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) a b) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fintype.card.{0} (Set.Elem.{0} (Equiv.Perm.{1} (Fin n)) (derangements.{0} (Fin n))) (instFintypeElemPermDerangements.{0} (Fin n) (fun (a : Fin n) (b : Fin n) => instDecidableEqFin n a b) (Fin.fintype n)))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fintype.card.{0} (Set.Elem.{0} (Equiv.Perm.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (derangements.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (instFintypeElemPermDerangements.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))))
Case conversion may be inaccurate. Consider using '#align card_derangements_fin_add_two card_derangements_fin_add_twoₓ'. -/
theorem card_derangements_fin_add_two (n : ℕ) :
    card (derangements (Fin (n + 2))) =
      (n + 1) * card (derangements (Fin n)) + (n + 1) * card (derangements (Fin (n + 1))) :=
  by
  -- get some basic results about the size of fin (n+1) plus or minus an element
  have h1 : ∀ a : Fin (n + 1), card ({a}ᶜ : Set (Fin (n + 1))) = card (Fin n) :=
    by
    intro a
    simp only [Fintype.card_fin, Finset.card_fin, Fintype.card_ofFinset, Finset.filter_ne' _ a,
      Set.mem_compl_singleton_iff, Finset.card_erase_of_mem (Finset.mem_univ a),
      add_tsub_cancel_right]
  have h2 : card (Fin (n + 2)) = card (Option (Fin (n + 1))) := by simp only [card_fin, card_option]
  -- rewrite the LHS and substitute in our fintype-level equivalence
  simp only [card_derangements_invariant h2,
    card_congr
      (@derangements_recursion_equiv (Fin (n + 1))
        _),-- push the cardinality through the Σ and ⊕ so that we can use `card_n`
    card_sigma,
    card_sum, card_derangements_invariant (h1 _), Finset.sum_const, nsmul_eq_mul, Finset.card_fin,
    mul_add, Nat.cast_id]
#align card_derangements_fin_add_two card_derangements_fin_add_two

#print numDerangements /-
/-- The number of derangements of an `n`-element set. -/
def numDerangements : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (numDerangements n + numDerangements (n + 1))
#align num_derangements numDerangements
-/

#print numDerangements_zero /-
@[simp]
theorem numDerangements_zero : numDerangements 0 = 1 :=
  rfl
#align num_derangements_zero numDerangements_zero
-/

#print numDerangements_one /-
@[simp]
theorem numDerangements_one : numDerangements 1 = 0 :=
  rfl
#align num_derangements_one numDerangements_one
-/

#print numDerangements_add_two /-
theorem numDerangements_add_two (n : ℕ) :
    numDerangements (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1)) :=
  rfl
#align num_derangements_add_two numDerangements_add_two
-/

/- warning: num_derangements_succ -> numDerangements_succ is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (numDerangements (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (numDerangements n))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) n))
but is expected to have type
  forall (n : Nat), Eq.{1} Int (Nat.cast.{0} Int instNatCastInt (numDerangements (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (Nat.cast.{0} Int instNatCastInt n) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (Nat.cast.{0} Int instNatCastInt (numDerangements n))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) n))
Case conversion may be inaccurate. Consider using '#align num_derangements_succ numDerangements_succₓ'. -/
theorem numDerangements_succ (n : ℕ) :
    (numDerangements (n + 1) : ℤ) = (n + 1) * (numDerangements n : ℤ) - (-1) ^ n :=
  by
  induction' n with n hn
  · rfl
  · simp only [numDerangements_add_two, hn, pow_succ, Int.ofNat_mul, Int.ofNat_add, Int.ofNat_succ]
    ring
#align num_derangements_succ numDerangements_succ

/- warning: card_derangements_fin_eq_num_derangements -> card_derangements_fin_eq_numDerangements is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Equiv.Perm.{1} (Fin n))) Type (Set.hasCoeToSort.{0} (Equiv.Perm.{1} (Fin n))) (derangements.{0} (Fin n))) (derangements.fintype.{0} (Fin n) (fun (a : Fin n) (b : Fin n) => Fin.decidableEq n a b) (Fin.fintype n))) (numDerangements n)
but is expected to have type
  forall {n : Nat}, Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Equiv.Perm.{1} (Fin n)) (derangements.{0} (Fin n))) (instFintypeElemPermDerangements.{0} (Fin n) (fun (a : Fin n) (b : Fin n) => instDecidableEqFin n a b) (Fin.fintype n))) (numDerangements n)
Case conversion may be inaccurate. Consider using '#align card_derangements_fin_eq_num_derangements card_derangements_fin_eq_numDerangementsₓ'. -/
theorem card_derangements_fin_eq_numDerangements {n : ℕ} :
    card (derangements (Fin n)) = numDerangements n :=
  by
  induction' n using Nat.strong_induction_on with n hyp
  obtain _ | _ | n := n; · rfl; · rfl
  -- knock out cases 0 and 1
  -- now we have n ≥ 2. rewrite everything in terms of card_derangements, so that we can use
  -- `card_derangements_fin_add_two`
  rw [numDerangements_add_two, card_derangements_fin_add_two, mul_add,
    hyp _ (Nat.lt_add_of_pos_right zero_lt_two), hyp _ (lt_add_one _)]
#align card_derangements_fin_eq_num_derangements card_derangements_fin_eq_numDerangements

/- warning: card_derangements_eq_num_derangements -> card_derangements_eq_numDerangements is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_3 : Fintype.{u1} α] [_inst_4 : DecidableEq.{succ u1} α], Eq.{1} Nat (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Equiv.Perm.{succ u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Equiv.Perm.{succ u1} α)) (derangements.{u1} α)) (derangements.fintype.{u1} α (fun (a : α) (b : α) => _inst_4 a b) _inst_3)) (numDerangements (Fintype.card.{u1} α _inst_3))
but is expected to have type
  forall (α : Type.{u1}) [_inst_3 : Fintype.{u1} α] [_inst_4 : DecidableEq.{succ u1} α], Eq.{1} Nat (Fintype.card.{u1} (Set.Elem.{u1} (Equiv.Perm.{succ u1} α) (derangements.{u1} α)) (instFintypeElemPermDerangements.{u1} α (fun (a : α) (b : α) => _inst_4 a b) _inst_3)) (numDerangements (Fintype.card.{u1} α _inst_3))
Case conversion may be inaccurate. Consider using '#align card_derangements_eq_num_derangements card_derangements_eq_numDerangementsₓ'. -/
theorem card_derangements_eq_numDerangements (α : Type _) [Fintype α] [DecidableEq α] :
    card (derangements α) = numDerangements (card α) :=
  by
  rw [← card_derangements_invariant (card_fin _)]
  exact card_derangements_fin_eq_numDerangements
#align card_derangements_eq_num_derangements card_derangements_eq_numDerangements

/- warning: num_derangements_sum -> numDerangements_sum is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (numDerangements n)) (Finset.sum.{0, 0} Int Nat Int.addCommMonoid (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) k) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Nat.ascFactorial k (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k)))))
but is expected to have type
  forall (n : Nat), Eq.{1} Int (Nat.cast.{0} Int instNatCastInt (numDerangements n)) (Finset.sum.{0, 0} Int Nat Int.instAddCommMonoidInt (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) k) (Nat.cast.{0} Int instNatCastInt (Nat.ascFactorial k (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k)))))
Case conversion may be inaccurate. Consider using '#align num_derangements_sum numDerangements_sumₓ'. -/
theorem numDerangements_sum (n : ℕ) :
    (numDerangements n : ℤ) =
      ∑ k in Finset.range (n + 1), (-1 : ℤ) ^ k * Nat.ascFactorial k (n - k) :=
  by
  induction' n with n hn; · rfl
  rw [Finset.sum_range_succ, numDerangements_succ, hn, Finset.mul_sum, tsub_self,
    Nat.ascFactorial_zero, Int.ofNat_one, mul_one, pow_succ, neg_one_mul, sub_eq_add_neg,
    add_left_inj, Finset.sum_congr rfl]
  -- show that (n + 1) * (-1)^x * asc_fac x (n - x) = (-1)^x * asc_fac x (n.succ - x)
  intro x hx
  have h_le : x ≤ n := finset.mem_range_succ_iff.mp hx
  rw [Nat.succ_sub h_le, Nat.ascFactorial_succ, add_tsub_cancel_of_le h_le, Int.ofNat_mul,
    Int.ofNat_succ, mul_left_comm]
#align num_derangements_sum numDerangements_sum

