/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies

! This file was ported from Lean 3 source module order.disjointed
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.PartialSups

/-!
# Consecutive differences of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the way to make a sequence of elements into a sequence of disjoint elements with
the same partial sups.

For a sequence `f : ℕ → α`, this new sequence will be `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1)`.
It is actually unique, as `disjointed_unique` shows.

## Main declarations

* `disjointed f`: The sequence `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1)`, ....
* `partial_sups_disjointed`: `disjointed f` has the same partial sups as `f`.
* `disjoint_disjointed`: The elements of `disjointed f` are pairwise disjoint.
* `disjointed_unique`: `disjointed f` is the only pairwise disjoint sequence having the same partial
  sups as `f`.
* `supr_disjointed`: `disjointed f` has the same supremum as `f`. Limiting case of
  `partial_sups_disjointed`.

We also provide set notation variants of some lemmas.

## TODO

Find a useful statement of `disjointed_rec_succ`.

One could generalize `disjointed` to any locally finite bot preorder domain, in place of `ℕ`.
Related to the TODO in the module docstring of `order.partial_sups`.
-/


variable {α β : Type _}

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

#print disjointed /-
/-- If `f : ℕ → α` is a sequence of elements, then `disjointed f` is the sequence formed by
subtracting each element from the nexts. This is the unique disjoint sequence whose partial sups
are the same as the original sequence. -/
def disjointed (f : ℕ → α) : ℕ → α
  | 0 => f 0
  | n + 1 => f (n + 1) \ partialSups f n
#align disjointed disjointed
-/

#print disjointed_zero /-
@[simp]
theorem disjointed_zero (f : ℕ → α) : disjointed f 0 = f 0 :=
  rfl
#align disjointed_zero disjointed_zero
-/

/- warning: disjointed_succ -> disjointed_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (disjointed.{u1} α _inst_1 f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (coeFn.{succ u1, succ u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (fun (_x : OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) => Nat -> α) (OrderHom.hasCoeToFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) f) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (disjointed.{u1} α _inst_1 f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (OrderHom.toFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) f) n))
Case conversion may be inaccurate. Consider using '#align disjointed_succ disjointed_succₓ'. -/
theorem disjointed_succ (f : ℕ → α) (n : ℕ) : disjointed f (n + 1) = f (n + 1) \ partialSups f n :=
  rfl
#align disjointed_succ disjointed_succ

#print disjointed_le_id /-
theorem disjointed_le_id : disjointed ≤ (id : (ℕ → α) → ℕ → α) :=
  by
  rintro f n
  cases n
  · rfl
  · exact sdiff_le
#align disjointed_le_id disjointed_le_id
-/

#print disjointed_le /-
theorem disjointed_le (f : ℕ → α) : disjointed f ≤ f :=
  disjointed_le_id f
#align disjointed_le disjointed_le
-/

#print disjoint_disjointed /-
theorem disjoint_disjointed (f : ℕ → α) : Pairwise (Disjoint on disjointed f) :=
  by
  refine' (Symmetric.pairwise_on Disjoint.symm _).2 fun m n h => _
  cases n
  · exact (Nat.not_lt_zero _ h).elim
  exact
    disjoint_sdiff_self_right.mono_left
      ((disjointed_le f m).trans (le_partialSups_of_le f (Nat.lt_add_one_iff.1 h)))
#align disjoint_disjointed disjoint_disjointed
-/

/- warning: disjointed_rec -> disjointedRec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {f : Nat -> α} {p : α -> Sort.{u2}}, (forall {{t : α}} {{i : Nat}}, (p t) -> (p (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) t (f i)))) -> (forall {{n : Nat}}, (p (f n)) -> (p (disjointed.{u1} α _inst_1 f n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {f : Nat -> α} {p : α -> Sort.{u2}}, (forall {{t : α}} {{i : Nat}}, (p t) -> (p (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) t (f i)))) -> (forall {{n : Nat}}, (p (f n)) -> (p (disjointed.{u1} α _inst_1 f n)))
Case conversion may be inaccurate. Consider using '#align disjointed_rec disjointedRecₓ'. -/
/-- An induction principle for `disjointed`. To define/prove something on `disjointed f n`, it's
enough to define/prove it for `f n` and being able to extend through diffs. -/
def disjointedRec {f : ℕ → α} {p : α → Sort _} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
    ∀ ⦃n⦄, p (f n) → p (disjointed f n)
  | 0 => id
  | n + 1 => fun h => by
    suffices H : ∀ k, p (f (n + 1) \ partialSups f k)
    · exact H n
    rintro k
    induction' k with k ih
    · exact hdiff h
    rw [partialSups_succ, ← sdiff_sdiff_left]
    exact hdiff ih
#align disjointed_rec disjointedRec

/- warning: disjointed_rec_zero -> disjointedRec_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {f : Nat -> α} {p : α -> Sort.{u2}} (hdiff : forall {{t : α}} {{i : Nat}}, (p t) -> (p (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) t (f i)))) (h₀ : p (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))), Eq.{u2} (p (disjointed.{u1} α _inst_1 (fun (i : Nat) => f i) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (disjointedRec.{u1, u2} α _inst_1 (fun (i : Nat) => f i) (fun (t : α) => p t) hdiff (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) h₀) h₀
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {f : Nat -> α} {p : α -> Sort.{u2}} (hdiff : forall {{t : α}} {{i : Nat}}, (p t) -> (p (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) t (f i)))) (h₀ : p (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))), Eq.{u2} (p (disjointed.{u1} α _inst_1 (fun (i : Nat) => f i) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (disjointedRec.{u1, u2} α _inst_1 (fun (i : Nat) => f i) (fun (t : α) => p t) hdiff (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) h₀) h₀
Case conversion may be inaccurate. Consider using '#align disjointed_rec_zero disjointedRec_zeroₓ'. -/
@[simp]
theorem disjointedRec_zero {f : ℕ → α} {p : α → Sort _} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i))
    (h₀ : p (f 0)) : disjointedRec hdiff h₀ = h₀ :=
  rfl
#align disjointed_rec_zero disjointedRec_zero

/- warning: monotone.disjointed_eq -> Monotone.disjointed_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {f : Nat -> α}, (Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))))) f) -> (forall (n : Nat), Eq.{succ u1} α (disjointed.{u1} α _inst_1 f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (f n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {f : Nat -> α}, (Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))))) f) -> (forall (n : Nat), Eq.{succ u1} α (disjointed.{u1} α _inst_1 f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f n)))
Case conversion may be inaccurate. Consider using '#align monotone.disjointed_eq Monotone.disjointed_eqₓ'. -/
-- TODO: Find a useful statement of `disjointed_rec_succ`.
theorem Monotone.disjointed_eq {f : ℕ → α} (hf : Monotone f) (n : ℕ) :
    disjointed f (n + 1) = f (n + 1) \ f n := by rw [disjointed_succ, hf.partial_sups_eq]
#align monotone.disjointed_eq Monotone.disjointed_eq

#print partialSups_disjointed /-
@[simp]
theorem partialSups_disjointed (f : ℕ → α) : partialSups (disjointed f) = partialSups f :=
  by
  ext n
  induction' n with k ih
  · rw [partialSups_zero, partialSups_zero, disjointed_zero]
  · rw [partialSups_succ, partialSups_succ, disjointed_succ, ih, sup_sdiff_self_right]
#align partial_sups_disjointed partialSups_disjointed
-/

#print disjointed_unique /-
/-- `disjointed f` is the unique sequence that is pairwise disjoint and has the same partial sups
as `f`. -/
theorem disjointed_unique {f d : ℕ → α} (hdisj : Pairwise (Disjoint on d))
    (hsups : partialSups d = partialSups f) : d = disjointed f :=
  by
  ext n
  cases n
  · rw [← partialSups_zero d, hsups, partialSups_zero, disjointed_zero]
  suffices h : d n.succ = partialSups d n.succ \ partialSups d n
  · rw [h, hsups, partialSups_succ, disjointed_succ, sup_sdiff, sdiff_self, bot_sup_eq]
  rw [partialSups_succ, sup_sdiff, sdiff_self, bot_sup_eq, eq_comm, sdiff_eq_self_iff_disjoint]
  suffices h : ∀ m ≤ n, Disjoint (partialSups d m) (d n.succ)
  · exact h n le_rfl
  rintro m hm
  induction' m with m ih
  · exact hdisj (Nat.succ_ne_zero _).symm
  rw [partialSups_succ, disjoint_iff, inf_sup_right, sup_eq_bot_iff, ← disjoint_iff, ← disjoint_iff]
  exact ⟨ih (Nat.le_of_succ_le hm), hdisj (Nat.lt_succ_of_le hm).Ne⟩
#align disjointed_unique disjointed_unique
-/

end GeneralizedBooleanAlgebra

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α]

/- warning: supr_disjointed -> supᵢ_disjointed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Nat -> α), Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) Nat (fun (n : Nat) => disjointed.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) f n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) Nat (fun (n : Nat) => f n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Nat -> α), Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) Nat (fun (n : Nat) => disjointed.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) f n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) Nat (fun (n : Nat) => f n))
Case conversion may be inaccurate. Consider using '#align supr_disjointed supᵢ_disjointedₓ'. -/
theorem supᵢ_disjointed (f : ℕ → α) : (⨆ n, disjointed f n) = ⨆ n, f n :=
  supᵢ_eq_supᵢ_of_partialSups_eq_partialSups (partialSups_disjointed f)
#align supr_disjointed supᵢ_disjointed

/- warning: disjointed_eq_inf_compl -> disjointed_eq_inf_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (disjointed.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) f n) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))))) (f n) (infᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (LT.lt.{0} Nat Nat.hasLt i n) (fun (H : LT.lt.{0} Nat Nat.hasLt i n) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (disjointed.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) f n) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))))) (f n) (infᵢ.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (LT.lt.{0} Nat instLTNat i n) (fun (H : LT.lt.{0} Nat instLTNat i n) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))))
Case conversion may be inaccurate. Consider using '#align disjointed_eq_inf_compl disjointed_eq_inf_complₓ'. -/
theorem disjointed_eq_inf_compl (f : ℕ → α) (n : ℕ) : disjointed f n = f n ⊓ ⨅ i < n, f iᶜ :=
  by
  cases n
  · rw [disjointed_zero, eq_comm, inf_eq_left]
    simp_rw [le_infᵢ_iff]
    exact fun i hi => (i.not_lt_zero hi).elim
  simp_rw [disjointed_succ, partialSups_eq_bsupᵢ, sdiff_eq, compl_supᵢ]
  congr
  ext i
  rw [Nat.lt_succ_iff]
#align disjointed_eq_inf_compl disjointed_eq_inf_compl

end CompleteBooleanAlgebra

/-! ### Set notation variants of lemmas -/


/- warning: disjointed_subset -> disjointed_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Nat -> (Set.{u1} α)) (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) f n) (f n)
but is expected to have type
  forall {α : Type.{u1}} (f : Nat -> (Set.{u1} α)) (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) f n) (f n)
Case conversion may be inaccurate. Consider using '#align disjointed_subset disjointed_subsetₓ'. -/
theorem disjointed_subset (f : ℕ → Set α) (n : ℕ) : disjointed f n ⊆ f n :=
  disjointed_le f n
#align disjointed_subset disjointed_subset

/- warning: Union_disjointed -> unionᵢ_disjointed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Nat -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, 1} α Nat (fun (n : Nat) => disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) f n)) (Set.unionᵢ.{u1, 1} α Nat (fun (n : Nat) => f n))
but is expected to have type
  forall {α : Type.{u1}} {f : Nat -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, 1} α Nat (fun (n : Nat) => disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) f n)) (Set.unionᵢ.{u1, 1} α Nat (fun (n : Nat) => f n))
Case conversion may be inaccurate. Consider using '#align Union_disjointed unionᵢ_disjointedₓ'. -/
theorem unionᵢ_disjointed {f : ℕ → Set α} : (⋃ n, disjointed f n) = ⋃ n, f n :=
  supᵢ_disjointed f
#align Union_disjointed unionᵢ_disjointed

/- warning: disjointed_eq_inter_compl -> disjointed_eq_inter_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) f n) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (f n) (Set.interᵢ.{u1, 1} α Nat (fun (i : Nat) => Set.interᵢ.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt i n) (fun (H : LT.lt.{0} Nat Nat.hasLt i n) => HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (f i)))))
but is expected to have type
  forall {α : Type.{u1}} (f : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) f n) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (f n) (Set.interᵢ.{u1, 1} α Nat (fun (i : Nat) => Set.interᵢ.{u1, 0} α (LT.lt.{0} Nat instLTNat i n) (fun (H : LT.lt.{0} Nat instLTNat i n) => HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (f i)))))
Case conversion may be inaccurate. Consider using '#align disjointed_eq_inter_compl disjointed_eq_inter_complₓ'. -/
theorem disjointed_eq_inter_compl (f : ℕ → Set α) (n : ℕ) : disjointed f n = f n ∩ ⋂ i < n, f iᶜ :=
  disjointed_eq_inf_compl f n
#align disjointed_eq_inter_compl disjointed_eq_inter_compl

/- warning: preimage_find_eq_disjointed -> preimage_find_eq_disjointed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Nat -> (Set.{u1} α)) (H : forall (x : α), Exists.{1} Nat (fun (n : Nat) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s n))) [_inst_1 : forall (x : α) (n : Nat), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s n))] (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Nat (fun (x : α) => Nat.find (fun (n : Nat) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s n)) (fun (a : Nat) => _inst_1 x a) (H x)) (Singleton.singleton.{0, 0} Nat (Set.{0} Nat) (Set.hasSingleton.{0} Nat) n)) (disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s n)
but is expected to have type
  forall {α : Type.{u1}} (s : Nat -> (Set.{u1} α)) (H : forall (x : α), Exists.{1} Nat (fun (n : Nat) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (s n))) [_inst_1 : forall (x : α) (n : Nat), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (s n))] (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Nat (fun (x : α) => Nat.find (fun (n : Nat) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (s n)) (fun (a : Nat) => _inst_1 x a) (H x)) (Singleton.singleton.{0, 0} Nat (Set.{0} Nat) (Set.instSingletonSet.{0} Nat) n)) (disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s n)
Case conversion may be inaccurate. Consider using '#align preimage_find_eq_disjointed preimage_find_eq_disjointedₓ'. -/
theorem preimage_find_eq_disjointed (s : ℕ → Set α) (H : ∀ x, ∃ n, x ∈ s n)
    [∀ x n, Decidable (x ∈ s n)] (n : ℕ) : (fun x => Nat.find (H x)) ⁻¹' {n} = disjointed s n :=
  by
  ext x
  simp [Nat.find_eq_iff, disjointed_eq_inter_compl]
#align preimage_find_eq_disjointed preimage_find_eq_disjointed

