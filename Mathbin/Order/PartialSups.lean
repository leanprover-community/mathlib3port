/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module order.partial_sups
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Lattice
import Mathbin.Order.Hom.Basic
import Mathbin.Order.ConditionallyCompleteLattice.Finset

/-!
# The monotone sequence of partial supremums of a sequence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `partial_sups : (ℕ → α) → ℕ →o α` inductively. For `f : ℕ → α`, `partial_sups f` is
the sequence `f 0 `, `f 0 ⊔ f 1`, `f 0 ⊔ f 1 ⊔ f 2`, ... The point of this definition is that
* it doesn't need a `⨆`, as opposed to `⨆ (i ≤ n), f i` (which also means the wrong thing on
  `conditionally_complete_lattice`s).
* it doesn't need a `⊥`, as opposed to `(finset.range (n + 1)).sup f`.
* it avoids needing to prove that `finset.range (n + 1)` is nonempty to use `finset.sup'`.

Equivalence with those definitions is shown by `partial_sups_eq_bsupr`, `partial_sups_eq_sup_range`,
`partial_sups_eq_sup'_range` and respectively.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because :
* Starting at `⊥` requires... having a bottom element.
* `λ f n, (finset.range n).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partial_sups.gi`.

## TODO

One could generalize `partial_sups` to any locally finite bot preorder domain, in place of `ℕ`.
Necessary for the TODO in the module docstring of `order.disjointed`.
-/


variable {α : Type _}

section SemilatticeSup

variable [SemilatticeSup α]

#print partialSups /-
/-- The monotone sequence whose value at `n` is the supremum of the `f m` where `m ≤ n`. -/
def partialSups (f : ℕ → α) : ℕ →o α :=
  ⟨@Nat.rec (fun _ => α) (f 0) fun (n : ℕ) (a : α) => a ⊔ f (n + 1),
    monotone_nat_of_le_succ fun n => le_sup_left⟩
#align partial_sups partialSups
-/

#print partialSups_zero /-
@[simp]
theorem partialSups_zero (f : ℕ → α) : partialSups f 0 = f 0 :=
  rfl
#align partial_sups_zero partialSups_zero
-/

#print partialSups_succ /-
@[simp]
theorem partialSups_succ (f : ℕ → α) (n : ℕ) :
    partialSups f (n + 1) = partialSups f n ⊔ f (n + 1) :=
  rfl
#align partial_sups_succ partialSups_succ
-/

#print le_partialSups_of_le /-
theorem le_partialSups_of_le (f : ℕ → α) {m n : ℕ} (h : m ≤ n) : f m ≤ partialSups f n :=
  by
  induction' n with n ih
  · cases h
    exact le_rfl
  · cases' h with h h
    · exact le_sup_right
    · exact (ih h).trans le_sup_left
#align le_partial_sups_of_le le_partialSups_of_le
-/

#print le_partialSups /-
theorem le_partialSups (f : ℕ → α) : f ≤ partialSups f := fun n => le_partialSups_of_le f le_rfl
#align le_partial_sups le_partialSups
-/

#print partialSups_le /-
theorem partialSups_le (f : ℕ → α) (n : ℕ) (a : α) (w : ∀ m, m ≤ n → f m ≤ a) :
    partialSups f n ≤ a := by
  induction' n with n ih
  · apply w 0 le_rfl
  · exact sup_le (ih fun m p => w m (Nat.le_succ_of_le p)) (w (n + 1) le_rfl)
#align partial_sups_le partialSups_le
-/

#print bddAbove_range_partialSups /-
@[simp]
theorem bddAbove_range_partialSups {f : ℕ → α} :
    BddAbove (Set.range (partialSups f)) ↔ BddAbove (Set.range f) :=
  by
  apply exists_congr fun a => _
  constructor
  · rintro h b ⟨i, rfl⟩
    exact (le_partialSups _ _).trans (h (Set.mem_range_self i))
  · rintro h b ⟨i, rfl⟩
    exact partialSups_le _ _ _ fun _ _ => h (Set.mem_range_self _)
#align bdd_above_range_partial_sups bddAbove_range_partialSups
-/

#print Monotone.partialSups_eq /-
theorem Monotone.partialSups_eq {f : ℕ → α} (hf : Monotone f) : (partialSups f : ℕ → α) = f :=
  by
  ext n
  induction' n with n ih
  · rfl
  · rw [partialSups_succ, ih, sup_eq_right.2 (hf (Nat.le_succ _))]
#align monotone.partial_sups_eq Monotone.partialSups_eq
-/

#print partialSups_mono /-
theorem partialSups_mono : Monotone (partialSups : (ℕ → α) → ℕ →o α) :=
  by
  rintro f g h n
  induction' n with n ih
  · exact h 0
  · exact sup_le_sup ih (h _)
#align partial_sups_mono partialSups_mono
-/

#print partialSups.gi /-
/-- `partial_sups` forms a Galois insertion with the coercion from monotone functions to functions.
-/
def partialSups.gi : GaloisInsertion (partialSups : (ℕ → α) → ℕ →o α) coeFn
    where
  choice f h :=
    ⟨f, by
      convert (partialSups f).Monotone
      exact (le_partialSups f).antisymm h⟩
  gc f g := by
    refine' ⟨(le_partialSups f).trans, fun h => _⟩
    convert partialSups_mono h
    exact OrderHom.ext _ _ g.monotone.partial_sups_eq.symm
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHom.ext _ _ ((le_partialSups f).antisymm h)
#align partial_sups.gi partialSups.gi
-/

#print partialSups_eq_sup'_range /-
theorem partialSups_eq_sup'_range (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup' ⟨n, Finset.self_mem_range_succ n⟩ f :=
  by
  induction' n with n ih
  · simp
  · dsimp [partialSups] at ih⊢
    simp_rw [@Finset.range_succ n.succ]
    rw [ih, Finset.sup'_insert, sup_comm]
#align partial_sups_eq_sup'_range partialSups_eq_sup'_range
-/

end SemilatticeSup

#print partialSups_eq_sup_range /-
theorem partialSups_eq_sup_range [SemilatticeSup α] [OrderBot α] (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup f :=
  by
  induction' n with n ih
  · simp
  · dsimp [partialSups] at ih⊢
    rw [Finset.range_succ, Finset.sup_insert, sup_comm, ih]
#align partial_sups_eq_sup_range partialSups_eq_sup_range
-/

#print partialSups_disjoint_of_disjoint /-
/- Note this lemma requires a distributive lattice, so is not useful (or true) in situations such as
submodules. -/
theorem partialSups_disjoint_of_disjoint [DistribLattice α] [OrderBot α] (f : ℕ → α)
    (h : Pairwise (Disjoint on f)) {m n : ℕ} (hmn : m < n) : Disjoint (partialSups f m) (f n) :=
  by
  induction' m with m ih
  · exact h hmn.ne
  · rw [partialSups_succ, disjoint_sup_left]
    exact ⟨ih (Nat.lt_of_succ_lt hmn), h hmn.ne⟩
#align partial_sups_disjoint_of_disjoint partialSups_disjoint_of_disjoint
-/

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

/- warning: partial_sups_eq_csupr_Iic -> partialSups_eq_csupᵢ_Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (fun (_x : OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) => Nat -> α) (OrderHom.hasCoeToFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) f) n) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) n)) (fun (i : coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) n)) => f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) n)) Nat (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) n)) Nat (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) n)) Nat (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) n)) Nat (coeSubtype.{1} Nat (fun (x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) x (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) n)))))) i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (OrderHom.toFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) f) n) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{0} Nat (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) n)) (fun (i : Set.Elem.{0} Nat (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) n)) => f (Subtype.val.{1} Nat (fun (x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) x (Set.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) n)) i)))
Case conversion may be inaccurate. Consider using '#align partial_sups_eq_csupr_Iic partialSups_eq_csupᵢ_Iicₓ'. -/
theorem partialSups_eq_csupᵢ_Iic (f : ℕ → α) (n : ℕ) : partialSups f n = ⨆ i : Set.Iic n, f i :=
  by
  have : Set.Iio (n + 1) = Set.Iic n := Set.ext fun _ => Nat.lt_succ_iff
  rw [partialSups_eq_sup'_range, Finset.sup'_eq_csupₛ_image, Finset.coe_range, supᵢ, Set.range_comp,
    Subtype.range_coe, this]
#align partial_sups_eq_csupr_Iic partialSups_eq_csupᵢ_Iic

/- warning: csupr_partial_sups_eq -> csupᵢ_partialSups_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : Nat -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, 1} α Nat f)) -> (Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) Nat (fun (n : Nat) => coeFn.{succ u1, succ u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (fun (_x : OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) => Nat -> α) (OrderHom.hasCoeToFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) f) n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) Nat (fun (n : Nat) => f n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : Nat -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, 1} α Nat f)) -> (Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => OrderHom.toFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) f) n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align csupr_partial_sups_eq csupᵢ_partialSups_eqₓ'. -/
@[simp]
theorem csupᵢ_partialSups_eq {f : ℕ → α} (h : BddAbove (Set.range f)) :
    (⨆ n, partialSups f n) = ⨆ n, f n :=
  by
  refine' (csupᵢ_le fun n => _).antisymm (csupᵢ_mono _ <| le_partialSups f)
  · rw [partialSups_eq_csupᵢ_Iic]
    exact csupᵢ_le fun i => le_csupᵢ h _
  · rwa [bddAbove_range_partialSups]
#align csupr_partial_sups_eq csupᵢ_partialSups_eq

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

/- warning: partial_sups_eq_bsupr -> partialSups_eq_bsupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (fun (_x : OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) => Nat -> α) (OrderHom.hasCoeToFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) f) n) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LE.le.{0} Nat Nat.hasLe i n) (fun (H : LE.le.{0} Nat Nat.hasLe i n) => f i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (OrderHom.toFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) f) n) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LE.le.{0} Nat instLENat i n) (fun (H : LE.le.{0} Nat instLENat i n) => f i)))
Case conversion may be inaccurate. Consider using '#align partial_sups_eq_bsupr partialSups_eq_bsupᵢₓ'. -/
theorem partialSups_eq_bsupᵢ (f : ℕ → α) (n : ℕ) : partialSups f n = ⨆ i ≤ n, f i := by
  simpa only [supᵢ_subtype] using partialSups_eq_csupᵢ_Iic f n
#align partial_sups_eq_bsupr partialSups_eq_bsupᵢ

/- warning: supr_partial_sups_eq -> supᵢ_partialSups_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => coeFn.{succ u1, succ u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (fun (_x : OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) => Nat -> α) (OrderHom.hasCoeToFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) f) n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => f n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => OrderHom.toFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) f) n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => f n))
Case conversion may be inaccurate. Consider using '#align supr_partial_sups_eq supᵢ_partialSups_eqₓ'. -/
@[simp]
theorem supᵢ_partialSups_eq (f : ℕ → α) : (⨆ n, partialSups f n) = ⨆ n, f n :=
  csupᵢ_partialSups_eq <| OrderTop.bddAbove _
#align supr_partial_sups_eq supᵢ_partialSups_eq

/- warning: supr_le_supr_of_partial_sups_le_partial_sups -> supᵢ_le_supᵢ_of_partialSups_le_partialSups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α} {g : Nat -> α}, (LE.le.{u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (Preorder.toLE.{u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (OrderHom.preorder.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) f) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) g)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => f n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => g n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α} {g : Nat -> α}, (LE.le.{u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (Preorder.toLE.{u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (OrderHom.instPreorderOrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) f) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) g)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => f n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => g n)))
Case conversion may be inaccurate. Consider using '#align supr_le_supr_of_partial_sups_le_partial_sups supᵢ_le_supᵢ_of_partialSups_le_partialSupsₓ'. -/
theorem supᵢ_le_supᵢ_of_partialSups_le_partialSups {f g : ℕ → α}
    (h : partialSups f ≤ partialSups g) : (⨆ n, f n) ≤ ⨆ n, g n :=
  by
  rw [← supᵢ_partialSups_eq f, ← supᵢ_partialSups_eq g]
  exact supᵢ_mono h
#align supr_le_supr_of_partial_sups_le_partial_sups supᵢ_le_supᵢ_of_partialSups_le_partialSups

/- warning: supr_eq_supr_of_partial_sups_eq_partial_sups -> supᵢ_eq_supᵢ_of_partialSups_eq_partialSups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α} {g : Nat -> α}, (Eq.{succ u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) f) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) g)) -> (Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => f n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => g n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α} {g : Nat -> α}, (Eq.{succ u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) f) (partialSups.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) g)) -> (Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => f n)) (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => g n)))
Case conversion may be inaccurate. Consider using '#align supr_eq_supr_of_partial_sups_eq_partial_sups supᵢ_eq_supᵢ_of_partialSups_eq_partialSupsₓ'. -/
theorem supᵢ_eq_supᵢ_of_partialSups_eq_partialSups {f g : ℕ → α}
    (h : partialSups f = partialSups g) : (⨆ n, f n) = ⨆ n, g n := by
  simp_rw [← supᵢ_partialSups_eq f, ← supᵢ_partialSups_eq g, h]
#align supr_eq_supr_of_partial_sups_eq_partial_sups supᵢ_eq_supᵢ_of_partialSups_eq_partialSups

end CompleteLattice

