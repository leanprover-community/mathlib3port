/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir

! This file was ported from Lean 3 source module data.complex.exponential
! leanprover-community/mathlib commit 372edc36e5d2caafdd135769e0136b5a59186834
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GeomSum
import Mathbin.Data.Complex.Basic
import Mathbin.Data.Nat.Choose.Sum

/-!
# Exponential, trigonometric and hyperbolic trigonometric functions

This file contains the definitions of the real and complex exponential, sine, cosine, tangent,
hyperbolic sine, hyperbolic cosine, and hyperbolic tangent functions.

-/


-- mathport name: exprabs'
local notation "abs'" => Abs.abs

open IsAbsoluteValue

open Classical BigOperators Nat ComplexConjugate

section

open Real IsAbsoluteValue Finset

section

variable {α : Type _} {β : Type _} [Ring β] [LinearOrderedField α] [Archimedean α] {abv : β → α}
  [IsAbsoluteValue abv]

/- warning: is_cau_of_decreasing_bounded -> isCauSeq_of_decreasing_bounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : LinearOrderedField.{u1} α] [_inst_3 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))] (f : Nat -> α) {a : α} {m : Nat}, (forall (n : Nat), (GE.ge.{0} Nat Nat.hasLe n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))) (f n)) a)) -> (forall (n : Nat), (GE.ge.{0} Nat Nat.hasLe n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))) (f (Nat.succ n)) (f n))) -> (IsCauSeq.{u1, u1} α _inst_2 α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))))) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : LinearOrderedField.{u1} α] [_inst_3 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_2))))))] (f : Nat -> α) {a : α} {m : Nat}, (forall (n : Nat), (GE.ge.{0} Nat instLENat n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))))) (f n)) a)) -> (forall (n : Nat), (GE.ge.{0} Nat instLENat n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))) (f (Nat.succ n)) (f n))) -> (IsCauSeq.{u1, u1} α _inst_2 α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))))) f)
Case conversion may be inaccurate. Consider using '#align is_cau_of_decreasing_bounded isCauSeq_of_decreasing_boundedₓ'. -/
theorem isCauSeq_of_decreasing_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
    (hnm : ∀ n ≥ m, f n.succ ≤ f n) : IsCauSeq abs f := fun ε ε0 =>
  by
  let ⟨k, hk⟩ := Archimedean.arch a ε0
  have h : ∃ l, ∀ n ≥ m, a - l • ε < f n :=
    ⟨k + k + 1, fun n hnm =>
      lt_of_lt_of_le
        (show a - (k + (k + 1)) • ε < -|f n| from
          lt_neg.1 <|
            lt_of_le_of_lt (ham n hnm)
              (by
                rw [neg_sub, lt_sub_iff_add_lt, add_nsmul, add_nsmul, one_nsmul]
                exact add_lt_add_of_le_of_lt hk (lt_of_le_of_lt hk (lt_add_of_pos_right _ ε0))))
        (neg_le.2 <| abs_neg (f n) ▸ le_abs_self _)⟩
  let l := Nat.find h
  have hl : ∀ n : ℕ, n ≥ m → f n > a - l • ε := Nat.find_spec h
  have hl0 : l ≠ 0 := fun hl0 =>
    not_lt_of_ge (ham m le_rfl)
      (lt_of_lt_of_le (by have := hl m (le_refl m) <;> simpa [hl0] using this) (le_abs_self (f m)))
  cases' not_forall.1 (Nat.find_min h (Nat.pred_lt hl0)) with i hi
  rw [not_imp, not_lt] at hi
  exists i
  intro j hj
  have hfij : f j ≤ f i := (Nat.rel_of_forall_rel_succ_of_le_of_le (· ≥ ·) hnm hi.1 hj).le
  rw [abs_of_nonpos (sub_nonpos.2 hfij), neg_sub, sub_lt_iff_lt_add']
  calc
    f i ≤ a - Nat.pred l • ε := hi.2
    _ = a - l • ε + ε := by
      conv =>
        rhs
        rw [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hl0), succ_nsmul', sub_add,
          add_sub_cancel]
    _ < f j + ε := add_lt_add_right (hl j (le_trans hi.1 hj)) _
    
#align is_cau_of_decreasing_bounded isCauSeq_of_decreasing_bounded

/- warning: is_cau_of_mono_bounded -> isCauSeq_of_mono_bounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : LinearOrderedField.{u1} α] [_inst_3 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))] (f : Nat -> α) {a : α} {m : Nat}, (forall (n : Nat), (GE.ge.{0} Nat Nat.hasLe n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))) (f n)) a)) -> (forall (n : Nat), (GE.ge.{0} Nat Nat.hasLe n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))) (f n) (f (Nat.succ n)))) -> (IsCauSeq.{u1, u1} α _inst_2 α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))))) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : LinearOrderedField.{u1} α] [_inst_3 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_2))))))] (f : Nat -> α) {a : α} {m : Nat}, (forall (n : Nat), (GE.ge.{0} Nat instLENat n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))))) (f n)) a)) -> (forall (n : Nat), (GE.ge.{0} Nat instLENat n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))) (f n) (f (Nat.succ n)))) -> (IsCauSeq.{u1, u1} α _inst_2 α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))))) f)
Case conversion may be inaccurate. Consider using '#align is_cau_of_mono_bounded isCauSeq_of_mono_boundedₓ'. -/
theorem isCauSeq_of_mono_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
    (hnm : ∀ n ≥ m, f n ≤ f n.succ) : IsCauSeq abs f :=
  by
  refine'
    @Eq.recOn (ℕ → α) _ (IsCauSeq abs) _ _
      (-⟨_, @isCauSeq_of_decreasing_bounded _ _ _ (fun n => -f n) a m (by simpa) (by simpa)⟩ :
          CauSeq α abs).2
  ext
  exact neg_neg _
#align is_cau_of_mono_bounded isCauSeq_of_mono_bounded

end

section NoArchimedean

variable {α : Type _} {β : Type _} [Ring β] [LinearOrderedField α] {abv : β → α}
  [IsAbsoluteValue abv]

/- warning: is_cau_series_of_abv_le_cau -> isCauSeq_series_of_abv_le_of_isCauSeq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u2} β] [_inst_2 : LinearOrderedField.{u1} α] {abv : β -> α} [_inst_3 : IsAbsoluteValue.{u1, u2} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))) β (Ring.toSemiring.{u2} β _inst_1) abv] {f : Nat -> β} {g : Nat -> α} (n : Nat), (forall (m : Nat), (LE.le.{0} Nat Nat.hasLe n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))) (abv (f m)) (g m))) -> (IsCauSeq.{u1, u1} α _inst_2 α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))))) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))) (Finset.range n) (fun (i : Nat) => g i))) -> (IsCauSeq.{u1, u2} α _inst_2 β _inst_1 abv (fun (n : Nat) => Finset.sum.{u2, 0} β Nat (AddCommGroup.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toAddCommGroup.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_1)))) (Finset.range n) (fun (i : Nat) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Ring.{u1} β] [_inst_2 : LinearOrderedField.{u2} α] {abv : β -> α} [_inst_3 : IsAbsoluteValue.{u2, u1} α (OrderedCommSemiring.toOrderedSemiring.{u2} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_2))))) β (Ring.toSemiring.{u1} β _inst_1) abv] {f : Nat -> β} {g : Nat -> α} (n : Nat), (forall (m : Nat), (LE.le.{0} Nat instLENat n m) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedRing.toPartialOrder.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_2)))))) (abv (f m)) (g m))) -> (IsCauSeq.{u2, u2} α _inst_2 α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_2)))) (Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (Ring.toNeg.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_2))))) (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedRing.toLinearOrder.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_2))))))))) (fun (n : Nat) => Finset.sum.{u2, 0} α Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_2)))))) (Finset.range n) (fun (i : Nat) => g i))) -> (IsCauSeq.{u2, u1} α _inst_2 β _inst_1 abv (fun (n : Nat) => Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_1)))) (Finset.range n) (fun (i : Nat) => f i)))
Case conversion may be inaccurate. Consider using '#align is_cau_series_of_abv_le_cau isCauSeq_series_of_abv_le_of_isCauSeqₓ'. -/
theorem isCauSeq_series_of_abv_le_of_isCauSeq {f : ℕ → β} {g : ℕ → α} (n : ℕ) :
    (∀ m, n ≤ m → abv (f m) ≤ g m) →
      (IsCauSeq abs fun n => ∑ i in range n, g i) → IsCauSeq abv fun n => ∑ i in range n, f i :=
  by
  intro hm hg ε ε0
  cases' hg (ε / 2) (div_pos ε0 (by norm_num)) with i hi
  exists max n i
  intro j ji
  have hi₁ := hi j (le_trans (le_max_right n i) ji)
  have hi₂ := hi (max n i) (le_max_right n i)
  have sub_le :=
    abs_sub_le (∑ k in range j, g k) (∑ k in range i, g k) (∑ k in range (max n i), g k)
  have := add_lt_add hi₁ hi₂
  rw [abs_sub_comm (∑ k in range (max n i), g k), add_halves ε] at this
  refine' lt_of_le_of_lt (le_trans (le_trans _ (le_abs_self _)) sub_le) this
  generalize hk : j - max n i = k
  clear this hi₂ hi₁ hi ε0 ε hg sub_le
  rw [tsub_eq_iff_eq_add_of_le ji] at hk
  rw [hk]
  clear hk ji j
  induction' k with k' hi
  · simp [abv_zero abv]
  · simp only [Nat.succ_add, sum_range_succ_comm, sub_eq_add_neg, add_assoc]
    refine' le_trans (abv_add _ _ _) _
    simp only [sub_eq_add_neg] at hi
    exact add_le_add (hm _ (le_add_of_nonneg_of_le (Nat.zero_le _) (le_max_left _ _))) hi
#align is_cau_series_of_abv_le_cau isCauSeq_series_of_abv_le_of_isCauSeq

/- warning: is_cau_series_of_abv_cau -> isCauSeq_series_of_abv_isCauSeq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u2} β] [_inst_2 : LinearOrderedField.{u1} α] {abv : β -> α} [_inst_3 : IsAbsoluteValue.{u1, u2} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))) β (Ring.toSemiring.{u2} β _inst_1) abv] {f : Nat -> β}, (IsCauSeq.{u1, u1} α _inst_2 α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2))))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))))) (fun (m : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_2)))))) (Finset.range m) (fun (n : Nat) => abv (f n)))) -> (IsCauSeq.{u1, u2} α _inst_2 β _inst_1 abv (fun (m : Nat) => Finset.sum.{u2, 0} β Nat (AddCommGroup.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toAddCommGroup.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_1)))) (Finset.range m) (fun (n : Nat) => f n)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Ring.{u1} β] [_inst_2 : LinearOrderedField.{u2} α] {abv : β -> α} [_inst_3 : IsAbsoluteValue.{u2, u1} α (OrderedCommSemiring.toOrderedSemiring.{u2} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_2))))) β (Ring.toSemiring.{u1} β _inst_1) abv] {f : Nat -> β}, (IsCauSeq.{u2, u2} α _inst_2 α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_2)))) (Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (Ring.toNeg.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_2))))) (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedRing.toLinearOrder.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_2))))))))) (fun (m : Nat) => Finset.sum.{u2, 0} α Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_2)))))) (Finset.range m) (fun (n : Nat) => abv (f n)))) -> (IsCauSeq.{u2, u1} α _inst_2 β _inst_1 abv (fun (m : Nat) => Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_1)))) (Finset.range m) (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align is_cau_series_of_abv_cau isCauSeq_series_of_abv_isCauSeqₓ'. -/
theorem isCauSeq_series_of_abv_isCauSeq {f : ℕ → β} :
    (IsCauSeq abs fun m => ∑ n in range m, abv (f n)) → IsCauSeq abv fun m => ∑ n in range m, f n :=
  isCauSeq_series_of_abv_le_of_isCauSeq 0 fun n h => le_rfl
#align is_cau_series_of_abv_cau isCauSeq_series_of_abv_isCauSeq

end NoArchimedean

section

variable {α : Type _} [LinearOrderedField α] [Archimedean α]

/- warning: is_cau_geo_series -> isCauSeq_geo_series is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))] {β : Type.{u2}} [_inst_3 : Ring.{u2} β] [_inst_4 : Nontrivial.{u2} β] {abv : β -> α} [_inst_5 : IsAbsoluteValue.{u1, u2} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))) β (Ring.toSemiring.{u2} β _inst_3) abv] (x : β), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (abv x) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))))))) -> (IsCauSeq.{u1, u2} α _inst_1 β _inst_3 abv (fun (n : Nat) => Finset.sum.{u2, 0} β Nat (AddCommGroup.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toAddCommGroup.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_3)))) (Finset.range n) (fun (m : Nat) => HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat (Monoid.Pow.{u2} β (Ring.toMonoid.{u2} β _inst_3))) x m)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))))] {β : Type.{u2}} [_inst_3 : Ring.{u2} β] [_inst_4 : Nontrivial.{u2} β] {abv : β -> α} [_inst_5 : IsAbsoluteValue.{u1, u2} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))) β (Ring.toSemiring.{u2} β _inst_3) abv] (x : β), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (abv x) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))) -> (IsCauSeq.{u1, u2} α _inst_1 β _inst_3 abv (fun (n : Nat) => Finset.sum.{u2, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_3)))) (Finset.range n) (fun (m : Nat) => HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat (Monoid.Pow.{u2} β (MonoidWithZero.toMonoid.{u2} β (Semiring.toMonoidWithZero.{u2} β (Ring.toSemiring.{u2} β _inst_3))))) x m)))
Case conversion may be inaccurate. Consider using '#align is_cau_geo_series isCauSeq_geo_seriesₓ'. -/
theorem isCauSeq_geo_series {β : Type _} [Ring β] [Nontrivial β] {abv : β → α} [IsAbsoluteValue abv]
    (x : β) (hx1 : abv x < 1) : IsCauSeq abv fun n => ∑ m in range n, x ^ m :=
  have hx1' : abv x ≠ 1 := fun h => by simpa [h, lt_irrefl] using hx1
  isCauSeq_series_of_abv_isCauSeq
    (by
      simp only [abv_pow abv, geom_sum_eq hx1']
      conv in _ / _ => rw [← neg_div_neg_eq, neg_sub, neg_sub]
      refine' @isCauSeq_of_mono_bounded _ _ _ _ ((1 : α) / (1 - abv x)) 0 _ _
      · intro n hn
        rw [abs_of_nonneg]
        refine'
          div_le_div_of_le (le_of_lt <| sub_pos.2 hx1)
            (sub_le_self _ (abv_pow abv x n ▸ abv_nonneg _ _))
        refine' div_nonneg (sub_nonneg.2 _) (sub_nonneg.2 <| le_of_lt hx1)
        clear hn
        induction' n with n ih
        · simp
        · rw [pow_succ, ← one_mul (1 : α)]
          refine' mul_le_mul (le_of_lt hx1) ih (abv_pow abv x n ▸ abv_nonneg _ _) (by norm_num)
      · intro n hn
        refine' div_le_div_of_le (le_of_lt <| sub_pos.2 hx1) (sub_le_sub_left _ _)
        rw [← one_mul (_ ^ n), pow_succ]
        exact mul_le_mul_of_nonneg_right (le_of_lt hx1) (pow_nonneg (abv_nonneg _ _) _))
#align is_cau_geo_series isCauSeq_geo_series

/- warning: is_cau_geo_series_const -> isCauSeq_geo_series_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))] (a : α) {x : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) x) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))))))) -> (IsCauSeq.{u1, u1} α _inst_1 α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))) (fun (m : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Finset.range m) (fun (n : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) a (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) x n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))))] (a : α) {x : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))) x) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))) -> (IsCauSeq.{u1, u1} α _inst_1 α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))) (fun (m : Nat) => Finset.sum.{u1, 0} α Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1)))))) (Finset.range m) (fun (n : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))) a (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))))))) x n))))
Case conversion may be inaccurate. Consider using '#align is_cau_geo_series_const isCauSeq_geo_series_constₓ'. -/
theorem isCauSeq_geo_series_const (a : α) {x : α} (hx1 : |x| < 1) :
    IsCauSeq abs fun m => ∑ n in range m, a * x ^ n :=
  by
  have : IsCauSeq abs fun m => a * ∑ n in range m, x ^ n :=
    (CauSeq.const abs a * ⟨_, isCauSeq_geo_series x hx1⟩).2
  simpa only [mul_sum]
#align is_cau_geo_series_const isCauSeq_geo_series_const

variable {β : Type _} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

/- warning: series_ratio_test -> series_ratio_test is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))] {β : Type.{u2}} [_inst_3 : Ring.{u2} β] {abv : β -> α} [_inst_4 : IsAbsoluteValue.{u1, u2} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))) β (Ring.toSemiring.{u2} β _inst_3) abv] {f : Nat -> β} (n : Nat) (r : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))))))) r) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) r (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))))))) -> (forall (m : Nat), (LE.le.{0} Nat Nat.hasLe n m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (abv (f (Nat.succ m))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) r (abv (f m))))) -> (IsCauSeq.{u1, u2} α _inst_1 β _inst_3 abv (fun (m : Nat) => Finset.sum.{u2, 0} β Nat (AddCommGroup.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toAddCommGroup.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_3)))) (Finset.range m) (fun (n : Nat) => f n)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} α] [_inst_2 : Archimedean.{u2} α (OrderedSemiring.toOrderedAddCommMonoid.{u2} α (OrderedCommSemiring.toOrderedSemiring.{u2} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1))))))] {β : Type.{u1}} [_inst_3 : Ring.{u1} β] {abv : β -> α} [_inst_4 : IsAbsoluteValue.{u2, u1} α (OrderedCommSemiring.toOrderedSemiring.{u2} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1))))) β (Ring.toSemiring.{u1} β _inst_3) abv] {f : Nat -> β} (n : Nat) (r : α), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedRing.toPartialOrder.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (CommMonoidWithZero.toZero.{u2} α (CommGroupWithZero.toCommMonoidWithZero.{u2} α (Semifield.toCommGroupWithZero.{u2} α (LinearOrderedSemifield.toSemifield.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1))))))) r) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedRing.toPartialOrder.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))) r (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (NonAssocRing.toOne.{u2} α (Ring.toNonAssocRing.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1))))))))) -> (forall (m : Nat), (LE.le.{0} Nat instLENat n m) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedRing.toPartialOrder.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))) (abv (f (Nat.succ m))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocRing.toMul.{u2} α (NonAssocRing.toNonUnitalNonAssocRing.{u2} α (Ring.toNonAssocRing.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))))) r (abv (f m))))) -> (IsCauSeq.{u2, u1} α _inst_1 β _inst_3 abv (fun (m : Nat) => Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_3)))) (Finset.range m) (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align series_ratio_test series_ratio_testₓ'. -/
theorem series_ratio_test {f : ℕ → β} (n : ℕ) (r : α) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ m, n ≤ m → abv (f m.succ) ≤ r * abv (f m)) : IsCauSeq abv fun m => ∑ n in range m, f n :=
  by
  have har1 : |r| < 1 := by rwa [abs_of_nonneg hr0]
  refine'
    isCauSeq_series_of_abv_le_of_isCauSeq n.succ _
      (isCauSeq_geo_series_const (abv (f n.succ) * r⁻¹ ^ n.succ) har1)
  intro m hmn
  cases' Classical.em (r = 0) with r_zero r_ne_zero
  · have m_pos := lt_of_lt_of_le (Nat.succ_pos n) hmn
    have := h m.pred (Nat.le_of_succ_le_succ (by rwa [Nat.succ_pred_eq_of_pos m_pos]))
    simpa [r_zero, Nat.succ_pred_eq_of_pos m_pos, pow_succ]
  generalize hk : m - n.succ = k
  have r_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm r_ne_zero)
  replace hk : m = k + n.succ := (tsub_eq_iff_eq_add_of_le hmn).1 hk
  induction' k with k ih generalizing m n
  · rw [hk, zero_add, mul_right_comm, inv_pow _ _, ← div_eq_mul_inv, mul_div_cancel]
    exact (ne_of_lt (pow_pos r_pos _)).symm
  · have kn : k + n.succ ≥ n.succ := by
      rw [← zero_add n.succ] <;> exact add_le_add (zero_le _) (by simp)
    rw [hk, Nat.succ_add, pow_succ' r, ← mul_assoc]
    exact
      le_trans (by rw [mul_comm] <;> exact h _ (Nat.le_of_succ_le kn))
        (mul_le_mul_of_nonneg_right (ih (k + n.succ) n h kn rfl) hr0)
#align series_ratio_test series_ratio_test

#print sum_range_diag_flip /-
theorem sum_range_diag_flip {α : Type _} [AddCommMonoid α] (n : ℕ) (f : ℕ → ℕ → α) :
    (∑ m in range n, ∑ k in range (m + 1), f k (m - k)) =
      ∑ m in range n, ∑ k in range (n - m), f m k :=
  by
  rw [sum_sigma', sum_sigma'] <;>
    exact
      sum_bij (fun a _ => ⟨a.2, a.1 - a.2⟩)
        (fun a ha =>
          have h₁ : a.1 < n := mem_range.1 (mem_sigma.1 ha).1
          have h₂ : a.2 < Nat.succ a.1 := mem_range.1 (mem_sigma.1 ha).2
          mem_sigma.2
            ⟨mem_range.2 (lt_of_lt_of_le h₂ h₁),
              mem_range.2 ((tsub_lt_tsub_iff_right (Nat.le_of_lt_succ h₂)).2 h₁)⟩)
        (fun _ _ => rfl)
        (fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h =>
          have ha : a₁ < n ∧ a₂ ≤ a₁ :=
            ⟨mem_range.1 (mem_sigma.1 ha).1, Nat.le_of_lt_succ (mem_range.1 (mem_sigma.1 ha).2)⟩
          have hb : b₁ < n ∧ b₂ ≤ b₁ :=
            ⟨mem_range.1 (mem_sigma.1 hb).1, Nat.le_of_lt_succ (mem_range.1 (mem_sigma.1 hb).2)⟩
          have h : a₂ = b₂ ∧ _ := Sigma.mk.inj h
          have h' : a₁ = b₁ - b₂ + a₂ := (tsub_eq_iff_eq_add_of_le ha.2).1 (eq_of_hEq h.2)
          Sigma.mk.inj_iff.2 ⟨tsub_add_cancel_of_le hb.2 ▸ h'.symm ▸ h.1 ▸ rfl, hEq_of_eq h.1⟩)
        fun ⟨a₁, a₂⟩ ha =>
        have ha : a₁ < n ∧ a₂ < n - a₁ :=
          ⟨mem_range.1 (mem_sigma.1 ha).1, mem_range.1 (mem_sigma.1 ha).2⟩
        ⟨⟨a₂ + a₁, a₁⟩,
          ⟨mem_sigma.2
              ⟨mem_range.2 (lt_tsub_iff_right.1 ha.2),
                mem_range.2 (Nat.lt_succ_of_le (Nat.le_add_left _ _))⟩,
            Sigma.mk.inj_iff.2 ⟨rfl, hEq_of_eq (add_tsub_cancel_right _ _).symm⟩⟩⟩
#align sum_range_diag_flip sum_range_diag_flip
-/

end

section NoArchimedean

variable {α : Type _} {β : Type _} [LinearOrderedField α] {abv : β → α}

section

variable [Semiring β] [IsAbsoluteValue abv]

/- warning: abv_sum_le_sum_abv -> abv_sum_le_sum_abv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} α] {abv : β -> α} [_inst_2 : Semiring.{u2} β] [_inst_3 : IsAbsoluteValue.{u1, u2} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))) β _inst_2 abv] {γ : Type.{u3}} (f : γ -> β) (s : Finset.{u3} γ), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (abv (Finset.sum.{u2, u3} β γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_2))) s (fun (k : γ) => f k))) (Finset.sum.{u1, u3} α γ (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) s (fun (k : γ) => abv (f k)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrderedField.{u2} α] {abv : β -> α} [_inst_2 : Semiring.{u1} β] [_inst_3 : IsAbsoluteValue.{u2, u1} α (OrderedCommSemiring.toOrderedSemiring.{u2} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1))))) β _inst_2 abv] {γ : Type.{u3}} (f : γ -> β) (s : Finset.{u3} γ), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedRing.toPartialOrder.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))) (abv (Finset.sum.{u1, u3} β γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_2))) s (fun (k : γ) => f k))) (Finset.sum.{u2, u3} α γ (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1)))))) s (fun (k : γ) => abv (f k)))
Case conversion may be inaccurate. Consider using '#align abv_sum_le_sum_abv abv_sum_le_sum_abvₓ'. -/
theorem abv_sum_le_sum_abv {γ : Type _} (f : γ → β) (s : Finset γ) :
    abv (∑ k in s, f k) ≤ ∑ k in s, abv (f k) :=
  haveI := Classical.decEq γ
  Finset.induction_on s (by simp [abv_zero abv]) fun a s has ih => by
    rw [sum_insert has, sum_insert has] <;> exact le_trans (abv_add abv _ _) (add_le_add_left ih _)
#align abv_sum_le_sum_abv abv_sum_le_sum_abv

end

section

variable [Ring β] [IsAbsoluteValue abv]

/- warning: cauchy_product -> cauchy_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} α] {abv : β -> α} [_inst_2 : Ring.{u2} β] [_inst_3 : IsAbsoluteValue.{u1, u2} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))) β (Ring.toSemiring.{u2} β _inst_2) abv] {a : Nat -> β} {b : Nat -> β}, (IsCauSeq.{u1, u1} α _inst_1 α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))) (fun (m : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Finset.range m) (fun (n : Nat) => abv (a n)))) -> (IsCauSeq.{u1, u2} α _inst_1 β _inst_2 abv (fun (m : Nat) => Finset.sum.{u2, 0} β Nat (AddCommGroup.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toAddCommGroup.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_2)))) (Finset.range m) (fun (n : Nat) => b n))) -> (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))))))) ε) -> (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat Nat.hasLe j i) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (abv (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddGroupWithOne.toAddGroup.{u2} β (NonAssocRing.toAddGroupWithOne.{u2} β (Ring.toNonAssocRing.{u2} β _inst_2)))))) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (Ring.toDistrib.{u2} β _inst_2))) (Finset.sum.{u2, 0} β Nat (AddCommGroup.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toAddCommGroup.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_2)))) (Finset.range j) (fun (k : Nat) => a k)) (Finset.sum.{u2, 0} β Nat (AddCommGroup.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toAddCommGroup.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_2)))) (Finset.range j) (fun (k : Nat) => b k))) (Finset.sum.{u2, 0} β Nat (AddCommGroup.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toAddCommGroup.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_2)))) (Finset.range j) (fun (n : Nat) => Finset.sum.{u2, 0} β Nat (AddCommGroup.toAddCommMonoid.{u2} β (NonUnitalNonAssocRing.toAddCommGroup.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_2)))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (m : Nat) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (Ring.toDistrib.{u2} β _inst_2))) (a m) (b (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n m))))))) ε))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrderedField.{u2} α] {abv : β -> α} [_inst_2 : Ring.{u1} β] [_inst_3 : IsAbsoluteValue.{u2, u1} α (OrderedCommSemiring.toOrderedSemiring.{u2} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1))))) β (Ring.toSemiring.{u1} β _inst_2) abv] {a : Nat -> β} {b : Nat -> β}, (IsCauSeq.{u2, u2} α _inst_1 α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))) (Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (Ring.toNeg.{u2} α (StrictOrderedRing.toRing.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1))))) (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedRing.toLinearOrder.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1))))))))) (fun (m : Nat) => Finset.sum.{u2, 0} α Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1)))))) (Finset.range m) (fun (n : Nat) => abv (a n)))) -> (IsCauSeq.{u2, u1} α _inst_1 β _inst_2 abv (fun (m : Nat) => Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_2)))) (Finset.range m) (fun (n : Nat) => b n))) -> (forall (ε : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedRing.toPartialOrder.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (CommMonoidWithZero.toZero.{u2} α (CommGroupWithZero.toCommMonoidWithZero.{u2} α (Semifield.toCommGroupWithZero.{u2} α (LinearOrderedSemifield.toSemifield.{u2} α (LinearOrderedField.toLinearOrderedSemifield.{u2} α _inst_1))))))) ε) -> (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat instLENat j i) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedRing.toPartialOrder.{u2} α (LinearOrderedRing.toStrictOrderedRing.{u2} α (LinearOrderedCommRing.toLinearOrderedRing.{u2} α (LinearOrderedField.toLinearOrderedCommRing.{u2} α _inst_1)))))) (abv (HSub.hSub.{u1, u1, u1} β β β (instHSub.{u1} β (Ring.toSub.{u1} β _inst_2)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (NonUnitalNonAssocRing.toMul.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_2)))) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_2)))) (Finset.range j) (fun (k : Nat) => a k)) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_2)))) (Finset.range j) (fun (k : Nat) => b k))) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_2)))) (Finset.range j) (fun (n : Nat) => Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_2)))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (m : Nat) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (NonUnitalNonAssocRing.toMul.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_2)))) (a m) (b (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n m))))))) ε))))
Case conversion may be inaccurate. Consider using '#align cauchy_product cauchy_productₓ'. -/
theorem cauchy_product {a b : ℕ → β} (ha : IsCauSeq abs fun m => ∑ n in range m, abv (a n))
    (hb : IsCauSeq abv fun m => ∑ n in range m, b n) (ε : α) (ε0 : 0 < ε) :
    ∃ i : ℕ,
      ∀ j ≥ i,
        abv
            (((∑ k in range j, a k) * ∑ k in range j, b k) -
              ∑ n in range j, ∑ m in range (n + 1), a m * b (n - m)) <
          ε :=
  let ⟨Q, hQ⟩ := CauSeq.bounded ⟨_, hb⟩
  let ⟨P, hP⟩ := CauSeq.bounded ⟨_, ha⟩
  have hP0 : 0 < P := lt_of_le_of_lt (abs_nonneg _) (hP 0)
  have hPε0 : 0 < ε / (2 * P) := div_pos ε0 (mul_pos (show (2 : α) > 0 by norm_num) hP0)
  let ⟨N, hN⟩ := CauSeq.cauchy₂ ⟨_, hb⟩ hPε0
  have hQε0 : 0 < ε / (4 * Q) :=
    div_pos ε0 (mul_pos (show (0 : α) < 4 by norm_num) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0)))
  let ⟨M, hM⟩ := CauSeq.cauchy₂ ⟨_, ha⟩ hQε0
  ⟨2 * (max N M + 1), fun K hK =>
    by
    have h₁ :
      (∑ m in range K, ∑ k in range (m + 1), a k * b (m - k)) =
        ∑ m in range K, ∑ n in range (K - m), a m * b n :=
      by simpa using sum_range_diag_flip K fun m n => a m * b n
    have h₂ :
      (fun i => ∑ k in range (K - i), a i * b k) = fun i => a i * ∑ k in range (K - i), b k := by
      simp [Finset.mul_sum]
    have h₃ :
      (∑ i in range K, a i * ∑ k in range (K - i), b k) =
        (∑ i in range K, a i * ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) +
          ∑ i in range K, a i * ∑ k in range K, b k :=
      by rw [← sum_add_distrib] <;> simp [(mul_add _ _ _).symm]
    have two_mul_two : (4 : α) = 2 * 2 := by norm_num
    have hQ0 : Q ≠ 0 := fun h => by simpa [h, lt_irrefl] using hQε0
    have h2Q0 : 2 * Q ≠ 0 := mul_ne_zero two_ne_zero hQ0
    have hε : ε / (2 * P) * P + ε / (4 * Q) * (2 * Q) = ε := by
      rw [← div_div, div_mul_cancel _ (Ne.symm (ne_of_lt hP0)), two_mul_two, mul_assoc, ← div_div,
        div_mul_cancel _ h2Q0, add_halves]
    have hNMK : max N M + 1 < K :=
      lt_of_lt_of_le (by rw [two_mul] <;> exact lt_add_of_pos_left _ (Nat.succ_pos _)) hK
    have hKN : N < K :=
      calc
        N ≤ max N M := le_max_left _ _
        _ < max N M + 1 := (Nat.lt_succ_self _)
        _ < K := hNMK
        
    have hsumlesum :
      (∑ i in range (max N M + 1),
          abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) ≤
        ∑ i in range (max N M + 1), abv (a i) * (ε / (2 * P)) :=
      sum_le_sum fun m hmJ =>
        mul_le_mul_of_nonneg_left
          (le_of_lt
            (hN (K - m)
              (le_tsub_of_add_le_left
                (le_trans
                  (by
                    rw [two_mul] <;>
                      exact
                        add_le_add (le_of_lt (mem_range.1 hmJ))
                          (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _))))
                  hK))
              K (le_of_lt hKN)))
          (abv_nonneg abv _)
    have hsumltP : (∑ n in range (max N M + 1), abv (a n)) < P :=
      calc
        (∑ n in range (max N M + 1), abv (a n)) = |∑ n in range (max N M + 1), abv (a n)| :=
          Eq.symm (abs_of_nonneg (sum_nonneg fun x h => abv_nonneg abv (a x)))
        _ < P := hP (max N M + 1)
        
    rw [h₁, h₂, h₃, sum_mul, ← sub_sub, sub_right_comm, sub_self, zero_sub, abv_neg abv]
    refine' lt_of_le_of_lt (abv_sum_le_sum_abv _ _) _
    suffices
      (∑ i in range (max N M + 1),
            abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) +
          ((∑ i in range K, abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) -
            ∑ i in range (max N M + 1),
              abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) <
        ε / (2 * P) * P + ε / (4 * Q) * (2 * Q)
      by
      rw [hε] at this
      simpa [abv_mul abv]
    refine'
      add_lt_add
        (lt_of_le_of_lt hsumlesum
          (by rw [← sum_mul, mul_comm] <;> exact (mul_lt_mul_left hPε0).mpr hsumltP))
        _
    rw [sum_range_sub_sum_range (le_of_lt hNMK)]
    calc
      (∑ i in (range K).filterₓ fun k => max N M + 1 ≤ k,
            abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) ≤
          ∑ i in (range K).filterₓ fun k => max N M + 1 ≤ k, abv (a i) * (2 * Q) :=
        sum_le_sum fun n hn =>
          by
          refine' mul_le_mul_of_nonneg_left _ (abv_nonneg _ _)
          rw [sub_eq_add_neg]
          refine' le_trans (abv_add _ _ _) _
          rw [two_mul, abv_neg abv]
          exact add_le_add (le_of_lt (hQ _)) (le_of_lt (hQ _))
      _ < ε / (4 * Q) * (2 * Q) := by
        rw [← sum_mul, ← sum_range_sub_sum_range (le_of_lt hNMK)] <;>
          refine'
            (mul_lt_mul_right <| by
                  rw [two_mul] <;>
                    exact
                      add_pos (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))
                        (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))).2
              (lt_of_le_of_lt (le_abs_self _)
                (hM _ (le_trans (Nat.le_succ_of_le (le_max_right _ _)) (le_of_lt hNMK)) _
                  (Nat.le_succ_of_le (le_max_right _ _))))
      ⟩
#align cauchy_product cauchy_product

end

end NoArchimedean

end

open Finset

open CauSeq

namespace Complex

/- warning: complex.is_cau_abs_exp -> Complex.isCauSeq_abs_exp is a dubious translation:
lean 3 declaration is
  forall (z : Complex), IsCauSeq.{0, 0} Real Real.linearOrderedField Real Real.ring (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup)) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (m : Nat) => coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) z m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) (Nat.factorial m)))))
but is expected to have type
  forall (z : Complex), IsCauSeq.{0, 0} Real Real.instLinearOrderedFieldReal Real Real.instRingReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal)) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (m : Nat) => FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) z m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))
Case conversion may be inaccurate. Consider using '#align complex.is_cau_abs_exp Complex.isCauSeq_abs_expₓ'. -/
theorem isCauSeq_abs_exp (z : ℂ) : IsCauSeq Abs.abs fun n => ∑ m in range n, abs (z ^ m / m !) :=
  let ⟨n, hn⟩ := exists_nat_gt (abs z)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs.NonNeg _) hn
  series_ratio_test n (Complex.abs z / n) (div_nonneg (abs.NonNeg _) (le_of_lt hn0))
    (by rwa [div_lt_iff hn0, one_mul]) fun m hm => by
    rw [abs_abs, abs_abs, Nat.factorial_succ, pow_succ, mul_comm m.succ, Nat.cast_mul, ← div_div,
        mul_div_assoc, mul_div_right_comm, abs.map_mul, map_div₀, abs_cast_nat] <;>
      exact
        mul_le_mul_of_nonneg_right
          (div_le_div_of_le_left (abs.nonneg _) hn0 (Nat.cast_le.2 (le_trans hm (Nat.le_succ _))))
          (abs.nonneg _)
#align complex.is_cau_abs_exp Complex.isCauSeq_abs_exp

noncomputable section

/- warning: complex.is_cau_exp -> Complex.isCauSeq_exp is a dubious translation:
lean 3 declaration is
  forall (z : Complex), IsCauSeq.{0, 0} Real Real.linearOrderedField Complex Complex.ring (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs) (fun (n : Nat) => Finset.sum.{0, 0} Complex Nat (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) z m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) (Nat.factorial m))))
but is expected to have type
  forall (z : Complex), IsCauSeq.{0, 0} Real Real.instLinearOrderedFieldReal Complex Complex.instRingComplex (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs) (fun (n : Nat) => Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) z m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m))))
Case conversion may be inaccurate. Consider using '#align complex.is_cau_exp Complex.isCauSeq_expₓ'. -/
theorem isCauSeq_exp (z : ℂ) : IsCauSeq abs fun n => ∑ m in range n, z ^ m / m ! :=
  isCauSeq_series_of_abv_isCauSeq (isCauSeq_abs_exp z)
#align complex.is_cau_exp Complex.isCauSeq_exp

/- warning: complex.exp' -> Complex.exp' is a dubious translation:
lean 3 declaration is
  Complex -> (CauSeq.{0, 0} Real Real.linearOrderedField Complex Complex.ring (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs))
but is expected to have type
  Complex -> (CauSeq.{0, 0} Real Real.instLinearOrderedFieldReal Complex Complex.instRingComplex (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs))
Case conversion may be inaccurate. Consider using '#align complex.exp' Complex.exp'ₓ'. -/
/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
@[pp_nodot]
def exp' (z : ℂ) : CauSeq ℂ Complex.abs :=
  ⟨fun n => ∑ m in range n, z ^ m / m !, isCauSeq_exp z⟩
#align complex.exp' Complex.exp'

#print Complex.exp /-
/-- The complex exponential function, defined via its Taylor series -/
@[pp_nodot]
irreducible_def exp (z : ℂ) : ℂ :=
  limUnder (exp' z)
#align complex.exp Complex.exp
-/

#print Complex.sin /-
/-- The complex sine function, defined via `exp` -/
@[pp_nodot]
def sin (z : ℂ) : ℂ :=
  (exp (-z * I) - exp (z * I)) * I / 2
#align complex.sin Complex.sin
-/

#print Complex.cos /-
/-- The complex cosine function, defined via `exp` -/
@[pp_nodot]
def cos (z : ℂ) : ℂ :=
  (exp (z * I) + exp (-z * I)) / 2
#align complex.cos Complex.cos
-/

#print Complex.tan /-
/-- The complex tangent function, defined as `sin z / cos z` -/
@[pp_nodot]
def tan (z : ℂ) : ℂ :=
  sin z / cos z
#align complex.tan Complex.tan
-/

#print Complex.sinh /-
/-- The complex hyperbolic sine function, defined via `exp` -/
@[pp_nodot]
def sinh (z : ℂ) : ℂ :=
  (exp z - exp (-z)) / 2
#align complex.sinh Complex.sinh
-/

#print Complex.cosh /-
/-- The complex hyperbolic cosine function, defined via `exp` -/
@[pp_nodot]
def cosh (z : ℂ) : ℂ :=
  (exp z + exp (-z)) / 2
#align complex.cosh Complex.cosh
-/

#print Complex.tanh /-
/-- The complex hyperbolic tangent function, defined as `sinh z / cosh z` -/
@[pp_nodot]
def tanh (z : ℂ) : ℂ :=
  sinh z / cosh z
#align complex.tanh Complex.tanh
-/

end Complex

namespace Real

open Complex

#print Real.exp /-
/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot]
def exp (x : ℝ) : ℝ :=
  (exp x).re
#align real.exp Real.exp
-/

#print Real.sin /-
/-- The real sine function, defined as the real part of the complex sine -/
@[pp_nodot]
def sin (x : ℝ) : ℝ :=
  (sin x).re
#align real.sin Real.sin
-/

#print Real.cos /-
/-- The real cosine function, defined as the real part of the complex cosine -/
@[pp_nodot]
def cos (x : ℝ) : ℝ :=
  (cos x).re
#align real.cos Real.cos
-/

#print Real.tan /-
/-- The real tangent function, defined as the real part of the complex tangent -/
@[pp_nodot]
def tan (x : ℝ) : ℝ :=
  (tan x).re
#align real.tan Real.tan
-/

#print Real.sinh /-
/-- The real hypebolic sine function, defined as the real part of the complex hyperbolic sine -/
@[pp_nodot]
def sinh (x : ℝ) : ℝ :=
  (sinh x).re
#align real.sinh Real.sinh
-/

#print Real.cosh /-
/-- The real hypebolic cosine function, defined as the real part of the complex hyperbolic cosine -/
@[pp_nodot]
def cosh (x : ℝ) : ℝ :=
  (cosh x).re
#align real.cosh Real.cosh
-/

#print Real.tanh /-
/-- The real hypebolic tangent function, defined as the real part of
the complex hyperbolic tangent -/
@[pp_nodot]
def tanh (x : ℝ) : ℝ :=
  (tanh x).re
#align real.tanh Real.tanh
-/

end Real

namespace Complex

variable (x y : ℂ)

/- warning: complex.exp_zero -> Complex.exp_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Complex (Complex.exp (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))
but is expected to have type
  Eq.{1} Complex (Complex.exp (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))
Case conversion may be inaccurate. Consider using '#align complex.exp_zero Complex.exp_zeroₓ'. -/
@[simp]
theorem exp_zero : exp 0 = 1 := by
  rw [exp]
  refine' lim_eq_of_equiv_const fun ε ε0 => ⟨1, fun j hj => _⟩
  convert ε0
  cases j
  · exact absurd hj (not_le_of_gt zero_lt_one)
  · dsimp [exp']
    induction' j with j ih
    · dsimp [exp'] <;> simp
    · rw [← ih (by decide)]
      simp only [sum_range_succ, pow_succ]
      simp
#align complex.exp_zero Complex.exp_zero

/- warning: complex.exp_add -> Complex.exp_add is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Complex), Eq.{1} Complex (Complex.exp (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) x y)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.exp x) (Complex.exp y))
but is expected to have type
  forall (x : Complex) (y : Complex), Eq.{1} Complex (Complex.exp (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) x y)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.exp x) (Complex.exp y))
Case conversion may be inaccurate. Consider using '#align complex.exp_add Complex.exp_addₓ'. -/
theorem exp_add : exp (x + y) = exp x * exp y :=
  by
  have hj :
    ∀ j : ℕ,
      (∑ m in range j, (x + y) ^ m / m !) =
        ∑ i in range j, ∑ k in range (i + 1), x ^ k / k ! * (y ^ (i - k) / (i - k)!) :=
    by
    intro j
    refine' Finset.sum_congr rfl fun m hm => _
    rw [add_pow, div_eq_mul_inv, sum_mul]
    refine' Finset.sum_congr rfl fun i hi => _
    have h₁ : (m.choose i : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (pos_iff_ne_zero.1 (Nat.choose_pos (Nat.le_of_lt_succ (mem_range.1 hi))))
    have h₂ := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ <| Finset.mem_range.1 hi)
    rw [← h₂, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv]
    simp only [mul_left_comm (m.choose i : ℂ), mul_assoc, mul_left_comm (m.choose i : ℂ)⁻¹,
      mul_comm (m.choose i : ℂ)]
    rw [inv_mul_cancel h₁]
    simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
  simp_rw [exp, exp', lim_mul_lim]
  apply (lim_eq_lim_of_equiv _).symm
  simp only [hj]
  exact cauchy_product (is_cau_abs_exp x) (is_cau_exp y)
#align complex.exp_add Complex.exp_add

#print Complex.exp_list_sum /-
theorem exp_list_sum (l : List ℂ) : exp l.Sum = (l.map exp).Prod :=
  @MonoidHom.map_list_prod (Multiplicative ℂ) ℂ _ _ ⟨exp, exp_zero, exp_add⟩ l
#align complex.exp_list_sum Complex.exp_list_sum
-/

#print Complex.exp_multiset_sum /-
theorem exp_multiset_sum (s : Multiset ℂ) : exp s.Sum = (s.map exp).Prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℂ) ℂ _ _ ⟨exp, exp_zero, exp_add⟩ s
#align complex.exp_multiset_sum Complex.exp_multiset_sum
-/

#print Complex.exp_sum /-
theorem exp_sum {α : Type _} (s : Finset α) (f : α → ℂ) :
    exp (∑ x in s, f x) = ∏ x in s, exp (f x) :=
  @MonoidHom.map_prod (Multiplicative ℂ) α ℂ _ _ ⟨exp, exp_zero, exp_add⟩ f s
#align complex.exp_sum Complex.exp_sum
-/

/- warning: complex.exp_nat_mul -> Complex.exp_nat_mul is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (n : Nat), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) n) x)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.exp x) n)
but is expected to have type
  forall (x : Complex) (n : Nat), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) n) x)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.exp x) n)
Case conversion may be inaccurate. Consider using '#align complex.exp_nat_mul Complex.exp_nat_mulₓ'. -/
theorem exp_nat_mul (x : ℂ) : ∀ n : ℕ, exp (n * x) = exp x ^ n
  | 0 => by rw [Nat.cast_zero, MulZeroClass.zero_mul, exp_zero, pow_zero]
  | Nat.succ n => by rw [pow_succ', Nat.cast_add_one, add_mul, exp_add, ← exp_nat_mul, one_mul]
#align complex.exp_nat_mul Complex.exp_nat_mul

/- warning: complex.exp_ne_zero -> Complex.exp_ne_zero is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Ne.{1} Complex (Complex.exp x) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))
but is expected to have type
  forall (x : Complex), Ne.{1} Complex (Complex.exp x) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))
Case conversion may be inaccurate. Consider using '#align complex.exp_ne_zero Complex.exp_ne_zeroₓ'. -/
theorem exp_ne_zero : exp x ≠ 0 := fun h =>
  zero_ne_one <| by rw [← exp_zero, ← add_neg_self x, exp_add, h] <;> simp
#align complex.exp_ne_zero Complex.exp_ne_zero

/- warning: complex.exp_neg -> Complex.exp_neg is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (Complex.exp (Neg.neg.{0} Complex Complex.hasNeg x)) (Inv.inv.{0} Complex Complex.hasInv (Complex.exp x))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (Complex.exp (Neg.neg.{0} Complex Complex.instNegComplex x)) (Inv.inv.{0} Complex Complex.instInvComplex (Complex.exp x))
Case conversion may be inaccurate. Consider using '#align complex.exp_neg Complex.exp_negₓ'. -/
theorem exp_neg : exp (-x) = (exp x)⁻¹ := by
  rw [← mul_right_inj' (exp_ne_zero x), ← exp_add] <;> simp [mul_inv_cancel (exp_ne_zero x)]
#align complex.exp_neg Complex.exp_neg

/- warning: complex.exp_sub -> Complex.exp_sub is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Complex), Eq.{1} Complex (Complex.exp (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) x y)) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (Complex.exp x) (Complex.exp y))
but is expected to have type
  forall (x : Complex) (y : Complex), Eq.{1} Complex (Complex.exp (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) x y)) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (Complex.exp x) (Complex.exp y))
Case conversion may be inaccurate. Consider using '#align complex.exp_sub Complex.exp_subₓ'. -/
theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]
#align complex.exp_sub Complex.exp_sub

/- warning: complex.exp_int_mul -> Complex.exp_int_mul is a dubious translation:
lean 3 declaration is
  forall (z : Complex) (n : Int), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Complex (HasLiftT.mk.{1, 1} Int Complex (CoeTCₓ.coe.{1, 1} Int Complex (Int.castCoe.{0} Complex (AddGroupWithOne.toHasIntCast.{0} Complex Complex.addGroupWithOne)))) n) z)) (HPow.hPow.{0, 0, 0} Complex Int Complex (instHPow.{0, 0} Complex Int (DivInvMonoid.Pow.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (Complex.exp z) n)
but is expected to have type
  forall (z : Complex) (n : Int), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Int.cast.{0} Complex (Ring.toIntCast.{0} Complex Complex.instRingComplex) n) z)) (HPow.hPow.{0, 0, 0} Complex Int Complex (instHPow.{0, 0} Complex Int (DivInvMonoid.Pow.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.instFieldComplex)))) (Complex.exp z) n)
Case conversion may be inaccurate. Consider using '#align complex.exp_int_mul Complex.exp_int_mulₓ'. -/
theorem exp_int_mul (z : ℂ) (n : ℤ) : Complex.exp (n * z) = Complex.exp z ^ n :=
  by
  cases n
  · apply Complex.exp_nat_mul
  · simpa [Complex.exp_neg, add_comm, ← neg_mul] using Complex.exp_nat_mul (-z) (1 + n)
#align complex.exp_int_mul Complex.exp_int_mul

/- warning: complex.exp_conj -> Complex.exp_conj is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (Complex.exp (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) x)) (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) (Complex.exp x))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (Complex.exp (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalRingToNonUnitalCommRingCommRing) x)) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalRingToNonUnitalCommRingCommRing) (Complex.exp x))
Case conversion may be inaccurate. Consider using '#align complex.exp_conj Complex.exp_conjₓ'. -/
@[simp]
theorem exp_conj : exp (conj x) = conj (exp x) :=
  by
  dsimp [exp]
  rw [← lim_conj]
  refine' congr_arg limUnder (CauSeq.ext fun _ => _)
  dsimp [exp', Function.comp, cau_seq_conj]
  rw [(starRingEnd _).map_sum]
  refine' sum_congr rfl fun n hn => _
  rw [map_div₀, map_pow, ← of_real_nat_cast, conj_of_real]
#align complex.exp_conj Complex.exp_conj

/- warning: complex.of_real_exp_of_real_re -> Complex.ofReal_exp_ofReal_re is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.re (Complex.exp ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x)))) (Complex.exp ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} Complex (Complex.ofReal' (Complex.re (Complex.exp (Complex.ofReal' x)))) (Complex.exp (Complex.ofReal' x))
Case conversion may be inaccurate. Consider using '#align complex.of_real_exp_of_real_re Complex.ofReal_exp_ofReal_reₓ'. -/
@[simp]
theorem ofReal_exp_ofReal_re (x : ℝ) : ((exp x).re : ℂ) = exp x :=
  eq_conj_iff_re.1 <| by rw [← exp_conj, conj_of_real]
#align complex.of_real_exp_of_real_re Complex.ofReal_exp_ofReal_re

/- warning: complex.of_real_exp -> Complex.ofReal_exp is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.exp x)) (Complex.exp ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} Complex (Complex.ofReal' (Real.exp x)) (Complex.exp (Complex.ofReal' x))
Case conversion may be inaccurate. Consider using '#align complex.of_real_exp Complex.ofReal_expₓ'. -/
@[simp, norm_cast]
theorem ofReal_exp (x : ℝ) : (Real.exp x : ℂ) = exp x :=
  ofReal_exp_ofReal_re _
#align complex.of_real_exp Complex.ofReal_exp

/- warning: complex.exp_of_real_im -> Complex.exp_ofReal_im is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Complex.im (Complex.exp ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Complex.im (Complex.exp (Complex.ofReal' x))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align complex.exp_of_real_im Complex.exp_ofReal_imₓ'. -/
@[simp]
theorem exp_ofReal_im (x : ℝ) : (exp x).im = 0 := by rw [← of_real_exp_of_real_re, of_real_im]
#align complex.exp_of_real_im Complex.exp_ofReal_im

/- warning: complex.exp_of_real_re -> Complex.exp_ofReal_re is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Complex.re (Complex.exp ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))) (Real.exp x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Complex.re (Complex.exp (Complex.ofReal' x))) (Real.exp x)
Case conversion may be inaccurate. Consider using '#align complex.exp_of_real_re Complex.exp_ofReal_reₓ'. -/
theorem exp_ofReal_re (x : ℝ) : (exp x).re = Real.exp x :=
  rfl
#align complex.exp_of_real_re Complex.exp_ofReal_re

/- warning: complex.two_sinh -> Complex.two_sinh is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) (Complex.sinh x)) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp x) (Complex.exp (Neg.neg.{0} Complex Complex.hasNeg x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.sinh x)) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Complex.exp (Neg.neg.{0} Complex Complex.instNegComplex x)))
Case conversion may be inaccurate. Consider using '#align complex.two_sinh Complex.two_sinhₓ'. -/
theorem two_sinh : 2 * sinh x = exp x - exp (-x) :=
  mul_div_cancel' _ two_ne_zero
#align complex.two_sinh Complex.two_sinh

/- warning: complex.two_cosh -> Complex.two_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) (Complex.cosh x)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.exp x) (Complex.exp (Neg.neg.{0} Complex Complex.hasNeg x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.cosh x)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.exp x) (Complex.exp (Neg.neg.{0} Complex Complex.instNegComplex x)))
Case conversion may be inaccurate. Consider using '#align complex.two_cosh Complex.two_coshₓ'. -/
theorem two_cosh : 2 * cosh x = exp x + exp (-x) :=
  mul_div_cancel' _ two_ne_zero
#align complex.two_cosh Complex.two_cosh

#print Complex.sinh_zero /-
@[simp]
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]
#align complex.sinh_zero Complex.sinh_zero
-/

#print Complex.sinh_neg /-
@[simp]
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]
#align complex.sinh_neg Complex.sinh_neg
-/

private theorem sinh_add_aux {a b c d : ℂ} :
    (a - b) * (c + d) + (a + b) * (c - d) = 2 * (a * c - b * d) := by ring
#align complex.sinh_add_aux complex.sinh_add_aux

#print Complex.sinh_add /-
theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y :=
  by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_sinh, exp_add, neg_add, exp_add, eq_comm, mul_add, ←
    mul_assoc, two_sinh, mul_left_comm, two_sinh, ← mul_right_inj' (two_ne_zero' ℂ), mul_add,
    mul_left_comm, two_cosh, ← mul_assoc, two_cosh]
  exact sinh_add_aux
#align complex.sinh_add Complex.sinh_add
-/

#print Complex.cosh_zero /-
@[simp]
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]
#align complex.cosh_zero Complex.cosh_zero
-/

#print Complex.cosh_neg /-
@[simp]
theorem cosh_neg : cosh (-x) = cosh x := by simp [add_comm, cosh, exp_neg]
#align complex.cosh_neg Complex.cosh_neg
-/

private theorem cosh_add_aux {a b c d : ℂ} :
    (a + b) * (c + d) + (a - b) * (c - d) = 2 * (a * c + b * d) := by ring
#align complex.cosh_add_aux complex.cosh_add_aux

#print Complex.cosh_add /-
theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y :=
  by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_cosh, exp_add, neg_add, exp_add, eq_comm, mul_add, ←
    mul_assoc, two_cosh, ← mul_assoc, two_sinh, ← mul_right_inj' (two_ne_zero' ℂ), mul_add,
    mul_left_comm, two_cosh, mul_left_comm, two_sinh]
  exact cosh_add_aux
#align complex.cosh_add Complex.cosh_add
-/

#print Complex.sinh_sub /-
theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]
#align complex.sinh_sub Complex.sinh_sub
-/

#print Complex.cosh_sub /-
theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]
#align complex.cosh_sub Complex.cosh_sub
-/

#print Complex.sinh_conj /-
theorem sinh_conj : sinh (conj x) = conj (sinh x) := by
  rw [sinh, ← RingHom.map_neg, exp_conj, exp_conj, ← RingHom.map_sub, sinh, map_div₀, conj_bit0,
    RingHom.map_one]
#align complex.sinh_conj Complex.sinh_conj
-/

#print Complex.ofReal_sinh_ofReal_re /-
@[simp]
theorem ofReal_sinh_ofReal_re (x : ℝ) : ((sinh x).re : ℂ) = sinh x :=
  eq_conj_iff_re.1 <| by rw [← sinh_conj, conj_of_real]
#align complex.of_real_sinh_of_real_re Complex.ofReal_sinh_ofReal_re
-/

/- warning: complex.of_real_sinh -> Complex.ofReal_sinh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.sinh x)) (Complex.sinh ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} Complex (Complex.ofReal' (Real.sinh x)) (Complex.sinh (Complex.ofReal' x))
Case conversion may be inaccurate. Consider using '#align complex.of_real_sinh Complex.ofReal_sinhₓ'. -/
@[simp, norm_cast]
theorem ofReal_sinh (x : ℝ) : (Real.sinh x : ℂ) = sinh x :=
  ofReal_sinh_ofReal_re _
#align complex.of_real_sinh Complex.ofReal_sinh

#print Complex.sinh_of_real_im /-
@[simp]
theorem sinh_of_real_im (x : ℝ) : (sinh x).im = 0 := by rw [← of_real_sinh_of_real_re, of_real_im]
#align complex.sinh_of_real_im Complex.sinh_of_real_im
-/

#print Complex.sinh_of_real_re /-
theorem sinh_of_real_re (x : ℝ) : (sinh x).re = Real.sinh x :=
  rfl
#align complex.sinh_of_real_re Complex.sinh_of_real_re
-/

#print Complex.cosh_conj /-
theorem cosh_conj : cosh (conj x) = conj (cosh x) := by
  rw [cosh, ← RingHom.map_neg, exp_conj, exp_conj, ← RingHom.map_add, cosh, map_div₀, conj_bit0,
    RingHom.map_one]
#align complex.cosh_conj Complex.cosh_conj
-/

#print Complex.ofReal_cosh_ofReal_re /-
theorem ofReal_cosh_ofReal_re (x : ℝ) : ((cosh x).re : ℂ) = cosh x :=
  eq_conj_iff_re.1 <| by rw [← cosh_conj, conj_of_real]
#align complex.of_real_cosh_of_real_re Complex.ofReal_cosh_ofReal_re
-/

/- warning: complex.of_real_cosh -> Complex.ofReal_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.cosh x)) (Complex.cosh ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} Complex (Complex.ofReal' (Real.cosh x)) (Complex.cosh (Complex.ofReal' x))
Case conversion may be inaccurate. Consider using '#align complex.of_real_cosh Complex.ofReal_coshₓ'. -/
@[simp, norm_cast]
theorem ofReal_cosh (x : ℝ) : (Real.cosh x : ℂ) = cosh x :=
  ofReal_cosh_ofReal_re _
#align complex.of_real_cosh Complex.ofReal_cosh

#print Complex.cosh_ofReal_im /-
@[simp]
theorem cosh_ofReal_im (x : ℝ) : (cosh x).im = 0 := by rw [← of_real_cosh_of_real_re, of_real_im]
#align complex.cosh_of_real_im Complex.cosh_ofReal_im
-/

#print Complex.cosh_ofReal_re /-
@[simp]
theorem cosh_ofReal_re (x : ℝ) : (cosh x).re = Real.cosh x :=
  rfl
#align complex.cosh_of_real_re Complex.cosh_ofReal_re
-/

/- warning: complex.tanh_eq_sinh_div_cosh -> Complex.tanh_eq_sinh_div_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (Complex.tanh x) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (Complex.sinh x) (Complex.cosh x))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (Complex.tanh x) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (Complex.sinh x) (Complex.cosh x))
Case conversion may be inaccurate. Consider using '#align complex.tanh_eq_sinh_div_cosh Complex.tanh_eq_sinh_div_coshₓ'. -/
theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  rfl
#align complex.tanh_eq_sinh_div_cosh Complex.tanh_eq_sinh_div_cosh

#print Complex.tanh_zero /-
@[simp]
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]
#align complex.tanh_zero Complex.tanh_zero
-/

#print Complex.tanh_neg /-
@[simp]
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]
#align complex.tanh_neg Complex.tanh_neg
-/

#print Complex.tanh_conj /-
theorem tanh_conj : tanh (conj x) = conj (tanh x) := by
  rw [tanh, sinh_conj, cosh_conj, ← map_div₀, tanh]
#align complex.tanh_conj Complex.tanh_conj
-/

#print Complex.ofReal_tanh_ofReal_re /-
@[simp]
theorem ofReal_tanh_ofReal_re (x : ℝ) : ((tanh x).re : ℂ) = tanh x :=
  eq_conj_iff_re.1 <| by rw [← tanh_conj, conj_of_real]
#align complex.of_real_tanh_of_real_re Complex.ofReal_tanh_ofReal_re
-/

/- warning: complex.of_real_tanh -> Complex.ofReal_tanh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.tanh x)) (Complex.tanh ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} Complex (Complex.ofReal' (Real.tanh x)) (Complex.tanh (Complex.ofReal' x))
Case conversion may be inaccurate. Consider using '#align complex.of_real_tanh Complex.ofReal_tanhₓ'. -/
@[simp, norm_cast]
theorem ofReal_tanh (x : ℝ) : (Real.tanh x : ℂ) = tanh x :=
  ofReal_tanh_ofReal_re _
#align complex.of_real_tanh Complex.ofReal_tanh

#print Complex.tanh_ofReal_im /-
@[simp]
theorem tanh_ofReal_im (x : ℝ) : (tanh x).im = 0 := by rw [← of_real_tanh_of_real_re, of_real_im]
#align complex.tanh_of_real_im Complex.tanh_ofReal_im
-/

#print Complex.tanh_ofReal_re /-
theorem tanh_ofReal_re (x : ℝ) : (tanh x).re = Real.tanh x :=
  rfl
#align complex.tanh_of_real_re Complex.tanh_ofReal_re
-/

/- warning: complex.cosh_add_sinh -> Complex.cosh_add_sinh is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cosh x) (Complex.sinh x)) (Complex.exp x)
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cosh x) (Complex.sinh x)) (Complex.exp x)
Case conversion may be inaccurate. Consider using '#align complex.cosh_add_sinh Complex.cosh_add_sinhₓ'. -/
@[simp]
theorem cosh_add_sinh : cosh x + sinh x = exp x := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), mul_add, two_cosh, two_sinh, add_add_sub_cancel, two_mul]
#align complex.cosh_add_sinh Complex.cosh_add_sinh

/- warning: complex.sinh_add_cosh -> Complex.sinh_add_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.sinh x) (Complex.cosh x)) (Complex.exp x)
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.sinh x) (Complex.cosh x)) (Complex.exp x)
Case conversion may be inaccurate. Consider using '#align complex.sinh_add_cosh Complex.sinh_add_coshₓ'. -/
@[simp]
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]
#align complex.sinh_add_cosh Complex.sinh_add_cosh

/- warning: complex.exp_sub_cosh -> Complex.exp_sub_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp x) (Complex.cosh x)) (Complex.sinh x)
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Complex.cosh x)) (Complex.sinh x)
Case conversion may be inaccurate. Consider using '#align complex.exp_sub_cosh Complex.exp_sub_coshₓ'. -/
@[simp]
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm
#align complex.exp_sub_cosh Complex.exp_sub_cosh

/- warning: complex.exp_sub_sinh -> Complex.exp_sub_sinh is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp x) (Complex.sinh x)) (Complex.cosh x)
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Complex.sinh x)) (Complex.cosh x)
Case conversion may be inaccurate. Consider using '#align complex.exp_sub_sinh Complex.exp_sub_sinhₓ'. -/
@[simp]
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm
#align complex.exp_sub_sinh Complex.exp_sub_sinh

/- warning: complex.cosh_sub_sinh -> Complex.cosh_sub_sinh is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.cosh x) (Complex.sinh x)) (Complex.exp (Neg.neg.{0} Complex Complex.hasNeg x))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.cosh x) (Complex.sinh x)) (Complex.exp (Neg.neg.{0} Complex Complex.instNegComplex x))
Case conversion may be inaccurate. Consider using '#align complex.cosh_sub_sinh Complex.cosh_sub_sinhₓ'. -/
@[simp]
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), mul_sub, two_cosh, two_sinh, add_sub_sub_cancel, two_mul]
#align complex.cosh_sub_sinh Complex.cosh_sub_sinh

/- warning: complex.sinh_sub_cosh -> Complex.sinh_sub_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.sinh x) (Complex.cosh x)) (Neg.neg.{0} Complex Complex.hasNeg (Complex.exp (Neg.neg.{0} Complex Complex.hasNeg x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.sinh x) (Complex.cosh x)) (Neg.neg.{0} Complex Complex.instNegComplex (Complex.exp (Neg.neg.{0} Complex Complex.instNegComplex x)))
Case conversion may be inaccurate. Consider using '#align complex.sinh_sub_cosh Complex.sinh_sub_coshₓ'. -/
@[simp]
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]
#align complex.sinh_sub_cosh Complex.sinh_sub_cosh

/- warning: complex.cosh_sq_sub_sinh_sq -> Complex.cosh_sq_sub_sinh_sq is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.cosh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.sinh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.cosh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.sinh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))
Case conversion may be inaccurate. Consider using '#align complex.cosh_sq_sub_sinh_sq Complex.cosh_sq_sub_sinh_sqₓ'. -/
@[simp]
theorem cosh_sq_sub_sinh_sq : cosh x ^ 2 - sinh x ^ 2 = 1 := by
  rw [sq_sub_sq, cosh_add_sinh, cosh_sub_sinh, ← exp_add, add_neg_self, exp_zero]
#align complex.cosh_sq_sub_sinh_sq Complex.cosh_sq_sub_sinh_sq

/- warning: complex.cosh_sq -> Complex.cosh_sq is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.cosh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.sinh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.cosh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.sinh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))
Case conversion may be inaccurate. Consider using '#align complex.cosh_sq Complex.cosh_sqₓ'. -/
theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 :=
  by
  rw [← cosh_sq_sub_sinh_sq x]
  ring
#align complex.cosh_sq Complex.cosh_sq

/- warning: complex.sinh_sq -> Complex.sinh_sq is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.sinh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.cosh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.sinh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.cosh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))
Case conversion may be inaccurate. Consider using '#align complex.sinh_sq Complex.sinh_sqₓ'. -/
theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 :=
  by
  rw [← cosh_sq_sub_sinh_sq x]
  ring
#align complex.sinh_sq Complex.sinh_sq

#print Complex.cosh_two_mul /-
theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by rw [two_mul, cosh_add, sq, sq]
#align complex.cosh_two_mul Complex.cosh_two_mul
-/

#print Complex.sinh_two_mul /-
theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x :=
  by
  rw [two_mul, sinh_add]
  ring
#align complex.sinh_two_mul Complex.sinh_two_mul
-/

#print Complex.cosh_three_mul /-
theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x :=
  by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, cosh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : sinh x * (2 * sinh x * cosh x) = 2 * cosh x * sinh x ^ 2 := by ring
  rw [h2, sinh_sq]
  ring
#align complex.cosh_three_mul Complex.cosh_three_mul
-/

#print Complex.sinh_three_mul /-
theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x :=
  by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, sinh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : cosh x * (2 * sinh x * cosh x) = 2 * sinh x * cosh x ^ 2 := by ring
  rw [h2, cosh_sq]
  ring
#align complex.sinh_three_mul Complex.sinh_three_mul
-/

#print Complex.sin_zero /-
@[simp]
theorem sin_zero : sin 0 = 0 := by simp [sin]
#align complex.sin_zero Complex.sin_zero
-/

#print Complex.sin_neg /-
@[simp]
theorem sin_neg : sin (-x) = -sin x := by
  simp [sin, sub_eq_add_neg, exp_neg, (neg_div _ _).symm, add_mul]
#align complex.sin_neg Complex.sin_neg
-/

/- warning: complex.two_sin -> Complex.two_sin is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) (Complex.sin x)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Neg.neg.{0} Complex Complex.hasNeg x) Complex.I)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) x Complex.I))) Complex.I)
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.sin x)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Neg.neg.{0} Complex Complex.instNegComplex x) Complex.I)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) x Complex.I))) Complex.I)
Case conversion may be inaccurate. Consider using '#align complex.two_sin Complex.two_sinₓ'. -/
theorem two_sin : 2 * sin x = (exp (-x * I) - exp (x * I)) * I :=
  mul_div_cancel' _ two_ne_zero
#align complex.two_sin Complex.two_sin

/- warning: complex.two_cos -> Complex.two_cos is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) (Complex.cos x)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) x Complex.I)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Neg.neg.{0} Complex Complex.hasNeg x) Complex.I)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.cos x)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) x Complex.I)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Neg.neg.{0} Complex Complex.instNegComplex x) Complex.I)))
Case conversion may be inaccurate. Consider using '#align complex.two_cos Complex.two_cosₓ'. -/
theorem two_cos : 2 * cos x = exp (x * I) + exp (-x * I) :=
  mul_div_cancel' _ two_ne_zero
#align complex.two_cos Complex.two_cos

#print Complex.sinh_mul_I /-
theorem sinh_mul_I : sinh (x * I) = sin x * I := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_sinh, ← mul_assoc, two_sin, mul_assoc, I_mul_I,
    mul_neg_one, neg_sub, neg_mul_eq_neg_mul]
#align complex.sinh_mul_I Complex.sinh_mul_I
-/

#print Complex.cosh_mul_I /-
theorem cosh_mul_I : cosh (x * I) = cos x := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_cosh, two_cos, neg_mul_eq_neg_mul]
#align complex.cosh_mul_I Complex.cosh_mul_I
-/

#print Complex.tanh_mul_I /-
theorem tanh_mul_I : tanh (x * I) = tan x * I := by
  rw [tanh_eq_sinh_div_cosh, cosh_mul_I, sinh_mul_I, mul_div_right_comm, tan]
#align complex.tanh_mul_I Complex.tanh_mul_I
-/

#print Complex.cos_mul_I /-
theorem cos_mul_I : cos (x * I) = cosh x := by rw [← cosh_mul_I] <;> ring_nf <;> simp
#align complex.cos_mul_I Complex.cos_mul_I
-/

#print Complex.sin_mul_I /-
theorem sin_mul_I : sin (x * I) = sinh x * I :=
  by
  have h : I * sin (x * I) = -sinh x :=
    by
    rw [mul_comm, ← sinh_mul_I]
    ring_nf
    simp
  simpa only [neg_mul, div_I, neg_neg] using CancelFactors.cancel_factors_eq_div h I_ne_zero
#align complex.sin_mul_I Complex.sin_mul_I
-/

#print Complex.tan_mul_I /-
theorem tan_mul_I : tan (x * I) = tanh x * I := by
  rw [tan, sin_mul_I, cos_mul_I, mul_div_right_comm, tanh_eq_sinh_div_cosh]
#align complex.tan_mul_I Complex.tan_mul_I
-/

#print Complex.sin_add /-
theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y := by
  rw [← mul_left_inj' I_ne_zero, ← sinh_mul_I, add_mul, add_mul, mul_right_comm, ← sinh_mul_I,
    mul_assoc, ← sinh_mul_I, ← cosh_mul_I, ← cosh_mul_I, sinh_add]
#align complex.sin_add Complex.sin_add
-/

#print Complex.cos_zero /-
@[simp]
theorem cos_zero : cos 0 = 1 := by simp [cos]
#align complex.cos_zero Complex.cos_zero
-/

#print Complex.cos_neg /-
@[simp]
theorem cos_neg : cos (-x) = cos x := by simp [cos, sub_eq_add_neg, exp_neg, add_comm]
#align complex.cos_neg Complex.cos_neg
-/

private theorem cos_add_aux {a b c d : ℂ} :
    (a + b) * (c + d) - (b - a) * (d - c) * -1 = 2 * (a * c + b * d) := by ring
#align complex.cos_add_aux complex.cos_add_aux

#print Complex.cos_add /-
theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y := by
  rw [← cosh_mul_I, add_mul, cosh_add, cosh_mul_I, cosh_mul_I, sinh_mul_I, sinh_mul_I,
    mul_mul_mul_comm, I_mul_I, mul_neg_one, sub_eq_add_neg]
#align complex.cos_add Complex.cos_add
-/

#print Complex.sin_sub /-
theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]
#align complex.sin_sub Complex.sin_sub
-/

#print Complex.cos_sub /-
theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]
#align complex.cos_sub Complex.cos_sub
-/

#print Complex.sin_add_mul_I /-
theorem sin_add_mul_I (x y : ℂ) : sin (x + y * I) = sin x * cosh y + cos x * sinh y * I := by
  rw [sin_add, cos_mul_I, sin_mul_I, mul_assoc]
#align complex.sin_add_mul_I Complex.sin_add_mul_I
-/

/- warning: complex.sin_eq -> Complex.sin_eq is a dubious translation:
lean 3 declaration is
  forall (z : Complex), Eq.{1} Complex (Complex.sin z) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.re z))) (Complex.cosh ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.im z)))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.re z))) (Complex.sinh ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.im z)))) Complex.I))
but is expected to have type
  forall (z : Complex), Eq.{1} Complex (Complex.sin z) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' (Complex.re z))) (Complex.cosh (Complex.ofReal' (Complex.im z)))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.cos (Complex.ofReal' (Complex.re z))) (Complex.sinh (Complex.ofReal' (Complex.im z)))) Complex.I))
Case conversion may be inaccurate. Consider using '#align complex.sin_eq Complex.sin_eqₓ'. -/
theorem sin_eq (z : ℂ) : sin z = sin z.re * cosh z.im + cos z.re * sinh z.im * I := by
  convert sin_add_mul_I z.re z.im <;> exact (re_add_im z).symm
#align complex.sin_eq Complex.sin_eq

#print Complex.cos_add_mul_I /-
theorem cos_add_mul_I (x y : ℂ) : cos (x + y * I) = cos x * cosh y - sin x * sinh y * I := by
  rw [cos_add, cos_mul_I, sin_mul_I, mul_assoc]
#align complex.cos_add_mul_I Complex.cos_add_mul_I
-/

/- warning: complex.cos_eq -> Complex.cos_eq is a dubious translation:
lean 3 declaration is
  forall (z : Complex), Eq.{1} Complex (Complex.cos z) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.re z))) (Complex.cosh ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.im z)))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.re z))) (Complex.sinh ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.im z)))) Complex.I))
but is expected to have type
  forall (z : Complex), Eq.{1} Complex (Complex.cos z) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.cos (Complex.ofReal' (Complex.re z))) (Complex.cosh (Complex.ofReal' (Complex.im z)))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' (Complex.re z))) (Complex.sinh (Complex.ofReal' (Complex.im z)))) Complex.I))
Case conversion may be inaccurate. Consider using '#align complex.cos_eq Complex.cos_eqₓ'. -/
theorem cos_eq (z : ℂ) : cos z = cos z.re * cosh z.im - sin z.re * sinh z.im * I := by
  convert cos_add_mul_I z.re z.im <;> exact (re_add_im z).symm
#align complex.cos_eq Complex.cos_eq

/- warning: complex.sin_sub_sin -> Complex.sin_sub_sin is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.sin x) (Complex.sin y)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) (Complex.sin (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) x y) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne))))))) (Complex.cos (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) x y) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))))))
but is expected to have type
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.sin x) (Complex.sin y)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.sin (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) x y) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Complex.cos (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) x y) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))
Case conversion may be inaccurate. Consider using '#align complex.sin_sub_sin Complex.sin_sub_sinₓ'. -/
theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) :=
  by
  have s1 := sin_add ((x + y) / 2) ((x - y) / 2)
  have s2 := sin_sub ((x + y) / 2) ((x - y) / 2)
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel, half_add_self] at s1
  rw [div_sub_div_same, ← sub_add, add_sub_cancel', half_add_self] at s2
  rw [s1, s2]
  ring
#align complex.sin_sub_sin Complex.sin_sub_sin

/- warning: complex.cos_sub_cos -> Complex.cos_sub_cos is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.cos x) (Complex.cos y)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Neg.neg.{0} Complex Complex.hasNeg (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne))))) (Complex.sin (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) x y) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne))))))) (Complex.sin (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) x y) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))))))
but is expected to have type
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.cos x) (Complex.cos y)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Neg.neg.{0} Complex Complex.instNegComplex (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Complex.sin (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) x y) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Complex.sin (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) x y) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))
Case conversion may be inaccurate. Consider using '#align complex.cos_sub_cos Complex.cos_sub_cosₓ'. -/
theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) :=
  by
  have s1 := cos_add ((x + y) / 2) ((x - y) / 2)
  have s2 := cos_sub ((x + y) / 2) ((x - y) / 2)
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel, half_add_self] at s1
  rw [div_sub_div_same, ← sub_add, add_sub_cancel', half_add_self] at s2
  rw [s1, s2]
  ring
#align complex.cos_sub_cos Complex.cos_sub_cos

/- warning: complex.cos_add_cos -> Complex.cos_add_cos is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos x) (Complex.cos y)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) (Complex.cos (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) x y) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne))))))) (Complex.cos (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) x y) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))))))
but is expected to have type
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos x) (Complex.cos y)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.cos (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) x y) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Complex.cos (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) x y) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))
Case conversion may be inaccurate. Consider using '#align complex.cos_add_cos Complex.cos_add_cosₓ'. -/
theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) :=
  by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  calc
    cos x + cos y = cos ((x + y) / 2 + (x - y) / 2) + cos ((x + y) / 2 - (x - y) / 2) := _
    _ =
        cos ((x + y) / 2) * cos ((x - y) / 2) - sin ((x + y) / 2) * sin ((x - y) / 2) +
          (cos ((x + y) / 2) * cos ((x - y) / 2) + sin ((x + y) / 2) * sin ((x - y) / 2)) :=
      _
    _ = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := _
    
  · congr <;> field_simp [h2] <;> ring
  · rw [cos_add, cos_sub]
  ring
#align complex.cos_add_cos Complex.cos_add_cos

#print Complex.sin_conj /-
theorem sin_conj : sin (conj x) = conj (sin x) := by
  rw [← mul_left_inj' I_ne_zero, ← sinh_mul_I, ← conj_neg_I, ← RingHom.map_mul, ← RingHom.map_mul,
    sinh_conj, mul_neg, sinh_neg, sinh_mul_I, mul_neg]
#align complex.sin_conj Complex.sin_conj
-/

#print Complex.ofReal_sin_ofReal_re /-
@[simp]
theorem ofReal_sin_ofReal_re (x : ℝ) : ((sin x).re : ℂ) = sin x :=
  eq_conj_iff_re.1 <| by rw [← sin_conj, conj_of_real]
#align complex.of_real_sin_of_real_re Complex.ofReal_sin_ofReal_re
-/

/- warning: complex.of_real_sin -> Complex.ofReal_sin is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.sin x)) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} Complex (Complex.ofReal' (Real.sin x)) (Complex.sin (Complex.ofReal' x))
Case conversion may be inaccurate. Consider using '#align complex.of_real_sin Complex.ofReal_sinₓ'. -/
@[simp, norm_cast]
theorem ofReal_sin (x : ℝ) : (Real.sin x : ℂ) = sin x :=
  ofReal_sin_ofReal_re _
#align complex.of_real_sin Complex.ofReal_sin

#print Complex.sin_ofReal_im /-
@[simp]
theorem sin_ofReal_im (x : ℝ) : (sin x).im = 0 := by rw [← of_real_sin_of_real_re, of_real_im]
#align complex.sin_of_real_im Complex.sin_ofReal_im
-/

#print Complex.sin_ofReal_re /-
theorem sin_ofReal_re (x : ℝ) : (sin x).re = Real.sin x :=
  rfl
#align complex.sin_of_real_re Complex.sin_ofReal_re
-/

#print Complex.cos_conj /-
theorem cos_conj : cos (conj x) = conj (cos x) := by
  rw [← cosh_mul_I, ← conj_neg_I, ← RingHom.map_mul, ← cosh_mul_I, cosh_conj, mul_neg, cosh_neg]
#align complex.cos_conj Complex.cos_conj
-/

#print Complex.ofReal_cos_ofReal_re /-
@[simp]
theorem ofReal_cos_ofReal_re (x : ℝ) : ((cos x).re : ℂ) = cos x :=
  eq_conj_iff_re.1 <| by rw [← cos_conj, conj_of_real]
#align complex.of_real_cos_of_real_re Complex.ofReal_cos_ofReal_re
-/

/- warning: complex.of_real_cos -> Complex.ofReal_cos is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.cos x)) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} Complex (Complex.ofReal' (Real.cos x)) (Complex.cos (Complex.ofReal' x))
Case conversion may be inaccurate. Consider using '#align complex.of_real_cos Complex.ofReal_cosₓ'. -/
@[simp, norm_cast]
theorem ofReal_cos (x : ℝ) : (Real.cos x : ℂ) = cos x :=
  ofReal_cos_ofReal_re _
#align complex.of_real_cos Complex.ofReal_cos

#print Complex.cos_ofReal_im /-
@[simp]
theorem cos_ofReal_im (x : ℝ) : (cos x).im = 0 := by rw [← of_real_cos_of_real_re, of_real_im]
#align complex.cos_of_real_im Complex.cos_ofReal_im
-/

#print Complex.cos_ofReal_re /-
theorem cos_ofReal_re (x : ℝ) : (cos x).re = Real.cos x :=
  rfl
#align complex.cos_of_real_re Complex.cos_ofReal_re
-/

#print Complex.tan_zero /-
@[simp]
theorem tan_zero : tan 0 = 0 := by simp [tan]
#align complex.tan_zero Complex.tan_zero
-/

/- warning: complex.tan_eq_sin_div_cos -> Complex.tan_eq_sin_div_cos is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (Complex.tan x) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (Complex.sin x) (Complex.cos x))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (Complex.tan x) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (Complex.sin x) (Complex.cos x))
Case conversion may be inaccurate. Consider using '#align complex.tan_eq_sin_div_cos Complex.tan_eq_sin_div_cosₓ'. -/
theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  rfl
#align complex.tan_eq_sin_div_cos Complex.tan_eq_sin_div_cos

/- warning: complex.tan_mul_cos -> Complex.tan_mul_cos is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Ne.{1} Complex (Complex.cos x) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.tan x) (Complex.cos x)) (Complex.sin x))
but is expected to have type
  forall {x : Complex}, (Ne.{1} Complex (Complex.cos x) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.tan x) (Complex.cos x)) (Complex.sin x))
Case conversion may be inaccurate. Consider using '#align complex.tan_mul_cos Complex.tan_mul_cosₓ'. -/
theorem tan_mul_cos {x : ℂ} (hx : cos x ≠ 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos, div_mul_cancel _ hx]
#align complex.tan_mul_cos Complex.tan_mul_cos

#print Complex.tan_neg /-
@[simp]
theorem tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]
#align complex.tan_neg Complex.tan_neg
-/

#print Complex.tan_conj /-
theorem tan_conj : tan (conj x) = conj (tan x) := by rw [tan, sin_conj, cos_conj, ← map_div₀, tan]
#align complex.tan_conj Complex.tan_conj
-/

#print Complex.ofReal_tan_ofReal_re /-
@[simp]
theorem ofReal_tan_ofReal_re (x : ℝ) : ((tan x).re : ℂ) = tan x :=
  eq_conj_iff_re.1 <| by rw [← tan_conj, conj_of_real]
#align complex.of_real_tan_of_real_re Complex.ofReal_tan_ofReal_re
-/

/- warning: complex.of_real_tan -> Complex.ofReal_tan is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.tan x)) (Complex.tan ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} Complex (Complex.ofReal' (Real.tan x)) (Complex.tan (Complex.ofReal' x))
Case conversion may be inaccurate. Consider using '#align complex.of_real_tan Complex.ofReal_tanₓ'. -/
@[simp, norm_cast]
theorem ofReal_tan (x : ℝ) : (Real.tan x : ℂ) = tan x :=
  ofReal_tan_ofReal_re _
#align complex.of_real_tan Complex.ofReal_tan

#print Complex.tan_of_real_im /-
@[simp]
theorem tan_of_real_im (x : ℝ) : (tan x).im = 0 := by rw [← of_real_tan_of_real_re, of_real_im]
#align complex.tan_of_real_im Complex.tan_of_real_im
-/

#print Complex.tan_of_real_re /-
theorem tan_of_real_re (x : ℝ) : (tan x).re = Real.tan x :=
  rfl
#align complex.tan_of_real_re Complex.tan_of_real_re
-/

/- warning: complex.cos_add_sin_I -> Complex.cos_add_sin_I is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos x) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin x) Complex.I)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) x Complex.I))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos x) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin x) Complex.I)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) x Complex.I))
Case conversion may be inaccurate. Consider using '#align complex.cos_add_sin_I Complex.cos_add_sin_Iₓ'. -/
theorem cos_add_sin_I : cos x + sin x * I = exp (x * I) := by
  rw [← cosh_add_sinh, sinh_mul_I, cosh_mul_I]
#align complex.cos_add_sin_I Complex.cos_add_sin_I

/- warning: complex.cos_sub_sin_I -> Complex.cos_sub_sin_I is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.cos x) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin x) Complex.I)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Neg.neg.{0} Complex Complex.hasNeg x) Complex.I))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.cos x) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin x) Complex.I)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Neg.neg.{0} Complex Complex.instNegComplex x) Complex.I))
Case conversion may be inaccurate. Consider using '#align complex.cos_sub_sin_I Complex.cos_sub_sin_Iₓ'. -/
theorem cos_sub_sin_I : cos x - sin x * I = exp (-x * I) := by
  rw [neg_mul, ← cosh_sub_sinh, sinh_mul_I, cosh_mul_I]
#align complex.cos_sub_sin_I Complex.cos_sub_sin_I

/- warning: complex.sin_sq_add_cos_sq -> Complex.sin_sq_add_cos_sq is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))
Case conversion may be inaccurate. Consider using '#align complex.sin_sq_add_cos_sq Complex.sin_sq_add_cos_sqₓ'. -/
@[simp]
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  Eq.trans (by rw [cosh_mul_I, sinh_mul_I, mul_pow, I_sq, mul_neg_one, sub_neg_eq_add, add_comm])
    (cosh_sq_sub_sinh_sq (x * I))
#align complex.sin_sq_add_cos_sq Complex.sin_sq_add_cos_sq

/- warning: complex.cos_sq_add_sin_sq -> Complex.cos_sq_add_sin_sq is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))
Case conversion may be inaccurate. Consider using '#align complex.cos_sq_add_sin_sq Complex.cos_sq_add_sin_sqₓ'. -/
@[simp]
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]
#align complex.cos_sq_add_sin_sq Complex.cos_sq_add_sin_sq

#print Complex.cos_two_mul' /-
theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by rw [two_mul, cos_add, ← sq, ← sq]
#align complex.cos_two_mul' Complex.cos_two_mul'
-/

#print Complex.cos_two_mul /-
theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
  rw [cos_two_mul', eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x), ← sub_add, sub_add_eq_add_sub,
    two_mul]
#align complex.cos_two_mul Complex.cos_two_mul
-/

#print Complex.sin_two_mul /-
theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x := by
  rw [two_mul, sin_add, two_mul, add_mul, mul_comm]
#align complex.sin_two_mul Complex.sin_two_mul
-/

/- warning: complex.cos_sq -> Complex.cos_sq is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne))))) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (Complex.cos (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) x)) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne))))))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (Complex.cos (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) x)) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align complex.cos_sq Complex.cos_sqₓ'. -/
theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 := by
  simp [cos_two_mul, div_add_div_same, mul_div_cancel_left, two_ne_zero, -one_div]
#align complex.cos_sq Complex.cos_sq

/- warning: complex.cos_sq' -> Complex.cos_sq' is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align complex.cos_sq' Complex.cos_sq'ₓ'. -/
theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel']
#align complex.cos_sq' Complex.cos_sq'

/- warning: complex.sin_sq -> Complex.sin_sq is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align complex.sin_sq Complex.sin_sqₓ'. -/
theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel]
#align complex.sin_sq Complex.sin_sq

/- warning: complex.inv_one_add_tan_sq -> Complex.inv_one_add_tan_sq is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Ne.{1} Complex (Complex.cos x) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Complex (Inv.inv.{0} Complex Complex.hasInv (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.tan x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {x : Complex}, (Ne.{1} Complex (Complex.cos x) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Complex (Inv.inv.{0} Complex Complex.instInvComplex (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.tan x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align complex.inv_one_add_tan_sq Complex.inv_one_add_tan_sqₓ'. -/
theorem inv_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 :=
  by
  have : cos x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  rw [tan_eq_sin_div_cos, div_pow]
  field_simp [this]
#align complex.inv_one_add_tan_sq Complex.inv_one_add_tan_sq

/- warning: complex.tan_sq_div_one_add_tan_sq -> Complex.tan_sq_div_one_add_tan_sq is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Ne.{1} Complex (Complex.cos x) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Complex (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.tan x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.tan x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {x : Complex}, (Ne.{1} Complex (Complex.cos x) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Complex (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.tan x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.tan x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Complex.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align complex.tan_sq_div_one_add_tan_sq Complex.tan_sq_div_one_add_tan_sqₓ'. -/
theorem tan_sq_div_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]
#align complex.tan_sq_div_one_add_tan_sq Complex.tan_sq_div_one_add_tan_sq

#print Complex.cos_three_mul /-
theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x :=
  by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, cos_add x (2 * x)]
  simp only [cos_two_mul, sin_two_mul, mul_add, mul_sub, mul_one, sq]
  have h2 : 4 * cos x ^ 3 = 2 * cos x * cos x * cos x + 2 * cos x * cos x ^ 2 := by ring
  rw [h2, cos_sq']
  ring
#align complex.cos_three_mul Complex.cos_three_mul
-/

#print Complex.sin_three_mul /-
theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 :=
  by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, sin_add x (2 * x)]
  simp only [cos_two_mul, sin_two_mul, cos_sq']
  have h2 : cos x * (2 * sin x * cos x) = 2 * sin x * cos x ^ 2 := by ring
  rw [h2, cos_sq']
  ring
#align complex.sin_three_mul Complex.sin_three_mul
-/

/- warning: complex.exp_mul_I -> Complex.exp_mul_I is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) x Complex.I)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos x) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin x) Complex.I))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) x Complex.I)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos x) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin x) Complex.I))
Case conversion may be inaccurate. Consider using '#align complex.exp_mul_I Complex.exp_mul_Iₓ'. -/
theorem exp_mul_I : exp (x * I) = cos x + sin x * I :=
  (cos_add_sin_I _).symm
#align complex.exp_mul_I Complex.exp_mul_I

/- warning: complex.exp_add_mul_I -> Complex.exp_add_mul_I is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Complex), Eq.{1} Complex (Complex.exp (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) x (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) y Complex.I))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.exp x) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos y) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin y) Complex.I)))
but is expected to have type
  forall (x : Complex) (y : Complex), Eq.{1} Complex (Complex.exp (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) x (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) y Complex.I))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.exp x) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos y) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin y) Complex.I)))
Case conversion may be inaccurate. Consider using '#align complex.exp_add_mul_I Complex.exp_add_mul_Iₓ'. -/
theorem exp_add_mul_I : exp (x + y * I) = exp x * (cos y + sin y * I) := by rw [exp_add, exp_mul_I]
#align complex.exp_add_mul_I Complex.exp_add_mul_I

/- warning: complex.exp_eq_exp_re_mul_sin_add_cos -> Complex.exp_eq_exp_re_mul_sin_add_cos is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (Complex.exp x) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.exp ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.re x))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.im x))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.im x))) Complex.I)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (Complex.exp x) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.exp (Complex.ofReal' (Complex.re x))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' (Complex.im x))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' (Complex.im x))) Complex.I)))
Case conversion may be inaccurate. Consider using '#align complex.exp_eq_exp_re_mul_sin_add_cos Complex.exp_eq_exp_re_mul_sin_add_cosₓ'. -/
theorem exp_eq_exp_re_mul_sin_add_cos : exp x = exp x.re * (cos x.im + sin x.im * I) := by
  rw [← exp_add_mul_I, re_add_im]
#align complex.exp_eq_exp_re_mul_sin_add_cos Complex.exp_eq_exp_re_mul_sin_add_cos

/- warning: complex.exp_re -> Complex.exp_re is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Real (Complex.re (Complex.exp x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.exp (Complex.re x)) (Real.cos (Complex.im x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Real (Complex.re (Complex.exp x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.exp (Complex.re x)) (Real.cos (Complex.im x)))
Case conversion may be inaccurate. Consider using '#align complex.exp_re Complex.exp_reₓ'. -/
theorem exp_re : (exp x).re = Real.exp x.re * Real.cos x.im :=
  by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_of_real_re, cos_of_real_re]
#align complex.exp_re Complex.exp_re

/- warning: complex.exp_im -> Complex.exp_im is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Real (Complex.im (Complex.exp x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.exp (Complex.re x)) (Real.sin (Complex.im x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Real (Complex.im (Complex.exp x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.exp (Complex.re x)) (Real.sin (Complex.im x)))
Case conversion may be inaccurate. Consider using '#align complex.exp_im Complex.exp_imₓ'. -/
theorem exp_im : (exp x).im = Real.exp x.re * Real.sin x.im :=
  by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_of_real_re, sin_of_real_re]
#align complex.exp_im Complex.exp_im

/- warning: complex.exp_of_real_mul_I_re -> Complex.exp_ofReal_mul_I_re is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Complex.re (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) Complex.I))) (Real.cos x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Complex.re (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' x) Complex.I))) (Real.cos x)
Case conversion may be inaccurate. Consider using '#align complex.exp_of_real_mul_I_re Complex.exp_ofReal_mul_I_reₓ'. -/
@[simp]
theorem exp_ofReal_mul_I_re (x : ℝ) : (exp (x * I)).re = Real.cos x := by
  simp [exp_mul_I, cos_of_real_re]
#align complex.exp_of_real_mul_I_re Complex.exp_ofReal_mul_I_re

/- warning: complex.exp_of_real_mul_I_im -> Complex.exp_ofReal_mul_I_im is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Complex.im (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) Complex.I))) (Real.sin x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Complex.im (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' x) Complex.I))) (Real.sin x)
Case conversion may be inaccurate. Consider using '#align complex.exp_of_real_mul_I_im Complex.exp_ofReal_mul_I_imₓ'. -/
@[simp]
theorem exp_ofReal_mul_I_im (x : ℝ) : (exp (x * I)).im = Real.sin x := by
  simp [exp_mul_I, sin_of_real_re]
#align complex.exp_of_real_mul_I_im Complex.exp_ofReal_mul_I_im

/- warning: complex.cos_add_sin_mul_I_pow -> Complex.cos_add_sin_mul_I_pow is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (z : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos z) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin z) Complex.I)) n) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) n) z)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) n) z)) Complex.I))
but is expected to have type
  forall (n : Nat) (z : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos z) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin z) Complex.I)) n) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) n) z)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) n) z)) Complex.I))
Case conversion may be inaccurate. Consider using '#align complex.cos_add_sin_mul_I_pow Complex.cos_add_sin_mul_I_powₓ'. -/
/-- **De Moivre's formula** -/
theorem cos_add_sin_mul_I_pow (n : ℕ) (z : ℂ) :
    (cos z + sin z * I) ^ n = cos (↑n * z) + sin (↑n * z) * I :=
  by
  rw [← exp_mul_I, ← exp_mul_I]
  induction' n with n ih
  · rw [pow_zero, Nat.cast_zero, MulZeroClass.zero_mul, MulZeroClass.zero_mul, exp_zero]
  · rw [pow_succ', ih, Nat.cast_succ, add_mul, add_mul, one_mul, exp_add]
#align complex.cos_add_sin_mul_I_pow Complex.cos_add_sin_mul_I_pow

end Complex

namespace Real

open Complex

variable (x y : ℝ)

/- warning: real.exp_zero -> Real.exp_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.exp (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Real.exp (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.exp_zero Real.exp_zeroₓ'. -/
@[simp]
theorem exp_zero : exp 0 = 1 := by simp [Real.exp]
#align real.exp_zero Real.exp_zero

/- warning: real.exp_add -> Real.exp_add is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Real (Real.exp (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.exp x) (Real.exp y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Real (Real.exp (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.exp x) (Real.exp y))
Case conversion may be inaccurate. Consider using '#align real.exp_add Real.exp_addₓ'. -/
theorem exp_add : exp (x + y) = exp x * exp y := by simp [exp_add, exp]
#align real.exp_add Real.exp_add

#print Real.exp_list_sum /-
theorem exp_list_sum (l : List ℝ) : exp l.Sum = (l.map exp).Prod :=
  @MonoidHom.map_list_prod (Multiplicative ℝ) ℝ _ _ ⟨exp, exp_zero, exp_add⟩ l
#align real.exp_list_sum Real.exp_list_sum
-/

#print Real.exp_multiset_sum /-
theorem exp_multiset_sum (s : Multiset ℝ) : exp s.Sum = (s.map exp).Prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℝ) ℝ _ _ ⟨exp, exp_zero, exp_add⟩ s
#align real.exp_multiset_sum Real.exp_multiset_sum
-/

#print Real.exp_sum /-
theorem exp_sum {α : Type _} (s : Finset α) (f : α → ℝ) :
    exp (∑ x in s, f x) = ∏ x in s, exp (f x) :=
  @MonoidHom.map_prod (Multiplicative ℝ) α ℝ _ _ ⟨exp, exp_zero, exp_add⟩ f s
#align real.exp_sum Real.exp_sum
-/

/- warning: real.exp_nat_mul -> Real.exp_nat_mul is a dubious translation:
lean 3 declaration is
  forall (x : Real) (n : Nat), Eq.{1} Real (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) x)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.exp x) n)
but is expected to have type
  forall (x : Real) (n : Nat), Eq.{1} Real (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast n) x)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.exp x) n)
Case conversion may be inaccurate. Consider using '#align real.exp_nat_mul Real.exp_nat_mulₓ'. -/
theorem exp_nat_mul (x : ℝ) : ∀ n : ℕ, exp (n * x) = exp x ^ n
  | 0 => by rw [Nat.cast_zero, MulZeroClass.zero_mul, exp_zero, pow_zero]
  | Nat.succ n => by rw [pow_succ', Nat.cast_add_one, add_mul, exp_add, ← exp_nat_mul, one_mul]
#align real.exp_nat_mul Real.exp_nat_mul

/- warning: real.exp_ne_zero -> Real.exp_ne_zero is a dubious translation:
lean 3 declaration is
  forall (x : Real), Ne.{1} Real (Real.exp x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall (x : Real), Ne.{1} Real (Real.exp x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.exp_ne_zero Real.exp_ne_zeroₓ'. -/
theorem exp_ne_zero : exp x ≠ 0 := fun h =>
  exp_ne_zero x <| by rw [exp, ← of_real_inj] at h <;> simp_all
#align real.exp_ne_zero Real.exp_ne_zero

/- warning: real.exp_neg -> Real.exp_neg is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.exp (Neg.neg.{0} Real Real.hasNeg x)) (Inv.inv.{0} Real Real.hasInv (Real.exp x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.exp (Neg.neg.{0} Real Real.instNegReal x)) (Inv.inv.{0} Real Real.instInvReal (Real.exp x))
Case conversion may be inaccurate. Consider using '#align real.exp_neg Real.exp_negₓ'. -/
theorem exp_neg : exp (-x) = (exp x)⁻¹ := by
  rw [← of_real_inj, exp, of_real_exp_of_real_re, of_real_neg, exp_neg, of_real_inv, of_real_exp]
#align real.exp_neg Real.exp_neg

/- warning: real.exp_sub -> Real.exp_sub is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Real (Real.exp (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x y)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.exp x) (Real.exp y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Real (Real.exp (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x y)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.exp x) (Real.exp y))
Case conversion may be inaccurate. Consider using '#align real.exp_sub Real.exp_subₓ'. -/
theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]
#align real.exp_sub Real.exp_sub

#print Real.sin_zero /-
@[simp]
theorem sin_zero : sin 0 = 0 := by simp [sin]
#align real.sin_zero Real.sin_zero
-/

#print Real.sin_neg /-
@[simp]
theorem sin_neg : sin (-x) = -sin x := by simp [sin, exp_neg, (neg_div _ _).symm, add_mul]
#align real.sin_neg Real.sin_neg
-/

#print Real.sin_add /-
theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y := by
  rw [← of_real_inj] <;> simp [sin, sin_add]
#align real.sin_add Real.sin_add
-/

#print Real.cos_zero /-
@[simp]
theorem cos_zero : cos 0 = 1 := by simp [cos]
#align real.cos_zero Real.cos_zero
-/

#print Real.cos_neg /-
@[simp]
theorem cos_neg : cos (-x) = cos x := by simp [cos, exp_neg]
#align real.cos_neg Real.cos_neg
-/

#print Real.cos_abs /-
@[simp]
theorem cos_abs : cos (|x|) = cos x := by
  cases le_total x 0 <;> simp only [*, _root_.abs_of_nonneg, abs_of_nonpos, cos_neg]
#align real.cos_abs Real.cos_abs
-/

#print Real.cos_add /-
theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y := by
  rw [← of_real_inj] <;> simp [cos, cos_add]
#align real.cos_add Real.cos_add
-/

#print Real.sin_sub /-
theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]
#align real.sin_sub Real.sin_sub
-/

#print Real.cos_sub /-
theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]
#align real.cos_sub Real.cos_sub
-/

/- warning: real.sin_sub_sin -> Real.sin_sub_sin is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.sin x) (Real.sin y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x y) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Real.cos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.sin x) (Real.sin y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x y) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Real.cos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))
Case conversion may be inaccurate. Consider using '#align real.sin_sub_sin Real.sin_sub_sinₓ'. -/
theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) :=
  by
  rw [← of_real_inj]
  simp only [sin, cos, of_real_sin_of_real_re, of_real_sub, of_real_add, of_real_div, of_real_mul,
    of_real_one, of_real_bit0]
  convert sin_sub_sin _ _ <;> norm_cast
#align real.sin_sub_sin Real.sin_sub_sin

/- warning: real.cos_sub_cos -> Real.cos_sub_cos is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.cos x) (Real.cos y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x y) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.cos x) (Real.cos y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x y) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))
Case conversion may be inaccurate. Consider using '#align real.cos_sub_cos Real.cos_sub_cosₓ'. -/
theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) :=
  by
  rw [← of_real_inj]
  simp only [cos, neg_mul, of_real_sin, of_real_sub, of_real_add, of_real_cos_of_real_re,
    of_real_div, of_real_mul, of_real_one, of_real_neg, of_real_bit0]
  convert cos_sub_cos _ _
  ring
#align real.cos_sub_cos Real.cos_sub_cos

/- warning: real.cos_add_cos -> Real.cos_add_cos is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.cos x) (Real.cos y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Real.cos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Real.cos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x y) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.cos x) (Real.cos y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Real.cos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Real.cos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x y) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))
Case conversion may be inaccurate. Consider using '#align real.cos_add_cos Real.cos_add_cosₓ'. -/
theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) :=
  by
  rw [← of_real_inj]
  simp only [cos, of_real_sub, of_real_add, of_real_cos_of_real_re, of_real_div, of_real_mul,
    of_real_one, of_real_bit0]
  convert cos_add_cos _ _ <;> norm_cast
#align real.cos_add_cos Real.cos_add_cos

/- warning: real.tan_eq_sin_div_cos -> Real.tan_eq_sin_div_cos is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.tan x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sin x) (Real.cos x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.tan x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sin x) (Real.cos x))
Case conversion may be inaccurate. Consider using '#align real.tan_eq_sin_div_cos Real.tan_eq_sin_div_cosₓ'. -/
theorem tan_eq_sin_div_cos : tan x = sin x / cos x := by
  rw [← of_real_inj, of_real_tan, tan_eq_sin_div_cos, of_real_div, of_real_sin, of_real_cos]
#align real.tan_eq_sin_div_cos Real.tan_eq_sin_div_cos

/- warning: real.tan_mul_cos -> Real.tan_mul_cos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.tan x) (Real.cos x)) (Real.sin x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.tan x) (Real.cos x)) (Real.sin x))
Case conversion may be inaccurate. Consider using '#align real.tan_mul_cos Real.tan_mul_cosₓ'. -/
theorem tan_mul_cos {x : ℝ} (hx : cos x ≠ 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos, div_mul_cancel _ hx]
#align real.tan_mul_cos Real.tan_mul_cos

#print Real.tan_zero /-
@[simp]
theorem tan_zero : tan 0 = 0 := by simp [tan]
#align real.tan_zero Real.tan_zero
-/

#print Real.tan_neg /-
@[simp]
theorem tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]
#align real.tan_neg Real.tan_neg
-/

/- warning: real.sin_sq_add_cos_sq -> Real.sin_sq_add_cos_sq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.sin_sq_add_cos_sq Real.sin_sq_add_cos_sqₓ'. -/
@[simp]
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  ofReal_inj.1 <| by simp
#align real.sin_sq_add_cos_sq Real.sin_sq_add_cos_sq

/- warning: real.cos_sq_add_sin_sq -> Real.cos_sq_add_sin_sq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.cos_sq_add_sin_sq Real.cos_sq_add_sin_sqₓ'. -/
@[simp]
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]
#align real.cos_sq_add_sin_sq Real.cos_sq_add_sin_sq

/- warning: real.sin_sq_le_one -> Real.sin_sq_le_one is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.sin_sq_le_one Real.sin_sq_le_oneₓ'. -/
theorem sin_sq_le_one : sin x ^ 2 ≤ 1 := by
  rw [← sin_sq_add_cos_sq x] <;> exact le_add_of_nonneg_right (sq_nonneg _)
#align real.sin_sq_le_one Real.sin_sq_le_one

/- warning: real.cos_sq_le_one -> Real.cos_sq_le_one is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.cos_sq_le_one Real.cos_sq_le_oneₓ'. -/
theorem cos_sq_le_one : cos x ^ 2 ≤ 1 := by
  rw [← sin_sq_add_cos_sq x] <;> exact le_add_of_nonneg_left (sq_nonneg _)
#align real.cos_sq_le_one Real.cos_sq_le_one

/- warning: real.abs_sin_le_one -> Real.abs_sin_le_one is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Real.sin x)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Real.sin x)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.abs_sin_le_one Real.abs_sin_le_oneₓ'. -/
theorem abs_sin_le_one : |sin x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 <| by simp only [← sq, sin_sq_le_one]
#align real.abs_sin_le_one Real.abs_sin_le_one

/- warning: real.abs_cos_le_one -> Real.abs_cos_le_one is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Real.cos x)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Real.cos x)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.abs_cos_le_one Real.abs_cos_le_oneₓ'. -/
theorem abs_cos_le_one : |cos x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 <| by simp only [← sq, cos_sq_le_one]
#align real.abs_cos_le_one Real.abs_cos_le_one

/- warning: real.sin_le_one -> Real.sin_le_one is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (Real.sin x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (Real.sin x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.sin_le_one Real.sin_le_oneₓ'. -/
theorem sin_le_one : sin x ≤ 1 :=
  (abs_le.1 (abs_sin_le_one _)).2
#align real.sin_le_one Real.sin_le_one

/- warning: real.cos_le_one -> Real.cos_le_one is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (Real.cos x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (Real.cos x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.cos_le_one Real.cos_le_oneₓ'. -/
theorem cos_le_one : cos x ≤ 1 :=
  (abs_le.1 (abs_cos_le_one _)).2
#align real.cos_le_one Real.cos_le_one

/- warning: real.neg_one_le_sin -> Real.neg_one_le_sin is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Real.sin x)
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Real.sin x)
Case conversion may be inaccurate. Consider using '#align real.neg_one_le_sin Real.neg_one_le_sinₓ'. -/
theorem neg_one_le_sin : -1 ≤ sin x :=
  (abs_le.1 (abs_sin_le_one _)).1
#align real.neg_one_le_sin Real.neg_one_le_sin

/- warning: real.neg_one_le_cos -> Real.neg_one_le_cos is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Real.cos x)
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Real.cos x)
Case conversion may be inaccurate. Consider using '#align real.neg_one_le_cos Real.neg_one_le_cosₓ'. -/
theorem neg_one_le_cos : -1 ≤ cos x :=
  (abs_le.1 (abs_cos_le_one _)).1
#align real.neg_one_le_cos Real.neg_one_le_cos

#print Real.cos_two_mul /-
theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
  rw [← of_real_inj] <;> simp [cos_two_mul]
#align real.cos_two_mul Real.cos_two_mul
-/

#print Real.cos_two_mul' /-
theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by
  rw [← of_real_inj] <;> simp [cos_two_mul']
#align real.cos_two_mul' Real.cos_two_mul'
-/

#print Real.sin_two_mul /-
theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x := by
  rw [← of_real_inj] <;> simp [sin_two_mul]
#align real.sin_two_mul Real.sin_two_mul
-/

/- warning: real.cos_sq -> Real.cos_sq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.cos (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) x)) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.cos (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) x)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.cos_sq Real.cos_sqₓ'. -/
theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
  ofReal_inj.1 <| by simpa using cos_sq x
#align real.cos_sq Real.cos_sq

/- warning: real.cos_sq' -> Real.cos_sq' is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align real.cos_sq' Real.cos_sq'ₓ'. -/
theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel']
#align real.cos_sq' Real.cos_sq'

/- warning: real.sin_sq -> Real.sin_sq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align real.sin_sq Real.sin_sqₓ'. -/
theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 :=
  eq_sub_iff_add_eq.2 <| sin_sq_add_cos_sq _
#align real.sin_sq Real.sin_sq

/- warning: real.abs_sin_eq_sqrt_one_sub_cos_sq -> Real.abs_sin_eq_sqrt_one_sub_cos_sq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Real.sin x)) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Real.sin x)) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align real.abs_sin_eq_sqrt_one_sub_cos_sq Real.abs_sin_eq_sqrt_one_sub_cos_sqₓ'. -/
theorem abs_sin_eq_sqrt_one_sub_cos_sq (x : ℝ) : |sin x| = sqrt (1 - cos x ^ 2) := by
  rw [← sin_sq, sqrt_sq_eq_abs]
#align real.abs_sin_eq_sqrt_one_sub_cos_sq Real.abs_sin_eq_sqrt_one_sub_cos_sq

/- warning: real.abs_cos_eq_sqrt_one_sub_sin_sq -> Real.abs_cos_eq_sqrt_one_sub_sin_sq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Real.cos x)) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Real.cos x)) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align real.abs_cos_eq_sqrt_one_sub_sin_sq Real.abs_cos_eq_sqrt_one_sub_sin_sqₓ'. -/
theorem abs_cos_eq_sqrt_one_sub_sin_sq (x : ℝ) : |cos x| = sqrt (1 - sin x ^ 2) := by
  rw [← cos_sq', sqrt_sq_eq_abs]
#align real.abs_cos_eq_sqrt_one_sub_sin_sq Real.abs_cos_eq_sqrt_one_sub_sin_sq

/- warning: real.inv_one_add_tan_sq -> Real.inv_one_add_tan_sq is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Inv.inv.{0} Real Real.hasInv (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Inv.inv.{0} Real Real.instInvReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align real.inv_one_add_tan_sq Real.inv_one_add_tan_sqₓ'. -/
theorem inv_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 :=
  have : Complex.cos x ≠ 0 := mt (congr_arg re) hx
  ofReal_inj.1 <| by simpa using Complex.inv_one_add_tan_sq this
#align real.inv_one_add_tan_sq Real.inv_one_add_tan_sq

/- warning: real.tan_sq_div_one_add_tan_sq -> Real.tan_sq_div_one_add_tan_sq is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align real.tan_sq_div_one_add_tan_sq Real.tan_sq_div_one_add_tan_sqₓ'. -/
theorem tan_sq_div_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]
#align real.tan_sq_div_one_add_tan_sq Real.tan_sq_div_one_add_tan_sq

/- warning: real.inv_sqrt_one_add_tan_sq -> Real.inv_sqrt_one_add_tan_sq is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.cos x)) -> (Eq.{1} Real (Inv.inv.{0} Real Real.hasInv (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))) (Real.cos x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.cos x)) -> (Eq.{1} Real (Inv.inv.{0} Real Real.instInvReal (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (Real.cos x))
Case conversion may be inaccurate. Consider using '#align real.inv_sqrt_one_add_tan_sq Real.inv_sqrt_one_add_tan_sqₓ'. -/
theorem inv_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) : (sqrt (1 + tan x ^ 2))⁻¹ = cos x := by
  rw [← sqrt_sq hx.le, ← sqrt_inv, inv_one_add_tan_sq hx.ne']
#align real.inv_sqrt_one_add_tan_sq Real.inv_sqrt_one_add_tan_sq

/- warning: real.tan_div_sqrt_one_add_tan_sq -> Real.tan_div_sqrt_one_add_tan_sq is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.cos x)) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.tan x) (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))) (Real.sin x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.cos x)) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.tan x) (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.tan x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (Real.sin x))
Case conversion may be inaccurate. Consider using '#align real.tan_div_sqrt_one_add_tan_sq Real.tan_div_sqrt_one_add_tan_sqₓ'. -/
theorem tan_div_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) :
    tan x / sqrt (1 + tan x ^ 2) = sin x := by
  rw [← tan_mul_cos hx.ne', ← inv_sqrt_one_add_tan_sq hx, div_eq_mul_inv]
#align real.tan_div_sqrt_one_add_tan_sq Real.tan_div_sqrt_one_add_tan_sq

#print Real.cos_three_mul /-
theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  rw [← of_real_inj] <;> simp [cos_three_mul]
#align real.cos_three_mul Real.cos_three_mul
-/

#print Real.sin_three_mul /-
theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  rw [← of_real_inj] <;> simp [sin_three_mul]
#align real.sin_three_mul Real.sin_three_mul
-/

/- warning: real.sinh_eq -> Real.sinh_eq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.sinh x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (Real.exp (Neg.neg.{0} Real Real.hasNeg x))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.sinh x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (Real.exp (Neg.neg.{0} Real Real.instNegReal x))) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real.sinh_eq Real.sinh_eqₓ'. -/
/-- The definition of `sinh` in terms of `exp`. -/
theorem sinh_eq (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
  eq_div_of_mul_eq two_ne_zero <| by
    rw [sinh, exp, exp, Complex.ofReal_neg, Complex.sinh, mul_two, ← Complex.add_re, ← mul_two,
      div_mul_cancel _ (two_ne_zero' ℂ), Complex.sub_re]
#align real.sinh_eq Real.sinh_eq

#print Real.sinh_zero /-
@[simp]
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]
#align real.sinh_zero Real.sinh_zero
-/

#print Real.sinh_neg /-
@[simp]
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]
#align real.sinh_neg Real.sinh_neg
-/

#print Real.sinh_add /-
theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← of_real_inj] <;> simp [sinh_add]
#align real.sinh_add Real.sinh_add
-/

/- warning: real.cosh_eq -> Real.cosh_eq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.cosh x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.exp x) (Real.exp (Neg.neg.{0} Real Real.hasNeg x))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.cosh x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.exp x) (Real.exp (Neg.neg.{0} Real Real.instNegReal x))) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real.cosh_eq Real.cosh_eqₓ'. -/
/-- The definition of `cosh` in terms of `exp`. -/
theorem cosh_eq (x : ℝ) : cosh x = (exp x + exp (-x)) / 2 :=
  eq_div_of_mul_eq two_ne_zero <| by
    rw [cosh, exp, exp, Complex.ofReal_neg, Complex.cosh, mul_two, ← Complex.add_re, ← mul_two,
      div_mul_cancel _ (two_ne_zero' ℂ), Complex.add_re]
#align real.cosh_eq Real.cosh_eq

#print Real.cosh_zero /-
@[simp]
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]
#align real.cosh_zero Real.cosh_zero
-/

#print Real.cosh_neg /-
@[simp]
theorem cosh_neg : cosh (-x) = cosh x :=
  ofReal_inj.1 <| by simp
#align real.cosh_neg Real.cosh_neg
-/

#print Real.cosh_abs /-
@[simp]
theorem cosh_abs : cosh (|x|) = cosh x := by
  cases le_total x 0 <;> simp [*, _root_.abs_of_nonneg, abs_of_nonpos]
#align real.cosh_abs Real.cosh_abs
-/

#print Real.cosh_add /-
theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← of_real_inj] <;> simp [cosh_add]
#align real.cosh_add Real.cosh_add
-/

#print Real.sinh_sub /-
theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]
#align real.sinh_sub Real.sinh_sub
-/

#print Real.cosh_sub /-
theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]
#align real.cosh_sub Real.cosh_sub
-/

/- warning: real.tanh_eq_sinh_div_cosh -> Real.tanh_eq_sinh_div_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.tanh x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sinh x) (Real.cosh x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.tanh x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sinh x) (Real.cosh x))
Case conversion may be inaccurate. Consider using '#align real.tanh_eq_sinh_div_cosh Real.tanh_eq_sinh_div_coshₓ'. -/
theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  ofReal_inj.1 <| by simp [tanh_eq_sinh_div_cosh]
#align real.tanh_eq_sinh_div_cosh Real.tanh_eq_sinh_div_cosh

#print Real.tanh_zero /-
@[simp]
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]
#align real.tanh_zero Real.tanh_zero
-/

#print Real.tanh_neg /-
@[simp]
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]
#align real.tanh_neg Real.tanh_neg
-/

/- warning: real.cosh_add_sinh -> Real.cosh_add_sinh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.cosh x) (Real.sinh x)) (Real.exp x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.cosh x) (Real.sinh x)) (Real.exp x)
Case conversion may be inaccurate. Consider using '#align real.cosh_add_sinh Real.cosh_add_sinhₓ'. -/
@[simp]
theorem cosh_add_sinh : cosh x + sinh x = exp x := by rw [← of_real_inj] <;> simp
#align real.cosh_add_sinh Real.cosh_add_sinh

/- warning: real.sinh_add_cosh -> Real.sinh_add_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.sinh x) (Real.cosh x)) (Real.exp x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.sinh x) (Real.cosh x)) (Real.exp x)
Case conversion may be inaccurate. Consider using '#align real.sinh_add_cosh Real.sinh_add_coshₓ'. -/
@[simp]
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]
#align real.sinh_add_cosh Real.sinh_add_cosh

/- warning: real.exp_sub_cosh -> Real.exp_sub_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (Real.cosh x)) (Real.sinh x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (Real.cosh x)) (Real.sinh x)
Case conversion may be inaccurate. Consider using '#align real.exp_sub_cosh Real.exp_sub_coshₓ'. -/
@[simp]
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm
#align real.exp_sub_cosh Real.exp_sub_cosh

/- warning: real.exp_sub_sinh -> Real.exp_sub_sinh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (Real.sinh x)) (Real.cosh x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (Real.sinh x)) (Real.cosh x)
Case conversion may be inaccurate. Consider using '#align real.exp_sub_sinh Real.exp_sub_sinhₓ'. -/
@[simp]
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm
#align real.exp_sub_sinh Real.exp_sub_sinh

/- warning: real.cosh_sub_sinh -> Real.cosh_sub_sinh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.cosh x) (Real.sinh x)) (Real.exp (Neg.neg.{0} Real Real.hasNeg x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.cosh x) (Real.sinh x)) (Real.exp (Neg.neg.{0} Real Real.instNegReal x))
Case conversion may be inaccurate. Consider using '#align real.cosh_sub_sinh Real.cosh_sub_sinhₓ'. -/
@[simp]
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) :=
  by
  rw [← of_real_inj]
  simp
#align real.cosh_sub_sinh Real.cosh_sub_sinh

/- warning: real.sinh_sub_cosh -> Real.sinh_sub_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.sinh x) (Real.cosh x)) (Neg.neg.{0} Real Real.hasNeg (Real.exp (Neg.neg.{0} Real Real.hasNeg x)))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.sinh x) (Real.cosh x)) (Neg.neg.{0} Real Real.instNegReal (Real.exp (Neg.neg.{0} Real Real.instNegReal x)))
Case conversion may be inaccurate. Consider using '#align real.sinh_sub_cosh Real.sinh_sub_coshₓ'. -/
@[simp]
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]
#align real.sinh_sub_cosh Real.sinh_sub_cosh

/- warning: real.cosh_sq_sub_sinh_sq -> Real.cosh_sq_sub_sinh_sq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cosh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sinh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cosh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sinh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.cosh_sq_sub_sinh_sq Real.cosh_sq_sub_sinh_sqₓ'. -/
@[simp]
theorem cosh_sq_sub_sinh_sq (x : ℝ) : cosh x ^ 2 - sinh x ^ 2 = 1 := by rw [← of_real_inj] <;> simp
#align real.cosh_sq_sub_sinh_sq Real.cosh_sq_sub_sinh_sq

/- warning: real.cosh_sq -> Real.cosh_sq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cosh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sinh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cosh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sinh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.cosh_sq Real.cosh_sqₓ'. -/
theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by rw [← of_real_inj] <;> simp [cosh_sq]
#align real.cosh_sq Real.cosh_sq

/- warning: real.cosh_sq' -> Real.cosh_sq' is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cosh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sinh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cosh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sinh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align real.cosh_sq' Real.cosh_sq'ₓ'. -/
theorem cosh_sq' : cosh x ^ 2 = 1 + sinh x ^ 2 :=
  (cosh_sq x).trans (add_comm _ _)
#align real.cosh_sq' Real.cosh_sq'

/- warning: real.sinh_sq -> Real.sinh_sq is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sinh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cosh x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sinh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cosh x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.sinh_sq Real.sinh_sqₓ'. -/
theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by rw [← of_real_inj] <;> simp [sinh_sq]
#align real.sinh_sq Real.sinh_sq

#print Real.cosh_two_mul /-
theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by
  rw [← of_real_inj] <;> simp [cosh_two_mul]
#align real.cosh_two_mul Real.cosh_two_mul
-/

#print Real.sinh_two_mul /-
theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [← of_real_inj] <;> simp [sinh_two_mul]
#align real.sinh_two_mul Real.sinh_two_mul
-/

#print Real.cosh_three_mul /-
theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x := by
  rw [← of_real_inj] <;> simp [cosh_three_mul]
#align real.cosh_three_mul Real.cosh_three_mul
-/

#print Real.sinh_three_mul /-
theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x := by
  rw [← of_real_inj] <;> simp [sinh_three_mul]
#align real.sinh_three_mul Real.sinh_three_mul
-/

open IsAbsoluteValue

/- warning: real.add_one_le_exp_of_nonneg -> Real.add_one_le_exp_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Real.exp x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Real.exp x))
Case conversion may be inaccurate. Consider using '#align real.add_one_le_exp_of_nonneg Real.add_one_le_exp_of_nonnegₓ'. -/
/-- This is an intermediate result that is later replaced by `real.add_one_le_exp`; use that lemma
instead. -/
theorem add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x :=
  calc
    x + 1 ≤ limUnder (⟨fun n : ℕ => ((exp' x) n).re, isCauSeq_re (exp' x)⟩ : CauSeq ℝ Abs.abs) :=
      le_lim
        (CauSeq.le_of_exists
          ⟨2, fun j hj =>
            show x + (1 : ℝ) ≤ (∑ m in range j, (x ^ m / m ! : ℂ)).re
              by
              have h₁ : (((fun m : ℕ => (x ^ m / m ! : ℂ)) ∘ Nat.succ) 0).re = x := by simp
              have h₂ : ((x : ℂ) ^ 0 / 0!).re = 1 := by simp
              rw [← tsub_add_cancel_of_le hj, sum_range_succ', sum_range_succ', add_re, add_re, h₁,
                h₂, add_assoc, ← coe_re_add_group_hom, re_add_group_hom.map_sum,
                coe_re_add_group_hom]
              refine' le_add_of_nonneg_of_le (sum_nonneg fun m hm => _) le_rfl
              rw [← of_real_pow, ← of_real_nat_cast, ← of_real_div, of_real_re]
              exact div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)⟩)
    _ = exp x := by rw [exp, Complex.exp, ← cau_seq_re, lim_re]
    
#align real.add_one_le_exp_of_nonneg Real.add_one_le_exp_of_nonneg

/- warning: real.one_le_exp -> Real.one_le_exp is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Real.exp x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Real.exp x))
Case conversion may be inaccurate. Consider using '#align real.one_le_exp Real.one_le_expₓ'. -/
theorem one_le_exp {x : ℝ} (hx : 0 ≤ x) : 1 ≤ exp x := by linarith [add_one_le_exp_of_nonneg hx]
#align real.one_le_exp Real.one_le_exp

/- warning: real.exp_pos -> Real.exp_pos is a dubious translation:
lean 3 declaration is
  forall (x : Real), LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.exp x)
but is expected to have type
  forall (x : Real), LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.exp x)
Case conversion may be inaccurate. Consider using '#align real.exp_pos Real.exp_posₓ'. -/
theorem exp_pos (x : ℝ) : 0 < exp x :=
  (le_total 0 x).elim (lt_of_lt_of_le zero_lt_one ∘ one_le_exp) fun h => by
    rw [← neg_neg x, Real.exp_neg] <;>
      exact inv_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_exp (neg_nonneg.2 h)))
#align real.exp_pos Real.exp_pos

/- warning: real.abs_exp -> Real.abs_exp is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Real.exp x)) (Real.exp x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Real.exp x)) (Real.exp x)
Case conversion may be inaccurate. Consider using '#align real.abs_exp Real.abs_expₓ'. -/
@[simp]
theorem abs_exp (x : ℝ) : |exp x| = exp x :=
  abs_of_pos (exp_pos _)
#align real.abs_exp Real.abs_exp

#print Real.exp_strictMono /-
@[mono]
theorem exp_strictMono : StrictMono exp := fun x y h => by
  rw [← sub_add_cancel y x, Real.exp_add] <;>
    exact
      (lt_mul_iff_one_lt_left (exp_pos _)).2
        (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))
#align real.exp_strict_mono Real.exp_strictMono
-/

#print Real.exp_monotone /-
@[mono]
theorem exp_monotone : Monotone exp :=
  exp_strictMono.Monotone
#align real.exp_monotone Real.exp_monotone
-/

/- warning: real.exp_lt_exp -> Real.exp_lt_exp is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (LT.lt.{0} Real Real.hasLt (Real.exp x) (Real.exp y)) (LT.lt.{0} Real Real.hasLt x y)
but is expected to have type
  forall {x : Real} {y : Real}, Iff (LT.lt.{0} Real Real.instLTReal (Real.exp x) (Real.exp y)) (LT.lt.{0} Real Real.instLTReal x y)
Case conversion may be inaccurate. Consider using '#align real.exp_lt_exp Real.exp_lt_expₓ'. -/
@[simp]
theorem exp_lt_exp {x y : ℝ} : exp x < exp y ↔ x < y :=
  exp_strictMono.lt_iff_lt
#align real.exp_lt_exp Real.exp_lt_exp

/- warning: real.exp_le_exp -> Real.exp_le_exp is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (LE.le.{0} Real Real.hasLe (Real.exp x) (Real.exp y)) (LE.le.{0} Real Real.hasLe x y)
but is expected to have type
  forall {x : Real} {y : Real}, Iff (LE.le.{0} Real Real.instLEReal (Real.exp x) (Real.exp y)) (LE.le.{0} Real Real.instLEReal x y)
Case conversion may be inaccurate. Consider using '#align real.exp_le_exp Real.exp_le_expₓ'. -/
@[simp]
theorem exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y :=
  exp_strictMono.le_iff_le
#align real.exp_le_exp Real.exp_le_exp

#print Real.exp_injective /-
theorem exp_injective : Function.Injective exp :=
  exp_strictMono.Injective
#align real.exp_injective Real.exp_injective
-/

#print Real.exp_eq_exp /-
@[simp]
theorem exp_eq_exp {x y : ℝ} : exp x = exp y ↔ x = y :=
  exp_injective.eq_iff
#align real.exp_eq_exp Real.exp_eq_exp
-/

/- warning: real.exp_eq_one_iff -> Real.exp_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall (x : Real), Iff (Eq.{1} Real (Real.exp x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall (x : Real), Iff (Eq.{1} Real (Real.exp x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.exp_eq_one_iff Real.exp_eq_one_iffₓ'. -/
@[simp]
theorem exp_eq_one_iff : exp x = 1 ↔ x = 0 :=
  exp_injective.eq_iff' exp_zero
#align real.exp_eq_one_iff Real.exp_eq_one_iff

/- warning: real.one_lt_exp_iff -> Real.one_lt_exp_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Real.exp x)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Real.exp x)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align real.one_lt_exp_iff Real.one_lt_exp_iffₓ'. -/
@[simp]
theorem one_lt_exp_iff {x : ℝ} : 1 < exp x ↔ 0 < x := by rw [← exp_zero, exp_lt_exp]
#align real.one_lt_exp_iff Real.one_lt_exp_iff

/- warning: real.exp_lt_one_iff -> Real.exp_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Real Real.hasLt (Real.exp x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Real Real.instLTReal (Real.exp x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.exp_lt_one_iff Real.exp_lt_one_iffₓ'. -/
@[simp]
theorem exp_lt_one_iff {x : ℝ} : exp x < 1 ↔ x < 0 := by rw [← exp_zero, exp_lt_exp]
#align real.exp_lt_one_iff Real.exp_lt_one_iff

/- warning: real.exp_le_one_iff -> Real.exp_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Real Real.hasLe (Real.exp x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Real Real.instLEReal (Real.exp x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.exp_le_one_iff Real.exp_le_one_iffₓ'. -/
@[simp]
theorem exp_le_one_iff {x : ℝ} : exp x ≤ 1 ↔ x ≤ 0 :=
  exp_zero ▸ exp_le_exp
#align real.exp_le_one_iff Real.exp_le_one_iff

/- warning: real.one_le_exp_iff -> Real.one_le_exp_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Real.exp x)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Real.exp x)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align real.one_le_exp_iff Real.one_le_exp_iffₓ'. -/
@[simp]
theorem one_le_exp_iff {x : ℝ} : 1 ≤ exp x ↔ 0 ≤ x :=
  exp_zero ▸ exp_le_exp
#align real.one_le_exp_iff Real.one_le_exp_iff

/- warning: real.cosh_pos -> Real.cosh_pos is a dubious translation:
lean 3 declaration is
  forall (x : Real), LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.cosh x)
but is expected to have type
  forall (x : Real), LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.cosh x)
Case conversion may be inaccurate. Consider using '#align real.cosh_pos Real.cosh_posₓ'. -/
/-- `real.cosh` is always positive -/
theorem cosh_pos (x : ℝ) : 0 < Real.cosh x :=
  (cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))
#align real.cosh_pos Real.cosh_pos

/- warning: real.sinh_lt_cosh -> Real.sinh_lt_cosh is a dubious translation:
lean 3 declaration is
  forall (x : Real), LT.lt.{0} Real Real.hasLt (Real.sinh x) (Real.cosh x)
but is expected to have type
  forall (x : Real), LT.lt.{0} Real Real.instLTReal (Real.sinh x) (Real.cosh x)
Case conversion may be inaccurate. Consider using '#align real.sinh_lt_cosh Real.sinh_lt_coshₓ'. -/
theorem sinh_lt_cosh : sinh x < cosh x :=
  lt_of_pow_lt_pow 2 (cosh_pos _).le <| (cosh_sq x).symm ▸ lt_add_one _
#align real.sinh_lt_cosh Real.sinh_lt_cosh

end Real

namespace Complex

/- warning: complex.sum_div_factorial_le -> Complex.sum_div_factorial_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] (n : Nat) (j : Nat), (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Finset.filter.{0} Nat (fun (k : Nat) => LE.le.{0} Nat Nat.hasLe n k) (fun (a : Nat) => Nat.decidableLe n a) (Finset.range j)) (fun (m : Nat) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))))) (Nat.factorial m)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))))) (Nat.succ n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))))) (Nat.factorial n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))))) n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] (n : Nat) (j : Nat), (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Finset.sum.{u1, 0} α Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1)))))) (Finset.filter.{0} Nat (fun (k : Nat) => LE.le.{0} Nat instLENat n k) (fun (a : Nat) => Nat.decLe n a) (Finset.range j)) (fun (m : Nat) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (LinearOrderedField.toDiv.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))) (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Nat.factorial m)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (LinearOrderedField.toDiv.{u1} α _inst_1)) (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Nat.succ n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))) (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Nat.factorial n)) (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) n))))
Case conversion may be inaccurate. Consider using '#align complex.sum_div_factorial_le Complex.sum_div_factorial_leₓ'. -/
theorem sum_div_factorial_le {α : Type _} [LinearOrderedField α] (n j : ℕ) (hn : 0 < n) :
    (∑ m in Filter (fun k => n ≤ k) (range j), (1 / m ! : α)) ≤ n.succ / (n ! * n) :=
  calc
    (∑ m in Filter (fun k => n ≤ k) (range j), (1 / m ! : α)) =
        ∑ m in range (j - n), 1 / (m + n)! :=
      sum_bij (fun m _ => m - n)
        (fun m hm =>
          mem_range.2 <|
            (tsub_lt_tsub_iff_right (by simp at hm <;> tauto)).2 (by simp at hm <;> tauto))
        (fun m hm => by rw [tsub_add_cancel_of_le] <;> simp at * <;> tauto)
        (fun a₁ a₂ ha₁ ha₂ h => by
          rwa [tsub_eq_iff_eq_add_of_le, tsub_add_eq_add_tsub, eq_comm, tsub_eq_iff_eq_add_of_le,
                add_left_inj, eq_comm] at h <;>
              simp at * <;>
            tauto)
        fun b hb =>
        ⟨b + n,
          mem_filter.2 ⟨mem_range.2 <| lt_tsub_iff_right.mp (mem_range.1 hb), Nat.le_add_left _ _⟩,
          by rw [add_tsub_cancel_right]⟩
    _ ≤ ∑ m in range (j - n), (n ! * n.succ ^ m)⁻¹ :=
      by
      refine' sum_le_sum fun m n => _
      rw [one_div, inv_le_inv]
      · rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.cast_le, add_comm]
        exact Nat.factorial_mul_pow_le_factorial
      · exact Nat.cast_pos.2 (Nat.factorial_pos _)
      ·
        exact
          mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _))
            (pow_pos (Nat.cast_pos.2 (Nat.succ_pos _)) _)
    _ = n !⁻¹ * ∑ m in range (j - n), n.succ⁻¹ ^ m := by
      simp [mul_inv, mul_sum.symm, sum_mul.symm, -Nat.factorial_succ, mul_comm, inv_pow]
    _ = (n.succ - n.succ * n.succ⁻¹ ^ (j - n)) / (n ! * n) :=
      by
      have h₁ : (n.succ : α) ≠ 1 :=
        @Nat.cast_one α _ ▸ mt Nat.cast_inj.1 (mt Nat.succ.inj (pos_iff_ne_zero.1 hn))
      have h₂ : (n.succ : α) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
      have h₃ : (n ! * n : α) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 (pos_iff_ne_zero.1 (Nat.factorial_pos _)))
          (Nat.cast_ne_zero.2 (pos_iff_ne_zero.1 hn))
      have h₄ : (n.succ - 1 : α) = n := by simp
      rw [geom_sum_inv h₁ h₂, eq_div_iff_mul_eq h₃, mul_comm _ (n ! * n : α), ←
          mul_assoc (n !⁻¹ : α), ← mul_inv_rev, h₄, ← mul_assoc (n ! * n : α), mul_comm (n : α) n !,
          mul_inv_cancel h₃] <;>
        simp [mul_add, add_mul, mul_assoc, mul_comm]
    _ ≤ n.succ / (n ! * n) :=
      by
      refine' Iff.mpr (div_le_div_right (mul_pos _ _)) _
      exact Nat.cast_pos.2 (Nat.factorial_pos _)
      exact Nat.cast_pos.2 hn
      exact
        sub_le_self _
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _))
    
#align complex.sum_div_factorial_le Complex.sum_div_factorial_le

/- warning: complex.exp_bound -> Complex.exp_bound is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LE.le.{0} Real Real.hasLe (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (LE.le.{0} Real Real.hasLe (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) x m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) (Nat.factorial m)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) n) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.succ n)) (Inv.inv.{0} Real Real.hasInv (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)))))))
but is expected to have type
  forall {x : Complex}, (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instLEReal (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs x) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instOneReal))) -> (forall {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) x m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))) Real.instLEReal (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) x m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))) (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (instHMul.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instMulReal) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Nat ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Nat (Monoid.Pow.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instMonoidReal)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs x) n) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast (Nat.succ n)) (Inv.inv.{0} Real Real.instInvReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast (Nat.factorial n)) (Nat.cast.{0} Real Real.natCast n)))))))
Case conversion may be inaccurate. Consider using '#align complex.exp_bound Complex.exp_boundₓ'. -/
theorem exp_bound {x : ℂ} (hx : abs x ≤ 1) {n : ℕ} (hn : 0 < n) :
    abs (exp x - ∑ m in range n, x ^ m / m !) ≤ abs x ^ n * (n.succ * (n ! * n)⁻¹) :=
  by
  rw [← lim_const (∑ m in range n, _), exp, sub_eq_add_neg, ← lim_neg, lim_add, ← lim_abs]
  refine' lim_le (CauSeq.le_of_exists ⟨n, fun j hj => _⟩)
  simp_rw [← sub_eq_add_neg]
  show
    abs ((∑ m in range j, x ^ m / m !) - ∑ m in range n, x ^ m / m !) ≤
      abs x ^ n * (n.succ * (n ! * n)⁻¹)
  rw [sum_range_sub_sum_range hj]
  calc
    abs (∑ m in (range j).filterₓ fun k => n ≤ k, (x ^ m / m ! : ℂ)) =
        abs (∑ m in (range j).filterₓ fun k => n ≤ k, (x ^ n * (x ^ (m - n) / m !) : ℂ)) :=
      by
      refine' congr_arg abs (sum_congr rfl fun m hm => _)
      rw [mem_filter, mem_range] at hm
      rw [← mul_div_assoc, ← pow_add, add_tsub_cancel_of_le hm.2]
    _ ≤ ∑ m in Filter (fun k => n ≤ k) (range j), abs (x ^ n * (_ / m !)) :=
      (abv_sum_le_sum_abv _ _)
    _ ≤ ∑ m in Filter (fun k => n ≤ k) (range j), abs x ^ n * (1 / m !) :=
      by
      refine' sum_le_sum fun m hm => _
      rw [map_mul, map_pow, map_div₀, abs_cast_nat]
      refine' mul_le_mul_of_nonneg_left ((div_le_div_right _).2 _) _
      · exact Nat.cast_pos.2 (Nat.factorial_pos _)
      · rw [abv_pow abs]
        exact pow_le_one _ (abs.nonneg _) hx
      · exact pow_nonneg (abs.nonneg _) _
    _ = abs x ^ n * ∑ m in (range j).filterₓ fun k => n ≤ k, (1 / m ! : ℝ) := by
      simp [abs_mul, abv_pow abs, abs_div, mul_sum.symm]
    _ ≤ abs x ^ n * (n.succ * (n ! * n)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_div_factorial_le _ _ hn) (pow_nonneg (abs.nonneg _) _)
    
#align complex.exp_bound Complex.exp_bound

/- warning: complex.exp_bound' -> Complex.exp_bound' is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {n : Nat}, (LE.le.{0} Real Real.hasLe (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.succ n))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LE.le.{0} Real Real.hasLe (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (Field.toDivisionRing.{0} Complex Complex.field)))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) x m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) (Nat.factorial m)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {x : Complex} {n : Nat}, (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instLEReal (HDiv.hDiv.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (instHDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (LinearOrderedField.toDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instLinearOrderedFieldReal)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs x) (Nat.cast.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.natCast (Nat.succ n))) (HDiv.hDiv.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (instHDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (LinearOrderedField.toDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instOneReal)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) 2 (instOfNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) x m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))) Real.instLEReal (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) x m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))) (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) x m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (instHMul.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instMulReal) (HDiv.hDiv.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) x m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (instHDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (LinearOrderedField.toDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Nat ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Nat (Monoid.Pow.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instMonoidReal)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs x) n) (Nat.cast.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) x m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))) Real.natCast (Nat.factorial n))) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) x m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))) 2 (instOfNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (Finset.sum.{0, 0} Complex Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) x m) (Nat.cast.{0} Complex (NonAssocRing.toNatCast.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)) (Nat.factorial m)))))) 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align complex.exp_bound' Complex.exp_bound'ₓ'. -/
theorem exp_bound' {x : ℂ} {n : ℕ} (hx : abs x / n.succ ≤ 1 / 2) :
    abs (exp x - ∑ m in range n, x ^ m / m !) ≤ abs x ^ n / n ! * 2 :=
  by
  rw [← lim_const (∑ m in range n, _), exp, sub_eq_add_neg, ← lim_neg, lim_add, ← lim_abs]
  refine' lim_le (CauSeq.le_of_exists ⟨n, fun j hj => _⟩)
  simp_rw [← sub_eq_add_neg]
  show abs ((∑ m in range j, x ^ m / m !) - ∑ m in range n, x ^ m / m !) ≤ abs x ^ n / n ! * 2
  let k := j - n
  have hj : j = n + k := (add_tsub_cancel_of_le hj).symm
  rw [hj, sum_range_add_sub_sum_range]
  calc
    abs (∑ i : ℕ in range k, x ^ (n + i) / ((n + i)! : ℂ)) ≤
        ∑ i : ℕ in range k, abs (x ^ (n + i) / ((n + i)! : ℂ)) :=
      abv_sum_le_sum_abv _ _
    _ ≤ ∑ i : ℕ in range k, abs x ^ (n + i) / (n + i)! := by
      simp only [Complex.abs_cast_nat, map_div₀, abv_pow abs]
    _ ≤ ∑ i : ℕ in range k, abs x ^ (n + i) / (n ! * n.succ ^ i) := _
    _ = ∑ i : ℕ in range k, abs x ^ n / n ! * (abs x ^ i / n.succ ^ i) := _
    _ ≤ abs x ^ n / ↑n ! * 2 := _
    
  · refine' sum_le_sum fun m hm => div_le_div (pow_nonneg (abs.nonneg x) (n + m)) le_rfl _ _
    · exact_mod_cast mul_pos n.factorial_pos (pow_pos n.succ_pos _)
    · exact_mod_cast Nat.factorial_mul_pow_le_factorial
  · refine' Finset.sum_congr rfl fun _ _ => _
    simp only [pow_add, div_eq_inv_mul, mul_inv, mul_left_comm, mul_assoc]
  · rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left
    · simp_rw [← div_pow]
      rw [geom_sum_eq, div_le_iff_of_neg]
      · trans (-1 : ℝ)
        · linarith
        · simp only [neg_le_sub_iff_le_add, div_pow, Nat.cast_succ, le_add_iff_nonneg_left]
          exact
            div_nonneg (pow_nonneg (abs.nonneg x) k)
              (pow_nonneg (add_nonneg n.cast_nonneg zero_le_one) k)
      · linarith
      · linarith
    · exact div_nonneg (pow_nonneg (abs.nonneg x) n) (Nat.cast_nonneg n !)
#align complex.exp_bound' Complex.exp_bound'

/- warning: complex.abs_exp_sub_one_le -> Complex.abs_exp_sub_one_le is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LE.le.{0} Real Real.hasLe (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x)))
but is expected to have type
  forall {x : Complex}, (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instLEReal (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs x) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instOneReal))) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) Real.instLEReal (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) (instHMul.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) Real.instMulReal) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) 2 (instOfNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs x)))
Case conversion may be inaccurate. Consider using '#align complex.abs_exp_sub_one_le Complex.abs_exp_sub_one_leₓ'. -/
theorem abs_exp_sub_one_le {x : ℂ} (hx : abs x ≤ 1) : abs (exp x - 1) ≤ 2 * abs x :=
  calc
    abs (exp x - 1) = abs (exp x - ∑ m in range 1, x ^ m / m !) := by simp [sum_range_succ]
    _ ≤ abs x ^ 1 * (Nat.succ 1 * (1! * (1 : ℕ))⁻¹) := (exp_bound hx (by decide))
    _ = 2 * abs x := by simp [two_mul, mul_two, mul_add, mul_comm]
    
#align complex.abs_exp_sub_one_le Complex.abs_exp_sub_one_le

/- warning: complex.abs_exp_sub_one_sub_id_le -> Complex.abs_exp_sub_one_sub_id_le is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LE.le.{0} Real Real.hasLe (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))) x)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {x : Complex}, (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instLEReal (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs x) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instOneReal))) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))) x)) Real.instLEReal (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))) x)) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Nat ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))) x)) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Nat (Monoid.Pow.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real.instMonoidReal)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align complex.abs_exp_sub_one_sub_id_le Complex.abs_exp_sub_one_sub_id_leₓ'. -/
theorem abs_exp_sub_one_sub_id_le {x : ℂ} (hx : abs x ≤ 1) : abs (exp x - 1 - x) ≤ abs x ^ 2 :=
  calc
    abs (exp x - 1 - x) = abs (exp x - ∑ m in range 2, x ^ m / m !) := by
      simp [sub_eq_add_neg, sum_range_succ_comm, add_assoc]
    _ ≤ abs x ^ 2 * (Nat.succ 2 * (2! * (2 : ℕ))⁻¹) := (exp_bound hx (by decide))
    _ ≤ abs x ^ 2 * 1 := (mul_le_mul_of_nonneg_left (by norm_num) (sq_nonneg (abs x)))
    _ = abs x ^ 2 := by rw [mul_one]
    
#align complex.abs_exp_sub_one_sub_id_le Complex.abs_exp_sub_one_sub_id_le

end Complex

namespace Real

open Complex Finset

/- warning: real.exp_bound -> Real.exp_bound is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial m)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) n) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.succ n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (forall {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x m) (Nat.cast.{0} Real Real.natCast (Nat.factorial m)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) n) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Nat.cast.{0} Real Real.natCast (Nat.succ n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast (Nat.factorial n)) (Nat.cast.{0} Real Real.natCast n))))))
Case conversion may be inaccurate. Consider using '#align real.exp_bound Real.exp_boundₓ'. -/
theorem exp_bound {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |exp x - ∑ m in range n, x ^ m / m !| ≤ |x| ^ n * (n.succ / (n ! * n)) :=
  by
  have hxc : Complex.abs x ≤ 1 := by exact_mod_cast hx
  convert exp_bound hxc hn <;> norm_cast
#align real.exp_bound Real.exp_bound

/- warning: real.exp_bound' -> Real.exp_bound' is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (LE.le.{0} Real Real.hasLe (Real.exp x) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial m)))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (forall {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (LE.le.{0} Real Real.instLEReal (Real.exp x) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (m : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x m) (Nat.cast.{0} Real Real.natCast (Nat.factorial m)))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast n) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast (Nat.factorial n)) (Nat.cast.{0} Real Real.natCast n))))))
Case conversion may be inaccurate. Consider using '#align real.exp_bound' Real.exp_bound'ₓ'. -/
theorem exp_bound' {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp x ≤ (∑ m in Finset.range n, x ^ m / m !) + x ^ n * (n + 1) / (n ! * n) :=
  by
  have h3 : |x| = x := by simpa
  have h4 : |x| ≤ 1 := by rwa [h3]
  have h' := Real.exp_bound h4 hn
  rw [h3] at h'
  have h'' := (abs_sub_le_iff.1 h').1
  have t := sub_le_iff_le_add'.1 h''
  simpa [mul_div_assoc] using t
#align real.exp_bound' Real.exp_bound'

/- warning: real.abs_exp_sub_one_le -> Real.abs_exp_sub_one_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x)))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x)))
Case conversion may be inaccurate. Consider using '#align real.abs_exp_sub_one_le Real.abs_exp_sub_one_leₓ'. -/
theorem abs_exp_sub_one_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1| ≤ 2 * |x| :=
  by
  have : Complex.abs x ≤ 1 := by exact_mod_cast hx
  exact_mod_cast Complex.abs_exp_sub_one_le this
#align real.abs_exp_sub_one_le Real.abs_exp_sub_one_le

/- warning: real.abs_exp_sub_one_sub_id_le -> Real.abs_exp_sub_one_sub_id_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align real.abs_exp_sub_one_sub_id_le Real.abs_exp_sub_one_sub_id_leₓ'. -/
theorem abs_exp_sub_one_sub_id_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1 - x| ≤ x ^ 2 :=
  by
  rw [← _root_.sq_abs]
  have : Complex.abs x ≤ 1 := by exact_mod_cast hx
  exact_mod_cast Complex.abs_exp_sub_one_sub_id_le this
#align real.abs_exp_sub_one_sub_id_le Real.abs_exp_sub_one_sub_id_le

#print Real.expNear /-
/-- A finite initial segment of the exponential series, followed by an arbitrary tail.
For fixed `n` this is just a linear map wrt `r`, and each map is a simple linear function
of the previous (see `exp_near_succ`), with `exp_near n x r ⟶ exp x` as `n ⟶ ∞`,
for any `r`. -/
def expNear (n : ℕ) (x r : ℝ) : ℝ :=
  (∑ m in range n, x ^ m / m !) + x ^ n / n ! * r
#align real.exp_near Real.expNear
-/

#print Real.expNear_zero /-
@[simp]
theorem expNear_zero (x r) : expNear 0 x r = r := by simp [exp_near]
#align real.exp_near_zero Real.expNear_zero
-/

/- warning: real.exp_near_succ -> Real.expNear_succ is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (x : Real) (r : Real), Eq.{1} Real (Real.expNear (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) x r) (Real.expNear n x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) r)))
but is expected to have type
  forall (n : Nat) (x : Real) (r : Real), Eq.{1} Real (Real.expNear (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) x r) (Real.expNear n x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast n) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) r)))
Case conversion may be inaccurate. Consider using '#align real.exp_near_succ Real.expNear_succₓ'. -/
@[simp]
theorem expNear_succ (n x r) : expNear (n + 1) x r = expNear n x (1 + x / (n + 1) * r) := by
  simp [exp_near, range_succ, mul_add, add_left_comm, add_assoc, pow_succ, div_eq_mul_inv,
      mul_inv] <;>
    ac_rfl
#align real.exp_near_succ Real.expNear_succ

/- warning: real.exp_near_sub -> Real.expNear_sub is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (x : Real) (r₁ : Real) (r₂ : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.expNear n x r₁) (Real.expNear n x r₂)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) r₁ r₂))
but is expected to have type
  forall (n : Nat) (x : Real) (r₁ : Real) (r₂ : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.expNear n x r₁) (Real.expNear n x r₂)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) (Nat.cast.{0} Real Real.natCast (Nat.factorial n))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) r₁ r₂))
Case conversion may be inaccurate. Consider using '#align real.exp_near_sub Real.expNear_subₓ'. -/
theorem expNear_sub (n x r₁ r₂) : expNear n x r₁ - expNear n x r₂ = x ^ n / n ! * (r₁ - r₂) := by
  simp [exp_near, mul_sub]
#align real.exp_near_sub Real.expNear_sub

/- warning: real.exp_approx_end -> Real.exp_approx_end is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (m : Nat) (x : Real), (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) m) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (Real.expNear m x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial m))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m))))
but is expected to have type
  forall (n : Nat) (m : Nat) (x : Real), (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) m) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (Real.expNear m x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) m) (Nat.cast.{0} Real Real.natCast (Nat.factorial m))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast m) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Nat.cast.{0} Real Real.natCast m))))
Case conversion may be inaccurate. Consider using '#align real.exp_approx_end Real.exp_approx_endₓ'. -/
theorem exp_approx_end (n m : ℕ) (x : ℝ) (e₁ : n + 1 = m) (h : |x| ≤ 1) :
    |exp x - expNear m x 0| ≤ |x| ^ m / m ! * ((m + 1) / m) :=
  by
  simp [exp_near]
  convert exp_bound h _ using 1
  field_simp [mul_comm]
  linarith
#align real.exp_approx_end Real.exp_approx_end

/- warning: real.exp_approx_succ -> Real.exp_approx_succ is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real} {a₁ : Real} {b₁ : Real} (m : Nat), (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) m) -> (forall (a₂ : Real) (b₂ : Real), (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m)) a₂)) a₁)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b₁ (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m)) b₂))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (Real.expNear m x a₂))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial m))) b₂)) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (Real.expNear n x a₁))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n))) b₁)))
but is expected to have type
  forall {n : Nat} {x : Real} {a₁ : Real} {b₁ : Real} (m : Nat), (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) m) -> (forall (a₂ : Real) (b₂ : Real), (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Nat.cast.{0} Real Real.natCast m)) a₂)) a₁)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b₁ (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (Nat.cast.{0} Real Real.natCast m)) b₂))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (Real.expNear m x a₂))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) m) (Nat.cast.{0} Real Real.natCast (Nat.factorial m))) b₂)) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (Real.expNear n x a₁))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) n) (Nat.cast.{0} Real Real.natCast (Nat.factorial n))) b₁)))
Case conversion may be inaccurate. Consider using '#align real.exp_approx_succ Real.exp_approx_succₓ'. -/
theorem exp_approx_succ {n} {x a₁ b₁ : ℝ} (m : ℕ) (e₁ : n + 1 = m) (a₂ b₂ : ℝ)
    (e : |1 + x / m * a₂ - a₁| ≤ b₁ - |x| / m * b₂)
    (h : |exp x - expNear m x a₂| ≤ |x| ^ m / m ! * b₂) :
    |exp x - expNear n x a₁| ≤ |x| ^ n / n ! * b₁ :=
  by
  refine' (_root_.abs_sub_le _ _ _).trans ((add_le_add_right h _).trans _)
  subst e₁; rw [exp_near_succ, exp_near_sub, _root_.abs_mul]
  convert mul_le_mul_of_nonneg_left (le_sub_iff_add_le'.1 e) _
  · simp [mul_add, pow_succ', div_eq_mul_inv, _root_.abs_mul, _root_.abs_inv, ← pow_abs, mul_inv]
    ac_rfl
  · simp [_root_.div_nonneg, _root_.abs_nonneg]
#align real.exp_approx_succ Real.exp_approx_succ

/- warning: real.exp_approx_end' -> Real.exp_approx_end' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real} {a : Real} {b : Real} (m : Nat), (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) m) -> (forall (rm : Real), (Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) rm) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) a)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) rm) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) rm (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) rm)))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (Real.expNear n x a))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n))) b)))
but is expected to have type
  forall {n : Nat} {x : Real} {a : Real} {b : Real} (m : Nat), (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) m) -> (forall (rm : Real), (Eq.{1} Real (Nat.cast.{0} Real Real.natCast m) rm) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) a)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) rm) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) rm (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) rm)))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (Real.expNear n x a))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) n) (Nat.cast.{0} Real Real.natCast (Nat.factorial n))) b)))
Case conversion may be inaccurate. Consider using '#align real.exp_approx_end' Real.exp_approx_end'ₓ'. -/
theorem exp_approx_end' {n} {x a b : ℝ} (m : ℕ) (e₁ : n + 1 = m) (rm : ℝ) (er : ↑m = rm)
    (h : |x| ≤ 1) (e : |1 - a| ≤ b - |x| / rm * ((rm + 1) / rm)) :
    |exp x - expNear n x a| ≤ |x| ^ n / n ! * b := by
  subst er <;> exact exp_approx_succ _ e₁ _ _ (by simpa using e) (exp_approx_end _ _ _ e₁ h)
#align real.exp_approx_end' Real.exp_approx_end'

/- warning: real.exp_1_approx_succ_eq -> Real.exp_1_approx_succ_eq is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {a₁ : Real} {b₁ : Real} {m : Nat}, (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) m) -> (forall {rm : Real}, (Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) rm) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Real.expNear m (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) a₁ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) rm)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial m))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) b₁ rm))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Real.expNear n (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) a₁))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n))) b₁)))
but is expected to have type
  forall {n : Nat} {a₁ : Real} {b₁ : Real} {m : Nat}, (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) m) -> (forall {rm : Real}, (Eq.{1} Real (Nat.cast.{0} Real Real.natCast m) rm) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Real.expNear m (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) a₁ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) rm)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) m) (Nat.cast.{0} Real Real.natCast (Nat.factorial m))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) b₁ rm))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Real.expNear n (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) a₁))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) n) (Nat.cast.{0} Real Real.natCast (Nat.factorial n))) b₁)))
Case conversion may be inaccurate. Consider using '#align real.exp_1_approx_succ_eq Real.exp_1_approx_succ_eqₓ'. -/
theorem exp_1_approx_succ_eq {n} {a₁ b₁ : ℝ} {m : ℕ} (en : n + 1 = m) {rm : ℝ} (er : ↑m = rm)
    (h : |exp 1 - expNear m 1 ((a₁ - 1) * rm)| ≤ |1| ^ m / m ! * (b₁ * rm)) :
    |exp 1 - expNear n 1 a₁| ≤ |1| ^ n / n ! * b₁ :=
  by
  subst er
  refine' exp_approx_succ _ en _ _ _ h
  field_simp [show (m : ℝ) ≠ 0 by norm_cast <;> linarith]
#align real.exp_1_approx_succ_eq Real.exp_1_approx_succ_eq

/- warning: real.exp_approx_start -> Real.exp_approx_start is a dubious translation:
lean 3 declaration is
  forall (x : Real) (a : Real) (b : Real), (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) (Real.expNear (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) x a))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))) b)) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.exp x) a)) b)
but is expected to have type
  forall (x : Real) (a : Real) (b : Real), (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) (Real.expNear (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) x a))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Nat.cast.{0} Real Real.natCast (Nat.factorial (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) b)) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.exp x) a)) b)
Case conversion may be inaccurate. Consider using '#align real.exp_approx_start Real.exp_approx_startₓ'. -/
theorem exp_approx_start (x a b : ℝ) (h : |exp x - expNear 0 x a| ≤ |x| ^ 0 / 0! * b) :
    |exp x - a| ≤ b := by simpa using h
#align real.exp_approx_start Real.exp_approx_start

/- warning: real.cos_bound -> Real.cos_bound is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.cos x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Nat 4 (OfNat.mk.{0} Nat 4 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 5 (OfNat.mk.{0} Real 5 (bit1.{0} Real Real.hasOne Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (OfNat.ofNat.{0} Real 96 (OfNat.mk.{0} Real 96 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne))))))))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.cos x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 5 (instOfNat.{0} Real 5 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))) (OfNat.ofNat.{0} Real 96 (instOfNat.{0} Real 96 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 94 (instOfNatNat 94))))))))
Case conversion may be inaccurate. Consider using '#align real.cos_bound Real.cos_boundₓ'. -/
theorem cos_bound {x : ℝ} (hx : |x| ≤ 1) : |cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 * (5 / 96) :=
  calc
    |cos x - (1 - x ^ 2 / 2)| = abs (Complex.cos x - (1 - x ^ 2 / 2)) := by
      rw [← abs_of_real] <;> simp [of_real_bit0, of_real_one, of_real_inv]
    _ = abs ((Complex.exp (x * I) + Complex.exp (-x * I) - (2 - x ^ 2)) / 2) := by
      simp [Complex.cos, sub_div, add_div, neg_div, div_self (two_ne_zero' ℂ)]
    _ =
        abs
          (((Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m !) +
              (Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m !)) /
            2) :=
      (congr_arg abs
        (congr_arg (fun x : ℂ => x / 2)
          (by
            simp only [sum_range_succ]
            simp [pow_succ]
            apply Complex.ext <;> simp [div_eq_mul_inv, norm_sq] <;> ring)))
    _ ≤
        abs ((Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m !) / 2) +
          abs ((Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m !) / 2) :=
      by rw [add_div] <;> exact complex.abs.add_le _ _
    _ =
        abs (Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m !) / 2 +
          abs (Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m !) / 2 :=
      by simp [map_div₀]
    _ ≤
        Complex.abs (x * I) ^ 4 * (Nat.succ 4 * (4! * (4 : ℕ))⁻¹) / 2 +
          Complex.abs (-x * I) ^ 4 * (Nat.succ 4 * (4! * (4 : ℕ))⁻¹) / 2 :=
      (add_le_add ((div_le_div_right (by norm_num)).2 (Complex.exp_bound (by simpa) (by decide)))
        ((div_le_div_right (by norm_num)).2 (Complex.exp_bound (by simpa) (by decide))))
    _ ≤ |x| ^ 4 * (5 / 96) := by
      norm_num <;> simp [mul_assoc, mul_comm, mul_left_comm, mul_div_assoc]
    
#align real.cos_bound Real.cos_bound

/- warning: real.sin_bound -> Real.sin_bound is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.sin x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Real 6 (OfNat.mk.{0} Real 6 (bit0.{0} Real Real.hasAdd (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne))))))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Nat 4 (OfNat.mk.{0} Nat 4 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 5 (OfNat.mk.{0} Real 5 (bit1.{0} Real Real.hasOne Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (OfNat.ofNat.{0} Real 96 (OfNat.mk.{0} Real 96 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne))))))))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.sin x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (OfNat.ofNat.{0} Real 6 (instOfNat.{0} Real 6 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))))))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 5 (instOfNat.{0} Real 5 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))) (OfNat.ofNat.{0} Real 96 (instOfNat.{0} Real 96 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 94 (instOfNatNat 94))))))))
Case conversion may be inaccurate. Consider using '#align real.sin_bound Real.sin_boundₓ'. -/
theorem sin_bound {x : ℝ} (hx : |x| ≤ 1) : |sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 4 * (5 / 96) :=
  calc
    |sin x - (x - x ^ 3 / 6)| = abs (Complex.sin x - (x - x ^ 3 / 6)) := by
      rw [← abs_of_real] <;> simp [of_real_bit0, of_real_one, of_real_inv]
    _ = abs (((Complex.exp (-x * I) - Complex.exp (x * I)) * I - (2 * x - x ^ 3 / 3)) / 2) := by
      simp [Complex.sin, sub_div, add_div, neg_div, mul_div_cancel_left _ (two_ne_zero' ℂ), div_div,
        show (3 : ℂ) * 2 = 6 by norm_num]
    _ =
        abs
          (((Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m !) -
                (Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m !)) *
              I /
            2) :=
      (congr_arg abs
        (congr_arg (fun x : ℂ => x / 2)
          (by
            simp only [sum_range_succ]
            simp [pow_succ]
            apply Complex.ext <;> simp [div_eq_mul_inv, norm_sq] <;> ring)))
    _ ≤
        abs ((Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m !) * I / 2) +
          abs (-((Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m !) * I) / 2) :=
      by rw [sub_mul, sub_eq_add_neg, add_div] <;> exact complex.abs.add_le _ _
    _ =
        abs (Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m !) / 2 +
          abs (Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m !) / 2 :=
      by simp [add_comm, map_div₀]
    _ ≤
        Complex.abs (x * I) ^ 4 * (Nat.succ 4 * (4! * (4 : ℕ))⁻¹) / 2 +
          Complex.abs (-x * I) ^ 4 * (Nat.succ 4 * (4! * (4 : ℕ))⁻¹) / 2 :=
      (add_le_add ((div_le_div_right (by norm_num)).2 (Complex.exp_bound (by simpa) (by decide)))
        ((div_le_div_right (by norm_num)).2 (Complex.exp_bound (by simpa) (by decide))))
    _ ≤ |x| ^ 4 * (5 / 96) := by
      norm_num <;> simp [mul_assoc, mul_comm, mul_left_comm, mul_div_assoc]
    
#align real.sin_bound Real.sin_bound

/- warning: real.cos_pos_of_le_one -> Real.cos_pos_of_le_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.cos x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.cos x))
Case conversion may be inaccurate. Consider using '#align real.cos_pos_of_le_one Real.cos_pos_of_le_oneₓ'. -/
theorem cos_pos_of_le_one {x : ℝ} (hx : |x| ≤ 1) : 0 < cos x :=
  calc
    0 < 1 - x ^ 2 / 2 - |x| ^ 4 * (5 / 96) :=
      sub_pos.2 <|
        lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 2 / 2 ≤ 1 * (5 / 96) + 1 / 2 :=
              add_le_add (mul_le_mul_of_nonneg_right (pow_le_one _ (abs_nonneg _) hx) (by norm_num))
                ((div_le_div_right (by norm_num)).2
                  (by
                    rw [sq, ← abs_mul_self, _root_.abs_mul] <;>
                      exact mul_le_one hx (abs_nonneg _) hx))
            _ < 1 := by norm_num
            )
    _ ≤ cos x := sub_le_comm.1 (abs_sub_le_iff.1 (cos_bound hx)).2
    
#align real.cos_pos_of_le_one Real.cos_pos_of_le_one

/- warning: real.sin_pos_of_pos_of_le_one -> Real.sin_pos_of_pos_of_le_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sin x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sin x))
Case conversion may be inaccurate. Consider using '#align real.sin_pos_of_pos_of_le_one Real.sin_pos_of_pos_of_le_oneₓ'. -/
theorem sin_pos_of_pos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) : 0 < sin x :=
  calc
    0 < x - x ^ 3 / 6 - |x| ^ 4 * (5 / 96) :=
      sub_pos.2 <|
        lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 3 / 6 ≤ x * (5 / 96) + x / 6 :=
              add_le_add
                (mul_le_mul_of_nonneg_right
                  (calc
                    |x| ^ 4 ≤ |x| ^ 1 :=
                      pow_le_pow_of_le_one (abs_nonneg _)
                        (by rwa [_root_.abs_of_nonneg (le_of_lt hx0)]) (by decide)
                    _ = x := by simp [_root_.abs_of_nonneg (le_of_lt hx0)]
                    )
                  (by norm_num))
                ((div_le_div_right (by norm_num)).2
                  (calc
                    x ^ 3 ≤ x ^ 1 := pow_le_pow_of_le_one (le_of_lt hx0) hx (by decide)
                    _ = x := pow_one _
                    ))
            _ < x := by linarith
            )
    _ ≤ sin x :=
      sub_le_comm.1 (abs_sub_le_iff.1 (sin_bound (by rwa [_root_.abs_of_nonneg (le_of_lt hx0)]))).2
    
#align real.sin_pos_of_pos_of_le_one Real.sin_pos_of_pos_of_le_one

/- warning: real.sin_pos_of_pos_of_le_two -> Real.sin_pos_of_pos_of_le_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sin x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sin x))
Case conversion may be inaccurate. Consider using '#align real.sin_pos_of_pos_of_le_two Real.sin_pos_of_pos_of_le_twoₓ'. -/
theorem sin_pos_of_pos_of_le_two {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 2) : 0 < sin x :=
  have : x / 2 ≤ 1 := (div_le_iff (by norm_num)).mpr (by simpa)
  calc
    0 < 2 * sin (x / 2) * cos (x / 2) :=
      mul_pos (mul_pos (by norm_num) (sin_pos_of_pos_of_le_one (half_pos hx0) this))
        (cos_pos_of_le_one (by rwa [_root_.abs_of_nonneg (le_of_lt (half_pos hx0))]))
    _ = sin x := by rw [← sin_two_mul, two_mul, add_halves]
    
#align real.sin_pos_of_pos_of_le_two Real.sin_pos_of_pos_of_le_two

/- warning: real.cos_one_le -> Real.cos_one_le is a dubious translation:
lean 3 declaration is
  LE.le.{0} Real Real.hasLe (Real.cos (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 3 (OfNat.mk.{0} Real 3 (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  LE.le.{0} Real Real.instLEReal (Real.cos (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (OfNat.ofNat.{0} Real 3 (instOfNat.{0} Real 3 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
Case conversion may be inaccurate. Consider using '#align real.cos_one_le Real.cos_one_leₓ'. -/
theorem cos_one_le : cos 1 ≤ 2 / 3 :=
  calc
    cos 1 ≤ |(1 : ℝ)| ^ 4 * (5 / 96) + (1 - 1 ^ 2 / 2) :=
      sub_le_iff_le_add.1 (abs_sub_le_iff.1 (cos_bound (by simp))).1
    _ ≤ 2 / 3 := by norm_num
    
#align real.cos_one_le Real.cos_one_le

/- warning: real.cos_one_pos -> Real.cos_one_pos is a dubious translation:
lean 3 declaration is
  LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.cos (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.cos (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.cos_one_pos Real.cos_one_posₓ'. -/
theorem cos_one_pos : 0 < cos 1 :=
  cos_pos_of_le_one (le_of_eq abs_one)
#align real.cos_one_pos Real.cos_one_pos

/- warning: real.cos_two_neg -> Real.cos_two_neg is a dubious translation:
lean 3 declaration is
  LT.lt.{0} Real Real.hasLt (Real.cos (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  LT.lt.{0} Real Real.instLTReal (Real.cos (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.cos_two_neg Real.cos_two_negₓ'. -/
theorem cos_two_neg : cos 2 < 0 :=
  calc
    cos 2 = cos (2 * 1) := congr_arg cos (mul_one _).symm
    _ = _ := (Real.cos_two_mul 1)
    _ ≤ 2 * (2 / 3) ^ 2 - 1 :=
      (sub_le_sub_right
        (mul_le_mul_of_nonneg_left
          (by
            rw [sq, sq]
            exact mul_self_le_mul_self (le_of_lt cos_one_pos) cos_one_le)
          zero_le_two)
        _)
    _ < 0 := by norm_num
    
#align real.cos_two_neg Real.cos_two_neg

theorem exp_bound_div_one_sub_of_interval_approx {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) :
    (∑ j : ℕ in Finset.range 3, x ^ j / j.factorial) +
        x ^ 3 * ((3 : ℕ) + 1) / ((3 : ℕ).factorial * (3 : ℕ)) ≤
      ∑ j in Finset.range 3, x ^ j :=
  by
  norm_num [Finset.sum]
  rw [add_assoc, add_comm (x + 1) (x ^ 3 * 4 / 18), ← add_assoc, add_le_add_iff_right, ←
    add_le_add_iff_left (-(x ^ 2 / 2)), ← add_assoc, CommRing.add_left_neg (x ^ 2 / 2), zero_add,
    neg_add_eq_sub, sub_half, sq, pow_succ, sq]
  have i1 : x * 4 / 18 ≤ 1 / 2 := by linarith
  have i2 : 0 ≤ x * 4 / 18 := by linarith
  have i3 := mul_le_mul h1 h1 le_rfl h1
  rw [MulZeroClass.zero_mul] at i3
  have t := mul_le_mul le_rfl i1 i2 i3
  rw [← mul_assoc]
  rwa [mul_one_div, ← mul_div_assoc, ← mul_assoc] at t
#align real.exp_bound_div_one_sub_of_interval_approx Real.exp_bound_div_one_sub_of_interval_approxₓ

/- warning: real.exp_bound_div_one_sub_of_interval -> Real.exp_bound_div_one_sub_of_interval is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Real.exp x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x)))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Real.exp x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x)))
Case conversion may be inaccurate. Consider using '#align real.exp_bound_div_one_sub_of_interval Real.exp_bound_div_one_sub_of_intervalₓ'. -/
theorem exp_bound_div_one_sub_of_interval {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) :
    Real.exp x ≤ 1 / (1 - x) :=
  haveI h : (∑ j in Finset.range 3, x ^ j) ≤ 1 / (1 - x) :=
    by
    norm_num [Finset.sum]
    have h1x : 0 < 1 - x := by simpa
    rw [le_div_iff h1x]
    norm_num [← add_assoc, mul_sub_left_distrib, mul_one, add_mul, sub_add_eq_sub_sub,
      pow_succ' x 2]
    have hx3 : 0 ≤ x ^ 3 := by
      norm_num
      exact h1
    linarith
  (exp_bound' h1 h2.le <| by linarith).trans
    ((exp_bound_div_one_sub_of_interval_approx h1 h2.le).trans h)
#align real.exp_bound_div_one_sub_of_interval Real.exp_bound_div_one_sub_of_interval

/- warning: real.one_sub_le_exp_minus_of_pos -> Real.one_sub_le_exp_minus_of_pos is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LE.le.{0} Real Real.hasLe (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) y) (Real.exp (Neg.neg.{0} Real Real.hasNeg y)))
but is expected to have type
  forall {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LE.le.{0} Real Real.instLEReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) y) (Real.exp (Neg.neg.{0} Real Real.instNegReal y)))
Case conversion may be inaccurate. Consider using '#align real.one_sub_le_exp_minus_of_pos Real.one_sub_le_exp_minus_of_posₓ'. -/
theorem one_sub_le_exp_minus_of_pos {y : ℝ} (h : 0 ≤ y) : 1 - y ≤ Real.exp (-y) :=
  by
  rw [Real.exp_neg]
  have r1 : (1 - y) * Real.exp y ≤ 1 :=
    by
    cases le_or_lt (1 - y) 0
    · have h'' : (1 - y) * y.exp ≤ 0 := by
        rw [mul_nonpos_iff]
        right
        exact ⟨h_1, y.exp_pos.le⟩
      linarith
    have hy1 : y < 1 := by linarith
    rw [← le_div_iff' h_1]
    exact exp_bound_div_one_sub_of_interval h hy1
  rw [inv_eq_one_div]
  rw [le_div_iff' y.exp_pos]
  rwa [mul_comm] at r1
#align real.one_sub_le_exp_minus_of_pos Real.one_sub_le_exp_minus_of_pos

/- warning: real.add_one_le_exp_of_nonpos -> Real.add_one_le_exp_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} Real Real.hasLe (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Real.exp x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} Real Real.instLEReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Real.exp x))
Case conversion may be inaccurate. Consider using '#align real.add_one_le_exp_of_nonpos Real.add_one_le_exp_of_nonposₓ'. -/
theorem add_one_le_exp_of_nonpos {x : ℝ} (h : x ≤ 0) : x + 1 ≤ Real.exp x :=
  by
  rw [add_comm]
  have h1 : 0 ≤ -x := by linarith
  simpa using one_sub_le_exp_minus_of_pos h1
#align real.add_one_le_exp_of_nonpos Real.add_one_le_exp_of_nonpos

/- warning: real.add_one_le_exp -> Real.add_one_le_exp is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Real.exp x)
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Real.exp x)
Case conversion may be inaccurate. Consider using '#align real.add_one_le_exp Real.add_one_le_expₓ'. -/
theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x :=
  by
  cases le_or_lt 0 x
  · exact Real.add_one_le_exp_of_nonneg h
  exact add_one_le_exp_of_nonpos h.le
#align real.add_one_le_exp Real.add_one_le_exp

/- warning: real.one_sub_div_pow_le_exp_neg -> Real.one_sub_div_pow_le_exp_neg is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {t : Real}, (LE.le.{0} Real Real.hasLe t ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)) -> (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) t ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) n) (Real.exp (Neg.neg.{0} Real Real.hasNeg t)))
but is expected to have type
  forall {n : Nat} {t : Real}, (LE.le.{0} Real Real.instLEReal t (Nat.cast.{0} Real Real.natCast n)) -> (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) t (Nat.cast.{0} Real Real.natCast n))) n) (Real.exp (Neg.neg.{0} Real Real.instNegReal t)))
Case conversion may be inaccurate. Consider using '#align real.one_sub_div_pow_le_exp_neg Real.one_sub_div_pow_le_exp_negₓ'. -/
theorem one_sub_div_pow_le_exp_neg {n : ℕ} {t : ℝ} (ht' : t ≤ n) : (1 - t / n) ^ n ≤ exp (-t) :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    rwa [Nat.cast_zero] at ht'
  convert pow_le_pow_of_le_left _ (add_one_le_exp (-(t / n))) n
  · abel
  · rw [← Real.exp_nat_mul]
    congr 1
    field_simp [nat.cast_ne_zero.mpr hn]
    ring
  · rwa [add_comm, ← sub_eq_add_neg, sub_nonneg, div_le_one]
    positivity
#align real.one_sub_div_pow_le_exp_neg Real.one_sub_div_pow_le_exp_neg

end Real

namespace Tactic

open Positivity Real

/-- Extension for the `positivity` tactic: `real.exp` is always positive. -/
@[positivity]
unsafe def positivity_exp : expr → tactic strictness
  | q(Real.exp $(a)) => positive <$> mk_app `real.exp_pos [a]
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `real.exp r`"
#align tactic.positivity_exp tactic.positivity_exp

end Tactic

namespace Complex

/- warning: complex.abs_cos_add_sin_mul_I -> Complex.abs_cos_add_sin_mul_I is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x)) Complex.I))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' x)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' x)) Complex.I))) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' x)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' x)) Complex.I))) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' x)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' x)) Complex.I))) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' x)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' x)) Complex.I))) Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align complex.abs_cos_add_sin_mul_I Complex.abs_cos_add_sin_mul_Iₓ'. -/
@[simp]
theorem abs_cos_add_sin_mul_I (x : ℝ) : abs (cos x + sin x * I) = 1 :=
  by
  have := Real.sin_sq_add_cos_sq x
  simp_all [add_comm, abs, norm_sq, sq, sin_of_real_re, cos_of_real_re, mul_re]
#align complex.abs_cos_add_sin_mul_I Complex.abs_cos_add_sin_mul_I

/- warning: complex.abs_exp_of_real -> Complex.abs_exp_ofReal is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (Complex.exp ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))) (Real.exp x)
but is expected to have type
  forall (x : Real), Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Complex.exp (Complex.ofReal' x))) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (Complex.exp (Complex.ofReal' x))) (Real.exp x)
Case conversion may be inaccurate. Consider using '#align complex.abs_exp_of_real Complex.abs_exp_ofRealₓ'. -/
@[simp]
theorem abs_exp_ofReal (x : ℝ) : abs (exp x) = Real.exp x := by
  rw [← of_real_exp] <;> exact abs_of_nonneg (le_of_lt (Real.exp_pos _))
#align complex.abs_exp_of_real Complex.abs_exp_ofReal

/- warning: complex.abs_exp_of_real_mul_I -> Complex.abs_exp_ofReal_mul_I is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) Complex.I))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' x) Complex.I))) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' x) Complex.I))) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' x) Complex.I))) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' x) Complex.I))) Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align complex.abs_exp_of_real_mul_I Complex.abs_exp_ofReal_mul_Iₓ'. -/
@[simp]
theorem abs_exp_ofReal_mul_I (x : ℝ) : abs (exp (x * I)) = 1 := by
  rw [exp_mul_I, abs_cos_add_sin_mul_I]
#align complex.abs_exp_of_real_mul_I Complex.abs_exp_ofReal_mul_I

/- warning: complex.abs_exp -> Complex.abs_exp is a dubious translation:
lean 3 declaration is
  forall (z : Complex), Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (Complex.exp z)) (Real.exp (Complex.re z))
but is expected to have type
  forall (z : Complex), Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Complex.exp z)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (Complex.exp z)) (Real.exp (Complex.re z))
Case conversion may be inaccurate. Consider using '#align complex.abs_exp Complex.abs_expₓ'. -/
theorem abs_exp (z : ℂ) : abs (exp z) = Real.exp z.re := by
  rw [exp_eq_exp_re_mul_sin_add_cos, map_mul, abs_exp_of_real, abs_cos_add_sin_mul_I, mul_one]
#align complex.abs_exp Complex.abs_exp

/- warning: complex.abs_exp_eq_iff_re_eq -> Complex.abs_exp_eq_iff_re_eq is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (Complex.exp x)) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (Complex.exp y))) (Eq.{1} Real (Complex.re x) (Complex.re y))
but is expected to have type
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Complex.exp x)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (Complex.exp x)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))))))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real (DivisionSemiring.toSemiring.{0} Complex (Semifield.toDivisionSemiring.{0} Complex (Field.toSemifield.{0} Complex Complex.instFieldComplex))) Real.orderedSemiring)) Complex.abs (Complex.exp y))) (Eq.{1} Real (Complex.re x) (Complex.re y))
Case conversion may be inaccurate. Consider using '#align complex.abs_exp_eq_iff_re_eq Complex.abs_exp_eq_iff_re_eqₓ'. -/
theorem abs_exp_eq_iff_re_eq {x y : ℂ} : abs (exp x) = abs (exp y) ↔ x.re = y.re := by
  rw [abs_exp, abs_exp, Real.exp_eq_exp]
#align complex.abs_exp_eq_iff_re_eq Complex.abs_exp_eq_iff_re_eq

end Complex

