/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov

! This file was ported from Lean 3 source module data.set.intervals.disjoint
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Lattice

/-!
# Extra lemmas about intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains lemmas about intervals that cannot be included into `data.set.intervals.basic`
because this would create an `import` cycle. Namely, lemmas in this file can use definitions
from `data.set.lattice`, including `disjoint`.
-/


universe u v w

variable {ι : Sort u} {α : Type v} {β : Type w}

open Set

open OrderDual (toDual)

namespace Set

section Preorder

variable [Preorder α] {a b c : α}

/- warning: set.Iic_disjoint_Ioi -> Set.Iic_disjoint_Ioi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.Iic.{u1} α _inst_1 a) (Set.Ioi.{u1} α _inst_1 b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.Iic.{u1} α _inst_1 a) (Set.Ioi.{u1} α _inst_1 b))
Case conversion may be inaccurate. Consider using '#align set.Iic_disjoint_Ioi Set.Iic_disjoint_Ioiₓ'. -/
@[simp]
theorem Iic_disjoint_Ioi (h : a ≤ b) : Disjoint (Iic a) (Ioi b) :=
  disjoint_left.mpr fun x ha hb => (h.trans_lt hb).not_le ha
#align set.Iic_disjoint_Ioi Set.Iic_disjoint_Ioi

/- warning: set.Iic_disjoint_Ioc -> Set.Iic_disjoint_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.Iic.{u1} α _inst_1 a) (Set.Ioc.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.Iic.{u1} α _inst_1 a) (Set.Ioc.{u1} α _inst_1 b c))
Case conversion may be inaccurate. Consider using '#align set.Iic_disjoint_Ioc Set.Iic_disjoint_Iocₓ'. -/
@[simp]
theorem Iic_disjoint_Ioc (h : a ≤ b) : Disjoint (Iic a) (Ioc b c) :=
  (Iic_disjoint_Ioi h).mono le_rfl fun _ => And.left
#align set.Iic_disjoint_Ioc Set.Iic_disjoint_Ioc

/- warning: set.Ioc_disjoint_Ioc_same -> Set.Ioc_disjoint_Ioc_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.Ioc.{u1} α _inst_1 a b) (Set.Ioc.{u1} α _inst_1 b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.Ioc.{u1} α _inst_1 a b) (Set.Ioc.{u1} α _inst_1 b c)
Case conversion may be inaccurate. Consider using '#align set.Ioc_disjoint_Ioc_same Set.Ioc_disjoint_Ioc_sameₓ'. -/
@[simp]
theorem Ioc_disjoint_Ioc_same {a b c : α} : Disjoint (Ioc a b) (Ioc b c) :=
  (Iic_disjoint_Ioc (le_refl b)).mono (fun _ => And.right) le_rfl
#align set.Ioc_disjoint_Ioc_same Set.Ioc_disjoint_Ioc_same

/- warning: set.Ico_disjoint_Ico_same -> Set.Ico_disjoint_Ico_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.Ico.{u1} α _inst_1 a b) (Set.Ico.{u1} α _inst_1 b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.Ico.{u1} α _inst_1 a b) (Set.Ico.{u1} α _inst_1 b c)
Case conversion may be inaccurate. Consider using '#align set.Ico_disjoint_Ico_same Set.Ico_disjoint_Ico_sameₓ'. -/
@[simp]
theorem Ico_disjoint_Ico_same {a b c : α} : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.mpr fun x hab hbc => hab.2.not_le hbc.1
#align set.Ico_disjoint_Ico_same Set.Ico_disjoint_Ico_same

/- warning: set.Ici_disjoint_Iic -> Set.Ici_disjoint_Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.Ici.{u1} α _inst_1 a) (Set.Iic.{u1} α _inst_1 b)) (Not (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.Ici.{u1} α _inst_1 a) (Set.Iic.{u1} α _inst_1 b)) (Not (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align set.Ici_disjoint_Iic Set.Ici_disjoint_Iicₓ'. -/
@[simp]
theorem Ici_disjoint_Iic : Disjoint (Ici a) (Iic b) ↔ ¬a ≤ b := by
  rw [Set.disjoint_iff_inter_eq_empty, Ici_inter_Iic, Icc_eq_empty_iff]
#align set.Ici_disjoint_Iic Set.Ici_disjoint_Iic

/- warning: set.Iic_disjoint_Ici -> Set.Iic_disjoint_Ici is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.Iic.{u1} α _inst_1 a) (Set.Ici.{u1} α _inst_1 b)) (Not (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.Iic.{u1} α _inst_1 a) (Set.Ici.{u1} α _inst_1 b)) (Not (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a))
Case conversion may be inaccurate. Consider using '#align set.Iic_disjoint_Ici Set.Iic_disjoint_Iciₓ'. -/
@[simp]
theorem Iic_disjoint_Ici : Disjoint (Iic a) (Ici b) ↔ ¬b ≤ a :=
  disjoint_comm.trans Ici_disjoint_Iic
#align set.Iic_disjoint_Ici Set.Iic_disjoint_Ici

#print Set.unionᵢ_Iic /-
@[simp]
theorem unionᵢ_Iic : (⋃ a : α, Iic a) = univ :=
  unionᵢ_eq_univ_iff.2 fun x => ⟨x, right_mem_Iic⟩
#align set.Union_Iic Set.unionᵢ_Iic
-/

#print Set.unionᵢ_Ici /-
@[simp]
theorem unionᵢ_Ici : (⋃ a : α, Ici a) = univ :=
  unionᵢ_eq_univ_iff.2 fun x => ⟨x, left_mem_Ici⟩
#align set.Union_Ici Set.unionᵢ_Ici
-/

#print Set.unionᵢ_Icc_right /-
@[simp]
theorem unionᵢ_Icc_right (a : α) : (⋃ b, Icc a b) = Ici a := by
  simp only [← Ici_inter_Iic, ← inter_Union, Union_Iic, inter_univ]
#align set.Union_Icc_right Set.unionᵢ_Icc_right
-/

#print Set.unionᵢ_Ioc_right /-
@[simp]
theorem unionᵢ_Ioc_right (a : α) : (⋃ b, Ioc a b) = Ioi a := by
  simp only [← Ioi_inter_Iic, ← inter_Union, Union_Iic, inter_univ]
#align set.Union_Ioc_right Set.unionᵢ_Ioc_right
-/

#print Set.unionᵢ_Icc_left /-
@[simp]
theorem unionᵢ_Icc_left (b : α) : (⋃ a, Icc a b) = Iic b := by
  simp only [← Ici_inter_Iic, ← Union_inter, Union_Ici, univ_inter]
#align set.Union_Icc_left Set.unionᵢ_Icc_left
-/

#print Set.unionᵢ_Ico_left /-
@[simp]
theorem unionᵢ_Ico_left (b : α) : (⋃ a, Ico a b) = Iio b := by
  simp only [← Ici_inter_Iio, ← Union_inter, Union_Ici, univ_inter]
#align set.Union_Ico_left Set.unionᵢ_Ico_left
-/

#print Set.unionᵢ_Iio /-
@[simp]
theorem unionᵢ_Iio [NoMaxOrder α] : (⋃ a : α, Iio a) = univ :=
  unionᵢ_eq_univ_iff.2 exists_gt
#align set.Union_Iio Set.unionᵢ_Iio
-/

#print Set.unionᵢ_Ioi /-
@[simp]
theorem unionᵢ_Ioi [NoMinOrder α] : (⋃ a : α, Ioi a) = univ :=
  unionᵢ_eq_univ_iff.2 exists_lt
#align set.Union_Ioi Set.unionᵢ_Ioi
-/

#print Set.unionᵢ_Ico_right /-
@[simp]
theorem unionᵢ_Ico_right [NoMaxOrder α] (a : α) : (⋃ b, Ico a b) = Ici a := by
  simp only [← Ici_inter_Iio, ← inter_Union, Union_Iio, inter_univ]
#align set.Union_Ico_right Set.unionᵢ_Ico_right
-/

#print Set.unionᵢ_Ioo_right /-
@[simp]
theorem unionᵢ_Ioo_right [NoMaxOrder α] (a : α) : (⋃ b, Ioo a b) = Ioi a := by
  simp only [← Ioi_inter_Iio, ← inter_Union, Union_Iio, inter_univ]
#align set.Union_Ioo_right Set.unionᵢ_Ioo_right
-/

#print Set.unionᵢ_Ioc_left /-
@[simp]
theorem unionᵢ_Ioc_left [NoMinOrder α] (b : α) : (⋃ a, Ioc a b) = Iic b := by
  simp only [← Ioi_inter_Iic, ← Union_inter, Union_Ioi, univ_inter]
#align set.Union_Ioc_left Set.unionᵢ_Ioc_left
-/

#print Set.unionᵢ_Ioo_left /-
@[simp]
theorem unionᵢ_Ioo_left [NoMinOrder α] (b : α) : (⋃ a, Ioo a b) = Iio b := by
  simp only [← Ioi_inter_Iio, ← Union_inter, Union_Ioi, univ_inter]
#align set.Union_Ioo_left Set.unionᵢ_Ioo_left
-/

end Preorder

section LinearOrder

variable [LinearOrder α] {a₁ a₂ b₁ b₂ : α}

/- warning: set.Ico_disjoint_Ico -> Set.Ico_disjoint_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a₁ a₂) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) b₁ b₂)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.min.{u1} α _inst_1 a₂ b₂) (LinearOrder.max.{u1} α _inst_1 a₁ b₁))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) a₁ a₂) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) b₁ b₂)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a₂ b₂) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a₁ b₁))
Case conversion may be inaccurate. Consider using '#align set.Ico_disjoint_Ico Set.Ico_disjoint_Icoₓ'. -/
@[simp]
theorem Ico_disjoint_Ico : Disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff, inf_eq_min, sup_eq_max,
    not_lt]
#align set.Ico_disjoint_Ico Set.Ico_disjoint_Ico

/- warning: set.Ioc_disjoint_Ioc -> Set.Ioc_disjoint_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a₁ a₂) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) b₁ b₂)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.min.{u1} α _inst_1 a₂ b₂) (LinearOrder.max.{u1} α _inst_1 a₁ b₁))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) a₁ a₂) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) b₁ b₂)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a₂ b₂) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a₁ b₁))
Case conversion may be inaccurate. Consider using '#align set.Ioc_disjoint_Ioc Set.Ioc_disjoint_Iocₓ'. -/
@[simp]
theorem Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ :=
  by
  have h : _ ↔ min (toDual a₁) (toDual b₁) ≤ max (toDual a₂) (toDual b₂) := Ico_disjoint_Ico
  simpa only [dual_Ico] using h
#align set.Ioc_disjoint_Ioc Set.Ioc_disjoint_Ioc

/- warning: set.eq_of_Ico_disjoint -> Set.eq_of_Ico_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {x₁ : α} {x₂ : α} {y₁ : α} {y₂ : α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) x₁ x₂) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) y₁ y₂)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x₁ x₂) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x₂ (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) y₁ y₂)) -> (Eq.{succ u1} α y₁ x₂)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {x₁ : α} {x₂ : α} {y₁ : α} {y₂ : α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) x₁ x₂) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) y₁ y₂)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x₁ x₂) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x₂ (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) y₁ y₂)) -> (Eq.{succ u1} α y₁ x₂)
Case conversion may be inaccurate. Consider using '#align set.eq_of_Ico_disjoint Set.eq_of_Ico_disjointₓ'. -/
/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
theorem eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α} (h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂)
    (h2 : x₂ ∈ Ico y₁ y₂) : y₁ = x₂ :=
  by
  rw [Ico_disjoint_Ico, min_eq_left (le_of_lt h2.2), le_max_iff] at h
  apply le_antisymm h2.1
  exact h.elim (fun h => absurd hx (not_lt_of_le h)) id
#align set.eq_of_Ico_disjoint Set.eq_of_Ico_disjoint

#print Set.unionᵢ_Ico_eq_Iio_self_iff /-
@[simp]
theorem unionᵢ_Ico_eq_Iio_self_iff {f : ι → α} {a : α} :
    (⋃ i, Ico (f i) a) = Iio a ↔ ∀ x < a, ∃ i, f i ≤ x := by
  simp [← Ici_inter_Iio, ← Union_inter, subset_def]
#align set.Union_Ico_eq_Iio_self_iff Set.unionᵢ_Ico_eq_Iio_self_iff
-/

#print Set.unionᵢ_Ioc_eq_Ioi_self_iff /-
@[simp]
theorem unionᵢ_Ioc_eq_Ioi_self_iff {f : ι → α} {a : α} :
    (⋃ i, Ioc a (f i)) = Ioi a ↔ ∀ x, a < x → ∃ i, x ≤ f i := by
  simp [← Ioi_inter_Iic, ← inter_Union, subset_def]
#align set.Union_Ioc_eq_Ioi_self_iff Set.unionᵢ_Ioc_eq_Ioi_self_iff
-/

#print Set.bunionᵢ_Ico_eq_Iio_self_iff /-
@[simp]
theorem bunionᵢ_Ico_eq_Iio_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    (⋃ (i) (hi : p i), Ico (f i hi) a) = Iio a ↔ ∀ x < a, ∃ i hi, f i hi ≤ x := by
  simp [← Ici_inter_Iio, ← Union_inter, subset_def]
#align set.bUnion_Ico_eq_Iio_self_iff Set.bunionᵢ_Ico_eq_Iio_self_iff
-/

#print Set.bunionᵢ_Ioc_eq_Ioi_self_iff /-
@[simp]
theorem bunionᵢ_Ioc_eq_Ioi_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    (⋃ (i) (hi : p i), Ioc a (f i hi)) = Ioi a ↔ ∀ x, a < x → ∃ i hi, x ≤ f i hi := by
  simp [← Ioi_inter_Iic, ← inter_Union, subset_def]
#align set.bUnion_Ioc_eq_Ioi_self_iff Set.bunionᵢ_Ioc_eq_Ioi_self_iff
-/

end LinearOrder

end Set

section UnionIxx

variable [LinearOrder α] {s : Set α} {a : α} {f : ι → α}

#print IsGLB.bunionᵢ_Ioi_eq /-
theorem IsGLB.bunionᵢ_Ioi_eq (h : IsGLB s a) : (⋃ x ∈ s, Ioi x) = Ioi a :=
  by
  refine' (Union₂_subset fun x hx => _).antisymm fun x hx => _
  · exact Ioi_subset_Ioi (h.1 hx)
  · rcases h.exists_between hx with ⟨y, hys, hay, hyx⟩
    exact mem_bUnion hys hyx
#align is_glb.bUnion_Ioi_eq IsGLB.bunionᵢ_Ioi_eq
-/

#print IsGLB.unionᵢ_Ioi_eq /-
theorem IsGLB.unionᵢ_Ioi_eq (h : IsGLB (range f) a) : (⋃ x, Ioi (f x)) = Ioi a :=
  bunionᵢ_range.symm.trans h.bunionᵢ_Ioi_eq
#align is_glb.Union_Ioi_eq IsGLB.unionᵢ_Ioi_eq
-/

#print IsLUB.bunionᵢ_Iio_eq /-
theorem IsLUB.bunionᵢ_Iio_eq (h : IsLUB s a) : (⋃ x ∈ s, Iio x) = Iio a :=
  h.dual.bunionᵢ_Ioi_eq
#align is_lub.bUnion_Iio_eq IsLUB.bunionᵢ_Iio_eq
-/

#print IsLUB.unionᵢ_Iio_eq /-
theorem IsLUB.unionᵢ_Iio_eq (h : IsLUB (range f) a) : (⋃ x, Iio (f x)) = Iio a :=
  h.dual.unionᵢ_Ioi_eq
#align is_lub.Union_Iio_eq IsLUB.unionᵢ_Iio_eq
-/

#print IsGLB.bunionᵢ_Ici_eq_Ioi /-
theorem IsGLB.bunionᵢ_Ici_eq_Ioi (a_glb : IsGLB s a) (a_not_mem : a ∉ s) :
    (⋃ x ∈ s, Ici x) = Ioi a :=
  by
  refine' (Union₂_subset fun x hx => _).antisymm fun x hx => _
  · exact Ici_subset_Ioi.mpr (lt_of_le_of_ne (a_glb.1 hx) fun h => (h ▸ a_not_mem) hx)
  · rcases a_glb.exists_between hx with ⟨y, hys, hay, hyx⟩
    apply mem_Union₂.mpr
    refine' ⟨y, hys, hyx.le⟩
#align is_glb.bUnion_Ici_eq_Ioi IsGLB.bunionᵢ_Ici_eq_Ioi
-/

#print IsGLB.bunionᵢ_Ici_eq_Ici /-
theorem IsGLB.bunionᵢ_Ici_eq_Ici (a_glb : IsGLB s a) (a_mem : a ∈ s) : (⋃ x ∈ s, Ici x) = Ici a :=
  by
  refine' (Union₂_subset fun x hx => _).antisymm fun x hx => _
  · exact Ici_subset_Ici.mpr (mem_lower_bounds.mp a_glb.1 x hx)
  · apply mem_Union₂.mpr
    refine' ⟨a, a_mem, hx⟩
#align is_glb.bUnion_Ici_eq_Ici IsGLB.bunionᵢ_Ici_eq_Ici
-/

#print IsLUB.bunionᵢ_Iic_eq_Iio /-
theorem IsLUB.bunionᵢ_Iic_eq_Iio (a_lub : IsLUB s a) (a_not_mem : a ∉ s) :
    (⋃ x ∈ s, Iic x) = Iio a :=
  a_lub.dual.bunionᵢ_Ici_eq_Ioi a_not_mem
#align is_lub.bUnion_Iic_eq_Iio IsLUB.bunionᵢ_Iic_eq_Iio
-/

#print IsLUB.bunionᵢ_Iic_eq_Iic /-
theorem IsLUB.bunionᵢ_Iic_eq_Iic (a_lub : IsLUB s a) (a_mem : a ∈ s) : (⋃ x ∈ s, Iic x) = Iic a :=
  a_lub.dual.bunionᵢ_Ici_eq_Ici a_mem
#align is_lub.bUnion_Iic_eq_Iic IsLUB.bunionᵢ_Iic_eq_Iic
-/

/- warning: Union_Ici_eq_Ioi_infi -> unionᵢ_Ici_eq_Ioi_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {R : Type.{u2}} [_inst_2 : CompleteLinearOrder.{u2} R] {f : ι -> R}, (Not (Membership.Mem.{u2, u2} R (Set.{u2} R) (Set.hasMem.{u2} R) (infᵢ.{u2, u1} R (CompleteSemilatticeInf.toHasInf.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))) ι (fun (i : ι) => f i)) (Set.range.{u2, u1} R ι f))) -> (Eq.{succ u2} (Set.{u2} R) (Set.unionᵢ.{u2, u1} R ι (fun (i : ι) => Set.Ici.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (f i))) (Set.Ioi.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (infᵢ.{u2, u1} R (CompleteSemilatticeInf.toHasInf.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {ι : Sort.{u2}} {R : Type.{u1}} [_inst_2 : CompleteLinearOrder.{u1} R] {f : ι -> R}, (Not (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) (infᵢ.{u1, u2} R (CompleteLattice.toInfSet.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) ι (fun (i : ι) => f i)) (Set.range.{u1, u2} R ι f))) -> (Eq.{succ u1} (Set.{u1} R) (Set.unionᵢ.{u1, u2} R ι (fun (i : ι) => Set.Ici.{u1} R (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (f i))) (Set.Ioi.{u1} R (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (infᵢ.{u1, u2} R (CompleteLattice.toInfSet.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align Union_Ici_eq_Ioi_infi unionᵢ_Ici_eq_Ioi_infᵢₓ'. -/
theorem unionᵢ_Ici_eq_Ioi_infᵢ {R : Type _} [CompleteLinearOrder R] {f : ι → R}
    (no_least_elem : (⨅ i, f i) ∉ range f) : (⋃ i : ι, Ici (f i)) = Ioi (⨅ i, f i) := by
  simp only [← IsGLB.bunionᵢ_Ici_eq_Ioi (@isGLB_infᵢ _ _ _ f) no_least_elem, mem_range,
    Union_exists, Union_Union_eq']
#align Union_Ici_eq_Ioi_infi unionᵢ_Ici_eq_Ioi_infᵢ

/- warning: Union_Iic_eq_Iio_supr -> unionᵢ_Iic_eq_Iio_supᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {R : Type.{u2}} [_inst_2 : CompleteLinearOrder.{u2} R] {f : ι -> R}, (Not (Membership.Mem.{u2, u2} R (Set.{u2} R) (Set.hasMem.{u2} R) (supᵢ.{u2, u1} R (CompleteSemilatticeSup.toHasSup.{u2} R (CompleteLattice.toCompleteSemilatticeSup.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))) ι (fun (i : ι) => f i)) (Set.range.{u2, u1} R ι f))) -> (Eq.{succ u2} (Set.{u2} R) (Set.unionᵢ.{u2, u1} R ι (fun (i : ι) => Set.Iic.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (f i))) (Set.Iio.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (supᵢ.{u2, u1} R (CompleteSemilatticeSup.toHasSup.{u2} R (CompleteLattice.toCompleteSemilatticeSup.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {ι : Sort.{u2}} {R : Type.{u1}} [_inst_2 : CompleteLinearOrder.{u1} R] {f : ι -> R}, (Not (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) (supᵢ.{u1, u2} R (CompleteLattice.toSupSet.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) ι (fun (i : ι) => f i)) (Set.range.{u1, u2} R ι f))) -> (Eq.{succ u1} (Set.{u1} R) (Set.unionᵢ.{u1, u2} R ι (fun (i : ι) => Set.Iic.{u1} R (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (f i))) (Set.Iio.{u1} R (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (supᵢ.{u1, u2} R (CompleteLattice.toSupSet.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align Union_Iic_eq_Iio_supr unionᵢ_Iic_eq_Iio_supᵢₓ'. -/
theorem unionᵢ_Iic_eq_Iio_supᵢ {R : Type _} [CompleteLinearOrder R] {f : ι → R}
    (no_greatest_elem : (⨆ i, f i) ∉ range f) : (⋃ i : ι, Iic (f i)) = Iio (⨆ i, f i) :=
  @unionᵢ_Ici_eq_Ioi_infᵢ ι (OrderDual R) _ f no_greatest_elem
#align Union_Iic_eq_Iio_supr unionᵢ_Iic_eq_Iio_supᵢ

/- warning: Union_Ici_eq_Ici_infi -> unionᵢ_Ici_eq_Ici_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {R : Type.{u2}} [_inst_2 : CompleteLinearOrder.{u2} R] {f : ι -> R}, (Membership.Mem.{u2, u2} R (Set.{u2} R) (Set.hasMem.{u2} R) (infᵢ.{u2, u1} R (CompleteSemilatticeInf.toHasInf.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))) ι (fun (i : ι) => f i)) (Set.range.{u2, u1} R ι f)) -> (Eq.{succ u2} (Set.{u2} R) (Set.unionᵢ.{u2, u1} R ι (fun (i : ι) => Set.Ici.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (f i))) (Set.Ici.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (infᵢ.{u2, u1} R (CompleteSemilatticeInf.toHasInf.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {ι : Sort.{u2}} {R : Type.{u1}} [_inst_2 : CompleteLinearOrder.{u1} R] {f : ι -> R}, (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) (infᵢ.{u1, u2} R (CompleteLattice.toInfSet.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) ι (fun (i : ι) => f i)) (Set.range.{u1, u2} R ι f)) -> (Eq.{succ u1} (Set.{u1} R) (Set.unionᵢ.{u1, u2} R ι (fun (i : ι) => Set.Ici.{u1} R (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (f i))) (Set.Ici.{u1} R (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (infᵢ.{u1, u2} R (CompleteLattice.toInfSet.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align Union_Ici_eq_Ici_infi unionᵢ_Ici_eq_Ici_infᵢₓ'. -/
theorem unionᵢ_Ici_eq_Ici_infᵢ {R : Type _} [CompleteLinearOrder R] {f : ι → R}
    (has_least_elem : (⨅ i, f i) ∈ range f) : (⋃ i : ι, Ici (f i)) = Ici (⨅ i, f i) := by
  simp only [← IsGLB.bunionᵢ_Ici_eq_Ici (@isGLB_infᵢ _ _ _ f) has_least_elem, mem_range,
    Union_exists, Union_Union_eq']
#align Union_Ici_eq_Ici_infi unionᵢ_Ici_eq_Ici_infᵢ

/- warning: Union_Iic_eq_Iic_supr -> unionᵢ_Iic_eq_Iic_supᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {R : Type.{u2}} [_inst_2 : CompleteLinearOrder.{u2} R] {f : ι -> R}, (Membership.Mem.{u2, u2} R (Set.{u2} R) (Set.hasMem.{u2} R) (supᵢ.{u2, u1} R (CompleteSemilatticeSup.toHasSup.{u2} R (CompleteLattice.toCompleteSemilatticeSup.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))) ι (fun (i : ι) => f i)) (Set.range.{u2, u1} R ι f)) -> (Eq.{succ u2} (Set.{u2} R) (Set.unionᵢ.{u2, u1} R ι (fun (i : ι) => Set.Iic.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (f i))) (Set.Iic.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (supᵢ.{u2, u1} R (CompleteSemilatticeSup.toHasSup.{u2} R (CompleteLattice.toCompleteSemilatticeSup.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {ι : Sort.{u2}} {R : Type.{u1}} [_inst_2 : CompleteLinearOrder.{u1} R] {f : ι -> R}, (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) (supᵢ.{u1, u2} R (CompleteLattice.toSupSet.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) ι (fun (i : ι) => f i)) (Set.range.{u1, u2} R ι f)) -> (Eq.{succ u1} (Set.{u1} R) (Set.unionᵢ.{u1, u2} R ι (fun (i : ι) => Set.Iic.{u1} R (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (f i))) (Set.Iic.{u1} R (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (supᵢ.{u1, u2} R (CompleteLattice.toSupSet.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align Union_Iic_eq_Iic_supr unionᵢ_Iic_eq_Iic_supᵢₓ'. -/
theorem unionᵢ_Iic_eq_Iic_supᵢ {R : Type _} [CompleteLinearOrder R] {f : ι → R}
    (has_greatest_elem : (⨆ i, f i) ∈ range f) : (⋃ i : ι, Iic (f i)) = Iic (⨆ i, f i) :=
  @unionᵢ_Ici_eq_Ici_infᵢ ι (OrderDual R) _ f has_greatest_elem
#align Union_Iic_eq_Iic_supr unionᵢ_Iic_eq_Iic_supᵢ

end UnionIxx

