/-
Copyright (c) 2022 Dagur Tómas Ásgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Tómas Ásgeirsson, Leonardo de Moura

! This file was ported from Lean 3 source module data.set.bool_indicator
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Image

/-!
# Indicator function valued in bool

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

See also `set.indicator` and `set.piecewise`.
-/


open Bool

namespace Set

variable {α : Type _} (s : Set α)

#print Set.boolIndicator /-
/-- `bool_indicator` maps `x` to `tt` if `x ∈ s`, else to `ff` -/
noncomputable def boolIndicator (x : α) :=
  @ite _ (x ∈ s) (Classical.propDecidable _) true false
#align set.bool_indicator Set.boolIndicator
-/

#print Set.mem_iff_boolIndicator /-
theorem mem_iff_boolIndicator (x : α) : x ∈ s ↔ s.boolIndicator x = true :=
  by
  unfold bool_indicator
  split_ifs <;> tauto
#align set.mem_iff_bool_indicator Set.mem_iff_boolIndicator
-/

#print Set.not_mem_iff_boolIndicator /-
theorem not_mem_iff_boolIndicator (x : α) : x ∉ s ↔ s.boolIndicator x = false :=
  by
  unfold bool_indicator
  split_ifs <;> tauto
#align set.not_mem_iff_bool_indicator Set.not_mem_iff_boolIndicator
-/

/- warning: set.preimage_bool_indicator_tt clashes with set.preimage_bool_indicator_true -> Set.preimage_boolIndicator_true
Case conversion may be inaccurate. Consider using '#align set.preimage_bool_indicator_tt Set.preimage_boolIndicator_trueₓ'. -/
#print Set.preimage_boolIndicator_true /-
theorem preimage_boolIndicator_true : s.boolIndicator ⁻¹' {true} = s :=
  ext fun x => (s.mem_iff_boolIndicator x).symm
#align set.preimage_bool_indicator_tt Set.preimage_boolIndicator_true
-/

/- warning: set.preimage_bool_indicator_ff clashes with set.preimage_bool_indicator_false -> Set.preimage_boolIndicator_false
warning: set.preimage_bool_indicator_ff -> Set.preimage_boolIndicator_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) (Singleton.singleton.{0, 0} Bool (Set.{0} Bool) (Set.hasSingleton.{0} Bool) Bool.false)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) (Singleton.singleton.{0, 0} Bool (Set.{0} Bool) (Set.instSingletonSet.{0} Bool) Bool.false)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)
Case conversion may be inaccurate. Consider using '#align set.preimage_bool_indicator_ff Set.preimage_boolIndicator_falseₓ'. -/
theorem preimage_boolIndicator_false : s.boolIndicator ⁻¹' {false} = sᶜ :=
  ext fun x => (s.not_mem_iff_boolIndicator x).symm
#align set.preimage_bool_indicator_ff Set.preimage_boolIndicator_false

open Classical

/- warning: set.preimage_bool_indicator_eq_union -> Set.preimage_boolIndicator_eq_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{0} Bool), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (ite.{succ u1} (Set.{u1} α) (Membership.Mem.{0, 0} Bool (Set.{0} Bool) (Set.hasMem.{0} Bool) Bool.true t) (Classical.propDecidable (Membership.Mem.{0, 0} Bool (Set.{0} Bool) (Set.hasMem.{0} Bool) Bool.true t)) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (ite.{succ u1} (Set.{u1} α) (Membership.Mem.{0, 0} Bool (Set.{0} Bool) (Set.hasMem.{0} Bool) Bool.false t) (Classical.propDecidable (Membership.Mem.{0, 0} Bool (Set.{0} Bool) (Set.hasMem.{0} Bool) Bool.false t)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{0} Bool), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (ite.{succ u1} (Set.{u1} α) (Membership.mem.{0, 0} Bool (Set.{0} Bool) (Set.instMembershipSet.{0} Bool) Bool.true t) (Classical.propDecidable (Membership.mem.{0, 0} Bool (Set.{0} Bool) (Set.instMembershipSet.{0} Bool) Bool.true t)) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (ite.{succ u1} (Set.{u1} α) (Membership.mem.{0, 0} Bool (Set.{0} Bool) (Set.instMembershipSet.{0} Bool) Bool.false t) (Classical.propDecidable (Membership.mem.{0, 0} Bool (Set.{0} Bool) (Set.instMembershipSet.{0} Bool) Bool.false t)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))))
Case conversion may be inaccurate. Consider using '#align set.preimage_bool_indicator_eq_union Set.preimage_boolIndicator_eq_unionₓ'. -/
theorem preimage_boolIndicator_eq_union (t : Set Bool) :
    s.boolIndicator ⁻¹' t = (if true ∈ t then s else ∅) ∪ if false ∈ t then sᶜ else ∅ :=
  by
  ext x
  dsimp [bool_indicator]
  split_ifs <;> tauto
#align set.preimage_bool_indicator_eq_union Set.preimage_boolIndicator_eq_union

/- warning: set.preimage_bool_indicator -> Set.preimage_boolIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{0} Bool), Or (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) (Set.univ.{u1} α)) (Or (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) s) (Or (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{0} Bool), Or (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) (Set.univ.{u1} α)) (Or (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) s) (Or (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, 0} α Bool (Set.boolIndicator.{u1} α s) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align set.preimage_bool_indicator Set.preimage_boolIndicatorₓ'. -/
theorem preimage_boolIndicator (t : Set Bool) :
    s.boolIndicator ⁻¹' t = univ ∨
      s.boolIndicator ⁻¹' t = s ∨ s.boolIndicator ⁻¹' t = sᶜ ∨ s.boolIndicator ⁻¹' t = ∅ :=
  by
  simp only [preimage_bool_indicator_eq_union]
  split_ifs <;> simp [s.union_compl_self]
#align set.preimage_bool_indicator Set.preimage_boolIndicator

end Set

