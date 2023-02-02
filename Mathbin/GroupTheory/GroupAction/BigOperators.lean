/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module group_theory.group_action.big_operators
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Finset.Basic
import Mathbin.Data.Multiset.Basic
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Lemmas about group actions on big operators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Note that analogous lemmas for `module`s like `finset.sum_smul` appear in other files.
-/


variable {α β γ : Type _}

open BigOperators

section

variable [AddMonoid β] [DistribSMul α β]

/- warning: list.smul_sum -> List.smul_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddMonoid.{u2} β] [_inst_2 : DistribSMul.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_1)] {r : α} {l : List.{u2} β}, Eq.{succ u2} β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_1)) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_1) _inst_2)) r (List.sum.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_1)) l)) (List.sum.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_1)) (List.map.{u2, u2} β β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_1)) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_1) _inst_2)) r) l))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddMonoid.{u2} β] [_inst_2 : DistribSMul.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_1)] {r : α} {l : List.{u2} β}, Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_1) _inst_2))) r (List.sum.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_1)) (AddMonoid.toZero.{u2} β _inst_1) l)) (List.sum.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_1)) (AddMonoid.toZero.{u2} β _inst_1) (List.map.{u2, u2} β β ((fun (x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.59 : α) (x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.61 : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_1) _inst_2))) x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.59 x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.61) r) l))
Case conversion may be inaccurate. Consider using '#align list.smul_sum List.smul_sumₓ'. -/
theorem List.smul_sum {r : α} {l : List β} : r • l.Sum = (l.map ((· • ·) r)).Sum :=
  (DistribSMul.toAddMonoidHom β r).map_list_sum l
#align list.smul_sum List.smul_sum

end

section

variable [Monoid α] [Monoid β] [MulDistribMulAction α β]

/- warning: list.smul_prod -> List.smul_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MulDistribMulAction.{u1, u2} α β _inst_1 _inst_2] {r : α} {l : List.{u2} β}, Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} α β _inst_1 _inst_2 _inst_3)) r (List.prod.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) l)) (List.prod.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (List.map.{u2, u2} β β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} α β _inst_1 _inst_2 _inst_3)) r) l))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MulDistribMulAction.{u1, u2} α β _inst_1 _inst_2] {r : α} {l : List.{u2} β}, Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} α β _inst_1 _inst_2 _inst_3))) r (List.prod.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (Monoid.toOne.{u2} β _inst_2) l)) (List.prod.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (Monoid.toOne.{u2} β _inst_2) (List.map.{u2, u2} β β ((fun (x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.137 : α) (x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.139 : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β _inst_1 (MulDistribMulAction.toMulAction.{u1, u2} α β _inst_1 _inst_2 _inst_3))) x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.137 x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.139) r) l))
Case conversion may be inaccurate. Consider using '#align list.smul_prod List.smul_prodₓ'. -/
theorem List.smul_prod {r : α} {l : List β} : r • l.Prod = (l.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_list_prod l
#align list.smul_prod List.smul_prod

end

section

variable [AddCommMonoid β] [DistribSMul α β]

/- warning: multiset.smul_sum -> Multiset.smul_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} β] [_inst_2 : DistribSMul.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1))] {r : α} {s : Multiset.{u2} β}, Eq.{succ u2} β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) _inst_2)) r (Multiset.sum.{u2} β _inst_1 s)) (Multiset.sum.{u2} β _inst_1 (Multiset.map.{u2, u2} β β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) _inst_2)) r) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} β] [_inst_2 : DistribSMul.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1))] {r : α} {s : Multiset.{u2} β}, Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) _inst_2))) r (Multiset.sum.{u2} β _inst_1 s)) (Multiset.sum.{u2} β _inst_1 (Multiset.map.{u2, u2} β β ((fun (x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.208 : α) (x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.210 : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) _inst_2))) x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.208 x._@.Mathlib.GroupTheory.GroupAction.BigOperators._hyg.210) r) s))
Case conversion may be inaccurate. Consider using '#align multiset.smul_sum Multiset.smul_sumₓ'. -/
theorem Multiset.smul_sum {r : α} {s : Multiset β} : r • s.Sum = (s.map ((· • ·) r)).Sum :=
  (DistribSMul.toAddMonoidHom β r).map_multiset_sum s
#align multiset.smul_sum Multiset.smul_sum

/- warning: finset.smul_sum -> Finset.smul_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} β] [_inst_2 : DistribSMul.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1))] {r : α} {f : γ -> β} {s : Finset.{u3} γ}, Eq.{succ u2} β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) _inst_2)) r (Finset.sum.{u2, u3} β γ _inst_1 s (fun (x : γ) => f x))) (Finset.sum.{u2, u3} β γ _inst_1 s (fun (x : γ) => SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) _inst_2)) r (f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} β] [_inst_2 : DistribSMul.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1))] {r : α} {f : γ -> β} {s : Finset.{u3} γ}, Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) _inst_2))) r (Finset.sum.{u2, u3} β γ _inst_1 s (fun (x : γ) => f x))) (Finset.sum.{u2, u3} β γ _inst_1 s (fun (x : γ) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_1)) _inst_2))) r (f x)))
Case conversion may be inaccurate. Consider using '#align finset.smul_sum Finset.smul_sumₓ'. -/
theorem Finset.smul_sum {r : α} {f : γ → β} {s : Finset γ} :
    (r • ∑ x in s, f x) = ∑ x in s, r • f x :=
  (DistribSMul.toAddMonoidHom β r).map_sum f s
#align finset.smul_sum Finset.smul_sum

end

section

variable [Monoid α] [CommMonoid β] [MulDistribMulAction α β]

#print Multiset.smul_prod /-
theorem Multiset.smul_prod {r : α} {s : Multiset β} : r • s.Prod = (s.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_multiset_prod s
#align multiset.smul_prod Multiset.smul_prod
-/

#print Finset.smul_prod /-
theorem Finset.smul_prod {r : α} {f : γ → β} {s : Finset γ} :
    (r • ∏ x in s, f x) = ∏ x in s, r • f x :=
  (MulDistribMulAction.toMonoidHom β r).map_prod f s
#align finset.smul_prod Finset.smul_prod
-/

end

