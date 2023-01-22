/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

! This file was ported from Lean 3 source module group_theory.group_action.pi
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Pi instances for multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for mul_action and related structures on Pi types.

## See also

* `group_theory.group_action.option`
* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
* `group_theory.group_action.sum`
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace Pi

#print Pi.smul' /-
@[to_additive Pi.vadd']
instance smul' {g : I → Type _} [∀ i, SMul (f i) (g i)] : SMul (∀ i, f i) (∀ i : I, g i) :=
  ⟨fun s x => fun i => s i • x i⟩
#align pi.has_smul' Pi.smul'
#align pi.has_vadd' Pi.vadd'
-/

/- warning: pi.smul_apply' -> Pi.smul_apply' is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} (i : I) {g : I -> Type.{u3}} [_inst_1 : forall (i : I), SMul.{u2, u3} (f i) (g i)] (s : forall (i : I), f i) (x : forall (i : I), g i), Eq.{succ u3} (g i) (SMul.smul.{max u1 u2, max u1 u3} (forall (i : I), f i) (forall (i : I), g i) (Pi.smul'.{u1, u2, u3} I (fun (i : I) => f i) (fun (i : I) => g i) (fun (i : I) => _inst_1 i)) s x i) (SMul.smul.{u2, u3} (f i) (g i) (_inst_1 i) (s i) (x i))
but is expected to have type
  forall {I : Type.{u2}} {f : I -> Type.{u3}} (i : I) {g : I -> Type.{u1}} [_inst_1 : forall (i : I), SMul.{u3, u1} (f i) (g i)] (s : forall (i : I), f i) (x : forall (i : I), g i), Eq.{succ u1} (g i) (HSMul.hSMul.{max u2 u3, max u2 u1, max u2 u1} (forall (i : I), f i) (forall (i : I), g i) (forall (i : I), g i) (instHSMul.{max u2 u3, max u2 u1} (forall (i : I), f i) (forall (i : I), g i) (Pi.smul'.{u2, u3, u1} I (fun (i : I) => f i) (fun (i : I) => g i) (fun (i : I) => _inst_1 i))) s x i) (HSMul.hSMul.{u3, u1, u1} (f i) (g i) (g i) (instHSMul.{u3, u1} (f i) (g i) (_inst_1 i)) (s i) (x i))
Case conversion may be inaccurate. Consider using '#align pi.smul_apply' Pi.smul_apply'ₓ'. -/
@[simp, to_additive]
theorem smul_apply' {g : I → Type _} [∀ i, SMul (f i) (g i)] (s : ∀ i, f i) (x : ∀ i, g i) :
    (s • x) i = s i • x i :=
  rfl
#align pi.smul_apply' Pi.smul_apply'
#align pi.vadd_apply' Pi.vadd_apply'

#print Pi.isScalarTower /-
@[to_additive]
instance isScalarTower {α β : Type _} [SMul α β] [∀ i, SMul β <| f i] [∀ i, SMul α <| f i]
    [∀ i, IsScalarTower α β (f i)] : IsScalarTower α β (∀ i : I, f i) :=
  ⟨fun x y z => funext fun i => smul_assoc x y (z i)⟩
#align pi.is_scalar_tower Pi.isScalarTower
#align pi.vadd_assoc_class Pi.vaddAssocClass
-/

#print Pi.isScalarTower' /-
@[to_additive]
instance isScalarTower' {g : I → Type _} {α : Type _} [∀ i, SMul α <| f i] [∀ i, SMul (f i) (g i)]
    [∀ i, SMul α <| g i] [∀ i, IsScalarTower α (f i) (g i)] :
    IsScalarTower α (∀ i : I, f i) (∀ i : I, g i) :=
  ⟨fun x y z => funext fun i => smul_assoc x (y i) (z i)⟩
#align pi.is_scalar_tower' Pi.isScalarTower'
#align pi.vadd_assoc_class' Pi.vaddAssocClass'
-/

#print Pi.isScalarTower'' /-
@[to_additive]
instance isScalarTower'' {g : I → Type _} {h : I → Type _} [∀ i, SMul (f i) (g i)]
    [∀ i, SMul (g i) (h i)] [∀ i, SMul (f i) (h i)] [∀ i, IsScalarTower (f i) (g i) (h i)] :
    IsScalarTower (∀ i, f i) (∀ i, g i) (∀ i, h i) :=
  ⟨fun x y z => funext fun i => smul_assoc (x i) (y i) (z i)⟩
#align pi.is_scalar_tower'' Pi.isScalarTower''
#align pi.vadd_assoc_class'' Pi.vaddAssocClass''
-/

#print Pi.smulCommClass /-
@[to_additive]
instance smulCommClass {α β : Type _} [∀ i, SMul α <| f i] [∀ i, SMul β <| f i]
    [∀ i, SMulCommClass α β (f i)] : SMulCommClass α β (∀ i : I, f i) :=
  ⟨fun x y z => funext fun i => smul_comm x y (z i)⟩
#align pi.smul_comm_class Pi.smulCommClass
#align pi.vadd_comm_class Pi.vaddCommClass
-/

#print Pi.smulCommClass' /-
@[to_additive]
instance smulCommClass' {g : I → Type _} {α : Type _} [∀ i, SMul α <| g i] [∀ i, SMul (f i) (g i)]
    [∀ i, SMulCommClass α (f i) (g i)] : SMulCommClass α (∀ i : I, f i) (∀ i : I, g i) :=
  ⟨fun x y z => funext fun i => smul_comm x (y i) (z i)⟩
#align pi.smul_comm_class' Pi.smulCommClass'
#align pi.vadd_comm_class' Pi.vaddCommClass'
-/

#print Pi.smulCommClass'' /-
@[to_additive]
instance smulCommClass'' {g : I → Type _} {h : I → Type _} [∀ i, SMul (g i) (h i)]
    [∀ i, SMul (f i) (h i)] [∀ i, SMulCommClass (f i) (g i) (h i)] :
    SMulCommClass (∀ i, f i) (∀ i, g i) (∀ i, h i) :=
  ⟨fun x y z => funext fun i => smul_comm (x i) (y i) (z i)⟩
#align pi.smul_comm_class'' Pi.smulCommClass''
#align pi.vadd_comm_class'' Pi.vaddCommClass''
-/

@[to_additive]
instance {α : Type _} [∀ i, SMul α <| f i] [∀ i, SMul αᵐᵒᵖ <| f i] [∀ i, IsCentralScalar α (f i)] :
    IsCentralScalar α (∀ i, f i) :=
  ⟨fun r m => funext fun i => op_smul_eq_smul _ _⟩

/- warning: pi.has_faithful_smul_at -> Pi.faithfulSMul_at is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {α : Type.{u3}} [_inst_1 : forall (i : I), SMul.{u3, u2} α (f i)] [_inst_2 : forall (i : I), Nonempty.{succ u2} (f i)] (i : I) [_inst_3 : FaithfulSMul.{u3, u2} α (f i) (_inst_1 i)], FaithfulSMul.{u3, max u1 u2} α (forall (i : I), f i) (Pi.instSMul.{u1, u2, u3} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i))
but is expected to have type
  forall {I : Type.{u2}} {f : I -> Type.{u3}} {α : Type.{u1}} [_inst_1 : forall (i : I), SMul.{u1, u3} α (f i)] [_inst_2 : forall (i : I), Nonempty.{succ u3} (f i)] (i : I) [_inst_3 : FaithfulSMul.{u1, u3} α (f i) (_inst_1 i)], FaithfulSMul.{u1, max u2 u3} α (forall (i : I), f i) (Pi.instSMul.{u2, u3, u1} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i))
Case conversion may be inaccurate. Consider using '#align pi.has_faithful_smul_at Pi.faithfulSMul_atₓ'. -/
/-- If `f i` has a faithful scalar action for a given `i`, then so does `Π i, f i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive Pi.faithfulVAdd_at
      "If `f i` has a faithful additive action for a given `i`, then\nso does `Π i, f i`. This is not an instance as `i` cannot be inferred"]
theorem faithfulSMul_at {α : Type _} [∀ i, SMul α <| f i] [∀ i, Nonempty (f i)] (i : I)
    [FaithfulSMul α (f i)] : FaithfulSMul α (∀ i, f i) :=
  ⟨fun x y h =>
    eq_of_smul_eq_smul fun a : f i => by
      classical
        have :=
          congr_fun (h <| Function.update (fun j => Classical.choice (‹∀ i, Nonempty (f i)› j)) i a)
            i
        simpa using this⟩
#align pi.has_faithful_smul_at Pi.faithfulSMul_at
#align pi.has_faithful_vadd_at Pi.faithfulVAdd_at

#print Pi.faithfulSMul /-
@[to_additive Pi.faithfulVAdd]
instance faithfulSMul {α : Type _} [Nonempty I] [∀ i, SMul α <| f i] [∀ i, Nonempty (f i)]
    [∀ i, FaithfulSMul α (f i)] : FaithfulSMul α (∀ i, f i) :=
  let ⟨i⟩ := ‹Nonempty I›
  faithfulSMul_at i
#align pi.has_faithful_smul Pi.faithfulSMul
#align pi.has_faithful_vadd Pi.faithfulVAdd
-/

#print Pi.mulAction /-
@[to_additive]
instance mulAction (α) {m : Monoid α} [∀ i, MulAction α <| f i] : @MulAction α (∀ i : I, f i) m
    where
  smul := (· • ·)
  mul_smul r s f := funext fun i => mul_smul _ _ _
  one_smul f := funext fun i => one_smul α _
#align pi.mul_action Pi.mulAction
#align pi.add_action Pi.addAction
-/

#print Pi.mulAction' /-
@[to_additive]
instance mulAction' {g : I → Type _} {m : ∀ i, Monoid (f i)} [∀ i, MulAction (f i) (g i)] :
    @MulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m)
    where
  smul := (· • ·)
  mul_smul r s f := funext fun i => mul_smul _ _ _
  one_smul f := funext fun i => one_smul _ _
#align pi.mul_action' Pi.mulAction'
#align pi.add_action' Pi.addAction'
-/

#print Pi.smulZeroClass /-
instance smulZeroClass (α) {n : ∀ i, Zero <| f i} [∀ i, SMulZeroClass α <| f i] :
    @SMulZeroClass α (∀ i : I, f i) (@Pi.instZero I f n)
    where smul_zero c := funext fun i => smul_zero _
#align pi.smul_zero_class Pi.smulZeroClass
-/

#print Pi.smulZeroClass' /-
instance smulZeroClass' {g : I → Type _} {n : ∀ i, Zero <| g i} [∀ i, SMulZeroClass (f i) (g i)] :
    @SMulZeroClass (∀ i, f i) (∀ i : I, g i) (@Pi.instZero I g n)
    where smul_zero := by
    intros
    ext x
    apply smul_zero
#align pi.smul_zero_class' Pi.smulZeroClass'
-/

#print Pi.distribSMul /-
instance distribSMul (α) {n : ∀ i, AddZeroClass <| f i} [∀ i, DistribSMul α <| f i] :
    @DistribSMul α (∀ i : I, f i) (@Pi.addZeroClass I f n)
    where smul_add c f g := funext fun i => smul_add _ _ _
#align pi.distrib_smul Pi.distribSMul
-/

#print Pi.distribSMul' /-
instance distribSMul' {g : I → Type _} {n : ∀ i, AddZeroClass <| g i}
    [∀ i, DistribSMul (f i) (g i)] : @DistribSMul (∀ i, f i) (∀ i : I, g i) (@Pi.addZeroClass I g n)
    where smul_add := by
    intros
    ext x
    apply smul_add
#align pi.distrib_smul' Pi.distribSMul'
-/

#print Pi.distribMulAction /-
instance distribMulAction (α) {m : Monoid α} {n : ∀ i, AddMonoid <| f i}
    [∀ i, DistribMulAction α <| f i] : @DistribMulAction α (∀ i : I, f i) m (@Pi.addMonoid I f n) :=
  { Pi.mulAction _, Pi.distribSMul _ with }
#align pi.distrib_mul_action Pi.distribMulAction
-/

#print Pi.distribMulAction' /-
instance distribMulAction' {g : I → Type _} {m : ∀ i, Monoid (f i)} {n : ∀ i, AddMonoid <| g i}
    [∀ i, DistribMulAction (f i) (g i)] :
    @DistribMulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m) (@Pi.addMonoid I g n) :=
  { Pi.mulAction', Pi.distribSMul' with }
#align pi.distrib_mul_action' Pi.distribMulAction'
-/

/- warning: pi.single_smul -> Pi.single_smul is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {α : Type.{u3}} [_inst_1 : Monoid.{u3} α] [_inst_2 : forall (i : I), AddMonoid.{u2} (f i)] [_inst_3 : forall (i : I), DistribMulAction.{u3, u2} α (f i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u1} I] (i : I) (r : α) (x : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddZeroClass.toHasZero.{u2} (f i) (AddMonoid.toAddZeroClass.{u2} (f i) (_inst_2 i))) i (SMul.smul.{u3, u2} α (f i) (SMulZeroClass.toHasSmul.{u3, u2} α (f i) (AddZeroClass.toHasZero.{u2} (f i) (AddMonoid.toAddZeroClass.{u2} (f i) (_inst_2 i))) (DistribSMul.toSmulZeroClass.{u3, u2} α (f i) (AddMonoid.toAddZeroClass.{u2} (f i) (_inst_2 i)) (DistribMulAction.toDistribSMul.{u3, u2} α (f i) _inst_1 (_inst_2 i) (_inst_3 i)))) r x)) (SMul.smul.{u3, max u1 u2} α (forall (i : I), f i) (Pi.instSMul.{u1, u2, u3} I α (fun (i : I) => f i) (fun (i : I) => SMulZeroClass.toHasSmul.{u3, u2} α (f i) (AddZeroClass.toHasZero.{u2} (f i) (AddMonoid.toAddZeroClass.{u2} (f i) (_inst_2 i))) (DistribSMul.toSmulZeroClass.{u3, u2} α (f i) (AddMonoid.toAddZeroClass.{u2} (f i) (_inst_2 i)) (DistribMulAction.toDistribSMul.{u3, u2} α (f i) _inst_1 (_inst_2 i) (_inst_3 i))))) r (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddZeroClass.toHasZero.{u2} (f i) (AddMonoid.toAddZeroClass.{u2} (f i) (_inst_2 i))) i x))
but is expected to have type
  forall {I : Type.{u2}} {f : I -> Type.{u3}} {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : forall (i : I), AddMonoid.{u3} (f i)] [_inst_3 : forall (i : I), DistribMulAction.{u1, u3} α (f i) _inst_1 (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} I] (i : I) (r : α) (x : f i), Eq.{max (succ u2) (succ u3)} (forall (i : I), f i) (Pi.single.{u2, u3} I f (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddMonoid.toZero.{u3} (f i) (_inst_2 i)) i (HSMul.hSMul.{u1, u3, u3} α (f i) (f i) (instHSMul.{u1, u3} α (f i) (SMulZeroClass.toSMul.{u1, u3} α (f i) (AddMonoid.toZero.{u3} (f i) (_inst_2 i)) (DistribSMul.toSMulZeroClass.{u1, u3} α (f i) (AddMonoid.toAddZeroClass.{u3} (f i) (_inst_2 i)) (DistribMulAction.toDistribSMul.{u1, u3} α (f i) _inst_1 (_inst_2 i) (_inst_3 i))))) r x)) (HSMul.hSMul.{u1, max u3 u2, max u2 u3} α (forall (j : I), f j) (forall (i : I), f i) (instHSMul.{u1, max u2 u3} α (forall (j : I), f j) (Pi.instSMul.{u2, u3, u1} I α (fun (j : I) => f j) (fun (i : I) => SMulZeroClass.toSMul.{u1, u3} α (f i) (AddMonoid.toZero.{u3} (f i) (_inst_2 i)) (DistribSMul.toSMulZeroClass.{u1, u3} α (f i) (AddMonoid.toAddZeroClass.{u3} (f i) (_inst_2 i)) (DistribMulAction.toDistribSMul.{u1, u3} α (f i) _inst_1 (_inst_2 i) (_inst_3 i)))))) r (Pi.single.{u2, u3} I f (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddMonoid.toZero.{u3} (f i) (_inst_2 i)) i x))
Case conversion may be inaccurate. Consider using '#align pi.single_smul Pi.single_smulₓ'. -/
theorem single_smul {α} [Monoid α] [∀ i, AddMonoid <| f i] [∀ i, DistribMulAction α <| f i]
    [DecidableEq I] (i : I) (r : α) (x : f i) : single i (r • x) = r • single i x :=
  single_op (fun i : I => ((· • ·) r : f i → f i)) (fun j => smul_zero _) _ _
#align pi.single_smul Pi.single_smul

/- warning: pi.single_smul' -> Pi.single_smul' is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u2} α] [_inst_2 : AddMonoid.{u3} β] [_inst_3 : DistribMulAction.{u2, u3} α β _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u1} I] (i : I) (r : α) (x : β), Eq.{max (succ u1) (succ u3)} (I -> β) (Pi.single.{u1, u3} I (fun (i : I) => β) (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β _inst_2)) i (SMul.smul.{u2, u3} α β (SMulZeroClass.toHasSmul.{u2, u3} α β (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β _inst_2)) (DistribSMul.toSmulZeroClass.{u2, u3} α β (AddMonoid.toAddZeroClass.{u3} β _inst_2) (DistribMulAction.toDistribSMul.{u2, u3} α β _inst_1 _inst_2 _inst_3))) r x)) (SMul.smul.{u2, max u1 u3} α (I -> β) (Pi.instSMul.{u1, u3, u2} I α (fun (i : I) => β) (fun (i : I) => SMulZeroClass.toHasSmul.{u2, u3} α β (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β _inst_2)) (DistribSMul.toSmulZeroClass.{u2, u3} α β (AddMonoid.toAddZeroClass.{u3} β _inst_2) (DistribMulAction.toDistribSMul.{u2, u3} α β _inst_1 _inst_2 _inst_3)))) r (Pi.single.{u1, u3} I (fun (i : I) => β) (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β _inst_2)) i x))
but is expected to have type
  forall {I : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u2} α] [_inst_2 : AddMonoid.{u1} β] [_inst_3 : DistribMulAction.{u2, u1} α β _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u3} I] (i : I) (r : α) (x : β), Eq.{max (succ u3) (succ u1)} (I -> β) (Pi.single.{u3, u1} I (fun (i : I) => β) (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddMonoid.toZero.{u1} ((fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.1988 : I) => β) i) _inst_2) i (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (SMulZeroClass.toSMul.{u2, u1} α β (AddMonoid.toZero.{u1} β _inst_2) (DistribSMul.toSMulZeroClass.{u2, u1} α β (AddMonoid.toAddZeroClass.{u1} β _inst_2) (DistribMulAction.toDistribSMul.{u2, u1} α β _inst_1 _inst_2 _inst_3)))) r x)) (HSMul.hSMul.{u2, max u1 u3, max u3 u1} α (forall (j : I), (fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) j) (forall (i : I), (fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) i) (instHSMul.{u2, max u3 u1} α (forall (j : I), (fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) j) (Pi.instSMul.{u3, u1, u2} I α (fun (j : I) => (fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) j) (fun (i : I) => SMulZeroClass.toSMul.{u2, u1} α ((fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) i) (AddMonoid.toZero.{u1} ((fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) i) _inst_2) (DistribSMul.toSMulZeroClass.{u2, u1} α ((fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) i) (AddMonoid.toAddZeroClass.{u1} ((fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) i) _inst_2) (DistribMulAction.toDistribSMul.{u2, u1} α ((fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) i) _inst_1 _inst_2 _inst_3))))) r (Pi.single.{u3, u1} I (fun (i : I) => β) (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddMonoid.toZero.{u1} ((fun (x._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2007 : I) => β) i) _inst_2) i x))
Case conversion may be inaccurate. Consider using '#align pi.single_smul' Pi.single_smul'ₓ'. -/
/-- A version of `pi.single_smul` for non-dependent functions. It is useful in cases Lean fails
to apply `pi.single_smul`. -/
theorem single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMulAction α β] [DecidableEq I] (i : I)
    (r : α) (x : β) : single i (r • x) = r • single i x :=
  single_smul i r x
#align pi.single_smul' Pi.single_smul'

/- warning: pi.single_smul₀ -> Pi.single_smul₀ is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {g : I -> Type.{u3}} [_inst_1 : forall (i : I), MonoidWithZero.{u2} (f i)] [_inst_2 : forall (i : I), AddMonoid.{u3} (g i)] [_inst_3 : forall (i : I), DistribMulAction.{u2, u3} (f i) (g i) (MonoidWithZero.toMonoid.{u2} (f i) (_inst_1 i)) (_inst_2 i)] [_inst_4 : DecidableEq.{succ u1} I] (i : I) (r : f i) (x : g i), Eq.{max (succ u1) (succ u3)} (forall (i : I), g i) (Pi.single.{u1, u3} I (fun (i : I) => g i) (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddZeroClass.toHasZero.{u3} (g i) (AddMonoid.toAddZeroClass.{u3} (g i) (_inst_2 i))) i (SMul.smul.{u2, u3} (f i) (g i) (SMulZeroClass.toHasSmul.{u2, u3} (f i) (g i) (AddZeroClass.toHasZero.{u3} (g i) (AddMonoid.toAddZeroClass.{u3} (g i) (_inst_2 i))) (DistribSMul.toSmulZeroClass.{u2, u3} (f i) (g i) (AddMonoid.toAddZeroClass.{u3} (g i) (_inst_2 i)) (DistribMulAction.toDistribSMul.{u2, u3} (f i) (g i) (MonoidWithZero.toMonoid.{u2} (f i) (_inst_1 i)) (_inst_2 i) (_inst_3 i)))) r x)) (SMul.smul.{max u1 u2, max u1 u3} (forall (i : I), f i) (forall (i : I), g i) (Pi.smul'.{u1, u2, u3} I (fun (i : I) => f i) (fun (i : I) => g i) (fun (i : I) => SMulZeroClass.toHasSmul.{u2, u3} (f i) (g i) (AddZeroClass.toHasZero.{u3} (g i) (AddMonoid.toAddZeroClass.{u3} (g i) (_inst_2 i))) (DistribSMul.toSmulZeroClass.{u2, u3} (f i) (g i) (AddMonoid.toAddZeroClass.{u3} (g i) (_inst_2 i)) (DistribMulAction.toDistribSMul.{u2, u3} (f i) (g i) (MonoidWithZero.toMonoid.{u2} (f i) (_inst_1 i)) (_inst_2 i) (_inst_3 i))))) (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => MulZeroClass.toHasZero.{u2} (f i) (MulZeroOneClass.toMulZeroClass.{u2} (f i) (MonoidWithZero.toMulZeroOneClass.{u2} (f i) (_inst_1 i)))) i r) (Pi.single.{u1, u3} I (fun (i : I) => g i) (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddZeroClass.toHasZero.{u3} (g i) (AddMonoid.toAddZeroClass.{u3} (g i) (_inst_2 i))) i x))
but is expected to have type
  forall {I : Type.{u2}} {f : I -> Type.{u3}} {g : I -> Type.{u1}} [_inst_1 : forall (i : I), MonoidWithZero.{u3} (f i)] [_inst_2 : forall (i : I), AddMonoid.{u1} (g i)] [_inst_3 : forall (i : I), DistribMulAction.{u3, u1} (f i) (g i) (MonoidWithZero.toMonoid.{u3} (f i) (_inst_1 i)) (_inst_2 i)] [_inst_4 : DecidableEq.{succ u2} I] (i : I) (r : f i) (x : g i), Eq.{max (succ u2) (succ u1)} (forall (i : I), g i) (Pi.single.{u2, u1} I g (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddMonoid.toZero.{u1} (g i) (_inst_2 i)) i (HSMul.hSMul.{u3, u1, u1} (f i) (g i) (g i) (instHSMul.{u3, u1} (f i) (g i) (SMulZeroClass.toSMul.{u3, u1} (f i) (g i) (AddMonoid.toZero.{u1} (g i) (_inst_2 i)) (DistribSMul.toSMulZeroClass.{u3, u1} (f i) (g i) (AddMonoid.toAddZeroClass.{u1} (g i) (_inst_2 i)) (DistribMulAction.toDistribSMul.{u3, u1} (f i) (g i) (MonoidWithZero.toMonoid.{u3} (f i) (_inst_1 i)) (_inst_2 i) (_inst_3 i))))) r x)) (HSMul.hSMul.{max u3 u2, max u1 u2, max u2 u1} (forall (j : I), f j) (forall (i : I), g i) (forall (i : I), g i) (instHSMul.{max u2 u3, max u2 u1} (forall (j : I), f j) (forall (j : I), g j) (Pi.smul'.{u2, u3, u1} I (fun (j : I) => f j) (fun (j : I) => g j) (fun (i : I) => SMulZeroClass.toSMul.{u3, u1} (f i) (g i) (AddMonoid.toZero.{u1} (g i) (_inst_2 i)) (DistribSMul.toSMulZeroClass.{u3, u1} (f i) (g i) (AddMonoid.toAddZeroClass.{u1} (g i) (_inst_2 i)) (DistribMulAction.toDistribSMul.{u3, u1} (f i) (g i) (MonoidWithZero.toMonoid.{u3} (f i) (_inst_1 i)) (_inst_2 i) (_inst_3 i)))))) (Pi.single.{u2, u3} I f (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => MonoidWithZero.toZero.{u3} (f i) (_inst_1 i)) i r) (Pi.single.{u2, u1} I g (fun (a : I) (b : I) => _inst_4 a b) (fun (i : I) => AddMonoid.toZero.{u1} (g i) (_inst_2 i)) i x))
Case conversion may be inaccurate. Consider using '#align pi.single_smul₀ Pi.single_smul₀ₓ'. -/
theorem single_smul₀ {g : I → Type _} [∀ i, MonoidWithZero (f i)] [∀ i, AddMonoid (g i)]
    [∀ i, DistribMulAction (f i) (g i)] [DecidableEq I] (i : I) (r : f i) (x : g i) :
    single i (r • x) = single i r • single i x :=
  single_op₂ (fun i : I => ((· • ·) : f i → g i → g i)) (fun j => smul_zero _) _ _ _
#align pi.single_smul₀ Pi.single_smul₀

#print Pi.mulDistribMulAction /-
instance mulDistribMulAction (α) {m : Monoid α} {n : ∀ i, Monoid <| f i}
    [∀ i, MulDistribMulAction α <| f i] :
    @MulDistribMulAction α (∀ i : I, f i) m (@Pi.monoid I f n) :=
  { Pi.mulAction _ with
    smul_one := fun c => funext fun i => smul_one _
    smul_mul := fun c f g => funext fun i => smul_mul' _ _ _ }
#align pi.mul_distrib_mul_action Pi.mulDistribMulAction
-/

#print Pi.mulDistribMulAction' /-
instance mulDistribMulAction' {g : I → Type _} {m : ∀ i, Monoid (f i)} {n : ∀ i, Monoid <| g i}
    [∀ i, MulDistribMulAction (f i) (g i)] :
    @MulDistribMulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m) (@Pi.monoid I g n)
    where
  smul_mul := by
    intros
    ext x
    apply smul_mul'
  smul_one := by
    intros
    ext x
    apply smul_one
#align pi.mul_distrib_mul_action' Pi.mulDistribMulAction'
-/

end Pi

namespace Function

#print Function.hasSMul /-
/-- Non-dependent version of `pi.has_smul`. Lean gets confused by the dependent instance if this
is not present. -/
@[to_additive
      "Non-dependent version of `pi.has_vadd`. Lean gets confused by the dependent instance\nif this is not present."]
instance hasSMul {ι R M : Type _} [SMul R M] : SMul R (ι → M) :=
  Pi.instSMul
#align function.has_smul Function.hasSMul
-/

#print Function.smulCommClass /-
/-- Non-dependent version of `pi.smul_comm_class`. Lean gets confused by the dependent instance if
this is not present. -/
@[to_additive
      "Non-dependent version of `pi.vadd_comm_class`. Lean gets confused by the dependent\ninstance if this is not present."]
instance smulCommClass {ι α β M : Type _} [SMul α M] [SMul β M] [SMulCommClass α β M] :
    SMulCommClass α β (ι → M) :=
  Pi.smulCommClass
#align function.smul_comm_class Function.smulCommClass
-/

/- warning: function.update_smul -> Function.update_smul is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {α : Type.{u3}} [_inst_1 : forall (i : I), SMul.{u3, u2} α (f i)] [_inst_2 : DecidableEq.{succ u1} I] (c : α) (f₁ : forall (i : I), f i) (i : I) (x₁ : f i), Eq.{max (succ u1) (succ u2)} (forall (a : I), f a) (Function.update.{succ u1, succ u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_2 a b) (SMul.smul.{u3, max u1 u2} α (forall (a : I), f a) (Pi.instSMul.{u1, u2, u3} I α (fun (a : I) => f a) (fun (i : I) => _inst_1 i)) c f₁) i (SMul.smul.{u3, u2} α (f i) (_inst_1 i) c x₁)) (SMul.smul.{u3, max u1 u2} α (forall (a : I), f a) (Pi.instSMul.{u1, u2, u3} I α (fun (a : I) => f a) (fun (i : I) => _inst_1 i)) c (Function.update.{succ u1, succ u2} I (fun (a : I) => f a) (fun (a : I) (b : I) => _inst_2 a b) f₁ i x₁))
but is expected to have type
  forall {I : Type.{u2}} {f : I -> Type.{u3}} {α : Type.{u1}} [_inst_1 : forall (i : I), SMul.{u1, u3} α (f i)] [_inst_2 : DecidableEq.{succ u2} I] (c : α) (f₁ : forall (i : I), f i) (i : I) (x₁ : f i), Eq.{max (succ u2) (succ u3)} (forall (a : I), f a) (Function.update.{succ u2, succ u3} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_2 a b) (HSMul.hSMul.{u1, max u2 u3, max u2 u3} α (forall (i : I), f i) (forall (a : I), f a) (instHSMul.{u1, max u2 u3} α (forall (i : I), f i) (Pi.instSMul.{u2, u3, u1} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) c f₁) i (HSMul.hSMul.{u1, u3, u3} α (f i) (f i) (instHSMul.{u1, u3} α (f i) (_inst_1 i)) c x₁)) (HSMul.hSMul.{u1, max u2 u3, max u2 u3} α (forall (a : I), f a) (forall (a : I), f a) (instHSMul.{u1, max u2 u3} α (forall (a : I), f a) (Pi.instSMul.{u2, u3, u1} I α (fun (a : I) => f a) (fun (i : I) => _inst_1 i))) c (Function.update.{succ u2, succ u3} I (fun (a : I) => f a) (fun (a : I) (b : I) => _inst_2 a b) f₁ i x₁))
Case conversion may be inaccurate. Consider using '#align function.update_smul Function.update_smulₓ'. -/
@[to_additive]
theorem update_smul {α : Type _} [∀ i, SMul α (f i)] [DecidableEq I] (c : α) (f₁ : ∀ i, f i) (i : I)
    (x₁ : f i) : update (c • f₁) i (c • x₁) = c • update f₁ i x₁ :=
  funext fun j => (apply_update (fun i => (· • ·) c) f₁ i x₁ j).symm
#align function.update_smul Function.update_smul
#align function.update_vadd Function.update_vadd

end Function

namespace Set

/- warning: set.piecewise_smul -> Set.piecewise_smul is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {α : Type.{u3}} [_inst_1 : forall (i : I), SMul.{u3, u2} α (f i)] (s : Set.{u1} I) [_inst_2 : forall (i : I), Decidable (Membership.Mem.{u1, u1} I (Set.{u1} I) (Set.hasMem.{u1} I) i s)] (c : α) (f₁ : forall (i : I), f i) (g₁ : forall (i : I), f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Set.piecewise.{u1, succ u2} I (fun (i : I) => f i) s (SMul.smul.{u3, max u1 u2} α (forall (i : I), f i) (Pi.instSMul.{u1, u2, u3} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i)) c f₁) (SMul.smul.{u3, max u1 u2} α (forall (i : I), f i) (Pi.instSMul.{u1, u2, u3} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i)) c g₁) (fun (j : I) => _inst_2 j)) (SMul.smul.{u3, max u1 u2} α (forall (i : I), f i) (Pi.instSMul.{u1, u2, u3} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i)) c (Set.piecewise.{u1, succ u2} I (fun (i : I) => f i) s f₁ g₁ (fun (j : I) => _inst_2 j)))
but is expected to have type
  forall {I : Type.{u2}} {f : I -> Type.{u3}} {α : Type.{u1}} [_inst_1 : forall (i : I), SMul.{u1, u3} α (f i)] (s : Set.{u2} I) [_inst_2 : forall (i : I), Decidable (Membership.mem.{u2, u2} I (Set.{u2} I) (Set.instMembershipSet.{u2} I) i s)] (c : α) (f₁ : forall (i : I), f i) (g₁ : forall (i : I), f i), Eq.{max (succ u2) (succ u3)} (forall (i : I), f i) (Set.piecewise.{u2, succ u3} I (fun (i : I) => f i) s (HSMul.hSMul.{u1, max u2 u3, max u2 u3} α (forall (i : I), f i) (forall (i : I), f i) (instHSMul.{u1, max u2 u3} α (forall (i : I), f i) (Pi.instSMul.{u2, u3, u1} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) c f₁) (HSMul.hSMul.{u1, max u2 u3, max u2 u3} α (forall (i : I), f i) (forall (i : I), f i) (instHSMul.{u1, max u2 u3} α (forall (i : I), f i) (Pi.instSMul.{u2, u3, u1} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) c g₁) (fun (j : I) => _inst_2 j)) (HSMul.hSMul.{u1, max u2 u3, max u2 u3} α (forall (i : I), f i) (forall (i : I), f i) (instHSMul.{u1, max u2 u3} α (forall (i : I), f i) (Pi.instSMul.{u2, u3, u1} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) c (Set.piecewise.{u2, succ u3} I (fun (i : I) => f i) s f₁ g₁ (fun (j : I) => _inst_2 j)))
Case conversion may be inaccurate. Consider using '#align set.piecewise_smul Set.piecewise_smulₓ'. -/
@[to_additive]
theorem piecewise_smul {α : Type _} [∀ i, SMul α (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (c : α)
    (f₁ g₁ : ∀ i, f i) : s.piecewise (c • f₁) (c • g₁) = c • s.piecewise f₁ g₁ :=
  s.piecewise_op _ _ fun _ => (· • ·) c
#align set.piecewise_smul Set.piecewise_smul
#align set.piecewise_vadd Set.piecewise_vadd

end Set

section Extend

/- warning: function.extend_smul -> Function.extend_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : SMul.{u1, u4} R γ] (r : R) (f : α -> β) (g : α -> γ) (e : β -> γ), Eq.{max (succ u3) (succ u4)} (β -> γ) (Function.extend.{succ u2, succ u3, succ u4} α β γ f (SMul.smul.{u1, max u2 u4} R (α -> γ) (Function.hasSMul.{u2, u1, u4} α R γ _inst_1) r g) (SMul.smul.{u1, max u3 u4} R (β -> γ) (Function.hasSMul.{u3, u1, u4} β R γ _inst_1) r e)) (SMul.smul.{u1, max u3 u4} R (β -> γ) (Function.hasSMul.{u3, u1, u4} β R γ _inst_1) r (Function.extend.{succ u2, succ u3, succ u4} α β γ f g e))
but is expected to have type
  forall {R : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : SMul.{u4, u1} R γ] (r : R) (f : α -> β) (g : α -> γ) (e : β -> γ), Eq.{max (succ u2) (succ u1)} (β -> γ) (Function.extend.{succ u3, succ u2, succ u1} α β γ f (HSMul.hSMul.{u4, max u3 u1, max u3 u1} R (α -> γ) (α -> γ) (instHSMul.{u4, max u3 u1} R (α -> γ) (Pi.instSMul.{u3, u1, u4} α R (fun (a._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2665 : α) => γ) (fun (i : α) => _inst_1))) r g) (HSMul.hSMul.{u4, max u2 u1, max u2 u1} R (β -> γ) (β -> γ) (instHSMul.{u4, max u2 u1} R (β -> γ) (Pi.instSMul.{u2, u1, u4} β R (fun (a._@.Mathlib.GroupTheory.GroupAction.Pi._hyg.2668 : β) => γ) (fun (i : β) => _inst_1))) r e)) (HSMul.hSMul.{u4, max u2 u1, max u2 u1} R (β -> γ) (β -> γ) (instHSMul.{u4, max u2 u1} R (β -> γ) (Pi.instSMul.{u2, u1, u4} β R (fun (a._@.Mathlib.Logic.Function.Basic._hyg.7419 : β) => γ) (fun (i : β) => _inst_1))) r (Function.extend.{succ u3, succ u2, succ u1} α β γ f g e))
Case conversion may be inaccurate. Consider using '#align function.extend_smul Function.extend_smulₓ'. -/
@[to_additive]
theorem Function.extend_smul {R α β γ : Type _} [SMul R γ] (r : R) (f : α → β) (g : α → γ)
    (e : β → γ) : Function.extend f (r • g) (r • e) = r • Function.extend f g e :=
  funext fun _ => by convert (apply_dite ((· • ·) r) _ _ _).symm
#align function.extend_smul Function.extend_smul
#align function.extend_vadd Function.extend_vadd

end Extend

