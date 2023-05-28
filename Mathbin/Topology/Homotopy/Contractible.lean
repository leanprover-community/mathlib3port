/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala

! This file was ported from Lean 3 source module topology.homotopy.contractible
! leanprover-community/mathlib commit dbdf71cee7bb20367cb7e37279c08b0c218cf967
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Homotopy.Path
import Mathbin.Topology.Homotopy.Equiv

/-!
# Contractible spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define `contractible_space`, a space that is homotopy equivalent to `unit`.
-/


noncomputable section

namespace ContinuousMap

variable {X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

#print ContinuousMap.Nullhomotopic /-
/-- A map is nullhomotopic if it is homotopic to a constant map. -/
def Nullhomotopic (f : C(X, Y)) : Prop :=
  ∃ y : Y, Homotopic f (ContinuousMap.const _ y)
#align continuous_map.nullhomotopic ContinuousMap.Nullhomotopic
-/

/- warning: continuous_map.nullhomotopic_of_constant -> ContinuousMap.nullhomotopic_of_constant is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (y : Y), ContinuousMap.Nullhomotopic.{u1, u2} X Y _inst_1 _inst_2 (ContinuousMap.const.{u1, u2} X Y _inst_1 _inst_2 y)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] (y : Y), ContinuousMap.Nullhomotopic.{u2, u1} X Y _inst_1 _inst_2 (ContinuousMap.const.{u2, u1} X Y _inst_1 _inst_2 y)
Case conversion may be inaccurate. Consider using '#align continuous_map.nullhomotopic_of_constant ContinuousMap.nullhomotopic_of_constantₓ'. -/
theorem nullhomotopic_of_constant (y : Y) : Nullhomotopic (ContinuousMap.const X y) :=
  ⟨y, by rfl⟩
#align continuous_map.nullhomotopic_of_constant ContinuousMap.nullhomotopic_of_constant

/- warning: continuous_map.nullhomotopic.comp_right -> ContinuousMap.Nullhomotopic.comp_right is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2}, (ContinuousMap.Nullhomotopic.{u1, u2} X Y _inst_1 _inst_2 f) -> (forall (g : ContinuousMap.{u2, u3} Y Z _inst_2 _inst_3), ContinuousMap.Nullhomotopic.{u1, u3} X Z _inst_1 _inst_3 (ContinuousMap.comp.{u1, u2, u3} X Y Z _inst_1 _inst_2 _inst_3 g f))
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u1} Z] {f : ContinuousMap.{u3, u2} X Y _inst_1 _inst_2}, (ContinuousMap.Nullhomotopic.{u3, u2} X Y _inst_1 _inst_2 f) -> (forall (g : ContinuousMap.{u2, u1} Y Z _inst_2 _inst_3), ContinuousMap.Nullhomotopic.{u3, u1} X Z _inst_1 _inst_3 (ContinuousMap.comp.{u3, u2, u1} X Y Z _inst_1 _inst_2 _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align continuous_map.nullhomotopic.comp_right ContinuousMap.Nullhomotopic.comp_rightₓ'. -/
theorem Nullhomotopic.comp_right {f : C(X, Y)} (hf : f.Nullhomotopic) (g : C(Y, Z)) :
    (g.comp f).Nullhomotopic := by cases' hf with y hy; use g y;
  exact homotopic.hcomp hy (homotopic.refl g)
#align continuous_map.nullhomotopic.comp_right ContinuousMap.Nullhomotopic.comp_right

/- warning: continuous_map.nullhomotopic.comp_left -> ContinuousMap.Nullhomotopic.comp_left is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {f : ContinuousMap.{u2, u3} Y Z _inst_2 _inst_3}, (ContinuousMap.Nullhomotopic.{u2, u3} Y Z _inst_2 _inst_3 f) -> (forall (g : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2), ContinuousMap.Nullhomotopic.{u1, u3} X Z _inst_1 _inst_3 (ContinuousMap.comp.{u1, u2, u3} X Y Z _inst_1 _inst_2 _inst_3 f g))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} Y] [_inst_3 : TopologicalSpace.{u2} Z] {f : ContinuousMap.{u3, u2} Y Z _inst_2 _inst_3}, (ContinuousMap.Nullhomotopic.{u3, u2} Y Z _inst_2 _inst_3 f) -> (forall (g : ContinuousMap.{u1, u3} X Y _inst_1 _inst_2), ContinuousMap.Nullhomotopic.{u1, u2} X Z _inst_1 _inst_3 (ContinuousMap.comp.{u1, u3, u2} X Y Z _inst_1 _inst_2 _inst_3 f g))
Case conversion may be inaccurate. Consider using '#align continuous_map.nullhomotopic.comp_left ContinuousMap.Nullhomotopic.comp_leftₓ'. -/
theorem Nullhomotopic.comp_left {f : C(Y, Z)} (hf : f.Nullhomotopic) (g : C(X, Y)) :
    (f.comp g).Nullhomotopic := by cases' hf with y hy; use y;
  exact homotopic.hcomp (homotopic.refl g) hy
#align continuous_map.nullhomotopic.comp_left ContinuousMap.Nullhomotopic.comp_left

end ContinuousMap

open ContinuousMap

open ContinuousMap

#print ContractibleSpace /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`hequiv_unit] [] -/
/-- A contractible space is one that is homotopy equivalent to `unit`. -/
class ContractibleSpace (X : Type _) [TopologicalSpace X] : Prop where
  hequiv_unit : Nonempty (X ≃ₕ Unit)
#align contractible_space ContractibleSpace
-/

#print id_nullhomotopic /-
theorem id_nullhomotopic (X : Type _) [TopologicalSpace X] [ContractibleSpace X] :
    (ContinuousMap.id X).Nullhomotopic :=
  by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit X
  use hv.inv_fun ()
  convert hv.left_inv.symm
  ext; simp; congr
#align id_nullhomotopic id_nullhomotopic
-/

#print contractible_iff_id_nullhomotopic /-
theorem contractible_iff_id_nullhomotopic (Y : Type _) [TopologicalSpace Y] :
    ContractibleSpace Y ↔ (ContinuousMap.id Y).Nullhomotopic :=
  by
  constructor; · intro ; apply id_nullhomotopic
  rintro ⟨p, h⟩
  refine_struct
    {
      hequiv_unit :=
        ⟨{  toFun := ContinuousMap.const _ ()
            invFun := ContinuousMap.const _ p }⟩ }
  · exact h.symm; · convert homotopic.refl (ContinuousMap.id Unit); ext
#align contractible_iff_id_nullhomotopic contractible_iff_id_nullhomotopic
-/

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]

#print ContinuousMap.HomotopyEquiv.contractibleSpace /-
protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace [ContractibleSpace Y] (e : X ≃ₕ Y) :
    ContractibleSpace X :=
  ⟨(ContractibleSpace.hequiv_unit Y).map e.trans⟩
#align continuous_map.homotopy_equiv.contractible_space ContinuousMap.HomotopyEquiv.contractibleSpace
-/

/- warning: continuous_map.homotopy_equiv.contractible_space_iff -> ContinuousMap.HomotopyEquiv.contractibleSpace_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y], (ContinuousMap.HomotopyEquiv.{u1, u2} X Y _inst_1 _inst_2) -> (Iff (ContractibleSpace.{u1} X _inst_1) (ContractibleSpace.{u2} Y _inst_2))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y], (ContinuousMap.HomotopyEquiv.{u2, u1} X Y _inst_1 _inst_2) -> (Iff (ContractibleSpace.{u2} X _inst_1) (ContractibleSpace.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align continuous_map.homotopy_equiv.contractible_space_iff ContinuousMap.HomotopyEquiv.contractibleSpace_iffₓ'. -/
protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace_iff (e : X ≃ₕ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  ⟨by intro h; exact e.symm.contractible_space, by intro h; exact e.contractible_space⟩
#align continuous_map.homotopy_equiv.contractible_space_iff ContinuousMap.HomotopyEquiv.contractibleSpace_iff

#print Homeomorph.contractibleSpace /-
protected theorem Homeomorph.contractibleSpace [ContractibleSpace Y] (e : X ≃ₜ Y) :
    ContractibleSpace X :=
  e.toHomotopyEquiv.ContractibleSpace
#align homeomorph.contractible_space Homeomorph.contractibleSpace
-/

/- warning: homeomorph.contractible_space_iff -> Homeomorph.contractibleSpace_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y], (Homeomorph.{u1, u2} X Y _inst_1 _inst_2) -> (Iff (ContractibleSpace.{u1} X _inst_1) (ContractibleSpace.{u2} Y _inst_2))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y], (Homeomorph.{u2, u1} X Y _inst_1 _inst_2) -> (Iff (ContractibleSpace.{u2} X _inst_1) (ContractibleSpace.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align homeomorph.contractible_space_iff Homeomorph.contractibleSpace_iffₓ'. -/
protected theorem Homeomorph.contractibleSpace_iff (e : X ≃ₜ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  e.toHomotopyEquiv.contractibleSpace_iff
#align homeomorph.contractible_space_iff Homeomorph.contractibleSpace_iff

namespace ContractibleSpace

instance (priority := 100) [ContractibleSpace X] : PathConnectedSpace X :=
  by
  obtain ⟨p, ⟨h⟩⟩ := id_nullhomotopic X
  have : ∀ x, Joined p x := fun x => ⟨(h.eval_at x).symm⟩
  rw [pathConnectedSpace_iff_eq]; use p; ext; tauto

end ContractibleSpace

