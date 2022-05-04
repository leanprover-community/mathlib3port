/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathbin.Topology.Homotopy.Path
import Mathbin.Topology.Homotopy.Equiv

/-!
# Contractible spaces

In this file, we define `contractible_space`, a space that is homotopy equivalent to `unit`.
-/


noncomputable section

namespace ContinuousMap

variable {X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A map is nullhomotopic if it is homotopic to a constant map. -/
def Nullhomotopic (f : C(X, Y)) : Prop :=
  ∃ y : Y, Homotopic f (ContinuousMap.const _ y)

theorem nullhomotopic_of_constant (y : Y) : Nullhomotopic (ContinuousMap.const X y) :=
  ⟨y, by
    rfl⟩

theorem Nullhomotopic.comp_right {f : C(X, Y)} (hf : f.Nullhomotopic) (g : C(Y, Z)) : (g.comp f).Nullhomotopic := by
  cases' hf with y hy
  use g y
  exact homotopic.hcomp hy (homotopic.refl g)

theorem Nullhomotopic.comp_left {f : C(Y, Z)} (hf : f.Nullhomotopic) (g : C(X, Y)) : (f.comp g).Nullhomotopic := by
  cases' hf with y hy
  use y
  exact homotopic.hcomp (homotopic.refl g) hy

end ContinuousMap

open ContinuousMap

open ContinuousMap

-- ././Mathport/Syntax/Translate/Basic.lean:1250:30: infer kinds are unsupported in Lean 4: #[`hequiv_unit] []
/-- A contractible space is one that is homotopy equivalent to `unit`. -/
class ContractibleSpace (X : Type _) [TopologicalSpace X] : Prop where
  hequiv_unit : Nonempty (X ≃ₕ Unit)

variable (X : Type _) [TopologicalSpace X] [ContractibleSpace X]

theorem id_nullhomotopic : (ContinuousMap.id X).Nullhomotopic := by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit X
  use hv.inv_fun ()
  convert hv.left_inv.symm
  ext
  simp
  congr

theorem contractible_iff_id_nullhomotopic (Y : Type _) [TopologicalSpace Y] :
    ContractibleSpace Y ↔ (ContinuousMap.id Y).Nullhomotopic := by
  constructor
  · intro
    apply id_nullhomotopic
    
  rintro ⟨p, h⟩
  refine_struct { hequiv_unit := ⟨{ toFun := ContinuousMap.const _ (), invFun := ContinuousMap.const _ p }⟩ }
  · exact h.symm
    
  · convert homotopic.refl (ContinuousMap.id Unit)
    ext
    

namespace ContractibleSpace

instance (priority := 100) : PathConnectedSpace X := by
  obtain ⟨p, ⟨h⟩⟩ := id_nullhomotopic X
  have : ∀ x, Joined p x := fun x => ⟨(h.eval_at x).symm⟩
  rw [path_connected_space_iff_eq]
  use p
  ext
  tauto

end ContractibleSpace

