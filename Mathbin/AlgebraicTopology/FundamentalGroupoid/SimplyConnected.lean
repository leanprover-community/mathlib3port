/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathbin.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathbin.Topology.Homotopy.Contractible
import Mathbin.CategoryTheory.Punit
import Mathbin.AlgebraicTopology.FundamentalGroupoid.Punit

/-!
# Simply connected spaces
This file defines simply connected spaces.
A topological space is simply connected if its fundamental groupoid is equivalent to `unit`.

## Main theorems
  - `simply_connected_iff_unique_homotopic` - A space is simply connected if and only if it is
    nonempty and there is a unique path up to homotopy between any two points

  - `simply_connected_space.of_contractible` - A contractible space is simply connected
-/


noncomputable section

open CategoryTheory

open ContinuousMap

open ContinuousMap

-- ./././Mathport/Syntax/Translate/Command.lean:324:30: infer kinds are unsupported in Lean 4: #[`equiv_unit] []
/-- A simply connected space is one whose fundamental groupoid is equivalent to `discrete unit` -/
class SimplyConnectedSpace (X : Type _) [TopologicalSpace X] : Prop where
  equiv_unit : Nonempty (FundamentalGroupoid X ≌ Discrete Unit)

theorem simply_connected_def (X : Type _) [TopologicalSpace X] :
    SimplyConnectedSpace X ↔ Nonempty (FundamentalGroupoid X ≌ Discrete Unit) :=
  ⟨fun h => @SimplyConnectedSpace.equiv_unit X _ h, fun h => ⟨h⟩⟩

theorem simply_connected_iff_unique_homotopic (X : Type _) [TopologicalSpace X] :
    SimplyConnectedSpace X ↔ Nonempty X ∧ ∀ x y : X, Nonempty (Unique (Path.Homotopic.Quotient x y)) := by
  rw [simply_connected_def, equiv_punit_iff_unique]
  rfl

namespace SimplyConnectedSpace

variable {X : Type _} [TopologicalSpace X] [SimplyConnectedSpace X]

instance (x y : X) : Subsingleton (Path.Homotopic.Quotient x y) :=
  @Unique.subsingleton _
    (Nonempty.some
      (by
        rw [simply_connected_iff_unique_homotopic] at *
        tauto))

attribute [local instance] Path.Homotopic.setoid

instance (priority := 100) : PathConnectedSpace X :=
  let unique_homotopic := (simply_connected_iff_unique_homotopic X).mp inferInstance
  { Nonempty := unique_homotopic.1, Joined := fun x y => ⟨(unique_homotopic.2 x y).some.default.out⟩ }

/-- In a simply connected space, any two paths are homotopic -/
theorem paths_homotopic {x y : X} (p₁ p₂ : Path x y) : Path.Homotopic p₁ p₂ := by
  simpa using @Subsingleton.elimₓ (Path.Homotopic.Quotient x y) _ ⟦p₁⟧ ⟦p₂⟧

instance (priority := 100) of_contractible (Y : Type _) [TopologicalSpace Y] [ContractibleSpace Y] :
    SimplyConnectedSpace Y where equiv_unit :=
    let H : Top.of Y ≃ₕ Top.of Unit := (ContractibleSpace.hequiv_unit Y).some
    ⟨(FundamentalGroupoidFunctor.equivOfHomotopyEquiv H).trans FundamentalGroupoid.punitEquivDiscretePunit⟩

end SimplyConnectedSpace

attribute [local instance] Path.Homotopic.setoid

/-- A space is simply connected iff it is path connected, and there is at most one path
  up to homotopy between any two points. -/
theorem simply_connected_iff_paths_homotopic {Y : Type _} [TopologicalSpace Y] :
    SimplyConnectedSpace Y ↔ PathConnectedSpace Y ∧ ∀ x y : Y, Subsingleton (Path.Homotopic.Quotient x y) :=
  ⟨by
    intro
    constructor <;> infer_instance, fun h => by
    cases h
    rw [simply_connected_iff_unique_homotopic]
    exact ⟨inferInstance, fun x y => ⟨uniqueOfSubsingleton ⟦PathConnectedSpace.somePath x y⟧⟩⟩⟩

/-- Another version of `simply_connected_iff_paths_homotopic` -/
theorem simply_connected_iff_paths_homotopic' {Y : Type _} [TopologicalSpace Y] :
    SimplyConnectedSpace Y ↔ PathConnectedSpace Y ∧ ∀ {x y : Y} (p₁ p₂ : Path x y), Path.Homotopic p₁ p₂ := by
  convert simply_connected_iff_paths_homotopic
  simp [Path.Homotopic.Quotient, Setoidₓ.eq_top_iff]
  rfl

