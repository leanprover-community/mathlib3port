/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury G. Kudryashov
-/
import Mathbin.Topology.Constructions

/-!
# Inseparable points

In this file we require two relations on a topological space: `specializes` (notation : `x ⤳ y`) and
`inseparable`, then prove some basic lemmas about these relations.

## Main definitions

* `specializes` : `specializes x y` (`x ⤳ y`) means that `x` specializes to `y`, i.e.
  `y` is in the closure of `x`.

* `specialization_preorder` : specialization gives a preorder on a topological space. In case of a
  T₀ space, this preorder is a partial order, see `specialization_order`.

* `inseparable x y` means that two points can't be separated by an open set.
-/


open TopologicalSpace

open Set

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X}

/-- `x` specializes to `y` if `y` is in the closure of `x`. The notation used is `x ⤳ y`. -/
def Specializes (x y : X) : Prop :=
  y ∈ Closure ({x} : Set X)

-- mathport name: «expr ⤳ »
infixl:300 " ⤳ " => Specializes

theorem specializes_def (x y : X) : x ⤳ y ↔ y ∈ Closure ({x} : Set X) :=
  Iff.rfl

theorem specializes_iff_closure_subset : x ⤳ y ↔ Closure ({y} : Set X) ⊆ Closure ({x} : Set X) :=
  is_closed_closure.mem_iff_closure_subset

theorem specializes_rfl : x ⤳ x :=
  subset_closure (mem_singleton x)

theorem specializes_refl (x : X) : x ⤳ x :=
  specializes_rfl

theorem Specializes.trans : x ⤳ y → y ⤳ z → x ⤳ z := by
  simp_rw [specializes_iff_closure_subset]
  exact fun a b => b.trans a

theorem specializes_iff_forall_closed : x ⤳ y ↔ ∀ Z : Set X h : IsClosed Z, x ∈ Z → y ∈ Z := by
  constructor
  · intro h Z hZ
    rw [hZ.mem_iff_closure_subset, hZ.mem_iff_closure_subset]
    exact (specializes_iff_closure_subset.mp h).trans
    
  · intro h
    exact h _ is_closed_closure (subset_closure <| Set.mem_singleton x)
    

theorem specializes_iff_forall_open : x ⤳ y ↔ ∀ U : Set X h : IsOpen U, y ∈ U → x ∈ U := by
  rw [specializes_iff_forall_closed]
  exact
    ⟨fun h U hU => not_imp_not.mp (h _ (is_closed_compl_iff.mpr hU)), fun h U hU =>
      not_imp_not.mp (h _ (is_open_compl_iff.mpr hU))⟩

theorem Specializes.map (h : x ⤳ y) {f : X → Y} (hf : Continuous f) : f x ⤳ f y := by
  rw [specializes_def, ← Set.image_singleton]
  exact image_closure_subset_closure_image hf ⟨_, h, rfl⟩

section SpecializeOrder

variable (X)

/-- Specialization forms a preorder on the topological space. -/
def specializationPreorder : Preorderₓ X where
  le := fun x y => y ⤳ x
  le_refl := fun x => specializes_refl x
  le_trans := fun _ _ _ h₁ h₂ => Specializes.trans h₂ h₁

attribute [local instance] specializationPreorder

variable {X}

theorem SpecializationOrder.monotone_of_continuous (f : X → Y) (hf : Continuous f) : Monotone f := fun x y h =>
  Specializes.map h hf

end SpecializeOrder

/-- Two points are topologically inseparable if no open set separates them. -/
def Inseparable (x y : X) : Prop :=
  ∀ U : Set X hU : IsOpen U, x ∈ U ↔ y ∈ U

theorem inseparable_iff_nhds_eq : Inseparable x y ↔ 𝓝 x = 𝓝 y :=
  ⟨fun h => by
    simp (config := { contextual := true })only [nhds_def', h _], fun h U hU => by
    simp only [← hU.mem_nhds_iff, h]⟩

alias inseparable_iff_nhds_eq ↔ Inseparable.nhds_eq _

theorem Inseparable.map {f : X → Y} (h : Inseparable x y) (hf : Continuous f) : Inseparable (f x) (f y) := fun U hU =>
  h (f ⁻¹' U) (hU.Preimage hf)

theorem inseparable_iff_closed : Inseparable x y ↔ ∀ U : Set X hU : IsClosed U, x ∈ U ↔ y ∈ U :=
  ⟨fun h U hU => not_iff_not.mp (h _ hU.1), fun h U hU => not_iff_not.mp (h _ (is_closed_compl_iff.mpr hU))⟩

theorem inseparable_iff_closure (x y : X) : Inseparable x y ↔ x ∈ Closure ({y} : Set X) ∧ y ∈ Closure ({x} : Set X) :=
  by
  rw [inseparable_iff_closed]
  exact
    ⟨fun h =>
      ⟨(h _ is_closed_closure).mpr (subset_closure <| Set.mem_singleton y),
        (h _ is_closed_closure).mp (subset_closure <| Set.mem_singleton x)⟩,
      fun h U hU =>
      ⟨fun hx => (IsClosed.closure_subset_iff hU).mpr (set.singleton_subset_iff.mpr hx) h.2, fun hy =>
        (IsClosed.closure_subset_iff hU).mpr (set.singleton_subset_iff.mpr hy) h.1⟩⟩

theorem inseparable_iff_specializes_and (x y : X) : Inseparable x y ↔ x ⤳ y ∧ y ⤳ x :=
  (inseparable_iff_closure x y).trans (and_comm _ _)

theorem subtype_inseparable_iff {U : Set X} (x y : U) : Inseparable x y ↔ Inseparable (x : X) y := by
  simp_rw [inseparable_iff_closure, closure_subtype, image_singleton]

