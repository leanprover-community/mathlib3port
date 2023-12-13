/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Topology.LocalHomeomorph

#align_import topology.is_locally_homeomorph from "leanprover-community/mathlib"@"23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6"

/-!
# Local homeomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines local homeomorphisms.

## Main definitions

* `is_locally_homeomorph`: A function `f : X → Y` satisfies `is_locally_homeomorph` if for each
  point `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.

  Note that `is_locally_homeomorph` is a global condition. This is in contrast to
  `local_homeomorph`, which is a homeomorphism between specific open subsets.
-/


open scoped Topology

variable {X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)

#print IsLocalHomeomorphOn /-
/-- A function `f : X → Y` satisfies `is_locally_homeomorph_on f s` if each `x ∈ s` is contained in
the source of some `e : local_homeomorph X Y` with `f = e`. -/
def IsLocalHomeomorphOn :=
  ∀ x ∈ s, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ f = e
#align is_locally_homeomorph_on IsLocalHomeomorphOn
-/

namespace IsLocalHomeomorphOn

#print IsLocalHomeomorphOn.mk /-
/-- Proves that `f` satisfies `is_locally_homeomorph_on f s`. The condition `h` is weaker than the
definition of `is_locally_homeomorph_on f s`, since it only requires `e : local_homeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x ∈ s, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ ∀ y ∈ e.source, f y = e y) :
    IsLocalHomeomorphOn f s := by
  intro x hx
  obtain ⟨e, hx, he⟩ := h x hx
  exact
    ⟨{ e with
        toFun := f
        map_source' := fun x hx => by rw [he x hx] <;> exact e.map_source' hx
        left_inv' := fun x hx => by rw [he x hx] <;> exact e.left_inv' hx
        right_inv' := fun y hy => by rw [he _ (e.map_target' hy)] <;> exact e.right_inv' hy
        continuous_toFun := (continuousOn_congr he).mpr e.continuous_to_fun },
      hx, rfl⟩
#align is_locally_homeomorph_on.mk IsLocalHomeomorphOn.mk
-/

variable {g f s t}

#print IsLocalHomeomorphOn.map_nhds_eq /-
theorem map_nhds_eq (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x ∈ s) : (𝓝 x).map f = 𝓝 (f x) :=
  let ⟨e, hx, he⟩ := hf x hx
  he.symm ▸ e.map_nhds_eq hx
#align is_locally_homeomorph_on.map_nhds_eq IsLocalHomeomorphOn.map_nhds_eq
-/

#print IsLocalHomeomorphOn.continuousAt /-
protected theorem continuousAt (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x ∈ s) :
    ContinuousAt f x :=
  (hf.map_nhds_eq hx).le
#align is_locally_homeomorph_on.continuous_at IsLocalHomeomorphOn.continuousAt
-/

#print IsLocalHomeomorphOn.continuousOn /-
protected theorem continuousOn (hf : IsLocalHomeomorphOn f s) : ContinuousOn f s :=
  ContinuousAt.continuousOn fun x => hf.ContinuousAt
#align is_locally_homeomorph_on.continuous_on IsLocalHomeomorphOn.continuousOn
-/

#print IsLocalHomeomorphOn.comp /-
protected theorem comp (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s :=
  by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩
#align is_locally_homeomorph_on.comp IsLocalHomeomorphOn.comp
-/

end IsLocalHomeomorphOn

#print IsLocalHomeomorph /-
/-- A function `f : X → Y` satisfies `is_locally_homeomorph f` if each `x : x` is contained in
  the source of some `e : local_homeomorph X Y` with `f = e`. -/
def IsLocalHomeomorph :=
  ∀ x : X, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ f = e
#align is_locally_homeomorph IsLocalHomeomorph
-/

variable {f}

#print isLocalHomeomorph_iff_isLocalHomeomorphOn_univ /-
theorem isLocalHomeomorph_iff_isLocalHomeomorphOn_univ :
    IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ := by
  simp only [IsLocalHomeomorph, IsLocalHomeomorphOn, Set.mem_univ, forall_true_left]
#align is_locally_homeomorph_iff_is_locally_homeomorph_on_univ isLocalHomeomorph_iff_isLocalHomeomorphOn_univ
-/

#print IsLocalHomeomorph.isLocalHomeomorphOn /-
protected theorem IsLocalHomeomorph.isLocalHomeomorphOn (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorphOn f Set.univ :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hf
#align is_locally_homeomorph.is_locally_homeomorph_on IsLocalHomeomorph.isLocalHomeomorphOn
-/

variable (f)

namespace IsLocalHomeomorph

#print IsLocalHomeomorph.mk /-
/-- Proves that `f` satisfies `is_locally_homeomorph f`. The condition `h` is weaker than the
definition of `is_locally_homeomorph f`, since it only requires `e : local_homeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x : X, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ ∀ y ∈ e.source, f y = e y) :
    IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (IsLocalHomeomorphOn.mk f Set.univ fun x hx => h x)
#align is_locally_homeomorph.mk IsLocalHomeomorph.mk
-/

variable {g f}

#print IsLocalHomeomorph.map_nhds_eq /-
theorem map_nhds_eq (hf : IsLocalHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
  hf.IsLocalHomeomorphOn.map_nhds_eq (Set.mem_univ x)
#align is_locally_homeomorph.map_nhds_eq IsLocalHomeomorph.map_nhds_eq
-/

#print IsLocalHomeomorph.continuous /-
protected theorem continuous (hf : IsLocalHomeomorph f) : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.IsLocalHomeomorphOn.ContinuousOn
#align is_locally_homeomorph.continuous IsLocalHomeomorph.continuous
-/

#print IsLocalHomeomorph.isOpenMap /-
protected theorem isOpenMap (hf : IsLocalHomeomorph f) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x => ge_of_eq (hf.map_nhds_eq x)
#align is_locally_homeomorph.is_open_map IsLocalHomeomorph.isOpenMap
-/

#print IsLocalHomeomorph.comp /-
protected theorem comp (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorph (g ∘ f) :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (hg.IsLocalHomeomorphOn.comp hf.IsLocalHomeomorphOn (Set.univ.mapsTo_univ f))
#align is_locally_homeomorph.comp IsLocalHomeomorph.comp
-/

end IsLocalHomeomorph

