/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.uniform_space.equicontinuity
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Equicontinuity of a family of functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `X` be a topological space and `α` a `uniform_space`. A family of functions `F : ι → X → α`
is said to be *equicontinuous at a point `x₀ : X`* when, for any entourage `U` in `α`, there is a
neighborhood `V` of `x₀` such that, for all `x ∈ V`, and *for all `i`*, `F i x` is `U`-close to
`F i x₀`. In other words, one has `∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x, ∀ i, dist x₀ x < δ → dist (F i x₀) (F i x) < ε`.

`F` is said to be *equicontinuous* if it is equicontinuous at each point.

A closely related concept is that of ***uniform*** *equicontinuity* of a family of functions
`F : ι → β → α` between uniform spaces, which means that, for any entourage `U` in `α`, there is an
entourage `V` in `β` such that, if `x` and `y` are `V`-close, then *for all `i`*, `F i x` and
`F i y` are `U`-close. In other words, one has
`∀ U ∈ 𝓤 α, ∀ᶠ xy in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x y, ∀ i, dist x y < δ → dist (F i x₀) (F i x) < ε`.

## Main definitions

* `equicontinuous_at`: equicontinuity of a family of functions at a point
* `equicontinuous`: equicontinuity of a family of functions on the whole domain
* `uniform_equicontinuous`: uniform equicontinuity of a family of functions on the whole domain

## Main statements

* `equicontinuous_iff_continuous`: equicontinuity can be expressed as a simple continuity
  condition between well-chosen function spaces. This is really useful for building up the theory.
* `equicontinuous.closure`: if a set of functions is equicontinuous, its closure
  *for the topology of uniform convergence* is also equicontinuous.

## Notations

Throughout this file, we use :
- `ι`, `κ` for indexing types
- `X`, `Y`, `Z` for topological spaces
- `α`, `β`, `γ` for uniform spaces

## Implementation details

We choose to express equicontinuity as a properties of indexed families of functions rather
than sets of functions for the following reasons:
- it is really easy to express equicontinuity of `H : set (X → α)` using our setup: it is just
  equicontinuity of the family `coe : ↥H → (X → α)`. On the other hand, going the other way around
  would require working with the range of the family, which is always annoying because it
  introduces useless existentials.
- in most applications, one doesn't work with bare functions but with a more specific hom type
  `hom`. Equicontinuity of a set `H : set hom` would then have to be expressed as equicontinuity
  of `coe_fn '' H`, which is super annoying to work with. This is much simpler with families,
  because equicontinuity of a family `𝓕 : ι → hom` would simply be expressed as equicontinuity
  of `coe_fn ∘ 𝓕`, which doesn't introduce any nasty existentials.

To simplify statements, we do provide abbreviations `set.equicontinuous_at`, `set.equicontinuous`
and `set.uniform_equicontinuous` asserting the corresponding fact about the family
`coe : ↥H → (X → α)` where `H : set (X → α)`. Note however that these won't work for sets of hom
types, and in that case one should go back to the family definition rather than using `set.image`.

Since we have no use case for it yet, we don't introduce any relative version
(i.e no `equicontinuous_within_at` or `equicontinuous_on`), but this is more of a conservative
position than a design decision, so anyone needing relative versions should feel free to add them,
and that should hopefully be a straightforward task.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]

## Tags

equicontinuity, uniform convergence, ascoli
-/


section

open UniformSpace Filter Set

open uniformity Topology UniformConvergence

variable {ι κ X Y Z α β γ 𝓕 : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [UniformSpace α] [UniformSpace β] [UniformSpace γ]

#print EquicontinuousAt /-
/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous at `x₀ : X`* if, for all entourage `U ∈ 𝓤 α`, there is a neighborhood `V` of `x₀`
such that, for all `x ∈ V` and for all `i : ι`, `F i x` is `U`-close to `F i x₀`. -/
def EquicontinuousAt (F : ι → X → α) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U
#align equicontinuous_at EquicontinuousAt
-/

#print Set.EquicontinuousAt /-
/-- We say that a set `H : set (X → α)` of functions is equicontinuous at a point if the family
`coe : ↥H → (X → α)` is equicontinuous at that point. -/
protected abbrev Set.EquicontinuousAt (H : Set <| X → α) (x₀ : X) : Prop :=
  EquicontinuousAt (coe : H → X → α) x₀
#align set.equicontinuous_at Set.EquicontinuousAt
-/

#print Equicontinuous /-
/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous* on all of `X` if it is equicontinuous at each point of `X`. -/
def Equicontinuous (F : ι → X → α) : Prop :=
  ∀ x₀, EquicontinuousAt F x₀
#align equicontinuous Equicontinuous
-/

#print Set.Equicontinuous /-
/-- We say that a set `H : set (X → α)` of functions is equicontinuous if the family
`coe : ↥H → (X → α)` is equicontinuous. -/
protected abbrev Set.Equicontinuous (H : Set <| X → α) : Prop :=
  Equicontinuous (coe : H → X → α)
#align set.equicontinuous Set.Equicontinuous
-/

#print UniformEquicontinuous /-
/-- A family `F : ι → β → α` of functions between uniform spaces is *uniformly equicontinuous* if,
for all entourage `U ∈ 𝓤 α`, there is an entourage `V ∈ 𝓤 β` such that, whenever `x` and `y` are
`V`-close, we have that, *for all `i : ι`*, `F i x` is `U`-close to `F i x₀`. -/
def UniformEquicontinuous (F : ι → β → α) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ xy : β × β in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U
#align uniform_equicontinuous UniformEquicontinuous
-/

#print Set.UniformEquicontinuous /-
/-- We say that a set `H : set (X → α)` of functions is uniformly equicontinuous if the family
`coe : ↥H → (X → α)` is uniformly equicontinuous. -/
protected abbrev Set.UniformEquicontinuous (H : Set <| β → α) : Prop :=
  UniformEquicontinuous (coe : H → β → α)
#align set.uniform_equicontinuous Set.UniformEquicontinuous
-/

/- warning: equicontinuous_at_iff_pair -> equicontinuousAt_iff_pair is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {F : ι -> X -> α} {x₀ : X}, Iff (EquicontinuousAt.{u1, u2, u3} ι X α _inst_1 _inst_4 F x₀) (forall (U : Set.{u3} (Prod.{u3, u3} α α)), (Membership.Mem.{u3, u3} (Set.{u3} (Prod.{u3, u3} α α)) (Filter.{u3} (Prod.{u3, u3} α α)) (Filter.hasMem.{u3} (Prod.{u3, u3} α α)) U (uniformity.{u3} α _inst_4)) -> (Exists.{succ u2} (Set.{u2} X) (fun (V : Set.{u2} X) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} X) (Filter.{u2} X) (Filter.hasMem.{u2} X) V (nhds.{u2} X _inst_1 x₀)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} X) (Filter.{u2} X) (Filter.hasMem.{u2} X) V (nhds.{u2} X _inst_1 x₀)) => forall (x : X), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x V) -> (forall (y : X), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) y V) -> (forall (i : ι), Membership.Mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.hasMem.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α (F i x) (F i y)) U))))))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {F : ι -> X -> α} {x₀ : X}, Iff (EquicontinuousAt.{u3, u2, u1} ι X α _inst_1 _inst_4 F x₀) (forall (U : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) U (uniformity.{u1} α _inst_4)) -> (Exists.{succ u2} (Set.{u2} X) (fun (V : Set.{u2} X) => And (Membership.mem.{u2, u2} (Set.{u2} X) (Filter.{u2} X) (instMembershipSetFilter.{u2} X) V (nhds.{u2} X _inst_1 x₀)) (forall (x : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x V) -> (forall (y : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) y V) -> (forall (i : ι), Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (F i x) (F i y)) U))))))
Case conversion may be inaccurate. Consider using '#align equicontinuous_at_iff_pair equicontinuousAt_iff_pairₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » V) -/
/-- Reformulation of equicontinuity at `x₀` comparing two variables near `x₀` instead of comparing
only one with `x₀`. -/
theorem equicontinuousAt_iff_pair {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔
      ∀ U ∈ 𝓤 α, ∃ V ∈ 𝓝 x₀, ∀ (x) (_ : x ∈ V) (y) (_ : y ∈ V) (i), (F i x, F i y) ∈ U :=
  by
  constructor <;> intro H U hU
  · rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
    refine' ⟨_, H V hV, fun x hx y hy i => hVU (prod_mk_mem_compRel _ (hy i))⟩
    exact hVsymm.mk_mem_comm.mp (hx i)
  · rcases H U hU with ⟨V, hV, hVU⟩
    filter_upwards [hV]using fun x hx i => hVU x₀ (mem_of_mem_nhds hV) x hx i
#align equicontinuous_at_iff_pair equicontinuousAt_iff_pair

/- warning: uniform_equicontinuous.equicontinuous -> UniformEquicontinuous.equicontinuous is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {F : ι -> β -> α}, (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) -> (Equicontinuous.{u1, u3, u2} ι β α (UniformSpace.toTopologicalSpace.{u3} β _inst_5) _inst_4 F)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] {F : ι -> β -> α}, (UniformEquicontinuous.{u3, u2, u1} ι α β _inst_4 _inst_5 F) -> (Equicontinuous.{u3, u1, u2} ι β α (UniformSpace.toTopologicalSpace.{u1} β _inst_5) _inst_4 F)
Case conversion may be inaccurate. Consider using '#align uniform_equicontinuous.equicontinuous UniformEquicontinuous.equicontinuousₓ'. -/
/-- Uniform equicontinuity implies equicontinuity. -/
theorem UniformEquicontinuous.equicontinuous {F : ι → β → α} (h : UniformEquicontinuous F) :
    Equicontinuous F := fun x₀ U hU =>
  mem_of_superset (ball_mem_nhds x₀ (h U hU)) fun x hx i => hx i
#align uniform_equicontinuous.equicontinuous UniformEquicontinuous.equicontinuous

/- warning: equicontinuous_at.continuous_at -> EquicontinuousAt.continuousAt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {F : ι -> X -> α} {x₀ : X}, (EquicontinuousAt.{u1, u2, u3} ι X α _inst_1 _inst_4 F x₀) -> (forall (i : ι), ContinuousAt.{u2, u3} X α _inst_1 (UniformSpace.toTopologicalSpace.{u3} α _inst_4) (F i) x₀)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {F : ι -> X -> α} {x₀ : X}, (EquicontinuousAt.{u3, u2, u1} ι X α _inst_1 _inst_4 F x₀) -> (forall (i : ι), ContinuousAt.{u2, u1} X α _inst_1 (UniformSpace.toTopologicalSpace.{u1} α _inst_4) (F i) x₀)
Case conversion may be inaccurate. Consider using '#align equicontinuous_at.continuous_at EquicontinuousAt.continuousAtₓ'. -/
/-- Each function of a family equicontinuous at `x₀` is continuous at `x₀`. -/
theorem EquicontinuousAt.continuousAt {F : ι → X → α} {x₀ : X} (h : EquicontinuousAt F x₀) (i : ι) :
    ContinuousAt (F i) x₀ := by
  intro U hU
  rw [UniformSpace.mem_nhds_iff] at hU
  rcases hU with ⟨V, hV₁, hV₂⟩
  exact mem_map.mpr (mem_of_superset (h V hV₁) fun x hx => hV₂ (hx i))
#align equicontinuous_at.continuous_at EquicontinuousAt.continuousAt

/- warning: set.equicontinuous_at.continuous_at_of_mem -> Set.EquicontinuousAt.continuousAt_of_mem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : UniformSpace.{u2} α] {H : Set.{max u1 u2} (X -> α)} {x₀ : X}, (Set.EquicontinuousAt.{u1, u2} X α _inst_1 _inst_4 H x₀) -> (forall {f : X -> α}, (Membership.Mem.{max u1 u2, max u1 u2} (X -> α) (Set.{max u1 u2} (X -> α)) (Set.hasMem.{max u1 u2} (X -> α)) f H) -> (ContinuousAt.{u1, u2} X α _inst_1 (UniformSpace.toTopologicalSpace.{u2} α _inst_4) f x₀))
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {H : Set.{max u2 u1} (X -> α)} {x₀ : X}, (Set.EquicontinuousAt.{u2, u1} X α _inst_1 _inst_4 H x₀) -> (forall {f : X -> α}, (Membership.mem.{max u2 u1, max u2 u1} (X -> α) (Set.{max u2 u1} (X -> α)) (Set.instMembershipSet.{max u2 u1} (X -> α)) f H) -> (ContinuousAt.{u2, u1} X α _inst_1 (UniformSpace.toTopologicalSpace.{u1} α _inst_4) f x₀))
Case conversion may be inaccurate. Consider using '#align set.equicontinuous_at.continuous_at_of_mem Set.EquicontinuousAt.continuousAt_of_memₓ'. -/
protected theorem Set.EquicontinuousAt.continuousAt_of_mem {H : Set <| X → α} {x₀ : X}
    (h : H.EquicontinuousAt x₀) {f : X → α} (hf : f ∈ H) : ContinuousAt f x₀ :=
  h.ContinuousAt ⟨f, hf⟩
#align set.equicontinuous_at.continuous_at_of_mem Set.EquicontinuousAt.continuousAt_of_mem

/- warning: equicontinuous.continuous -> Equicontinuous.continuous is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {F : ι -> X -> α}, (Equicontinuous.{u1, u2, u3} ι X α _inst_1 _inst_4 F) -> (forall (i : ι), Continuous.{u2, u3} X α _inst_1 (UniformSpace.toTopologicalSpace.{u3} α _inst_4) (F i))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {F : ι -> X -> α}, (Equicontinuous.{u3, u2, u1} ι X α _inst_1 _inst_4 F) -> (forall (i : ι), Continuous.{u2, u1} X α _inst_1 (UniformSpace.toTopologicalSpace.{u1} α _inst_4) (F i))
Case conversion may be inaccurate. Consider using '#align equicontinuous.continuous Equicontinuous.continuousₓ'. -/
/-- Each function of an equicontinuous family is continuous. -/
theorem Equicontinuous.continuous {F : ι → X → α} (h : Equicontinuous F) (i : ι) :
    Continuous (F i) :=
  continuous_iff_continuousAt.mpr fun x => (h x).ContinuousAt i
#align equicontinuous.continuous Equicontinuous.continuous

/- warning: set.equicontinuous.continuous_of_mem -> Set.Equicontinuous.continuous_of_mem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : UniformSpace.{u2} α] {H : Set.{max u1 u2} (X -> α)}, (Set.Equicontinuous.{u1, u2} X α _inst_1 _inst_4 H) -> (forall {f : X -> α}, (Membership.Mem.{max u1 u2, max u1 u2} (X -> α) (Set.{max u1 u2} (X -> α)) (Set.hasMem.{max u1 u2} (X -> α)) f H) -> (Continuous.{u1, u2} X α _inst_1 (UniformSpace.toTopologicalSpace.{u2} α _inst_4) f))
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {H : Set.{max u2 u1} (X -> α)}, (Set.Equicontinuous.{u2, u1} X α _inst_1 _inst_4 H) -> (forall {f : X -> α}, (Membership.mem.{max u2 u1, max u2 u1} (X -> α) (Set.{max u2 u1} (X -> α)) (Set.instMembershipSet.{max u2 u1} (X -> α)) f H) -> (Continuous.{u2, u1} X α _inst_1 (UniformSpace.toTopologicalSpace.{u1} α _inst_4) f))
Case conversion may be inaccurate. Consider using '#align set.equicontinuous.continuous_of_mem Set.Equicontinuous.continuous_of_memₓ'. -/
protected theorem Set.Equicontinuous.continuous_of_mem {H : Set <| X → α} (h : H.Equicontinuous)
    {f : X → α} (hf : f ∈ H) : Continuous f :=
  h.Continuous ⟨f, hf⟩
#align set.equicontinuous.continuous_of_mem Set.Equicontinuous.continuous_of_mem

/- warning: uniform_equicontinuous.uniform_continuous -> UniformEquicontinuous.uniformContinuous is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {F : ι -> β -> α}, (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) -> (forall (i : ι), UniformContinuous.{u3, u2} β α _inst_5 _inst_4 (F i))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] {F : ι -> β -> α}, (UniformEquicontinuous.{u3, u2, u1} ι α β _inst_4 _inst_5 F) -> (forall (i : ι), UniformContinuous.{u1, u2} β α _inst_5 _inst_4 (F i))
Case conversion may be inaccurate. Consider using '#align uniform_equicontinuous.uniform_continuous UniformEquicontinuous.uniformContinuousₓ'. -/
/-- Each function of a uniformly equicontinuous family is uniformly continuous. -/
theorem UniformEquicontinuous.uniformContinuous {F : ι → β → α} (h : UniformEquicontinuous F)
    (i : ι) : UniformContinuous (F i) := fun U hU =>
  mem_map.mpr (mem_of_superset (h U hU) fun xy hxy => hxy i)
#align uniform_equicontinuous.uniform_continuous UniformEquicontinuous.uniformContinuous

/- warning: set.uniform_equicontinuous.uniform_continuous_of_mem -> Set.UniformEquicontinuous.uniformContinuous_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : UniformSpace.{u1} α] [_inst_5 : UniformSpace.{u2} β] {H : Set.{max u2 u1} (β -> α)}, (Set.UniformEquicontinuous.{u1, u2} α β _inst_4 _inst_5 H) -> (forall {f : β -> α}, (Membership.Mem.{max u2 u1, max u2 u1} (β -> α) (Set.{max u2 u1} (β -> α)) (Set.hasMem.{max u2 u1} (β -> α)) f H) -> (UniformContinuous.{u2, u1} β α _inst_5 _inst_4 f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] {H : Set.{max u2 u1} (β -> α)}, (Set.UniformEquicontinuous.{u2, u1} α β _inst_4 _inst_5 H) -> (forall {f : β -> α}, (Membership.mem.{max u2 u1, max u2 u1} (β -> α) (Set.{max u2 u1} (β -> α)) (Set.instMembershipSet.{max u2 u1} (β -> α)) f H) -> (UniformContinuous.{u1, u2} β α _inst_5 _inst_4 f))
Case conversion may be inaccurate. Consider using '#align set.uniform_equicontinuous.uniform_continuous_of_mem Set.UniformEquicontinuous.uniformContinuous_of_memₓ'. -/
protected theorem Set.UniformEquicontinuous.uniformContinuous_of_mem {H : Set <| β → α}
    (h : H.UniformEquicontinuous) {f : β → α} (hf : f ∈ H) : UniformContinuous f :=
  h.UniformContinuous ⟨f, hf⟩
#align set.uniform_equicontinuous.uniform_continuous_of_mem Set.UniformEquicontinuous.uniformContinuous_of_mem

/- warning: equicontinuous_at.comp -> EquicontinuousAt.comp is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {X : Type.{u3}} {α : Type.{u4}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_4 : UniformSpace.{u4} α] {F : ι -> X -> α} {x₀ : X}, (EquicontinuousAt.{u1, u3, u4} ι X α _inst_1 _inst_4 F x₀) -> (forall (u : κ -> ι), EquicontinuousAt.{u2, u3, u4} κ X α _inst_1 _inst_4 (Function.comp.{succ u2, succ u1, max (succ u3) (succ u4)} κ ι (X -> α) F u) x₀)
but is expected to have type
  forall {ι : Type.{u4}} {κ : Type.{u1}} {X : Type.{u3}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_4 : UniformSpace.{u2} α] {F : ι -> X -> α} {x₀ : X}, (EquicontinuousAt.{u4, u3, u2} ι X α _inst_1 _inst_4 F x₀) -> (forall (u : κ -> ι), EquicontinuousAt.{u1, u3, u2} κ X α _inst_1 _inst_4 (Function.comp.{succ u1, succ u4, max (succ u2) (succ u3)} κ ι (X -> α) F u) x₀)
Case conversion may be inaccurate. Consider using '#align equicontinuous_at.comp EquicontinuousAt.compₓ'. -/
/-- Taking sub-families preserves equicontinuity at a point. -/
theorem EquicontinuousAt.comp {F : ι → X → α} {x₀ : X} (h : EquicontinuousAt F x₀) (u : κ → ι) :
    EquicontinuousAt (F ∘ u) x₀ := fun U hU => (h U hU).mono fun x H k => H (u k)
#align equicontinuous_at.comp EquicontinuousAt.comp

/- warning: set.equicontinuous_at.mono -> Set.EquicontinuousAt.mono is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : UniformSpace.{u2} α] {H : Set.{max u1 u2} (X -> α)} {H' : Set.{max u1 u2} (X -> α)} {x₀ : X}, (Set.EquicontinuousAt.{u1, u2} X α _inst_1 _inst_4 H x₀) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (X -> α)) (Set.hasSubset.{max u1 u2} (X -> α)) H' H) -> (Set.EquicontinuousAt.{u1, u2} X α _inst_1 _inst_4 H' x₀)
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {H : Set.{max u2 u1} (X -> α)} {H' : Set.{max u2 u1} (X -> α)} {x₀ : X}, (Set.EquicontinuousAt.{u2, u1} X α _inst_1 _inst_4 H x₀) -> (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (X -> α)) (Set.instHasSubsetSet.{max u2 u1} (X -> α)) H' H) -> (Set.EquicontinuousAt.{u2, u1} X α _inst_1 _inst_4 H' x₀)
Case conversion may be inaccurate. Consider using '#align set.equicontinuous_at.mono Set.EquicontinuousAt.monoₓ'. -/
protected theorem Set.EquicontinuousAt.mono {H H' : Set <| X → α} {x₀ : X}
    (h : H.EquicontinuousAt x₀) (hH : H' ⊆ H) : H'.EquicontinuousAt x₀ :=
  h.comp (inclusion hH)
#align set.equicontinuous_at.mono Set.EquicontinuousAt.mono

/- warning: equicontinuous.comp -> Equicontinuous.comp is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {X : Type.{u3}} {α : Type.{u4}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_4 : UniformSpace.{u4} α] {F : ι -> X -> α}, (Equicontinuous.{u1, u3, u4} ι X α _inst_1 _inst_4 F) -> (forall (u : κ -> ι), Equicontinuous.{u2, u3, u4} κ X α _inst_1 _inst_4 (Function.comp.{succ u2, succ u1, max (succ u3) (succ u4)} κ ι (X -> α) F u))
but is expected to have type
  forall {ι : Type.{u4}} {κ : Type.{u1}} {X : Type.{u3}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_4 : UniformSpace.{u2} α] {F : ι -> X -> α}, (Equicontinuous.{u4, u3, u2} ι X α _inst_1 _inst_4 F) -> (forall (u : κ -> ι), Equicontinuous.{u1, u3, u2} κ X α _inst_1 _inst_4 (Function.comp.{succ u1, succ u4, max (succ u2) (succ u3)} κ ι (X -> α) F u))
Case conversion may be inaccurate. Consider using '#align equicontinuous.comp Equicontinuous.compₓ'. -/
/-- Taking sub-families preserves equicontinuity. -/
theorem Equicontinuous.comp {F : ι → X → α} (h : Equicontinuous F) (u : κ → ι) :
    Equicontinuous (F ∘ u) := fun x => (h x).comp u
#align equicontinuous.comp Equicontinuous.comp

/- warning: set.equicontinuous.mono -> Set.Equicontinuous.mono is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : UniformSpace.{u2} α] {H : Set.{max u1 u2} (X -> α)} {H' : Set.{max u1 u2} (X -> α)}, (Set.Equicontinuous.{u1, u2} X α _inst_1 _inst_4 H) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (X -> α)) (Set.hasSubset.{max u1 u2} (X -> α)) H' H) -> (Set.Equicontinuous.{u1, u2} X α _inst_1 _inst_4 H')
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {H : Set.{max u2 u1} (X -> α)} {H' : Set.{max u2 u1} (X -> α)}, (Set.Equicontinuous.{u2, u1} X α _inst_1 _inst_4 H) -> (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (X -> α)) (Set.instHasSubsetSet.{max u2 u1} (X -> α)) H' H) -> (Set.Equicontinuous.{u2, u1} X α _inst_1 _inst_4 H')
Case conversion may be inaccurate. Consider using '#align set.equicontinuous.mono Set.Equicontinuous.monoₓ'. -/
protected theorem Set.Equicontinuous.mono {H H' : Set <| X → α} (h : H.Equicontinuous)
    (hH : H' ⊆ H) : H'.Equicontinuous :=
  h.comp (inclusion hH)
#align set.equicontinuous.mono Set.Equicontinuous.mono

/- warning: uniform_equicontinuous.comp -> UniformEquicontinuous.comp is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_4 : UniformSpace.{u3} α] [_inst_5 : UniformSpace.{u4} β] {F : ι -> β -> α}, (UniformEquicontinuous.{u1, u3, u4} ι α β _inst_4 _inst_5 F) -> (forall (u : κ -> ι), UniformEquicontinuous.{u2, u3, u4} κ α β _inst_4 _inst_5 (Function.comp.{succ u2, succ u1, max (succ u4) (succ u3)} κ ι (β -> α) F u))
but is expected to have type
  forall {ι : Type.{u4}} {κ : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_4 : UniformSpace.{u3} α] [_inst_5 : UniformSpace.{u2} β] {F : ι -> β -> α}, (UniformEquicontinuous.{u4, u3, u2} ι α β _inst_4 _inst_5 F) -> (forall (u : κ -> ι), UniformEquicontinuous.{u1, u3, u2} κ α β _inst_4 _inst_5 (Function.comp.{succ u1, succ u4, max (succ u2) (succ u3)} κ ι (β -> α) F u))
Case conversion may be inaccurate. Consider using '#align uniform_equicontinuous.comp UniformEquicontinuous.compₓ'. -/
/-- Taking sub-families preserves uniform equicontinuity. -/
theorem UniformEquicontinuous.comp {F : ι → β → α} (h : UniformEquicontinuous F) (u : κ → ι) :
    UniformEquicontinuous (F ∘ u) := fun U hU => (h U hU).mono fun x H k => H (u k)
#align uniform_equicontinuous.comp UniformEquicontinuous.comp

/- warning: set.uniform_equicontinuous.mono -> Set.UniformEquicontinuous.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : UniformSpace.{u1} α] [_inst_5 : UniformSpace.{u2} β] {H : Set.{max u2 u1} (β -> α)} {H' : Set.{max u2 u1} (β -> α)}, (Set.UniformEquicontinuous.{u1, u2} α β _inst_4 _inst_5 H) -> (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (β -> α)) (Set.hasSubset.{max u2 u1} (β -> α)) H' H) -> (Set.UniformEquicontinuous.{u1, u2} α β _inst_4 _inst_5 H')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] {H : Set.{max u2 u1} (β -> α)} {H' : Set.{max u2 u1} (β -> α)}, (Set.UniformEquicontinuous.{u2, u1} α β _inst_4 _inst_5 H) -> (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (β -> α)) (Set.instHasSubsetSet.{max u2 u1} (β -> α)) H' H) -> (Set.UniformEquicontinuous.{u2, u1} α β _inst_4 _inst_5 H')
Case conversion may be inaccurate. Consider using '#align set.uniform_equicontinuous.mono Set.UniformEquicontinuous.monoₓ'. -/
protected theorem Set.UniformEquicontinuous.mono {H H' : Set <| β → α} (h : H.UniformEquicontinuous)
    (hH : H' ⊆ H) : H'.UniformEquicontinuous :=
  h.comp (inclusion hH)
#align set.uniform_equicontinuous.mono Set.UniformEquicontinuous.mono

/- warning: equicontinuous_at_iff_range -> equicontinuousAt_iff_range is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {F : ι -> X -> α} {x₀ : X}, Iff (EquicontinuousAt.{u1, u2, u3} ι X α _inst_1 _inst_4 F x₀) (EquicontinuousAt.{max u2 u3, u2, u3} (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) X α _inst_1 _inst_4 ((fun (a : Type.{max u2 u3}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{succ (max u2 u3), max (succ u2) (succ u3)} a b] => self.0) (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) (X -> α) (HasLiftT.mk.{succ (max u2 u3), max (succ u2) (succ u3)} (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) (X -> α) (CoeTCₓ.coe.{succ (max u2 u3), max (succ u2) (succ u3)} (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) (X -> α) (coeBase.{succ (max u2 u3), max (succ u2) (succ u3)} (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) (X -> α) (coeSubtype.{max (succ u2) (succ u3)} (X -> α) (fun (x : X -> α) => Membership.Mem.{max u2 u3, max u2 u3} (X -> α) (Set.{max u2 u3} (X -> α)) (Set.hasMem.{max u2 u3} (X -> α)) x (Set.range.{max u2 u3, succ u1} (X -> α) ι F))))))) x₀)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {F : ι -> X -> α} {x₀ : X}, Iff (EquicontinuousAt.{u3, u2, u1} ι X α _inst_1 _inst_4 F x₀) (EquicontinuousAt.{max u2 u1, u2, u1} (Subtype.{succ (max u2 u1)} (X -> α) (fun (x : X -> α) => Membership.mem.{max u2 u1, max u2 u1} (X -> α) (Set.{max u2 u1} (X -> α)) (Set.instMembershipSet.{max u2 u1} (X -> α)) x (Set.range.{max u2 u1, succ u3} (X -> α) ι F))) X α _inst_1 _inst_4 (Subtype.val.{succ (max u2 u1)} (X -> α) (fun (x : X -> α) => Membership.mem.{max u2 u1, max u2 u1} (X -> α) (Set.{max u2 u1} (X -> α)) (Set.instMembershipSet.{max u2 u1} (X -> α)) x (Set.range.{max u2 u1, succ u3} (X -> α) ι F))) x₀)
Case conversion may be inaccurate. Consider using '#align equicontinuous_at_iff_range equicontinuousAt_iff_rangeₓ'. -/
/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff `range 𝓕` is equicontinuous at `x₀`,
i.e the family `coe : range F → X → α` is equicontinuous at `x₀`. -/
theorem equicontinuousAt_iff_range {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ EquicontinuousAt (coe : range F → X → α) x₀ :=
  ⟨fun h => by rw [← comp_range_splitting F] <;> exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩
#align equicontinuous_at_iff_range equicontinuousAt_iff_range

/- warning: equicontinuous_iff_range -> equicontinuous_iff_range is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {F : ι -> X -> α}, Iff (Equicontinuous.{u1, u2, u3} ι X α _inst_1 _inst_4 F) (Equicontinuous.{max u2 u3, u2, u3} (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) X α _inst_1 _inst_4 ((fun (a : Type.{max u2 u3}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{succ (max u2 u3), max (succ u2) (succ u3)} a b] => self.0) (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) (X -> α) (HasLiftT.mk.{succ (max u2 u3), max (succ u2) (succ u3)} (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) (X -> α) (CoeTCₓ.coe.{succ (max u2 u3), max (succ u2) (succ u3)} (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) (X -> α) (coeBase.{succ (max u2 u3), max (succ u2) (succ u3)} (coeSort.{succ (max u2 u3), succ (succ (max u2 u3))} (Set.{max u2 u3} (X -> α)) Type.{max u2 u3} (Set.hasCoeToSort.{max u2 u3} (X -> α)) (Set.range.{max u2 u3, succ u1} (X -> α) ι F)) (X -> α) (coeSubtype.{max (succ u2) (succ u3)} (X -> α) (fun (x : X -> α) => Membership.Mem.{max u2 u3, max u2 u3} (X -> α) (Set.{max u2 u3} (X -> α)) (Set.hasMem.{max u2 u3} (X -> α)) x (Set.range.{max u2 u3, succ u1} (X -> α) ι F))))))))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {F : ι -> X -> α}, Iff (Equicontinuous.{u3, u2, u1} ι X α _inst_1 _inst_4 F) (Equicontinuous.{max u2 u1, u2, u1} (Subtype.{succ (max u2 u1)} (X -> α) (fun (x : X -> α) => Membership.mem.{max u2 u1, max u2 u1} (X -> α) (Set.{max u2 u1} (X -> α)) (Set.instMembershipSet.{max u2 u1} (X -> α)) x (Set.range.{max u2 u1, succ u3} (X -> α) ι F))) X α _inst_1 _inst_4 (Subtype.val.{succ (max u2 u1)} (X -> α) (fun (x : X -> α) => Membership.mem.{max u2 u1, max u2 u1} (X -> α) (Set.{max u2 u1} (X -> α)) (Set.instMembershipSet.{max u2 u1} (X -> α)) x (Set.range.{max u2 u1, succ u3} (X -> α) ι F))))
Case conversion may be inaccurate. Consider using '#align equicontinuous_iff_range equicontinuous_iff_rangeₓ'. -/
/-- A family `𝓕 : ι → X → α` is equicontinuous iff `range 𝓕` is equicontinuous,
i.e the family `coe : range F → X → α` is equicontinuous. -/
theorem equicontinuous_iff_range {F : ι → X → α} :
    Equicontinuous F ↔ Equicontinuous (coe : range F → X → α) :=
  forall_congr' fun x₀ => equicontinuousAt_iff_range
#align equicontinuous_iff_range equicontinuous_iff_range

/- warning: uniform_equicontinuous_at_iff_range -> uniformEquicontinuous_at_iff_range is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {F : ι -> β -> α}, Iff (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) (UniformEquicontinuous.{max u3 u2, u2, u3} (coeSort.{succ (max u3 u2), succ (succ (max u3 u2))} (Set.{max u3 u2} (β -> α)) Type.{max u3 u2} (Set.hasCoeToSort.{max u3 u2} (β -> α)) (Set.range.{max u3 u2, succ u1} (β -> α) ι F)) α β _inst_4 _inst_5 ((fun (a : Type.{max u3 u2}) (b : Sort.{max (succ u3) (succ u2)}) [self : HasLiftT.{succ (max u3 u2), max (succ u3) (succ u2)} a b] => self.0) (coeSort.{succ (max u3 u2), succ (succ (max u3 u2))} (Set.{max u3 u2} (β -> α)) Type.{max u3 u2} (Set.hasCoeToSort.{max u3 u2} (β -> α)) (Set.range.{max u3 u2, succ u1} (β -> α) ι F)) (β -> α) (HasLiftT.mk.{succ (max u3 u2), max (succ u3) (succ u2)} (coeSort.{succ (max u3 u2), succ (succ (max u3 u2))} (Set.{max u3 u2} (β -> α)) Type.{max u3 u2} (Set.hasCoeToSort.{max u3 u2} (β -> α)) (Set.range.{max u3 u2, succ u1} (β -> α) ι F)) (β -> α) (CoeTCₓ.coe.{succ (max u3 u2), max (succ u3) (succ u2)} (coeSort.{succ (max u3 u2), succ (succ (max u3 u2))} (Set.{max u3 u2} (β -> α)) Type.{max u3 u2} (Set.hasCoeToSort.{max u3 u2} (β -> α)) (Set.range.{max u3 u2, succ u1} (β -> α) ι F)) (β -> α) (coeBase.{succ (max u3 u2), max (succ u3) (succ u2)} (coeSort.{succ (max u3 u2), succ (succ (max u3 u2))} (Set.{max u3 u2} (β -> α)) Type.{max u3 u2} (Set.hasCoeToSort.{max u3 u2} (β -> α)) (Set.range.{max u3 u2, succ u1} (β -> α) ι F)) (β -> α) (coeSubtype.{max (succ u3) (succ u2)} (β -> α) (fun (x : β -> α) => Membership.Mem.{max u3 u2, max u3 u2} (β -> α) (Set.{max u3 u2} (β -> α)) (Set.hasMem.{max u3 u2} (β -> α)) x (Set.range.{max u3 u2, succ u1} (β -> α) ι F))))))))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] {F : ι -> β -> α}, Iff (UniformEquicontinuous.{u3, u2, u1} ι α β _inst_4 _inst_5 F) (UniformEquicontinuous.{max u2 u1, u2, u1} (Subtype.{succ (max u2 u1)} (β -> α) (fun (x : β -> α) => Membership.mem.{max u2 u1, max u2 u1} (β -> α) (Set.{max u2 u1} (β -> α)) (Set.instMembershipSet.{max u2 u1} (β -> α)) x (Set.range.{max u2 u1, succ u3} (β -> α) ι F))) α β _inst_4 _inst_5 (Subtype.val.{succ (max u2 u1)} (β -> α) (fun (x : β -> α) => Membership.mem.{max u2 u1, max u2 u1} (β -> α) (Set.{max u2 u1} (β -> α)) (Set.instMembershipSet.{max u2 u1} (β -> α)) x (Set.range.{max u2 u1, succ u3} (β -> α) ι F))))
Case conversion may be inaccurate. Consider using '#align uniform_equicontinuous_at_iff_range uniformEquicontinuous_at_iff_rangeₓ'. -/
/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous iff `range 𝓕` is uniformly equicontinuous,
i.e the family `coe : range F → β → α` is uniformly equicontinuous. -/
theorem uniformEquicontinuous_at_iff_range {F : ι → β → α} :
    UniformEquicontinuous F ↔ UniformEquicontinuous (coe : range F → β → α) :=
  ⟨fun h => by rw [← comp_range_splitting F] <;> exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩
#align uniform_equicontinuous_at_iff_range uniformEquicontinuous_at_iff_range

section

open UniformFun

/- warning: equicontinuous_at_iff_continuous_at -> equicontinuousAt_iff_continuousAt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {F : ι -> X -> α} {x₀ : X}, Iff (EquicontinuousAt.{u1, u2, u3} ι X α _inst_1 _inst_4 F x₀) (ContinuousAt.{u2, max u1 u3} X (UniformFun.{u1, u3} ι α) _inst_1 (UniformFun.topologicalSpace.{u1, u3} ι α _inst_4) (Function.comp.{succ u2, max (succ u1) (succ u3), max (succ u1) (succ u3)} X (ι -> α) (UniformFun.{u1, u3} ι α) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u1, u3} ι α)) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u1, u3} ι α)) => (ι -> α) -> (UniformFun.{u1, u3} ι α)) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u1, u3} ι α)) (UniformFun.ofFun.{u1, u3} ι α)) (Function.swap.{succ u1, succ u2, succ u3} ι X (fun (ᾰ : ι) (ᾰ : X) => α) F)) x₀)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {F : ι -> X -> α} {x₀ : X}, Iff (EquicontinuousAt.{u3, u2, u1} ι X α _inst_1 _inst_4 F x₀) (ContinuousAt.{u2, max u3 u1} X (UniformFun.{u3, u1} ι α) _inst_1 (UniformFun.topologicalSpace.{u3, u1} ι α _inst_4) (Function.comp.{succ u2, max (succ u1) (succ u3), max (succ u3) (succ u1)} X (ι -> α) (UniformFun.{u3, u1} ι α) (FunLike.coe.{max (succ u1) (succ u3), max (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u3, u1} ι α)) (ι -> α) (fun (_x : ι -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : ι -> α) => UniformFun.{u3, u1} ι α) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u3, u1} ι α)) (UniformFun.ofFun.{u3, u1} ι α)) (Function.swap.{succ u3, succ u2, succ u1} ι X (fun (ᾰ : ι) (ᾰ : X) => α) F)) x₀)
Case conversion may be inaccurate. Consider using '#align equicontinuous_at_iff_continuous_at equicontinuousAt_iff_continuousAtₓ'. -/
/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff the function `swap 𝓕 : X → ι → α` is
continuous at `x₀` *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developping the equicontinuity API, but it should not be used directly for other
purposes. -/
theorem equicontinuousAt_iff_continuousAt {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function.swap F : X → ι →ᵤ α) x₀ := by
  rw [ContinuousAt, (UniformFun.hasBasis_nhds ι α _).tendsto_right_iff] <;> rfl
#align equicontinuous_at_iff_continuous_at equicontinuousAt_iff_continuousAt

/- warning: equicontinuous_iff_continuous -> equicontinuous_iff_continuous is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {F : ι -> X -> α}, Iff (Equicontinuous.{u1, u2, u3} ι X α _inst_1 _inst_4 F) (Continuous.{u2, max u1 u3} X (UniformFun.{u1, u3} ι α) _inst_1 (UniformFun.topologicalSpace.{u1, u3} ι α _inst_4) (Function.comp.{succ u2, max (succ u1) (succ u3), max (succ u1) (succ u3)} X (ι -> α) (UniformFun.{u1, u3} ι α) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u1, u3} ι α)) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u1, u3} ι α)) => (ι -> α) -> (UniformFun.{u1, u3} ι α)) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u1, u3} ι α)) (UniformFun.ofFun.{u1, u3} ι α)) (Function.swap.{succ u1, succ u2, succ u3} ι X (fun (ᾰ : ι) (ᾰ : X) => α) F)))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {F : ι -> X -> α}, Iff (Equicontinuous.{u3, u2, u1} ι X α _inst_1 _inst_4 F) (Continuous.{u2, max u3 u1} X (UniformFun.{u3, u1} ι α) _inst_1 (UniformFun.topologicalSpace.{u3, u1} ι α _inst_4) (Function.comp.{succ u2, max (succ u1) (succ u3), max (succ u3) (succ u1)} X (ι -> α) (UniformFun.{u3, u1} ι α) (FunLike.coe.{max (succ u1) (succ u3), max (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u3, u1} ι α)) (ι -> α) (fun (_x : ι -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : ι -> α) => UniformFun.{u3, u1} ι α) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ι -> α) (UniformFun.{u3, u1} ι α)) (UniformFun.ofFun.{u3, u1} ι α)) (Function.swap.{succ u3, succ u2, succ u1} ι X (fun (ᾰ : ι) (ᾰ : X) => α) F)))
Case conversion may be inaccurate. Consider using '#align equicontinuous_iff_continuous equicontinuous_iff_continuousₓ'. -/
/-- A family `𝓕 : ι → X → α` is equicontinuous iff the function `swap 𝓕 : X → ι → α` is
continuous *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developping the equicontinuity API, but it should not be used directly for other
purposes. -/
theorem equicontinuous_iff_continuous {F : ι → X → α} :
    Equicontinuous F ↔ Continuous (ofFun ∘ Function.swap F : X → ι →ᵤ α) := by
  simp_rw [Equicontinuous, continuous_iff_continuousAt, equicontinuousAt_iff_continuousAt]
#align equicontinuous_iff_continuous equicontinuous_iff_continuous

/- warning: uniform_equicontinuous_iff_uniform_continuous -> uniformEquicontinuous_iff_uniformContinuous is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {F : ι -> β -> α}, Iff (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) (UniformContinuous.{u3, max u1 u2} β (UniformFun.{u1, u2} ι α) _inst_5 (UniformFun.uniformSpace.{u1, u2} ι α _inst_4) (Function.comp.{succ u3, max (succ u1) (succ u2), max (succ u1) (succ u2)} β (ι -> α) (UniformFun.{u1, u2} ι α) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ι -> α) (UniformFun.{u1, u2} ι α)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ι -> α) (UniformFun.{u1, u2} ι α)) => (ι -> α) -> (UniformFun.{u1, u2} ι α)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ι -> α) (UniformFun.{u1, u2} ι α)) (UniformFun.ofFun.{u1, u2} ι α)) (Function.swap.{succ u1, succ u3, succ u2} ι β (fun (ᾰ : ι) (ᾰ : β) => α) F)))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] {F : ι -> β -> α}, Iff (UniformEquicontinuous.{u3, u2, u1} ι α β _inst_4 _inst_5 F) (UniformContinuous.{u1, max u3 u2} β (UniformFun.{u3, u2} ι α) _inst_5 (UniformFun.uniformSpace.{u3, u2} ι α _inst_4) (Function.comp.{succ u1, max (succ u2) (succ u3), max (succ u3) (succ u2)} β (ι -> α) (UniformFun.{u3, u2} ι α) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (ι -> α) (UniformFun.{u3, u2} ι α)) (ι -> α) (fun (_x : ι -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : ι -> α) => UniformFun.{u3, u2} ι α) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ι -> α) (UniformFun.{u3, u2} ι α)) (UniformFun.ofFun.{u3, u2} ι α)) (Function.swap.{succ u3, succ u1, succ u2} ι β (fun (ᾰ : ι) (ᾰ : β) => α) F)))
Case conversion may be inaccurate. Consider using '#align uniform_equicontinuous_iff_uniform_continuous uniformEquicontinuous_iff_uniformContinuousₓ'. -/
/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous iff the function `swap 𝓕 : β → ι → α` is
uniformly continuous *when `ι → α` is equipped with the uniform structure of uniform convergence*.
This is very useful for developping the equicontinuity API, but it should not be used directly
for other purposes. -/
theorem uniformEquicontinuous_iff_uniformContinuous {F : ι → β → α} :
    UniformEquicontinuous F ↔ UniformContinuous (ofFun ∘ Function.swap F : β → ι →ᵤ α) := by
  rw [UniformContinuous, (UniformFun.hasBasis_uniformity ι α).tendsto_right_iff] <;> rfl
#align uniform_equicontinuous_iff_uniform_continuous uniformEquicontinuous_iff_uniformContinuous

/- warning: filter.has_basis.equicontinuous_at_iff_left -> Filter.HasBasis.equicontinuousAt_iff_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {κ : Type.{u4}} {p : κ -> Prop} {s : κ -> (Set.{u2} X)} {F : ι -> X -> α} {x₀ : X}, (Filter.HasBasis.{u2, succ u4} X κ (nhds.{u2} X _inst_1 x₀) p s) -> (Iff (EquicontinuousAt.{u1, u2, u3} ι X α _inst_1 _inst_4 F x₀) (forall (U : Set.{u3} (Prod.{u3, u3} α α)), (Membership.Mem.{u3, u3} (Set.{u3} (Prod.{u3, u3} α α)) (Filter.{u3} (Prod.{u3, u3} α α)) (Filter.hasMem.{u3} (Prod.{u3, u3} α α)) U (uniformity.{u3} α _inst_4)) -> (Exists.{succ u4} κ (fun (k : κ) => Exists.{0} (p k) (fun (_x : p k) => forall (x : X), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (s k)) -> (forall (i : ι), Membership.Mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.hasMem.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α (F i x₀) (F i x)) U))))))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u3}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_4 : UniformSpace.{u1} α] {κ : Type.{u4}} {p : κ -> Prop} {s : κ -> (Set.{u3} X)} {F : ι -> X -> α} {x₀ : X}, (Filter.HasBasis.{u3, succ u4} X κ (nhds.{u3} X _inst_1 x₀) p s) -> (Iff (EquicontinuousAt.{u2, u3, u1} ι X α _inst_1 _inst_4 F x₀) (forall (U : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) U (uniformity.{u1} α _inst_4)) -> (Exists.{succ u4} κ (fun (k : κ) => And (p k) (forall (x : X), (Membership.mem.{u3, u3} X (Set.{u3} X) (Set.instMembershipSet.{u3} X) x (s k)) -> (forall (i : ι), Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (F i x₀) (F i x)) U))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.equicontinuous_at_iff_left Filter.HasBasis.equicontinuousAt_iff_leftₓ'. -/
theorem Filter.HasBasis.equicontinuousAt_iff_left {κ : Type _} {p : κ → Prop} {s : κ → Set X}
    {F : ι → X → α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p s) :
    EquicontinuousAt F x₀ ↔ ∀ U ∈ 𝓤 α, ∃ (k : _)(_ : p k), ∀ x ∈ s k, ∀ i, (F i x₀, F i x) ∈ U :=
  by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl
#align filter.has_basis.equicontinuous_at_iff_left Filter.HasBasis.equicontinuousAt_iff_left

/- warning: filter.has_basis.equicontinuous_at_iff_right -> Filter.HasBasis.equicontinuousAt_iff_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {κ : Type.{u4}} {p : κ -> Prop} {s : κ -> (Set.{u3} (Prod.{u3, u3} α α))} {F : ι -> X -> α} {x₀ : X}, (Filter.HasBasis.{u3, succ u4} (Prod.{u3, u3} α α) κ (uniformity.{u3} α _inst_4) p s) -> (Iff (EquicontinuousAt.{u1, u2, u3} ι X α _inst_1 _inst_4 F x₀) (forall (k : κ), (p k) -> (Filter.Eventually.{u2} X (fun (x : X) => forall (i : ι), Membership.Mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.hasMem.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α (F i x₀) (F i x)) (s k)) (nhds.{u2} X _inst_1 x₀))))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : UniformSpace.{u3} α] {κ : Type.{u4}} {p : κ -> Prop} {s : κ -> (Set.{u3} (Prod.{u3, u3} α α))} {F : ι -> X -> α} {x₀ : X}, (Filter.HasBasis.{u3, succ u4} (Prod.{u3, u3} α α) κ (uniformity.{u3} α _inst_4) p s) -> (Iff (EquicontinuousAt.{u2, u1, u3} ι X α _inst_1 _inst_4 F x₀) (forall (k : κ), (p k) -> (Filter.Eventually.{u1} X (fun (x : X) => forall (i : ι), Membership.mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.instMembershipSet.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α (F i x₀) (F i x)) (s k)) (nhds.{u1} X _inst_1 x₀))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.equicontinuous_at_iff_right Filter.HasBasis.equicontinuousAt_iff_rightₓ'. -/
theorem Filter.HasBasis.equicontinuousAt_iff_right {κ : Type _} {p : κ → Prop} {s : κ → Set (α × α)}
    {F : ι → X → α} {x₀ : X} (hα : (𝓤 α).HasBasis p s) :
    EquicontinuousAt F x₀ ↔ ∀ k, p k → ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ s k :=
  by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    (UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl
#align filter.has_basis.equicontinuous_at_iff_right Filter.HasBasis.equicontinuousAt_iff_right

/- warning: filter.has_basis.equicontinuous_at_iff -> Filter.HasBasis.equicontinuousAt_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {κ₁ : Type.{u4}} {κ₂ : Type.{u5}} {p₁ : κ₁ -> Prop} {s₁ : κ₁ -> (Set.{u2} X)} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> (Set.{u3} (Prod.{u3, u3} α α))} {F : ι -> X -> α} {x₀ : X}, (Filter.HasBasis.{u2, succ u4} X κ₁ (nhds.{u2} X _inst_1 x₀) p₁ s₁) -> (Filter.HasBasis.{u3, succ u5} (Prod.{u3, u3} α α) κ₂ (uniformity.{u3} α _inst_4) p₂ s₂) -> (Iff (EquicontinuousAt.{u1, u2, u3} ι X α _inst_1 _inst_4 F x₀) (forall (k₂ : κ₂), (p₂ k₂) -> (Exists.{succ u4} κ₁ (fun (k₁ : κ₁) => Exists.{0} (p₁ k₁) (fun (_x : p₁ k₁) => forall (x : X), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (s₁ k₁)) -> (forall (i : ι), Membership.Mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.hasMem.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α (F i x₀) (F i x)) (s₂ k₂)))))))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u3}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_4 : UniformSpace.{u2} α] {κ₁ : Type.{u5}} {κ₂ : Type.{u4}} {p₁ : κ₁ -> Prop} {s₁ : κ₁ -> (Set.{u3} X)} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> (Set.{u2} (Prod.{u2, u2} α α))} {F : ι -> X -> α} {x₀ : X}, (Filter.HasBasis.{u3, succ u5} X κ₁ (nhds.{u3} X _inst_1 x₀) p₁ s₁) -> (Filter.HasBasis.{u2, succ u4} (Prod.{u2, u2} α α) κ₂ (uniformity.{u2} α _inst_4) p₂ s₂) -> (Iff (EquicontinuousAt.{u1, u3, u2} ι X α _inst_1 _inst_4 F x₀) (forall (k₂ : κ₂), (p₂ k₂) -> (Exists.{succ u5} κ₁ (fun (k₁ : κ₁) => And (p₁ k₁) (forall (x : X), (Membership.mem.{u3, u3} X (Set.{u3} X) (Set.instMembershipSet.{u3} X) x (s₁ k₁)) -> (forall (i : ι), Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α (F i x₀) (F i x)) (s₂ k₂)))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.equicontinuous_at_iff Filter.HasBasis.equicontinuousAt_iffₓ'. -/
theorem Filter.HasBasis.equicontinuousAt_iff {κ₁ κ₂ : Type _} {p₁ : κ₁ → Prop} {s₁ : κ₁ → Set X}
    {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → X → α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p₁ s₁)
    (hα : (𝓤 α).HasBasis p₂ s₂) :
    EquicontinuousAt F x₀ ↔
      ∀ k₂, p₂ k₂ → ∃ (k₁ : _)(_ : p₁ k₁), ∀ x ∈ s₁ k₁, ∀ i, (F i x₀, F i x) ∈ s₂ k₂ :=
  by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl
#align filter.has_basis.equicontinuous_at_iff Filter.HasBasis.equicontinuousAt_iff

/- warning: filter.has_basis.uniform_equicontinuous_iff_left -> Filter.HasBasis.uniformEquicontinuous_iff_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {κ : Type.{u4}} {p : κ -> Prop} {s : κ -> (Set.{u3} (Prod.{u3, u3} β β))} {F : ι -> β -> α}, (Filter.HasBasis.{u3, succ u4} (Prod.{u3, u3} β β) κ (uniformity.{u3} β _inst_5) p s) -> (Iff (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) (forall (U : Set.{u2} (Prod.{u2, u2} α α)), (Membership.Mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} α α)) (Filter.{u2} (Prod.{u2, u2} α α)) (Filter.hasMem.{u2} (Prod.{u2, u2} α α)) U (uniformity.{u2} α _inst_4)) -> (Exists.{succ u4} κ (fun (k : κ) => Exists.{0} (p k) (fun (_x : p k) => forall (x : β) (y : β), (Membership.Mem.{u3, u3} (Prod.{u3, u3} β β) (Set.{u3} (Prod.{u3, u3} β β)) (Set.hasMem.{u3} (Prod.{u3, u3} β β)) (Prod.mk.{u3, u3} β β x y) (s k)) -> (forall (i : ι), Membership.Mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.hasMem.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α (F i x) (F i y)) U))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u1} α] [_inst_5 : UniformSpace.{u3} β] {κ : Type.{u4}} {p : κ -> Prop} {s : κ -> (Set.{u3} (Prod.{u3, u3} β β))} {F : ι -> β -> α}, (Filter.HasBasis.{u3, succ u4} (Prod.{u3, u3} β β) κ (uniformity.{u3} β _inst_5) p s) -> (Iff (UniformEquicontinuous.{u2, u1, u3} ι α β _inst_4 _inst_5 F) (forall (U : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) U (uniformity.{u1} α _inst_4)) -> (Exists.{succ u4} κ (fun (k : κ) => And (p k) (forall (x : β) (y : β), (Membership.mem.{u3, u3} (Prod.{u3, u3} β β) (Set.{u3} (Prod.{u3, u3} β β)) (Set.instMembershipSet.{u3} (Prod.{u3, u3} β β)) (Prod.mk.{u3, u3} β β x y) (s k)) -> (forall (i : ι), Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (F i x) (F i y)) U))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniform_equicontinuous_iff_left Filter.HasBasis.uniformEquicontinuous_iff_leftₓ'. -/
theorem Filter.HasBasis.uniformEquicontinuous_iff_left {κ : Type _} {p : κ → Prop}
    {s : κ → Set (β × β)} {F : ι → β → α} (hβ : (𝓤 β).HasBasis p s) :
    UniformEquicontinuous F ↔
      ∀ U ∈ 𝓤 α, ∃ (k : _)(_ : p k), ∀ x y, (x, y) ∈ s k → ∀ i, (F i x, F i y) ∈ U :=
  by
  rw [uniformEquicontinuous_iff_uniformContinuous, UniformContinuous,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp_rw [Prod.forall]
  rfl
#align filter.has_basis.uniform_equicontinuous_iff_left Filter.HasBasis.uniformEquicontinuous_iff_left

/- warning: filter.has_basis.uniform_equicontinuous_iff_right -> Filter.HasBasis.uniformEquicontinuous_iff_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {κ : Type.{u4}} {p : κ -> Prop} {s : κ -> (Set.{u2} (Prod.{u2, u2} α α))} {F : ι -> β -> α}, (Filter.HasBasis.{u2, succ u4} (Prod.{u2, u2} α α) κ (uniformity.{u2} α _inst_4) p s) -> (Iff (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) (forall (k : κ), (p k) -> (Filter.Eventually.{u3} (Prod.{u3, u3} β β) (fun (xy : Prod.{u3, u3} β β) => forall (i : ι), Membership.Mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.hasMem.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α (F i (Prod.fst.{u3, u3} β β xy)) (F i (Prod.snd.{u3, u3} β β xy))) (s k)) (uniformity.{u3} β _inst_5))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u3}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u3} α] [_inst_5 : UniformSpace.{u1} β] {κ : Type.{u4}} {p : κ -> Prop} {s : κ -> (Set.{u3} (Prod.{u3, u3} α α))} {F : ι -> β -> α}, (Filter.HasBasis.{u3, succ u4} (Prod.{u3, u3} α α) κ (uniformity.{u3} α _inst_4) p s) -> (Iff (UniformEquicontinuous.{u2, u3, u1} ι α β _inst_4 _inst_5 F) (forall (k : κ), (p k) -> (Filter.Eventually.{u1} (Prod.{u1, u1} β β) (fun (xy : Prod.{u1, u1} β β) => forall (i : ι), Membership.mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.instMembershipSet.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α (F i (Prod.fst.{u1, u1} β β xy)) (F i (Prod.snd.{u1, u1} β β xy))) (s k)) (uniformity.{u1} β _inst_5))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniform_equicontinuous_iff_right Filter.HasBasis.uniformEquicontinuous_iff_rightₓ'. -/
theorem Filter.HasBasis.uniformEquicontinuous_iff_right {κ : Type _} {p : κ → Prop}
    {s : κ → Set (α × α)} {F : ι → β → α} (hα : (𝓤 α).HasBasis p s) :
    UniformEquicontinuous F ↔ ∀ k, p k → ∀ᶠ xy : β × β in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ s k :=
  by
  rw [uniformEquicontinuous_iff_uniformContinuous, UniformContinuous,
    (UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl
#align filter.has_basis.uniform_equicontinuous_iff_right Filter.HasBasis.uniformEquicontinuous_iff_right

/- warning: filter.has_basis.uniform_equicontinuous_iff -> Filter.HasBasis.uniformEquicontinuous_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {κ₁ : Type.{u4}} {κ₂ : Type.{u5}} {p₁ : κ₁ -> Prop} {s₁ : κ₁ -> (Set.{u3} (Prod.{u3, u3} β β))} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> (Set.{u2} (Prod.{u2, u2} α α))} {F : ι -> β -> α}, (Filter.HasBasis.{u3, succ u4} (Prod.{u3, u3} β β) κ₁ (uniformity.{u3} β _inst_5) p₁ s₁) -> (Filter.HasBasis.{u2, succ u5} (Prod.{u2, u2} α α) κ₂ (uniformity.{u2} α _inst_4) p₂ s₂) -> (Iff (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) (forall (k₂ : κ₂), (p₂ k₂) -> (Exists.{succ u4} κ₁ (fun (k₁ : κ₁) => Exists.{0} (p₁ k₁) (fun (_x : p₁ k₁) => forall (x : β) (y : β), (Membership.Mem.{u3, u3} (Prod.{u3, u3} β β) (Set.{u3} (Prod.{u3, u3} β β)) (Set.hasMem.{u3} (Prod.{u3, u3} β β)) (Prod.mk.{u3, u3} β β x y) (s₁ k₁)) -> (forall (i : ι), Membership.Mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.hasMem.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α (F i x) (F i y)) (s₂ k₂)))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {κ₁ : Type.{u5}} {κ₂ : Type.{u4}} {p₁ : κ₁ -> Prop} {s₁ : κ₁ -> (Set.{u3} (Prod.{u3, u3} β β))} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> (Set.{u2} (Prod.{u2, u2} α α))} {F : ι -> β -> α}, (Filter.HasBasis.{u3, succ u5} (Prod.{u3, u3} β β) κ₁ (uniformity.{u3} β _inst_5) p₁ s₁) -> (Filter.HasBasis.{u2, succ u4} (Prod.{u2, u2} α α) κ₂ (uniformity.{u2} α _inst_4) p₂ s₂) -> (Iff (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) (forall (k₂ : κ₂), (p₂ k₂) -> (Exists.{succ u5} κ₁ (fun (k₁ : κ₁) => And (p₁ k₁) (forall (x : β) (y : β), (Membership.mem.{u3, u3} (Prod.{u3, u3} β β) (Set.{u3} (Prod.{u3, u3} β β)) (Set.instMembershipSet.{u3} (Prod.{u3, u3} β β)) (Prod.mk.{u3, u3} β β x y) (s₁ k₁)) -> (forall (i : ι), Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α (F i x) (F i y)) (s₂ k₂)))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniform_equicontinuous_iff Filter.HasBasis.uniformEquicontinuous_iffₓ'. -/
theorem Filter.HasBasis.uniformEquicontinuous_iff {κ₁ κ₂ : Type _} {p₁ : κ₁ → Prop}
    {s₁ : κ₁ → Set (β × β)} {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → β → α}
    (hβ : (𝓤 β).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    UniformEquicontinuous F ↔
      ∀ k₂, p₂ k₂ → ∃ (k₁ : _)(_ : p₁ k₁), ∀ x y, (x, y) ∈ s₁ k₁ → ∀ i, (F i x, F i y) ∈ s₂ k₂ :=
  by
  rw [uniformEquicontinuous_iff_uniformContinuous, UniformContinuous,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp_rw [Prod.forall]
  rfl
#align filter.has_basis.uniform_equicontinuous_iff Filter.HasBasis.uniformEquicontinuous_iff

/- warning: uniform_inducing.equicontinuous_at_iff -> UniformInducing.equicontinuousAt_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] [_inst_5 : UniformSpace.{u4} β] {F : ι -> X -> α} {x₀ : X} {u : α -> β}, (UniformInducing.{u3, u4} α β _inst_4 _inst_5 u) -> (Iff (EquicontinuousAt.{u1, u2, u3} ι X α _inst_1 _inst_4 F x₀) (EquicontinuousAt.{u1, u2, u4} ι X β _inst_1 _inst_5 (Function.comp.{succ u1, max (succ u2) (succ u3), max (succ u2) (succ u4)} ι (X -> α) (X -> β) (Function.comp.{succ u2, succ u3, succ u4} X α β u) F) x₀))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} {α : Type.{u4}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : UniformSpace.{u4} α] [_inst_5 : UniformSpace.{u3} β] {F : ι -> X -> α} {x₀ : X} {u : α -> β}, (UniformInducing.{u4, u3} α β _inst_4 _inst_5 u) -> (Iff (EquicontinuousAt.{u2, u1, u4} ι X α _inst_1 _inst_4 F x₀) (EquicontinuousAt.{u2, u1, u3} ι X β _inst_1 _inst_5 (Function.comp.{succ u2, max (succ u4) (succ u1), max (succ u3) (succ u1)} ι (X -> α) (X -> β) ((fun (x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3100 : α -> β) (x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3102 : X -> α) => Function.comp.{succ u1, succ u4, succ u3} X α β x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3100 x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3102) u) F) x₀))
Case conversion may be inaccurate. Consider using '#align uniform_inducing.equicontinuous_at_iff UniformInducing.equicontinuousAt_iffₓ'. -/
/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous at a point
`x₀ : X` iff the family `𝓕'`, obtained by precomposing each function of `𝓕` by `u`, is
equicontinuous at `x₀`. -/
theorem UniformInducing.equicontinuousAt_iff {F : ι → X → α} {x₀ : X} {u : α → β}
    (hu : UniformInducing u) : EquicontinuousAt F x₀ ↔ EquicontinuousAt ((· ∘ ·) u ∘ F) x₀ :=
  by
  have := (UniformFun.postcomp_uniformInducing hu).Inducing
  rw [equicontinuousAt_iff_continuousAt, equicontinuousAt_iff_continuousAt, this.continuous_at_iff]
  rfl
#align uniform_inducing.equicontinuous_at_iff UniformInducing.equicontinuousAt_iff

/- warning: uniform_inducing.equicontinuous_iff -> UniformInducing.equicontinuous_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] [_inst_5 : UniformSpace.{u4} β] {F : ι -> X -> α} {u : α -> β}, (UniformInducing.{u3, u4} α β _inst_4 _inst_5 u) -> (Iff (Equicontinuous.{u1, u2, u3} ι X α _inst_1 _inst_4 F) (Equicontinuous.{u1, u2, u4} ι X β _inst_1 _inst_5 (Function.comp.{succ u1, max (succ u2) (succ u3), max (succ u2) (succ u4)} ι (X -> α) (X -> β) (Function.comp.{succ u2, succ u3, succ u4} X α β u) F)))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} {α : Type.{u4}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : UniformSpace.{u4} α] [_inst_5 : UniformSpace.{u3} β] {F : ι -> X -> α} {u : α -> β}, (UniformInducing.{u4, u3} α β _inst_4 _inst_5 u) -> (Iff (Equicontinuous.{u2, u1, u4} ι X α _inst_1 _inst_4 F) (Equicontinuous.{u2, u1, u3} ι X β _inst_1 _inst_5 (Function.comp.{succ u2, max (succ u4) (succ u1), max (succ u3) (succ u1)} ι (X -> α) (X -> β) ((fun (x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3236 : α -> β) (x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3238 : X -> α) => Function.comp.{succ u1, succ u4, succ u3} X α β x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3236 x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3238) u) F)))
Case conversion may be inaccurate. Consider using '#align uniform_inducing.equicontinuous_iff UniformInducing.equicontinuous_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ∀ x, (_ : exprProp())]] -/
/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous iff the
family `𝓕'`, obtained by precomposing each function of `𝓕` by `u`, is equicontinuous. -/
theorem UniformInducing.equicontinuous_iff {F : ι → X → α} {u : α → β} (hu : UniformInducing u) :
    Equicontinuous F ↔ Equicontinuous ((· ∘ ·) u ∘ F) :=
  by
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ∀ x, (_ : exprProp())]]"
  rw [hu.equicontinuous_at_iff]
#align uniform_inducing.equicontinuous_iff UniformInducing.equicontinuous_iff

/- warning: uniform_inducing.uniform_equicontinuous_iff -> UniformInducing.uniformEquicontinuous_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] [_inst_6 : UniformSpace.{u4} γ] {F : ι -> β -> α} {u : α -> γ}, (UniformInducing.{u2, u4} α γ _inst_4 _inst_6 u) -> (Iff (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) (UniformEquicontinuous.{u1, u4, u3} ι γ β _inst_6 _inst_5 (Function.comp.{succ u1, max (succ u3) (succ u2), max (succ u3) (succ u4)} ι (β -> α) (β -> γ) (Function.comp.{succ u3, succ u2, succ u4} β α γ u) F)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u4}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_4 : UniformSpace.{u4} α] [_inst_5 : UniformSpace.{u1} β] [_inst_6 : UniformSpace.{u3} γ] {F : ι -> β -> α} {u : α -> γ}, (UniformInducing.{u4, u3} α γ _inst_4 _inst_6 u) -> (Iff (UniformEquicontinuous.{u2, u4, u1} ι α β _inst_4 _inst_5 F) (UniformEquicontinuous.{u2, u3, u1} ι γ β _inst_6 _inst_5 (Function.comp.{succ u2, max (succ u4) (succ u1), max (succ u1) (succ u3)} ι (β -> α) (β -> γ) ((fun (x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3423 : α -> γ) (x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3425 : β -> α) => Function.comp.{succ u1, succ u4, succ u3} β α γ x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3423 x._@.Mathlib.Topology.UniformSpace.Equicontinuity._hyg.3425) u) F)))
Case conversion may be inaccurate. Consider using '#align uniform_inducing.uniform_equicontinuous_iff UniformInducing.uniformEquicontinuous_iffₓ'. -/
/-- Given `u : α → γ` a uniform inducing map, a family `𝓕 : ι → β → α` is uniformly equicontinuous
iff the family `𝓕'`, obtained by precomposing each function of `𝓕` by `u`, is uniformly
equicontinuous. -/
theorem UniformInducing.uniformEquicontinuous_iff {F : ι → β → α} {u : α → γ}
    (hu : UniformInducing u) : UniformEquicontinuous F ↔ UniformEquicontinuous ((· ∘ ·) u ∘ F) :=
  by
  have := UniformFun.postcomp_uniformInducing hu
  rw [uniformEquicontinuous_iff_uniformContinuous, uniformEquicontinuous_iff_uniformContinuous,
    this.uniform_continuous_iff]
  rfl
#align uniform_inducing.uniform_equicontinuous_iff UniformInducing.uniformEquicontinuous_iff

/- warning: equicontinuous_at.closure' -> EquicontinuousAt.closure' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_4 : UniformSpace.{u3} α] {A : Set.{u2} Y} {u : Y -> X -> α} {x₀ : X}, (EquicontinuousAt.{u2, u1, u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) X α _inst_1 _inst_4 (Function.comp.{succ u2, succ u2, max (succ u1) (succ u3)} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (X -> α) u ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (coeSubtype.{succ u2} Y (fun (x : Y) => Membership.Mem.{u2, u2} Y (Set.{u2} Y) (Set.hasMem.{u2} Y) x A))))))) x₀) -> (Continuous.{u2, max u1 u3} Y (X -> α) _inst_2 (Pi.topologicalSpace.{u1, u3} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u3} α _inst_4)) u) -> (EquicontinuousAt.{u2, u1, u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) X α _inst_1 _inst_4 (Function.comp.{succ u2, succ u2, max (succ u1) (succ u3)} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (X -> α) u ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (coeSubtype.{succ u2} Y (fun (x : Y) => Membership.Mem.{u2, u2} Y (Set.{u2} Y) (Set.hasMem.{u2} Y) x (closure.{u2} Y _inst_2 A)))))))) x₀)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u3}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} Y] [_inst_4 : UniformSpace.{u1} α] {A : Set.{u3} Y} {u : Y -> X -> α} {x₀ : X}, (EquicontinuousAt.{u3, u2, u1} (Set.Elem.{u3} Y A) X α _inst_1 _inst_4 (Function.comp.{succ u3, succ u3, max (succ u2) (succ u1)} (Set.Elem.{u3} Y A) Y (X -> α) u (Subtype.val.{succ u3} Y (fun (x : Y) => Membership.mem.{u3, u3} Y (Set.{u3} Y) (Set.instMembershipSet.{u3} Y) x A))) x₀) -> (Continuous.{u3, max u2 u1} Y (X -> α) _inst_2 (Pi.topologicalSpace.{u2, u1} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u1} α _inst_4)) u) -> (EquicontinuousAt.{u3, u2, u1} (Set.Elem.{u3} Y (closure.{u3} Y _inst_2 A)) X α _inst_1 _inst_4 (Function.comp.{succ u3, succ u3, max (succ u2) (succ u1)} (Set.Elem.{u3} Y (closure.{u3} Y _inst_2 A)) Y (X -> α) u (Subtype.val.{succ u3} Y (fun (x : Y) => Membership.mem.{u3, u3} Y (Set.{u3} Y) (Set.instMembershipSet.{u3} Y) x (closure.{u3} Y _inst_2 A)))) x₀)
Case conversion may be inaccurate. Consider using '#align equicontinuous_at.closure' EquicontinuousAt.closure'ₓ'. -/
/-- A version of `equicontinuous_at.closure` applicable to subsets of types which embed continuously
into `X → α` with the product topology. It turns out we don't need any other condition on the
embedding than continuity, but in practice this will mostly be applied to `fun_like` types where
the coercion is injective. -/
theorem EquicontinuousAt.closure' {A : Set Y} {u : Y → X → α} {x₀ : X}
    (hA : EquicontinuousAt (u ∘ coe : A → X → α) x₀) (hu : Continuous u) :
    EquicontinuousAt (u ∘ coe : closure A → X → α) x₀ :=
  by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV]with x hx
  rw [SetCoe.forall] at *
  change A ⊆ (fun f => (u f x₀, u f x)) ⁻¹' V at hx
  refine' (closure_minimal hx <| hVclosed.preimage <| _).trans (preimage_mono hVU)
  exact Continuous.prod_mk ((continuous_apply x₀).comp hu) ((continuous_apply x).comp hu)
#align equicontinuous_at.closure' EquicontinuousAt.closure'

/- warning: equicontinuous_at.closure -> EquicontinuousAt.closure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : UniformSpace.{u2} α] {A : Set.{max u1 u2} (X -> α)} {x₀ : X}, (Set.EquicontinuousAt.{u1, u2} X α _inst_1 _inst_4 A x₀) -> (Set.EquicontinuousAt.{u1, u2} X α _inst_1 _inst_4 (closure.{max u1 u2} (X -> α) (Pi.topologicalSpace.{u1, u2} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u2} α _inst_4)) A) x₀)
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {A : Set.{max u2 u1} (X -> α)} {x₀ : X}, (Set.EquicontinuousAt.{u2, u1} X α _inst_1 _inst_4 A x₀) -> (Set.EquicontinuousAt.{u2, u1} X α _inst_1 _inst_4 (closure.{max u2 u1} (X -> α) (Pi.topologicalSpace.{u2, u1} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u1} α _inst_4)) A) x₀)
Case conversion may be inaccurate. Consider using '#align equicontinuous_at.closure EquicontinuousAt.closureₓ'. -/
/-- If a set of functions is equicontinuous at some `x₀`, its closure for the product topology is
also equicontinuous at `x₀`. -/
theorem EquicontinuousAt.closure {A : Set <| X → α} {x₀ : X} (hA : A.EquicontinuousAt x₀) :
    (closure A).EquicontinuousAt x₀ :=
  @EquicontinuousAt.closure' _ _ _ _ _ _ _ id _ hA continuous_id
#align equicontinuous_at.closure EquicontinuousAt.closure

/- warning: filter.tendsto.continuous_at_of_equicontinuous_at -> Filter.Tendsto.continuousAt_of_equicontinuousAt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {l : Filter.{u1} ι} [_inst_7 : Filter.NeBot.{u1} ι l] {F : ι -> X -> α} {f : X -> α} {x₀ : X}, (Filter.Tendsto.{u1, max u2 u3} ι (X -> α) F l (nhds.{max u2 u3} (X -> α) (Pi.topologicalSpace.{u2, u3} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u3} α _inst_4)) f)) -> (EquicontinuousAt.{u1, u2, u3} ι X α _inst_1 _inst_4 F x₀) -> (ContinuousAt.{u2, u3} X α _inst_1 (UniformSpace.toTopologicalSpace.{u3} α _inst_4) f x₀)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {l : Filter.{u3} ι} [_inst_7 : Filter.NeBot.{u3} ι l] {F : ι -> X -> α} {f : X -> α} {x₀ : X}, (Filter.Tendsto.{u3, max u2 u1} ι (X -> α) F l (nhds.{max u2 u1} (X -> α) (Pi.topologicalSpace.{u2, u1} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u1} α _inst_4)) f)) -> (EquicontinuousAt.{u3, u2, u1} ι X α _inst_1 _inst_4 F x₀) -> (ContinuousAt.{u2, u1} X α _inst_1 (UniformSpace.toTopologicalSpace.{u1} α _inst_4) f x₀)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.continuous_at_of_equicontinuous_at Filter.Tendsto.continuousAt_of_equicontinuousAtₓ'. -/
/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise* along some nontrivial filter, and if the
family `𝓕` is equicontinuous at some `x₀ : X`, then the limit is continuous at `x₀`. -/
theorem Filter.Tendsto.continuousAt_of_equicontinuousAt {l : Filter ι} [l.ne_bot] {F : ι → X → α}
    {f : X → α} {x₀ : X} (h₁ : Tendsto F l (𝓝 f)) (h₂ : EquicontinuousAt F x₀) :
    ContinuousAt f x₀ :=
  (equicontinuousAt_iff_range.mp h₂).closure.ContinuousAt
    ⟨f, mem_closure_of_tendsto h₁ <| eventually_of_forall mem_range_self⟩
#align filter.tendsto.continuous_at_of_equicontinuous_at Filter.Tendsto.continuousAt_of_equicontinuousAt

/- warning: equicontinuous.closure' -> Equicontinuous.closure' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_4 : UniformSpace.{u3} α] {A : Set.{u2} Y} {u : Y -> X -> α}, (Equicontinuous.{u2, u1, u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) X α _inst_1 _inst_4 (Function.comp.{succ u2, succ u2, max (succ u1) (succ u3)} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (X -> α) u ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) A) Y (coeSubtype.{succ u2} Y (fun (x : Y) => Membership.Mem.{u2, u2} Y (Set.{u2} Y) (Set.hasMem.{u2} Y) x A)))))))) -> (Continuous.{u2, max u1 u3} Y (X -> α) _inst_2 (Pi.topologicalSpace.{u1, u3} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u3} α _inst_4)) u) -> (Equicontinuous.{u2, u1, u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) X α _inst_1 _inst_4 (Function.comp.{succ u2, succ u2, max (succ u1) (succ u3)} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (X -> α) u ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} Y) Type.{u2} (Set.hasCoeToSort.{u2} Y) (closure.{u2} Y _inst_2 A)) Y (coeSubtype.{succ u2} Y (fun (x : Y) => Membership.Mem.{u2, u2} Y (Set.{u2} Y) (Set.hasMem.{u2} Y) x (closure.{u2} Y _inst_2 A)))))))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u3}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} Y] [_inst_4 : UniformSpace.{u1} α] {A : Set.{u3} Y} {u : Y -> X -> α}, (Equicontinuous.{u3, u2, u1} (Set.Elem.{u3} Y A) X α _inst_1 _inst_4 (Function.comp.{succ u3, succ u3, max (succ u2) (succ u1)} (Set.Elem.{u3} Y A) Y (X -> α) u (Subtype.val.{succ u3} Y (fun (x : Y) => Membership.mem.{u3, u3} Y (Set.{u3} Y) (Set.instMembershipSet.{u3} Y) x A)))) -> (Continuous.{u3, max u2 u1} Y (X -> α) _inst_2 (Pi.topologicalSpace.{u2, u1} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u1} α _inst_4)) u) -> (Equicontinuous.{u3, u2, u1} (Set.Elem.{u3} Y (closure.{u3} Y _inst_2 A)) X α _inst_1 _inst_4 (Function.comp.{succ u3, succ u3, max (succ u2) (succ u1)} (Set.Elem.{u3} Y (closure.{u3} Y _inst_2 A)) Y (X -> α) u (Subtype.val.{succ u3} Y (fun (x : Y) => Membership.mem.{u3, u3} Y (Set.{u3} Y) (Set.instMembershipSet.{u3} Y) x (closure.{u3} Y _inst_2 A)))))
Case conversion may be inaccurate. Consider using '#align equicontinuous.closure' Equicontinuous.closure'ₓ'. -/
/-- A version of `equicontinuous.closure` applicable to subsets of types which embed continuously
into `X → α` with the product topology. It turns out we don't need any other condition on the
embedding than continuity, but in practice this will mostly be applied to `fun_like` types where
the coercion is injective. -/
theorem Equicontinuous.closure' {A : Set Y} {u : Y → X → α}
    (hA : Equicontinuous (u ∘ coe : A → X → α)) (hu : Continuous u) :
    Equicontinuous (u ∘ coe : closure A → X → α) := fun x => (hA x).closure' hu
#align equicontinuous.closure' Equicontinuous.closure'

/- warning: equicontinuous.closure -> Equicontinuous.closure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : UniformSpace.{u2} α] {A : Set.{max u1 u2} (X -> α)}, (Set.Equicontinuous.{u1, u2} X α _inst_1 _inst_4 A) -> (Set.Equicontinuous.{u1, u2} X α _inst_1 _inst_4 (closure.{max u1 u2} (X -> α) (Pi.topologicalSpace.{u1, u2} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u2} α _inst_4)) A))
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {A : Set.{max u2 u1} (X -> α)}, (Set.Equicontinuous.{u2, u1} X α _inst_1 _inst_4 A) -> (Set.Equicontinuous.{u2, u1} X α _inst_1 _inst_4 (closure.{max u2 u1} (X -> α) (Pi.topologicalSpace.{u2, u1} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u1} α _inst_4)) A))
Case conversion may be inaccurate. Consider using '#align equicontinuous.closure Equicontinuous.closureₓ'. -/
/-- If a set of functions is equicontinuous, its closure for the product topology is also
equicontinuous. -/
theorem Equicontinuous.closure {A : Set <| X → α} (hA : A.Equicontinuous) :
    (closure A).Equicontinuous := fun x => (hA x).closure
#align equicontinuous.closure Equicontinuous.closure

/- warning: filter.tendsto.continuous_of_equicontinuous_at -> Filter.Tendsto.continuous_of_equicontinuous_at is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u3} α] {l : Filter.{u1} ι} [_inst_7 : Filter.NeBot.{u1} ι l] {F : ι -> X -> α} {f : X -> α}, (Filter.Tendsto.{u1, max u2 u3} ι (X -> α) F l (nhds.{max u2 u3} (X -> α) (Pi.topologicalSpace.{u2, u3} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u3} α _inst_4)) f)) -> (Equicontinuous.{u1, u2, u3} ι X α _inst_1 _inst_4 F) -> (Continuous.{u2, u3} X α _inst_1 (UniformSpace.toTopologicalSpace.{u3} α _inst_4) f)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_4 : UniformSpace.{u1} α] {l : Filter.{u3} ι} [_inst_7 : Filter.NeBot.{u3} ι l] {F : ι -> X -> α} {f : X -> α}, (Filter.Tendsto.{u3, max u2 u1} ι (X -> α) F l (nhds.{max u2 u1} (X -> α) (Pi.topologicalSpace.{u2, u1} X (fun (ᾰ : X) => α) (fun (a : X) => UniformSpace.toTopologicalSpace.{u1} α _inst_4)) f)) -> (Equicontinuous.{u3, u2, u1} ι X α _inst_1 _inst_4 F) -> (Continuous.{u2, u1} X α _inst_1 (UniformSpace.toTopologicalSpace.{u1} α _inst_4) f)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.continuous_of_equicontinuous_at Filter.Tendsto.continuous_of_equicontinuous_atₓ'. -/
/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise* along some nontrivial filter, and if the
family `𝓕` is equicontinuous, then the limit is continuous. -/
theorem Filter.Tendsto.continuous_of_equicontinuous_at {l : Filter ι} [l.ne_bot] {F : ι → X → α}
    {f : X → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : Equicontinuous F) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x => h₁.continuousAt_of_equicontinuousAt (h₂ x)
#align filter.tendsto.continuous_of_equicontinuous_at Filter.Tendsto.continuous_of_equicontinuous_at

/- warning: uniform_equicontinuous.closure' -> UniformEquicontinuous.closure' is a dubious translation:
lean 3 declaration is
  forall {Y : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : TopologicalSpace.{u1} Y] [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {A : Set.{u1} Y} {u : Y -> β -> α}, (UniformEquicontinuous.{u1, u2, u3} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) A) α β _inst_4 _inst_5 (Function.comp.{succ u1, succ u1, max (succ u3) (succ u2)} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) A) Y (β -> α) u ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) A) Y (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) A) Y (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) A) Y (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) A) Y (coeSubtype.{succ u1} Y (fun (x : Y) => Membership.Mem.{u1, u1} Y (Set.{u1} Y) (Set.hasMem.{u1} Y) x A)))))))) -> (Continuous.{u1, max u3 u2} Y (β -> α) _inst_2 (Pi.topologicalSpace.{u3, u2} β (fun (ᾰ : β) => α) (fun (a : β) => UniformSpace.toTopologicalSpace.{u2} α _inst_4)) u) -> (UniformEquicontinuous.{u1, u2, u3} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) (closure.{u1} Y _inst_2 A)) α β _inst_4 _inst_5 (Function.comp.{succ u1, succ u1, max (succ u3) (succ u2)} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) (closure.{u1} Y _inst_2 A)) Y (β -> α) u ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) (closure.{u1} Y _inst_2 A)) Y (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) (closure.{u1} Y _inst_2 A)) Y (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) (closure.{u1} Y _inst_2 A)) Y (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} Y) Type.{u1} (Set.hasCoeToSort.{u1} Y) (closure.{u1} Y _inst_2 A)) Y (coeSubtype.{succ u1} Y (fun (x : Y) => Membership.Mem.{u1, u1} Y (Set.{u1} Y) (Set.hasMem.{u1} Y) x (closure.{u1} Y _inst_2 A)))))))))
but is expected to have type
  forall {Y : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} Y] [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] {A : Set.{u3} Y} {u : Y -> β -> α}, (UniformEquicontinuous.{u3, u2, u1} (Set.Elem.{u3} Y A) α β _inst_4 _inst_5 (Function.comp.{succ u3, succ u3, max (succ u2) (succ u1)} (Set.Elem.{u3} Y A) Y (β -> α) u (Subtype.val.{succ u3} Y (fun (x : Y) => Membership.mem.{u3, u3} Y (Set.{u3} Y) (Set.instMembershipSet.{u3} Y) x A)))) -> (Continuous.{u3, max u2 u1} Y (β -> α) _inst_2 (Pi.topologicalSpace.{u1, u2} β (fun (ᾰ : β) => α) (fun (a : β) => UniformSpace.toTopologicalSpace.{u2} α _inst_4)) u) -> (UniformEquicontinuous.{u3, u2, u1} (Set.Elem.{u3} Y (closure.{u3} Y _inst_2 A)) α β _inst_4 _inst_5 (Function.comp.{succ u3, succ u3, max (succ u2) (succ u1)} (Set.Elem.{u3} Y (closure.{u3} Y _inst_2 A)) Y (β -> α) u (Subtype.val.{succ u3} Y (fun (x : Y) => Membership.mem.{u3, u3} Y (Set.{u3} Y) (Set.instMembershipSet.{u3} Y) x (closure.{u3} Y _inst_2 A)))))
Case conversion may be inaccurate. Consider using '#align uniform_equicontinuous.closure' UniformEquicontinuous.closure'ₓ'. -/
/-- A version of `uniform_equicontinuous.closure` applicable to subsets of types which embed
continuously into `β → α` with the product topology. It turns out we don't need any other condition
on the embedding than continuity, but in practice this will mostly be applied to `fun_like` types
where the coercion is injective. -/
theorem UniformEquicontinuous.closure' {A : Set Y} {u : Y → β → α}
    (hA : UniformEquicontinuous (u ∘ coe : A → β → α)) (hu : Continuous u) :
    UniformEquicontinuous (u ∘ coe : closure A → β → α) :=
  by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV]
  rintro ⟨x, y⟩ hxy
  rw [SetCoe.forall] at *
  change A ⊆ (fun f => (u f x, u f y)) ⁻¹' V at hxy
  refine' (closure_minimal hxy <| hVclosed.preimage <| _).trans (preimage_mono hVU)
  exact Continuous.prod_mk ((continuous_apply x).comp hu) ((continuous_apply y).comp hu)
#align uniform_equicontinuous.closure' UniformEquicontinuous.closure'

/- warning: uniform_equicontinuous.closure -> UniformEquicontinuous.closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : UniformSpace.{u1} α] [_inst_5 : UniformSpace.{u2} β] {A : Set.{max u2 u1} (β -> α)}, (Set.UniformEquicontinuous.{u1, u2} α β _inst_4 _inst_5 A) -> (Set.UniformEquicontinuous.{u1, u2} α β _inst_4 _inst_5 (closure.{max u2 u1} (β -> α) (Pi.topologicalSpace.{u2, u1} β (fun (ᾰ : β) => α) (fun (a : β) => UniformSpace.toTopologicalSpace.{u1} α _inst_4)) A))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] {A : Set.{max u2 u1} (β -> α)}, (Set.UniformEquicontinuous.{u2, u1} α β _inst_4 _inst_5 A) -> (Set.UniformEquicontinuous.{u2, u1} α β _inst_4 _inst_5 (closure.{max u2 u1} (β -> α) (Pi.topologicalSpace.{u1, u2} β (fun (ᾰ : β) => α) (fun (a : β) => UniformSpace.toTopologicalSpace.{u2} α _inst_4)) A))
Case conversion may be inaccurate. Consider using '#align uniform_equicontinuous.closure UniformEquicontinuous.closureₓ'. -/
/-- If a set of functions is uniformly equicontinuous, its closure for the product topology is also
uniformly equicontinuous. -/
theorem UniformEquicontinuous.closure {A : Set <| β → α} (hA : A.UniformEquicontinuous) :
    (closure A).UniformEquicontinuous :=
  @UniformEquicontinuous.closure' _ _ _ _ _ _ _ id hA continuous_id
#align uniform_equicontinuous.closure UniformEquicontinuous.closure

/- warning: filter.tendsto.uniform_continuous_of_uniform_equicontinuous -> Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u3} β] {l : Filter.{u1} ι} [_inst_7 : Filter.NeBot.{u1} ι l] {F : ι -> β -> α} {f : β -> α}, (Filter.Tendsto.{u1, max u3 u2} ι (β -> α) F l (nhds.{max u3 u2} (β -> α) (Pi.topologicalSpace.{u3, u2} β (fun (ᾰ : β) => α) (fun (a : β) => UniformSpace.toTopologicalSpace.{u2} α _inst_4)) f)) -> (UniformEquicontinuous.{u1, u2, u3} ι α β _inst_4 _inst_5 F) -> (UniformContinuous.{u3, u2} β α _inst_5 _inst_4 f)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] {l : Filter.{u3} ι} [_inst_7 : Filter.NeBot.{u3} ι l] {F : ι -> β -> α} {f : β -> α}, (Filter.Tendsto.{u3, max u2 u1} ι (β -> α) F l (nhds.{max u2 u1} (β -> α) (Pi.topologicalSpace.{u1, u2} β (fun (ᾰ : β) => α) (fun (a : β) => UniformSpace.toTopologicalSpace.{u2} α _inst_4)) f)) -> (UniformEquicontinuous.{u3, u2, u1} ι α β _inst_4 _inst_5 F) -> (UniformContinuous.{u1, u2} β α _inst_5 _inst_4 f)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.uniform_continuous_of_uniform_equicontinuous Filter.Tendsto.uniformContinuous_of_uniformEquicontinuousₓ'. -/
/-- If `𝓕 : ι → β → α` tends to `f : β → α` *pointwise* along some nontrivial filter, and if the
family `𝓕` is uniformly equicontinuous, then the limit is uniformly continuous. -/
theorem Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous {l : Filter ι} [l.ne_bot]
    {F : ι → β → α} {f : β → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : UniformEquicontinuous F) :
    UniformContinuous f :=
  (uniformEquicontinuous_at_iff_range.mp h₂).closure.UniformContinuous
    ⟨f, mem_closure_of_tendsto h₁ <| eventually_of_forall mem_range_self⟩
#align filter.tendsto.uniform_continuous_of_uniform_equicontinuous Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous

end

end

