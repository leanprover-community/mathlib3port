/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module topology.algebra.star
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Pi
import Mathbin.Algebra.Star.Prod
import Mathbin.Topology.Algebra.Constructions
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Continuity of `star`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `has_continuous_star` typeclass, along with instances on `pi`, `prod`,
`mul_opposite`, and `units`.
-/


open Filter Topology

open Filter

universe u

variable {ι α R S : Type _}

#print ContinuousStar /-
/-- Basic hypothesis to talk about a topological space with a continuous `star` operator. -/
class ContinuousStar (R : Type u) [TopologicalSpace R] [Star R] : Prop where
  continuous_star : Continuous (star : R → R)
#align has_continuous_star ContinuousStar
-/

export ContinuousStar (continuous_star)

section Continuity

variable [TopologicalSpace R] [Star R] [ContinuousStar R]

#print continuousOn_star /-
theorem continuousOn_star {s : Set R} : ContinuousOn star s :=
  continuous_star.ContinuousOn
#align continuous_on_star continuousOn_star
-/

#print continuousWithinAt_star /-
theorem continuousWithinAt_star {s : Set R} {x : R} : ContinuousWithinAt star s x :=
  continuous_star.ContinuousWithinAt
#align continuous_within_at_star continuousWithinAt_star
-/

#print continuousAt_star /-
theorem continuousAt_star {x : R} : ContinuousAt star x :=
  continuous_star.ContinuousAt
#align continuous_at_star continuousAt_star
-/

#print tendsto_star /-
theorem tendsto_star (a : R) : Tendsto star (𝓝 a) (𝓝 (star a)) :=
  continuousAt_star
#align tendsto_star tendsto_star
-/

/- warning: filter.tendsto.star -> Filter.Tendsto.star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : Star.{u2} R] [_inst_3 : ContinuousStar.{u2} R _inst_1 _inst_2] {f : α -> R} {l : Filter.{u1} α} {y : R}, (Filter.Tendsto.{u1, u2} α R f l (nhds.{u2} R _inst_1 y)) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => Star.star.{u2} R _inst_2 (f x)) l (nhds.{u2} R _inst_1 (Star.star.{u2} R _inst_2 y)))
but is expected to have type
  forall {α : Type.{u1}} [R : TopologicalSpace.{u1} α] [_inst_1 : Star.{u1} α] [_inst_2 : ContinuousStar.{u1} α R _inst_1] {_inst_3 : Type.{u2}} {f : _inst_3 -> α} {l : Filter.{u2} _inst_3} {y : α}, (Filter.Tendsto.{u2, u1} _inst_3 α f l (nhds.{u1} α R y)) -> (Filter.Tendsto.{u2, u1} _inst_3 α (fun (x : _inst_3) => Star.star.{u1} α _inst_1 (f x)) l (nhds.{u1} α R (Star.star.{u1} α _inst_1 y)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.star Filter.Tendsto.starₓ'. -/
theorem Filter.Tendsto.star {f : α → R} {l : Filter α} {y : R} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => star (f x)) l (𝓝 (star y)) :=
  (continuous_star.Tendsto y).comp h
#align filter.tendsto.star Filter.Tendsto.star

variable [TopologicalSpace α] {f : α → R} {s : Set α} {x : α}

/- warning: continuous.star -> Continuous.star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : Star.{u2} R] [_inst_3 : ContinuousStar.{u2} R _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u1} α] {f : α -> R}, (Continuous.{u1, u2} α R _inst_4 _inst_1 f) -> (Continuous.{u1, u2} α R _inst_4 _inst_1 (fun (x : α) => Star.star.{u2} R _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Star.{u1} α] [_inst_3 : ContinuousStar.{u1} α _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u2} R] {f : R -> α}, (Continuous.{u2, u1} R α _inst_4 _inst_1 f) -> (Continuous.{u2, u1} R α _inst_4 _inst_1 (fun (x : R) => Star.star.{u1} α _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align continuous.star Continuous.starₓ'. -/
@[continuity]
theorem Continuous.star (hf : Continuous f) : Continuous fun x => star (f x) :=
  continuous_star.comp hf
#align continuous.star Continuous.star

/- warning: continuous_at.star -> ContinuousAt.star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : Star.{u2} R] [_inst_3 : ContinuousStar.{u2} R _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u1} α] {f : α -> R} {x : α}, (ContinuousAt.{u1, u2} α R _inst_4 _inst_1 f x) -> (ContinuousAt.{u1, u2} α R _inst_4 _inst_1 (fun (x : α) => Star.star.{u2} R _inst_2 (f x)) x)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Star.{u1} α] [_inst_3 : ContinuousStar.{u1} α _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u2} R] {f : R -> α} {x : R}, (ContinuousAt.{u2, u1} R α _inst_4 _inst_1 f x) -> (ContinuousAt.{u2, u1} R α _inst_4 _inst_1 (fun (x : R) => Star.star.{u1} α _inst_2 (f x)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.star ContinuousAt.starₓ'. -/
theorem ContinuousAt.star (hf : ContinuousAt f x) : ContinuousAt (fun x => star (f x)) x :=
  continuousAt_star.comp hf
#align continuous_at.star ContinuousAt.star

/- warning: continuous_on.star -> ContinuousOn.star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : Star.{u2} R] [_inst_3 : ContinuousStar.{u2} R _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u1} α] {f : α -> R} {s : Set.{u1} α}, (ContinuousOn.{u1, u2} α R _inst_4 _inst_1 f s) -> (ContinuousOn.{u1, u2} α R _inst_4 _inst_1 (fun (x : α) => Star.star.{u2} R _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Star.{u1} α] [_inst_3 : ContinuousStar.{u1} α _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u2} R] {f : R -> α} {s : Set.{u2} R}, (ContinuousOn.{u2, u1} R α _inst_4 _inst_1 f s) -> (ContinuousOn.{u2, u1} R α _inst_4 _inst_1 (fun (x : R) => Star.star.{u1} α _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.star ContinuousOn.starₓ'. -/
theorem ContinuousOn.star (hf : ContinuousOn f s) : ContinuousOn (fun x => star (f x)) s :=
  continuous_star.comp_continuousOn hf
#align continuous_on.star ContinuousOn.star

/- warning: continuous_within_at.star -> ContinuousWithinAt.star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : Star.{u2} R] [_inst_3 : ContinuousStar.{u2} R _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u1} α] {f : α -> R} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, u2} α R _inst_4 _inst_1 f s x) -> (ContinuousWithinAt.{u1, u2} α R _inst_4 _inst_1 (fun (x : α) => Star.star.{u2} R _inst_2 (f x)) s x)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Star.{u1} α] [_inst_3 : ContinuousStar.{u1} α _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u2} R] {f : R -> α} {s : Set.{u2} R} {x : R}, (ContinuousWithinAt.{u2, u1} R α _inst_4 _inst_1 f s x) -> (ContinuousWithinAt.{u2, u1} R α _inst_4 _inst_1 (fun (x : R) => Star.star.{u1} α _inst_2 (f x)) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.star ContinuousWithinAt.starₓ'. -/
theorem ContinuousWithinAt.star (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => star (f x)) s x :=
  hf.unit
#align continuous_within_at.star ContinuousWithinAt.star

#print starContinuousMap /-
/-- The star operation bundled as a continuous map. -/
@[simps]
def starContinuousMap : C(R, R) :=
  ⟨star, continuous_star⟩
#align star_continuous_map starContinuousMap
-/

end Continuity

section Instances

instance [Star R] [Star S] [TopologicalSpace R] [TopologicalSpace S] [ContinuousStar R]
    [ContinuousStar S] : ContinuousStar (R × S) :=
  ⟨(continuous_star.comp continuous_fst).prod_mk (continuous_star.comp continuous_snd)⟩

instance {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, Star (C i)]
    [∀ i, ContinuousStar (C i)] : ContinuousStar (∀ i, C i)
    where continuous_star := continuous_pi fun i => Continuous.star (continuous_apply i)

instance [Star R] [TopologicalSpace R] [ContinuousStar R] : ContinuousStar Rᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.unit⟩

instance [Monoid R] [StarSemigroup R] [TopologicalSpace R] [ContinuousStar R] : ContinuousStar Rˣ :=
  ⟨continuous_induced_rng.2 Units.continuous_embedProduct.unit⟩

end Instances

