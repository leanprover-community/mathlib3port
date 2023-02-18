/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.extr_closure
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.LocalExtr
import Mathbin.Topology.Order.Basic

/-!
# Maximum/minimum on the closure of a set

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove several versions of the following statement: if `f : X → Y` has a (local or
not) maximum (or minimum) on a set `s` at a point `a` and is continuous on the closure of `s`, then
`f` has an extremum of the same type on `closure s` at `a`.
-/


open Filter Set

open Topology

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] [Preorder Y]
  [OrderClosedTopology Y] {f g : X → Y} {s : Set X} {a : X}

/- warning: is_max_on.closure -> IsMaxOn.closure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : Preorder.{u2} Y] [_inst_4 : OrderClosedTopology.{u2} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u1} X} {a : X}, (IsMaxOn.{u1, u2} X Y _inst_3 f s a) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f (closure.{u1} X _inst_1 s)) -> (IsMaxOn.{u1, u2} X Y _inst_3 f (closure.{u1} X _inst_1 s) a)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : Preorder.{u1} Y] [_inst_4 : OrderClosedTopology.{u1} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u2} X} {a : X}, (IsMaxOn.{u2, u1} X Y _inst_3 f s a) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f (closure.{u2} X _inst_1 s)) -> (IsMaxOn.{u2, u1} X Y _inst_3 f (closure.{u2} X _inst_1 s) a)
Case conversion may be inaccurate. Consider using '#align is_max_on.closure IsMaxOn.closureₓ'. -/
protected theorem IsMaxOn.closure (h : IsMaxOn f s a) (hc : ContinuousOn f (closure s)) :
    IsMaxOn f (closure s) a := fun x hx =>
  ContinuousWithinAt.closure_le hx ((hc x hx).mono subset_closure) continuousWithinAt_const h
#align is_max_on.closure IsMaxOn.closure

/- warning: is_min_on.closure -> IsMinOn.closure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : Preorder.{u2} Y] [_inst_4 : OrderClosedTopology.{u2} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u1} X} {a : X}, (IsMinOn.{u1, u2} X Y _inst_3 f s a) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f (closure.{u1} X _inst_1 s)) -> (IsMinOn.{u1, u2} X Y _inst_3 f (closure.{u1} X _inst_1 s) a)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : Preorder.{u1} Y] [_inst_4 : OrderClosedTopology.{u1} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u2} X} {a : X}, (IsMinOn.{u2, u1} X Y _inst_3 f s a) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f (closure.{u2} X _inst_1 s)) -> (IsMinOn.{u2, u1} X Y _inst_3 f (closure.{u2} X _inst_1 s) a)
Case conversion may be inaccurate. Consider using '#align is_min_on.closure IsMinOn.closureₓ'. -/
protected theorem IsMinOn.closure (h : IsMinOn f s a) (hc : ContinuousOn f (closure s)) :
    IsMinOn f (closure s) a :=
  h.dual.closure hc
#align is_min_on.closure IsMinOn.closure

/- warning: is_extr_on.closure -> IsExtrOn.closure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : Preorder.{u2} Y] [_inst_4 : OrderClosedTopology.{u2} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u1} X} {a : X}, (IsExtrOn.{u1, u2} X Y _inst_3 f s a) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f (closure.{u1} X _inst_1 s)) -> (IsExtrOn.{u1, u2} X Y _inst_3 f (closure.{u1} X _inst_1 s) a)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : Preorder.{u1} Y] [_inst_4 : OrderClosedTopology.{u1} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u2} X} {a : X}, (IsExtrOn.{u2, u1} X Y _inst_3 f s a) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f (closure.{u2} X _inst_1 s)) -> (IsExtrOn.{u2, u1} X Y _inst_3 f (closure.{u2} X _inst_1 s) a)
Case conversion may be inaccurate. Consider using '#align is_extr_on.closure IsExtrOn.closureₓ'. -/
protected theorem IsExtrOn.closure (h : IsExtrOn f s a) (hc : ContinuousOn f (closure s)) :
    IsExtrOn f (closure s) a :=
  h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr <| h.closure hc
#align is_extr_on.closure IsExtrOn.closure

/- warning: is_local_max_on.closure -> IsLocalMaxOn.closure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : Preorder.{u2} Y] [_inst_4 : OrderClosedTopology.{u2} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u1} X} {a : X}, (IsLocalMaxOn.{u1, u2} X Y _inst_1 _inst_3 f s a) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f (closure.{u1} X _inst_1 s)) -> (IsLocalMaxOn.{u1, u2} X Y _inst_1 _inst_3 f (closure.{u1} X _inst_1 s) a)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : Preorder.{u1} Y] [_inst_4 : OrderClosedTopology.{u1} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u2} X} {a : X}, (IsLocalMaxOn.{u2, u1} X Y _inst_1 _inst_3 f s a) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f (closure.{u2} X _inst_1 s)) -> (IsLocalMaxOn.{u2, u1} X Y _inst_1 _inst_3 f (closure.{u2} X _inst_1 s) a)
Case conversion may be inaccurate. Consider using '#align is_local_max_on.closure IsLocalMaxOn.closureₓ'. -/
protected theorem IsLocalMaxOn.closure (h : IsLocalMaxOn f s a) (hc : ContinuousOn f (closure s)) :
    IsLocalMaxOn f (closure s) a :=
  by
  rcases mem_nhdsWithin.1 h with ⟨U, Uo, aU, hU⟩
  refine' mem_nhdsWithin.2 ⟨U, Uo, aU, _⟩
  rintro x ⟨hxU, hxs⟩
  refine' ContinuousWithinAt.closure_le _ _ continuousWithinAt_const hU
  · rwa [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_inter_of_mem, ←
      mem_closure_iff_nhdsWithin_neBot]
    exact nhdsWithin_le_nhds (Uo.mem_nhds hxU)
  · exact (hc _ hxs).mono ((inter_subset_right _ _).trans subset_closure)
#align is_local_max_on.closure IsLocalMaxOn.closure

/- warning: is_local_min_on.closure -> IsLocalMinOn.closure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : Preorder.{u2} Y] [_inst_4 : OrderClosedTopology.{u2} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u1} X} {a : X}, (IsLocalMinOn.{u1, u2} X Y _inst_1 _inst_3 f s a) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f (closure.{u1} X _inst_1 s)) -> (IsLocalMinOn.{u1, u2} X Y _inst_1 _inst_3 f (closure.{u1} X _inst_1 s) a)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : Preorder.{u1} Y] [_inst_4 : OrderClosedTopology.{u1} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u2} X} {a : X}, (IsLocalMinOn.{u2, u1} X Y _inst_1 _inst_3 f s a) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f (closure.{u2} X _inst_1 s)) -> (IsLocalMinOn.{u2, u1} X Y _inst_1 _inst_3 f (closure.{u2} X _inst_1 s) a)
Case conversion may be inaccurate. Consider using '#align is_local_min_on.closure IsLocalMinOn.closureₓ'. -/
protected theorem IsLocalMinOn.closure (h : IsLocalMinOn f s a) (hc : ContinuousOn f (closure s)) :
    IsLocalMinOn f (closure s) a :=
  IsLocalMaxOn.closure h.dual hc
#align is_local_min_on.closure IsLocalMinOn.closure

/- warning: is_local_extr_on.closure -> IsLocalExtrOn.closure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : Preorder.{u2} Y] [_inst_4 : OrderClosedTopology.{u2} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u1} X} {a : X}, (IsLocalExtrOn.{u1, u2} X Y _inst_1 _inst_3 f s a) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f (closure.{u1} X _inst_1 s)) -> (IsLocalExtrOn.{u1, u2} X Y _inst_1 _inst_3 f (closure.{u1} X _inst_1 s) a)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : Preorder.{u1} Y] [_inst_4 : OrderClosedTopology.{u1} Y _inst_2 _inst_3] {f : X -> Y} {s : Set.{u2} X} {a : X}, (IsLocalExtrOn.{u2, u1} X Y _inst_1 _inst_3 f s a) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f (closure.{u2} X _inst_1 s)) -> (IsLocalExtrOn.{u2, u1} X Y _inst_1 _inst_3 f (closure.{u2} X _inst_1 s) a)
Case conversion may be inaccurate. Consider using '#align is_local_extr_on.closure IsLocalExtrOn.closureₓ'. -/
protected theorem IsLocalExtrOn.closure (h : IsLocalExtrOn f s a)
    (hc : ContinuousOn f (closure s)) : IsLocalExtrOn f (closure s) a :=
  h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr <| h.closure hc
#align is_local_extr_on.closure IsLocalExtrOn.closure

