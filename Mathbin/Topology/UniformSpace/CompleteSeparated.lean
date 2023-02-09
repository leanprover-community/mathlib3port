/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.uniform_space.complete_separated
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.Cauchy
import Mathbin.Topology.UniformSpace.Separation
import Mathbin.Topology.DenseEmbedding

/-!
# Theory of complete separated uniform spaces.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/


open Filter

open Topology Filter

variable {α : Type _}

#print IsComplete.isClosed /-
--In a separated space, a complete set is closed
theorem IsComplete.isClosed [UniformSpace α] [SeparatedSpace α] {s : Set α} (h : IsComplete s) :
    IsClosed s :=
  isClosed_iff_clusterPt.2 fun a ha => by
    let f := 𝓝[s] a
    have : Cauchy f := cauchy_nhds.mono' ha inf_le_left
    rcases h f this inf_le_right with ⟨y, ys, fy⟩
    rwa [(tendsto_nhds_unique' ha inf_le_left fy : a = y)]
#align is_complete.is_closed IsComplete.isClosed
-/

namespace DenseInducing

open Filter

variable [TopologicalSpace α] {β : Type _} [TopologicalSpace β]

variable {γ : Type _} [UniformSpace γ] [CompleteSpace γ] [SeparatedSpace γ]

/- warning: dense_inducing.continuous_extend_of_cauchy -> DenseInducing.continuous_extend_of_cauchy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {γ : Type.{u3}} [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : CompleteSpace.{u3} γ _inst_3] [_inst_5 : SeparatedSpace.{u3} γ _inst_3] {e : α -> β} {f : α -> γ} (de : DenseInducing.{u1, u2} α β _inst_1 _inst_2 e), (forall (b : β), Cauchy.{u3} γ _inst_3 (Filter.map.{u1, u3} α γ f (Filter.comap.{u1, u2} α β e (nhds.{u2} β _inst_2 b)))) -> (Continuous.{u2, u3} β γ _inst_2 (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 e (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) de f))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {γ : Type.{u1}} [_inst_3 : UniformSpace.{u1} γ] [_inst_4 : CompleteSpace.{u1} γ _inst_3] [_inst_5 : SeparatedSpace.{u1} γ _inst_3] {e : α -> β} {f : α -> γ} (de : DenseInducing.{u3, u2} α β _inst_1 _inst_2 e), (forall (b : β), Cauchy.{u1} γ _inst_3 (Filter.map.{u3, u1} α γ f (Filter.comap.{u3, u2} α β e (nhds.{u2} β _inst_2 b)))) -> (Continuous.{u2, u1} β γ _inst_2 (UniformSpace.toTopologicalSpace.{u1} γ _inst_3) (DenseInducing.extend.{u3, u2, u1} α β γ _inst_1 _inst_2 e (UniformSpace.toTopologicalSpace.{u1} γ _inst_3) de f))
Case conversion may be inaccurate. Consider using '#align dense_inducing.continuous_extend_of_cauchy DenseInducing.continuous_extend_of_cauchyₓ'. -/
theorem continuous_extend_of_cauchy {e : α → β} {f : α → γ} (de : DenseInducing e)
    (h : ∀ b : β, Cauchy (map f (comap e <| 𝓝 b))) : Continuous (de.extend f) :=
  de.continuous_extend fun b => CompleteSpace.complete (h b)
#align dense_inducing.continuous_extend_of_cauchy DenseInducing.continuous_extend_of_cauchy

end DenseInducing

