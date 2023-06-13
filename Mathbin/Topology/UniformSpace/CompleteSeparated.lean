/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.uniform_space.complete_separated
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
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

open scoped Topology Filter

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

#print DenseInducing.continuous_extend_of_cauchy /-
theorem continuous_extend_of_cauchy {e : α → β} {f : α → γ} (de : DenseInducing e)
    (h : ∀ b : β, Cauchy (map f (comap e <| 𝓝 b))) : Continuous (de.extend f) :=
  de.continuous_extend fun b => CompleteSpace.complete (h b)
#align dense_inducing.continuous_extend_of_cauchy DenseInducing.continuous_extend_of_cauchy
-/

end DenseInducing

