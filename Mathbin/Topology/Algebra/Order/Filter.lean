/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.filter
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Basic
import Mathbin.Topology.Filter

/-!
# Topology on filters of a space with order topology

In this file we prove that `𝓝 (f x)` tends to `𝓝 filter.at_top` provided that `f` tends to
`filter.at_top`, and similarly for `filter.at_bot`.
-/


open TopologicalSpace

namespace Filter

variable {α X : Type _} [TopologicalSpace X] [PartialOrder X] [OrderTopology X]

protected theorem tendsto_nhds_at_top [NoMaxOrder X] : Tendsto 𝓝 (atTop : Filter X) (𝓝 atTop) :=
  Filter.tendsto_nhds_at_top_iff.2 fun x => (eventually_gt_at_top x).mono fun y => le_mem_nhds
#align filter.tendsto_nhds_at_top Filter.tendsto_nhds_at_top

protected theorem tendsto_nhds_at_bot [NoMinOrder X] : Tendsto 𝓝 (atBot : Filter X) (𝓝 atBot) :=
  @Filter.tendsto_nhds_at_top Xᵒᵈ _ _ _ _
#align filter.tendsto_nhds_at_bot Filter.tendsto_nhds_at_bot

theorem Tendsto.nhds_at_top [NoMaxOrder X] {f : α → X} {l : Filter α} (h : Tendsto f l atTop) :
    Tendsto (𝓝 ∘ f) l (𝓝 atTop) :=
  Filter.tendsto_nhds_at_top.comp h
#align filter.tendsto.nhds_at_top Filter.Tendsto.nhds_at_top

theorem Tendsto.nhds_at_bot [NoMinOrder X] {f : α → X} {l : Filter α} (h : Tendsto f l atBot) :
    Tendsto (𝓝 ∘ f) l (𝓝 atBot) :=
  @Tendsto.nhds_at_top α Xᵒᵈ _ _ _ _ _ _ h
#align filter.tendsto.nhds_at_bot Filter.Tendsto.nhds_at_bot

end Filter

