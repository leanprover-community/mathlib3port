/-
Copyright (c) 202 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import SetTheory.Ordinal.Basic
import Topology.MetricSpace.EmetricSpace
import Topology.Paracompact

#align_import topology.metric_space.emetric_paracompact from "leanprover-community/mathlib"@"f47581155c818e6361af4e4fda60d27d020c226b"

/-!
# (Extended) metric spaces are paracompact

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we provide two instances:

* `emetric.paracompact_space`: a `pseudo_emetric_space` is paracompact; formalization is based
  on [MR0236876];
* `emetric.normal_of_metric`: an `emetric_space` is a normal topological space.

## Tags

metric space, paracompact space, normal space
-/


variable {α : Type _}

open scoped ENNReal Topology

open Set

namespace Emetric

-- See note [lower instance priority]
/-- A `pseudo_emetric_space` is always a paracompact space. Formalization is based
on [MR0236876]. -/
instance (priority := 100) [PseudoEMetricSpace α] : ParacompactSpace α := by classical

#print EMetric.t4Space /-
/- We start with trivial observations about `1 / 2 ^ k`. Here and below we use `1 / 2 ^ k` in
  the comments and `2⁻¹ ^ k` in the code. -/
-- Consider an open covering `S : set (set α)`
-- choose a well founded order on `S`
-- Let `ind x` be the minimal index `s : S` such that `x ∈ s`.
/- The refinement `D : ℕ → ι → set α` is defined recursively. For each `n` and `i`, `D n i`
  is the union of balls `ball x (1 / 2 ^ n)` over all points `x` such that

  * `ind x = i`;
  * `x` does not belong to any `D m j`, `m < n`;
  * `ball x (3 / 2 ^ n) ⊆ s i`;

  We define this sequence using `nat.strong_rec_on'`, then restate it as `Dn` and `memD`.
  -/
-- The sets `D n i` cover the whole space. Indeed, for each `x` we can choose `n` such that
-- `ball x (3 / 2 ^ n) ⊆ s (ind x)`, then either `x ∈ D n i`, or `x ∈ D m i` for some `m < n`.
-- This proof takes 5 lines because we can't import `specific_limits` here
-- Each `D n i` is a union of open balls, hence it is an open set
-- the covering `D n i` is a refinement of the original covering: `D n i ⊆ s i`
-- TODO: use `norm_num`
-- Let us show the rest of the properties. Since the definition expects a family indexed
-- by a single parameter, we use `ℕ × ι` as the domain.
-- The sets `D n i` cover the whole space as we proved earlier
/- Let us prove that the covering `D n i` is locally finite. Take a point `x` and choose
    `n`, `i` so that `x ∈ D n i`. Since `D n i` is an open set, we can choose `k` so that
    `B = ball x (1 / 2 ^ (n + k + 1)) ⊆ D n i`. -/
-- The sets `D m i`, `m > n + k`, are disjoint with `B`
-- For each `m ≤ n + k` there is at most one `j` such that `D m j ∩ B` is nonempty.
-- Finally, we glue `Hgt` and `Hle`
-- see Note [lower instance priority]
instance (priority := 100) t4Space [EMetricSpace α] : NormalSpace α :=
  T4Space.of_paracompactSpace_t2Space
#align emetric.normal_of_emetric EMetric.t4Space
-/

end Emetric

