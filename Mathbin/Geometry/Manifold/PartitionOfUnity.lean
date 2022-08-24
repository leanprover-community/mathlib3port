/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Geometry.Manifold.Algebra.Structures
import Mathbin.Geometry.Manifold.BumpFunction
import Mathbin.Topology.MetricSpace.PartitionOfUnity
import Mathbin.Topology.ShrinkingLemma

/-!
# Smooth partition of unity

In this file we define two structures, `smooth_bump_covering` and `smooth_partition_of_unity`. Both
structures describe coverings of a set by a locally finite family of supports of smooth functions
with some additional properties. The former structure is mostly useful as an intermediate step in
the construction of a smooth partition of unity but some proofs that traditionally deal with a
partition of unity can use a `smooth_bump_covering` as well.

Given a real manifold `M` and its subset `s`, a `smooth_bump_covering ι I M s` is a collection of
`smooth_bump_function`s `f i` indexed by `i : ι` such that

* the center of each `f i` belongs to `s`;
* the family of sets `support (f i)` is locally finite;
* for each `x ∈ s`, there exists `i : ι` such that `f i =ᶠ[𝓝 x] 1`.
In the same settings, a `smooth_partition_of_unity ι I M s` is a collection of smooth nonnegative
functions `f i : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`, `i : ι`, such that

* the family of sets `support (f i)` is locally finite;
* for each `x ∈ s`, the sum `∑ᶠ i, f i x` equals one;
* for each `x`, the sum `∑ᶠ i, f i x` is less than or equal to one.

We say that `f : smooth_bump_covering ι I M s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `tsupport (f i) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.

We prove that on a smooth finitely dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering ι I M s`
subordinate to `U`. Then we use this fact to prove a similar statement about smooth partitions of
unity, see `smooth_partition_of_unity.exists_is_subordinate`.

Finally, we use existence of a partition of unity to prove lemma
`exists_smooth_forall_mem_convex_of_local` that allows us to construct a globally defined smooth
function from local functions.

## TODO

* Build a framework for to transfer local definitions to global using partition of unity and use it
  to define, e.g., the integral of a differential form over a manifold. Lemma
  `exists_smooth_forall_mem_convex_of_local` is a first step in this direction.

## Tags

smooth bump function, partition of unity
-/


universe uι uE uH uM uF

open Function Filter FiniteDimensional Set

open TopologicalSpace Manifold Classical Filter BigOperators

noncomputable section

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-!
### Covering by supports of smooth bump functions

In this section we define `smooth_bump_covering ι I M s` to be a collection of
`smooth_bump_function`s such that their supports is a locally finite family of sets and for each `x
∈ s` some function `f i` from the collection is equal to `1` in a neighborhood of `x`. A covering of
this type is useful to construct a smooth partition of unity and can be used instead of a partition
of unity in some proofs.

We prove that on a smooth finite dimensional real manifold with `σ`-compact Hausdorff topology, for
any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering ι I M s`
subordinate to `U`. Then we use this fact to prove a version of the Whitney embedding theorem: any
compact real manifold can be embedded into `ℝ^n` for large enough `n`.  -/


variable (ι M)

/-- We say that a collection of `smooth_bump_function`s is a `smooth_bump_covering` of a set `s` if

* `(f i).c ∈ s` for all `i`;
* the family `λ i, support (f i)` is locally finite;
* for each point `x ∈ s` there exists `i` such that `f i =ᶠ[𝓝 x] 1`;
  in other words, `x` belongs to the interior of `{y | f i y = 1}`;

If `M` is a finite dimensional real manifold which is a `σ`-compact Hausdorff topological space,
then for every covering `U : M → set M`, `∀ x, U x ∈ 𝓝 x`, there exists a `smooth_bump_covering`
subordinate to `U`, see `smooth_bump_covering.exists_is_subordinate`.

This covering can be used, e.g., to construct a partition of unity and to prove the weak
Whitney embedding theorem. -/
@[nolint has_nonempty_instance]
structure SmoothBumpCovering (s : Set M := Univ) where
  c : ι → M
  toFun : ∀ i, SmoothBumpFunction I (c i)
  c_mem' : ∀ i, c i ∈ s
  locally_finite' : LocallyFinite fun i => Support (to_fun i)
  eventually_eq_one' : ∀ x ∈ s, ∃ i, to_fun i =ᶠ[𝓝 x] 1

/-- We say that that a collection of functions form a smooth partition of unity on a set `s` if

* all functions are infinitely smooth and nonnegative;
* the family `λ i, support (f i)` is locally finite;
* for all `x ∈ s` the sum `∑ᶠ i, f i x` equals one;
* for all `x`, the sum `∑ᶠ i, f i x` is less than or equal to one. -/
structure SmoothPartitionOfUnity (s : Set M := Univ) where
  toFun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯
  locally_finite' : LocallyFinite fun i => Support (to_fun i)
  nonneg' : ∀ i x, 0 ≤ to_fun i x
  sum_eq_one' : ∀ x ∈ s, (∑ᶠ i, to_fun i x) = 1
  sum_le_one' : ∀ x, (∑ᶠ i, to_fun i x) ≤ 1

variable {ι I M}

namespace SmoothPartitionOfUnity

variable {s : Set M} (f : SmoothPartitionOfUnity ι I M s) {n : WithTop ℕ}

instance {s : Set M} : CoeFun (SmoothPartitionOfUnity ι I M s) fun _ => ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ :=
  ⟨SmoothPartitionOfUnity.toFun⟩

protected theorem locally_finite : LocallyFinite fun i => Support (f i) :=
  f.locally_finite'

theorem nonneg (i : ι) (x : M) : 0 ≤ f i x :=
  f.nonneg' i x

theorem sum_eq_one {x} (hx : x ∈ s) : (∑ᶠ i, f i x) = 1 :=
  f.sum_eq_one' x hx

theorem sum_le_one (x : M) : (∑ᶠ i, f i x) ≤ 1 :=
  f.sum_le_one' x

/-- Reinterpret a smooth partition of unity as a continuous partition of unity. -/
def toPartitionOfUnity : PartitionOfUnity ι M s :=
  { f with toFun := fun i => f i }

theorem smooth_sum : Smooth I 𝓘(ℝ) fun x => ∑ᶠ i, f i x :=
  smooth_finsum (fun i => (f i).Smooth) f.LocallyFinite

theorem le_one (i : ι) (x : M) : f i x ≤ 1 :=
  f.toPartitionOfUnity.le_one i x

theorem sum_nonneg (x : M) : 0 ≤ ∑ᶠ i, f i x :=
  f.toPartitionOfUnity.sum_nonneg x

theorem cont_mdiff_smul {g : M → F} {i} (hg : ∀ x ∈ Tsupport (f i), ContMdiffAt I 𝓘(ℝ, F) n g x) :
    ContMdiff I 𝓘(ℝ, F) n fun x => f i x • g x :=
  cont_mdiff_of_support fun x hx =>
    ((f i).ContMdiff.ContMdiffAt.of_le le_top).smul <| hg x <| tsupport_smul_subset_left _ _ hx

theorem smooth_smul {g : M → F} {i} (hg : ∀ x ∈ Tsupport (f i), SmoothAt I 𝓘(ℝ, F) g x) :
    Smooth I 𝓘(ℝ, F) fun x => f i x • g x :=
  f.cont_mdiff_smul hg

/-- If `f` is a smooth partition of unity on a set `s : set M` and `g : ι → M → F` is a family of
functions such that `g i` is $C^n$ smooth at every point of the topological support of `f i`, then
the sum `λ x, ∑ᶠ i, f i x • g i x` is smooth on the whole manifold. -/
theorem cont_mdiff_finsum_smul {g : ι → M → F} (hg : ∀ (i), ∀ x ∈ Tsupport (f i), ContMdiffAt I 𝓘(ℝ, F) n (g i) x) :
    ContMdiff I 𝓘(ℝ, F) n fun x => ∑ᶠ i, f i x • g i x :=
  (cont_mdiff_finsum fun i => f.cont_mdiff_smul (hg i)) <| f.LocallyFinite.Subset fun i => support_smul_subset_left _ _

/-- If `f` is a smooth partition of unity on a set `s : set M` and `g : ι → M → F` is a family of
functions such that `g i` is smooth at every point of the topological support of `f i`, then the sum
`λ x, ∑ᶠ i, f i x • g i x` is smooth on the whole manifold. -/
theorem smooth_finsum_smul {g : ι → M → F} (hg : ∀ (i), ∀ x ∈ Tsupport (f i), SmoothAt I 𝓘(ℝ, F) (g i) x) :
    Smooth I 𝓘(ℝ, F) fun x => ∑ᶠ i, f i x • g i x :=
  f.cont_mdiff_finsum_smul hg

theorem finsum_smul_mem_convex {g : ι → M → F} {t : Set F} {x : M} (hx : x ∈ s) (hg : ∀ i, f i x ≠ 0 → g i x ∈ t)
    (ht : Convex ℝ t) : (∑ᶠ i, f i x • g i x) ∈ t :=
  ht.finsum_mem (fun i => f.Nonneg _ _) (f.sum_eq_one hx) hg

/-- A smooth partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same
type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def IsSubordinate (f : SmoothPartitionOfUnity ι I M s) (U : ι → Set M) :=
  ∀ i, Tsupport (f i) ⊆ U i

variable {f} {U : ι → Set M}

@[simp]
theorem is_subordinate_to_partition_of_unity : f.toPartitionOfUnity.IsSubordinate U ↔ f.IsSubordinate U :=
  Iff.rfl

alias is_subordinate_to_partition_of_unity ↔ _ is_subordinate.to_partition_of_unity

/-- If `f` is a smooth partition of unity on a set `s : set M` subordinate to a family of open sets
`U : ι → set M` and `g : ι → M → F` is a family of functions such that `g i` is $C^n$ smooth on
`U i`, then the sum `λ x, ∑ᶠ i, f i x • g i x` is $C^n$ smooth on the whole manifold. -/
theorem IsSubordinate.cont_mdiff_finsum_smul {g : ι → M → F} (hf : f.IsSubordinate U) (ho : ∀ i, IsOpen (U i))
    (hg : ∀ i, ContMdiffOn I 𝓘(ℝ, F) n (g i) (U i)) : ContMdiff I 𝓘(ℝ, F) n fun x => ∑ᶠ i, f i x • g i x :=
  f.cont_mdiff_finsum_smul fun i x hx => (hg i).ContMdiffAt <| (ho i).mem_nhds (hf i hx)

/-- If `f` is a smooth partition of unity on a set `s : set M` subordinate to a family of open sets
`U : ι → set M` and `g : ι → M → F` is a family of functions such that `g i` is smooth on `U i`,
then the sum `λ x, ∑ᶠ i, f i x • g i x` is smooth on the whole manifold. -/
theorem IsSubordinate.smooth_finsum_smul {g : ι → M → F} (hf : f.IsSubordinate U) (ho : ∀ i, IsOpen (U i))
    (hg : ∀ i, SmoothOn I 𝓘(ℝ, F) (g i) (U i)) : Smooth I 𝓘(ℝ, F) fun x => ∑ᶠ i, f i x • g i x :=
  hf.cont_mdiff_finsum_smul ho hg

end SmoothPartitionOfUnity

namespace BumpCovering

-- Repeat variables to drop [finite_dimensional ℝ E] and [smooth_manifold_with_corners I M]
theorem smooth_to_partition_of_unity {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type uH}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
    (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) (i : ι) : Smooth I 𝓘(ℝ) (f.toPartitionOfUnity i) :=
  (hf i).mul <|
    (smooth_finprod_cond fun j _ => smooth_const.sub (hf j)) <| by
      simp only [mul_support_one_sub]
      exact f.locally_finite

variable {s : Set M}

/-- A `bump_covering` such that all functions in this covering are smooth generates a smooth
partition of unity.

In our formalization, not every `f : bump_covering ι M s` with smooth functions `f i` is a
`smooth_bump_covering`; instead, a `smooth_bump_covering` is a covering by supports of
`smooth_bump_function`s. So, we define `bump_covering.to_smooth_partition_of_unity`, then reuse it
in `smooth_bump_covering.to_smooth_partition_of_unity`. -/
def toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) :
    SmoothPartitionOfUnity ι I M s :=
  { f.toPartitionOfUnity with toFun := fun i => ⟨f.toPartitionOfUnity i, f.smooth_to_partition_of_unity hf i⟩ }

@[simp]
theorem to_smooth_partition_of_unity_to_partition_of_unity (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) :
    (f.toSmoothPartitionOfUnity hf).toPartitionOfUnity = f.toPartitionOfUnity :=
  rfl

@[simp]
theorem coe_to_smooth_partition_of_unity (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) (i : ι) :
    ⇑(f.toSmoothPartitionOfUnity hf i) = f.toPartitionOfUnity i :=
  rfl

theorem IsSubordinate.to_smooth_partition_of_unity {f : BumpCovering ι M s} {U : ι → Set M} (h : f.IsSubordinate U)
    (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) : (f.toSmoothPartitionOfUnity hf).IsSubordinate U :=
  h.toPartitionOfUnity

end BumpCovering

namespace SmoothBumpCovering

variable {s : Set M} {U : M → Set M} (fs : SmoothBumpCovering ι I M s) {I}

instance : CoeFun (SmoothBumpCovering ι I M s) fun x => ∀ i : ι, SmoothBumpFunction I (x.c i) :=
  ⟨toFun⟩

@[simp]
theorem coe_mk (c : ι → M) (to_fun : ∀ i, SmoothBumpFunction I (c i)) (h₁ h₂ h₃) :
    ⇑(mk c to_fun h₁ h₂ h₃ : SmoothBumpCovering ι I M s) = to_fun :=
  rfl

/-- We say that `f : smooth_bump_covering ι I M s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `tsupport (f i) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.
-/
def IsSubordinate {s : Set M} (f : SmoothBumpCovering ι I M s) (U : M → Set M) :=
  ∀ i, Tsupport (f i) ⊆ U (f.c i)

theorem IsSubordinate.support_subset {fs : SmoothBumpCovering ι I M s} {U : M → Set M} (h : fs.IsSubordinate U)
    (i : ι) : Support (fs i) ⊆ U (fs.c i) :=
  Subset.trans subset_closure (h i)

variable (I)

/-- Let `M` be a smooth manifold with corners modelled on a finite dimensional real vector space.
Suppose also that `M` is a Hausdorff `σ`-compact topological space. Let `s` be a closed set
in `M` and `U : M → set M` be a collection of sets such that `U x ∈ 𝓝 x` for every `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`. -/
theorem exists_is_subordinate [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s) (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ (ι : Type uM)(f : SmoothBumpCovering ι I M s), f.IsSubordinate U := by
  -- First we deduce some missing instances
  haveI : LocallyCompactSpace H := I.locally_compact
  haveI : LocallyCompactSpace M := ChartedSpace.locally_compact H M
  haveI : NormalSpace M := normal_of_paracompact_t2
  -- Next we choose a covering by supports of smooth bump functions
  have hB := fun x hx => SmoothBumpFunction.nhds_basis_support I (hU x hx)
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis_set hs hB with ⟨ι, c, f, hf, hsub', hfin⟩
  choose hcs hfU using hf
  -- Then we use the shrinking lemma to get a covering by smaller open
  rcases exists_subset_Union_closed_subset hs (fun i => (f i).open_support) (fun x hx => hfin.point_finite x) hsub' with
    ⟨V, hsV, hVc, hVf⟩
  choose r hrR hr using fun i => (f i).exists_r_pos_lt_subset_ball (hVc i) (hVf i)
  refine' ⟨ι, ⟨c, fun i => (f i).updateR (r i) (hrR i), hcs, _, fun x hx => _⟩, fun i => _⟩
  · simpa only [SmoothBumpFunction.support_update_r]
    
  · refine' (mem_Union.1 <| hsV hx).imp fun i hi => _
    exact ((f i).updateR _ _).eventually_eq_one_of_dist_lt ((f i).support_subset_source <| hVf _ hi) (hr i hi).2
    
  · simpa only [coe_mk, SmoothBumpFunction.support_update_r, Tsupport] using hfU i
    

variable {I M}

protected theorem locally_finite : LocallyFinite fun i => Support (fs i) :=
  fs.locally_finite'

protected theorem point_finite (x : M) : { i | fs i x ≠ 0 }.Finite :=
  fs.LocallyFinite.point_finite x

theorem mem_chart_at_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) : x ∈ (chartAt H (fs.c i)).Source :=
  (fs i).support_subset_source <| by
    simp [h]

theorem mem_ext_chart_at_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) : x ∈ (extChartAt I (fs.c i)).Source := by
  rw [ext_chart_at_source]
  exact fs.mem_chart_at_source_of_eq_one h

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : M) (hx : x ∈ s) : ι :=
  (fs.eventually_eq_one' x hx).some

theorem eventually_eq_one (x : M) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
  (fs.eventually_eq_one' x hx).some_spec

theorem apply_ind (x : M) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
  (fs.eventually_eq_one x hx).eq_of_nhds

theorem mem_support_ind (x : M) (hx : x ∈ s) : x ∈ Support (fs <| fs.ind x hx) := by
  simp [fs.apply_ind x hx]

theorem mem_chart_at_ind_source (x : M) (hx : x ∈ s) : x ∈ (chartAt H (fs.c (fs.ind x hx))).Source :=
  fs.mem_chart_at_source_of_eq_one (fs.apply_ind x hx)

theorem mem_ext_chart_at_ind_source (x : M) (hx : x ∈ s) : x ∈ (extChartAt I (fs.c (fs.ind x hx))).Source :=
  fs.mem_ext_chart_at_source_of_eq_one (fs.apply_ind x hx)

/-- The index type of a `smooth_bump_covering` of a compact manifold is finite. -/
protected def fintype [CompactSpace M] : Fintype ι :=
  fs.LocallyFinite.fintypeOfCompact fun i => (fs i).nonempty_support

variable [T2Space M]

/-- Reinterpret a `smooth_bump_covering` as a continuous `bump_covering`. Note that not every
`f : bump_covering ι M s` with smooth functions `f i` is a `smooth_bump_covering`. -/
def toBumpCovering : BumpCovering ι M s where
  toFun := fun i => ⟨fs i, (fs i).Continuous⟩
  locally_finite' := fs.LocallyFinite
  nonneg' := fun i x => (fs i).Nonneg
  le_one' := fun i x => (fs i).le_one
  eventually_eq_one' := fs.eventually_eq_one'

@[simp]
theorem is_subordinate_to_bump_covering {f : SmoothBumpCovering ι I M s} {U : M → Set M} :
    (f.toBumpCovering.IsSubordinate fun i => U (f.c i)) ↔ f.IsSubordinate U :=
  Iff.rfl

alias is_subordinate_to_bump_covering ↔ _ is_subordinate.to_bump_covering

/-- Every `smooth_bump_covering` defines a smooth partition of unity. -/
def toSmoothPartitionOfUnity : SmoothPartitionOfUnity ι I M s :=
  fs.toBumpCovering.toSmoothPartitionOfUnity fun i => (fs i).Smooth

theorem to_smooth_partition_of_unity_apply (i : ι) (x : M) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ᶠ (j) (hj : WellOrderingRel j i), 1 - fs j x :=
  rfl

theorem to_smooth_partition_of_unity_eq_mul_prod (i : ι) (x : M) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → fs j x ≠ 0 → j ∈ t) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ j in t.filter fun j => WellOrderingRel j i, 1 - fs j x :=
  fs.toBumpCovering.to_partition_of_unity_eq_mul_prod i x t ht

theorem exists_finset_to_smooth_partition_of_unity_eventually_eq (i : ι) (x : M) :
    ∃ t : Finset ι,
      fs.toSmoothPartitionOfUnity i =ᶠ[𝓝 x] fs i * ∏ j in t.filter fun j => WellOrderingRel j i, 1 - fs j :=
  fs.toBumpCovering.exists_finset_to_partition_of_unity_eventually_eq i x

theorem to_smooth_partition_of_unity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) :
    fs.toSmoothPartitionOfUnity i x = 0 :=
  fs.toBumpCovering.to_partition_of_unity_zero_of_zero h

theorem support_to_smooth_partition_of_unity_subset (i : ι) :
    Support (fs.toSmoothPartitionOfUnity i) ⊆ Support (fs i) :=
  fs.toBumpCovering.support_to_partition_of_unity_subset i

theorem IsSubordinate.to_smooth_partition_of_unity {f : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : f.IsSubordinate U) : f.toSmoothPartitionOfUnity.IsSubordinate fun i => U (f.c i) :=
  h.toBumpCovering.toPartitionOfUnity

theorem sum_to_smooth_partition_of_unity_eq (x : M) : (∑ᶠ i, fs.toSmoothPartitionOfUnity i x) = 1 - ∏ᶠ i, 1 - fs i x :=
  fs.toBumpCovering.sum_to_partition_of_unity_eq x

end SmoothBumpCovering

variable (I)

/-- Given two disjoint closed sets in a Hausdorff σ-compact finite dimensional manifold, there
exists an infinitely smooth function that is equal to `0` on one of them and is equal to one on the
other. -/
theorem exists_smooth_zero_one_of_closed [T2Space M] [SigmaCompactSpace M] {s t : Set M} (hs : IsClosed s)
    (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  have : ∀ x ∈ t, sᶜ ∈ 𝓝 x := fun x hx => hs.is_open_compl.mem_nhds (disjoint_right.1 hd hx)
  rcases SmoothBumpCovering.exists_is_subordinate I ht this with ⟨ι, f, hf⟩
  set g := f.to_smooth_partition_of_unity
  refine' ⟨⟨_, g.smooth_sum⟩, fun x hx => _, fun x => g.sum_eq_one, fun x => ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩
  suffices ∀ i, g i x = 0 by
    simp only [this, ContMdiffMap.coe_fn_mk, finsum_zero, Pi.zero_apply]
  refine' fun i => f.to_smooth_partition_of_unity_zero_of_zero _
  exact nmem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)

namespace SmoothPartitionOfUnity

/-- A `smooth_partition_of_unity` that consists of a single function, uniformly equal to one,
defined as an example for `inhabited` instance. -/
def single (i : ι) (s : Set M) : SmoothPartitionOfUnity ι I M s :=
  (BumpCovering.single i s).toSmoothPartitionOfUnity fun j => by
    rcases eq_or_ne j i with (rfl | h)
    · simp only [smooth_one, ContinuousMap.coe_one, BumpCovering.coe_single, Pi.single_eq_same]
      
    · simp only [smooth_zero, BumpCovering.coe_single, Pi.single_eq_of_ne h, ContinuousMap.coe_zero]
      

instance [Inhabited ι] (s : Set M) : Inhabited (SmoothPartitionOfUnity ι I M s) :=
  ⟨single I default s⟩

variable [T2Space M] [SigmaCompactSpace M]

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. -/
theorem exists_is_subordinate {s : Set M} (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) : ∃ f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U := by
  haveI : LocallyCompactSpace H := I.locally_compact
  haveI : LocallyCompactSpace M := ChartedSpace.locally_compact H M
  haveI : NormalSpace M := normal_of_paracompact_t2
  rcases BumpCovering.exists_is_subordinate_of_prop (Smooth I 𝓘(ℝ)) _ hs U ho hU with ⟨f, hf, hfU⟩
  · exact ⟨f.to_smooth_partition_of_unity hf, hfU.to_smooth_partition_of_unity hf⟩
    
  · intro s t hs ht hd
    rcases exists_smooth_zero_one_of_closed I hs ht hd with ⟨f, hf⟩
    exact ⟨f, f.smooth, hf⟩
    

end SmoothPartitionOfUnity

variable [SigmaCompactSpace M] [T2Space M] {t : M → Set F} {n : WithTop ℕ}

/-- Let `M` be a σ-compact Hausdorff finite dimensional topological manifold. Let `t : M → set F`
be a family of convex sets. Suppose that for each point `x : M` there exists a neighborhood
`U ∈ 𝓝 x` and a function `g : M → F` such that `g` is $C^n$ smooth on `U` and `g y ∈ t y` for all
`y ∈ U`. Then there exists a $C^n$ smooth function `g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x`
for all `x`. See also `exists_smooth_forall_mem_convex_of_local` and
`exists_smooth_forall_mem_convex_of_local_const`. -/
theorem exists_cont_mdiff_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ g : M → F, ContMdiffOn I 𝓘(ℝ, F) n g U ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x := by
  choose U hU g hgs hgt using Hloc
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_is_subordinate I is_closed_univ (fun x => Interior (U x)) (fun x => is_open_interior)
      fun x hx => mem_Union.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  refine'
    ⟨⟨fun x => ∑ᶠ i, f i x • g i x,
        (hf.cont_mdiff_finsum_smul fun i => is_open_interior) fun i => (hgs i).mono interior_subset⟩,
      fun x => f.finsum_smul_mem_convex (mem_univ x) (fun i hi => hgt _ _ _) (ht _)⟩
  exact interior_subset (hf _ <| subset_closure hi)

/-- Let `M` be a σ-compact Hausdorff finite dimensional topological manifold. Let `t : M → set F`
be a family of convex sets. Suppose that for each point `x : M` there exists a neighborhood
`U ∈ 𝓝 x` and a function `g : M → F` such that `g` is smooth on `U` and `g y ∈ t y` for all `y ∈ U`.
Then there exists a smooth function `g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x` for all `x`.
See also `exists_cont_mdiff_forall_mem_convex_of_local` and
`exists_smooth_forall_mem_convex_of_local_const`. -/
theorem exists_smooth_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ g : M → F, SmoothOn I 𝓘(ℝ, F) g U ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  exists_cont_mdiff_forall_mem_convex_of_local I ht Hloc

/-- Let `M` be a σ-compact Hausdorff finite dimensional topological manifold. Let `t : M → set F` be
a family of convex sets. Suppose that for each point `x : M` there exists a vector `c : F` such that
for all `y` in a neighborhood of `x` we have `c ∈ t y`. Then there exists a smooth function
`g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x` for all `x`.  See also
`exists_cont_mdiff_forall_mem_convex_of_local` and `exists_smooth_forall_mem_convex_of_local`. -/
theorem exists_smooth_forall_mem_convex_of_local_const (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ c : F, ∀ᶠ y in 𝓝 x, c ∈ t y) : ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  (exists_smooth_forall_mem_convex_of_local I ht) fun x =>
    let ⟨c, hc⟩ := Hloc x
    ⟨_, hc, fun _ => c, smooth_on_const, fun y => id⟩

/-- Let `M` be a smooth σ-compact manifold with extended distance. Let `K : ι → set M` be a locally
finite family of closed sets, let `U : ι → set M` be a family of open sets such that `K i ⊆ U i` for
all `i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that for any `i` and
`x ∈ K i`, we have `emetric.closed_ball x (δ x) ⊆ U i`. -/
theorem Emetric.exists_smooth_forall_closed_ball_subset {M} [EmetricSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M} (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, Emetric.ClosedBall x (Ennreal.ofReal (δ x)) ⊆ U i :=
  by
  simpa only [mem_inter_eq, forall_and_distrib, mem_preimage, mem_Inter, @forall_swap ι M] using
    exists_smooth_forall_mem_convex_of_local_const I Emetric.exists_forall_closed_ball_subset_aux₂
      (Emetric.exists_forall_closed_ball_subset_aux₁ hK hU hKU hfin)

/-- Let `M` be a smooth σ-compact manifold with a metric. Let `K : ι → set M` be a locally finite
family of closed sets, let `U : ι → set M` be a family of open sets such that `K i ⊆ U i` for all
`i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that for any `i` and `x ∈ K i`,
we have `metric.closed_ball x (δ x) ⊆ U i`. -/
theorem Metric.exists_smooth_forall_closed_ball_subset {M} [MetricSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M} (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, Metric.ClosedBall x (δ x) ⊆ U i := by
  rcases Emetric.exists_smooth_forall_closed_ball_subset I hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine' ⟨δ, hδ0, fun i x hx => _⟩
  rw [← Metric.emetric_closed_ball (hδ0 _).le]
  exact hδ i x hx

