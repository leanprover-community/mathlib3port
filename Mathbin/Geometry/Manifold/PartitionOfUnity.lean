import Mathbin.Geometry.Manifold.Algebra.Structures 
import Mathbin.Geometry.Manifold.BumpFunction 
import Mathbin.Topology.Paracompact 
import Mathbin.Topology.PartitionOfUnity 
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
index `i`, we have `closure (support (f i)) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.

We prove that on a smooth finitely dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering ι I M s`
subordinate to `U`. Then we use this fact to prove a similar statement about smooth partitions of
unity.

## Implementation notes



## TODO

* Build a framework for to transfer local definitions to global using partition of unity and use it
  to define, e.g., the integral of a differential form over a manifold.

## Tags

smooth bump function, partition of unity
-/


universe uι uE uH uM

open Function Filter FiniteDimensional Set

open_locale TopologicalSpace Manifold Classical Filter BigOperators

noncomputable theory

variable {ι : Type uι} {E : Type uE} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type uH}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

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

If `M` is a finite dimensional real manifold which is a sigma-compact Hausdorff topological space,
then for every covering `U : M → set M`, `∀ x, U x ∈ 𝓝 x`, there exists a `smooth_bump_covering`
subordinate to `U`, see `smooth_bump_covering.exists_is_subordinate`.

This covering can be used, e.g., to construct a partition of unity and to prove the weak
Whitney embedding theorem. -/
@[nolint has_inhabited_instance]
structure SmoothBumpCovering (s : Set M := univ) where 
  c : ι → M 
  toFun : ∀ i, SmoothBumpFunction I (c i)
  c_mem' : ∀ i, c i ∈ s 
  locally_finite' : LocallyFinite fun i => support (to_fun i)
  eventually_eq_one' : ∀ x _ : x ∈ s, ∃ i, to_fun i =ᶠ[𝓝 x] 1

/-- We say that that a collection of functions form a smooth partition of unity on a set `s` if

* all functions are infinitely smooth and nonnegative;
* the family `λ i, support (f i)` is locally finite;
* for all `x ∈ s` the sum `∑ᶠ i, f i x` equals one;
* for all `x`, the sum `∑ᶠ i, f i x` is less than or equal to one. -/
structure SmoothPartitionOfUnity (s : Set M := univ) where 
  toFun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯
  locally_finite' : LocallyFinite fun i => support (to_fun i)
  nonneg' : ∀ i x, 0 ≤ to_fun i x 
  sum_eq_one' : ∀ x _ : x ∈ s, (∑ᶠi, to_fun i x) = 1
  sum_le_one' : ∀ x, (∑ᶠi, to_fun i x) ≤ 1

variable {ι I M}

namespace SmoothPartitionOfUnity

variable {s : Set M} (f : SmoothPartitionOfUnity ι I M s)

instance {s : Set M} : CoeFun (SmoothPartitionOfUnity ι I M s) fun _ => ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ :=
  ⟨SmoothPartitionOfUnity.toFun⟩

protected theorem LocallyFinite : LocallyFinite fun i => support (f i) :=
  f.locally_finite'

theorem nonneg (i : ι) (x : M) : 0 ≤ f i x :=
  f.nonneg' i x

theorem sum_eq_one {x} (hx : x ∈ s) : (∑ᶠi, f i x) = 1 :=
  f.sum_eq_one' x hx

theorem sum_le_one (x : M) : (∑ᶠi, f i x) ≤ 1 :=
  f.sum_le_one' x

/-- Reinterpret a smooth partition of unity as a continuous partition of unity. -/
def to_partition_of_unity : PartitionOfUnity ι M s :=
  { f with toFun := fun i => f i }

theorem smooth_sum : Smooth I 𝓘(ℝ) fun x => ∑ᶠi, f i x :=
  smooth_finsum (fun i => (f i).Smooth) f.locally_finite

theorem le_one (i : ι) (x : M) : f i x ≤ 1 :=
  f.to_partition_of_unity.le_one i x

theorem sum_nonneg (x : M) : 0 ≤ ∑ᶠi, f i x :=
  f.to_partition_of_unity.sum_nonneg x

/-- A smooth partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same
type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def is_subordinate (f : SmoothPartitionOfUnity ι I M s) (U : ι → Set M) :=
  ∀ i, Closure (support (f i)) ⊆ U i

@[simp]
theorem is_subordinate_to_partition_of_unity {f : SmoothPartitionOfUnity ι I M s} {U : ι → Set M} :
  f.to_partition_of_unity.is_subordinate U ↔ f.is_subordinate U :=
  Iff.rfl

alias is_subordinate_to_partition_of_unity ↔ _ SmoothPartitionOfUnity.IsSubordinate.to_partition_of_unity

end SmoothPartitionOfUnity

namespace BumpCovering

theorem smooth_to_partition_of_unity {E : Type uE} [NormedGroup E] [NormedSpace ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
  (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) (i : ι) : Smooth I 𝓘(ℝ) (f.to_partition_of_unity i) :=
  (hf i).mul$
    (smooth_finprod_cond fun j _ => smooth_const.sub (hf j))$
      by 
        simp only [mul_support_one_sub]
        exact f.locally_finite

variable {s : Set M}

/-- A `bump_covering` such that all functions in this covering are smooth generates a smooth
partition of unity.

In our formalization, not every `f : bump_covering ι M s` with smooth functions `f i` is a
`smooth_bump_covering`; instead, a `smooth_bump_covering` is a covering by supports of
`smooth_bump_function`s. So, we define `bump_covering.to_smooth_partition_of_unity`, then reuse it
in `smooth_bump_covering.to_smooth_partition_of_unity`. -/
def to_smooth_partition_of_unity (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) :
  SmoothPartitionOfUnity ι I M s :=
  { f.to_partition_of_unity with toFun := fun i => ⟨f.to_partition_of_unity i, f.smooth_to_partition_of_unity hf i⟩ }

@[simp]
theorem to_smooth_partition_of_unity_to_partition_of_unity (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) :
  (f.to_smooth_partition_of_unity hf).toPartitionOfUnity = f.to_partition_of_unity :=
  rfl

@[simp]
theorem coe_to_smooth_partition_of_unity (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) (i : ι) :
  «expr⇑ » (f.to_smooth_partition_of_unity hf i) = f.to_partition_of_unity i :=
  rfl

theorem is_subordinate.to_smooth_partition_of_unity {f : BumpCovering ι M s} {U : ι → Set M} (h : f.is_subordinate U)
  (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) : (f.to_smooth_partition_of_unity hf).IsSubordinate U :=
  h.to_partition_of_unity

end BumpCovering

namespace SmoothBumpCovering

variable {s : Set M} {U : M → Set M} (fs : SmoothBumpCovering ι I M s) {I}

instance : CoeFun (SmoothBumpCovering ι I M s) fun x => ∀ i : ι, SmoothBumpFunction I (x.c i) :=
  ⟨to_fun⟩

@[simp]
theorem coe_mk (c : ι → M) (to_fun : ∀ i, SmoothBumpFunction I (c i)) h₁ h₂ h₃ :
  «expr⇑ » (mk c to_fun h₁ h₂ h₃ : SmoothBumpCovering ι I M s) = to_fun :=
  rfl

/--
We say that `f : smooth_bump_covering ι I M s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `closure (support (f i)) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.
-/
def is_subordinate {s : Set M} (f : SmoothBumpCovering ι I M s) (U : M → Set M) :=
  ∀ i, Closure (support$ f i) ⊆ U (f.c i)

theorem is_subordinate.support_subset {fs : SmoothBumpCovering ι I M s} {U : M → Set M} (h : fs.is_subordinate U)
  (i : ι) : support (fs i) ⊆ U (fs.c i) :=
  subset.trans subset_closure (h i)

variable (I)

-- error in Geometry.Manifold.PartitionOfUnity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Let `M` be a smooth manifold with corners modelled on a finite dimensional real vector space.
Suppose also that `M` is a Hausdorff `σ`-compact topological space. Let `s` be a closed set
in `M` and `U : M → set M` be a collection of sets such that `U x ∈ 𝓝 x` for every `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`. -/
theorem exists_is_subordinate
[t2_space M]
[sigma_compact_space M]
(hs : is_closed s)
(hU : ∀
 x «expr ∈ » s, «expr ∈ »(U x, expr𝓝() x)) : «expr∃ , »((ι : Type uM)
 (f : smooth_bump_covering ι I M s), f.is_subordinate U) :=
begin
  haveI [] [":", expr locally_compact_space H] [":=", expr I.locally_compact],
  haveI [] [":", expr locally_compact_space M] [":=", expr charted_space.locally_compact H],
  haveI [] [":", expr normal_space M] [":=", expr normal_of_paracompact_t2],
  have [ident hB] [] [":=", expr λ x hx, smooth_bump_function.nhds_basis_support I (hU x hx)],
  rcases [expr refinement_of_locally_compact_sigma_compact_of_nhds_basis_set hs hB, "with", "⟨", ident ι, ",", ident c, ",", ident f, ",", ident hf, ",", ident hsub', ",", ident hfin, "⟩"],
  choose [] [ident hcs] [ident hfU] ["using", expr hf],
  rcases [expr exists_subset_Union_closed_subset hs (λ
    i, (f i).open_support) (λ
    x hx, hfin.point_finite x) hsub', "with", "⟨", ident V, ",", ident hsV, ",", ident hVc, ",", ident hVf, "⟩"],
  choose [] [ident r] [ident hrR, ident hr] ["using", expr λ i, (f i).exists_r_pos_lt_subset_ball (hVc i) (hVf i)],
  refine [expr ⟨ι, ⟨c, λ i, (f i).update_r (r i) (hrR i), hcs, _, λ x hx, _⟩, λ i, _⟩],
  { simpa [] [] ["only"] ["[", expr smooth_bump_function.support_update_r, "]"] [] [] },
  { refine [expr «expr $ »(mem_Union.1, hsV hx).imp (λ i hi, _)],
    exact [expr ((f i).update_r _ _).eventually_eq_one_of_dist_lt «expr $ »((f i).support_subset_source, hVf _ hi) (hr i hi).2] },
  { simpa [] [] ["only"] ["[", expr coe_mk, ",", expr smooth_bump_function.support_update_r, "]"] [] ["using", expr hfU i] }
end

variable {I M}

protected theorem LocallyFinite : LocallyFinite fun i => support (fs i) :=
  fs.locally_finite'

protected theorem point_finite (x : M) : { i | fs i x ≠ 0 }.Finite :=
  fs.locally_finite.point_finite x

theorem mem_chart_at_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) : x ∈ (chart_at H (fs.c i)).Source :=
  (fs i).support_subset_source$
    by 
      simp [h]

theorem mem_ext_chart_at_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) : x ∈ (extChartAt I (fs.c i)).Source :=
  by 
    rw [ext_chart_at_source]
    exact fs.mem_chart_at_source_of_eq_one h

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : M) (hx : x ∈ s) : ι :=
  (fs.eventually_eq_one' x hx).some

theorem eventually_eq_one (x : M) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
  (fs.eventually_eq_one' x hx).some_spec

theorem apply_ind (x : M) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
  (fs.eventually_eq_one x hx).eq_of_nhds

theorem mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (fs$ fs.ind x hx) :=
  by 
    simp [fs.apply_ind x hx]

theorem mem_chart_at_ind_source (x : M) (hx : x ∈ s) : x ∈ (chart_at H (fs.c (fs.ind x hx))).Source :=
  fs.mem_chart_at_source_of_eq_one (fs.apply_ind x hx)

theorem mem_ext_chart_at_ind_source (x : M) (hx : x ∈ s) : x ∈ (extChartAt I (fs.c (fs.ind x hx))).Source :=
  fs.mem_ext_chart_at_source_of_eq_one (fs.apply_ind x hx)

/-- The index type of a `smooth_bump_covering` of a compact manifold is finite. -/
protected def Fintype [CompactSpace M] : Fintype ι :=
  fs.locally_finite.fintype_of_compact$ fun i => (fs i).nonempty_support

variable [T2Space M]

/-- Reinterpret a `smooth_bump_covering` as a continuous `bump_covering`. Note that not every
`f : bump_covering ι M s` with smooth functions `f i` is a `smooth_bump_covering`. -/
def to_bump_covering : BumpCovering ι M s :=
  { toFun := fun i => ⟨fs i, (fs i).Continuous⟩, locally_finite' := fs.locally_finite,
    nonneg' := fun i x => (fs i).Nonneg, le_one' := fun i x => (fs i).le_one,
    eventually_eq_one' := fs.eventually_eq_one' }

@[simp]
theorem is_subordinate_to_bump_covering {f : SmoothBumpCovering ι I M s} {U : M → Set M} :
  (f.to_bump_covering.is_subordinate fun i => U (f.c i)) ↔ f.is_subordinate U :=
  Iff.rfl

alias is_subordinate_to_bump_covering ↔ _ SmoothBumpCovering.IsSubordinate.to_bump_covering

/-- Every `smooth_bump_covering` defines a smooth partition of unity. -/
def to_smooth_partition_of_unity : SmoothPartitionOfUnity ι I M s :=
  fs.to_bump_covering.to_smooth_partition_of_unity fun i => (fs i).Smooth

theorem to_smooth_partition_of_unity_apply (i : ι) (x : M) :
  fs.to_smooth_partition_of_unity i x = fs i x*∏ᶠ(j : _)(hj : WellOrderingRel j i), 1 - fs j x :=
  rfl

theorem to_smooth_partition_of_unity_eq_mul_prod (i : ι) (x : M) (t : Finset ι)
  (ht : ∀ j, WellOrderingRel j i → fs j x ≠ 0 → j ∈ t) :
  fs.to_smooth_partition_of_unity i x = fs i x*∏j in t.filter fun j => WellOrderingRel j i, 1 - fs j x :=
  fs.to_bump_covering.to_partition_of_unity_eq_mul_prod i x t ht

theorem exists_finset_to_smooth_partition_of_unity_eventually_eq (i : ι) (x : M) :
  ∃ t : Finset ι,
    fs.to_smooth_partition_of_unity i =ᶠ[𝓝 x] fs i*∏j in t.filter fun j => WellOrderingRel j i, 1 - fs j :=
  fs.to_bump_covering.exists_finset_to_partition_of_unity_eventually_eq i x

theorem to_smooth_partition_of_unity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) :
  fs.to_smooth_partition_of_unity i x = 0 :=
  fs.to_bump_covering.to_partition_of_unity_zero_of_zero h

theorem support_to_smooth_partition_of_unity_subset (i : ι) :
  support (fs.to_smooth_partition_of_unity i) ⊆ support (fs i) :=
  fs.to_bump_covering.support_to_partition_of_unity_subset i

theorem is_subordinate.to_smooth_partition_of_unity {f : SmoothBumpCovering ι I M s} {U : M → Set M}
  (h : f.is_subordinate U) : f.to_smooth_partition_of_unity.is_subordinate fun i => U (f.c i) :=
  h.to_bump_covering.to_partition_of_unity

theorem sum_to_smooth_partition_of_unity_eq (x : M) :
  (∑ᶠi, fs.to_smooth_partition_of_unity i x) = 1 - ∏ᶠi, 1 - fs i x :=
  fs.to_bump_covering.sum_to_partition_of_unity_eq x

end SmoothBumpCovering

variable (I)

-- error in Geometry.Manifold.PartitionOfUnity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given two disjoint closed sets in a Hausdorff σ-compact finite dimensional manifold, there
exists an infinitely smooth function that is equal to `0` on one of them and is equal to one on the
other. -/
theorem exists_smooth_zero_one_of_closed
[t2_space M]
[sigma_compact_space M]
{s t : set M}
(hs : is_closed s)
(ht : is_closed t)
(hd : disjoint s t) : «expr∃ , »((f : «exprC^ ⟮ , ; , ⟯»(«expr∞»(), I, M, «expr𝓘( )»(exprℝ()), exprℝ())), «expr ∧ »(eq_on f 0 s, «expr ∧ »(eq_on f 1 t, ∀
   x, «expr ∈ »(f x, Icc (0 : exprℝ()) 1)))) :=
begin
  have [] [":", expr ∀ x «expr ∈ » t, «expr ∈ »(«expr ᶜ»(s), expr𝓝() x)] [],
  from [expr λ x hx, hs.is_open_compl.mem_nhds (disjoint_right.1 hd hx)],
  rcases [expr smooth_bump_covering.exists_is_subordinate I ht this, "with", "⟨", ident ι, ",", ident f, ",", ident hf, "⟩"],
  set [] [ident g] [] [":="] [expr f.to_smooth_partition_of_unity] [],
  refine [expr ⟨⟨_, g.smooth_sum⟩, λ x hx, _, λ x, g.sum_eq_one, λ x, ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩],
  suffices [] [":", expr ∀ i, «expr = »(g i x, 0)],
  by simp [] [] ["only"] ["[", expr this, ",", expr times_cont_mdiff_map.coe_fn_mk, ",", expr finsum_zero, ",", expr pi.zero_apply, "]"] [] [],
  refine [expr λ i, f.to_smooth_partition_of_unity_zero_of_zero _],
  exact [expr nmem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)]
end

variable {I}

namespace SmoothPartitionOfUnity

/-- A `smooth_partition_of_unity` that consists of a single function, uniformly equal to one,
defined as an example for `inhabited` instance. -/
def single (i : ι) (s : Set M) : SmoothPartitionOfUnity ι I M s :=
  (BumpCovering.single i s).toSmoothPartitionOfUnity$
    fun j =>
      by 
        rcases eq_or_ne j i with (rfl | h)
        ·
          simp only [smooth_one, ContinuousMap.coe_one, BumpCovering.coe_single, Pi.single_eq_same]
        ·
          simp only [smooth_zero, BumpCovering.coe_single, Pi.single_eq_of_ne h, ContinuousMap.coe_zero]

instance [Inhabited ι] (s : Set M) : Inhabited (SmoothPartitionOfUnity ι I M s) :=
  ⟨single (default ι) s⟩

variable [T2Space M] [SigmaCompactSpace M]

-- error in Geometry.Manifold.PartitionOfUnity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. -/
theorem exists_is_subordinate
{s : set M}
(hs : is_closed s)
(U : ι → set M)
(ho : ∀ i, is_open (U i))
(hU : «expr ⊆ »(s, «expr⋃ , »((i), U i))) : «expr∃ , »((f : smooth_partition_of_unity ι I M s), f.is_subordinate U) :=
begin
  haveI [] [":", expr locally_compact_space H] [":=", expr I.locally_compact],
  haveI [] [":", expr locally_compact_space M] [":=", expr charted_space.locally_compact H],
  haveI [] [":", expr normal_space M] [":=", expr normal_of_paracompact_t2],
  rcases [expr bump_covering.exists_is_subordinate_of_prop (smooth I «expr𝓘( )»(exprℝ())) _ hs U ho hU, "with", "⟨", ident f, ",", ident hf, ",", ident hfU, "⟩"],
  { exact [expr ⟨f.to_smooth_partition_of_unity hf, hfU.to_smooth_partition_of_unity hf⟩] },
  { intros [ident s, ident t, ident hs, ident ht, ident hd],
    rcases [expr exists_smooth_zero_one_of_closed I hs ht hd, "with", "⟨", ident f, ",", ident hf, "⟩"],
    exact [expr ⟨f, f.smooth, hf⟩] }
end

end SmoothPartitionOfUnity

