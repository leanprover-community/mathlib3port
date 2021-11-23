import Mathbin.MeasureTheory.Measure.Hausdorff

/-!
# Hausdorff dimension

The Hausdorff dimension of a set `X` in an (extended) metric space is the unique number
`dimH s : ℝ≥0∞` such that for any `d : ℝ≥0` we have

- `μH[d] s = 0` if `dimH s < d`, and
- `μH[d] s = ∞` if `d < dimH s`.

In this file we define `dimH s` to be the Hausdorff dimension of `s`, then prove some basic
properties of Hausdorff dimension.

## Main definitions

* `measure_theory.dimH`: the Hausdorff dimension of a set. For the Hausdorff dimension of the whole
  space we use `measure_theory.dimH (set.univ : set X)`.

## Main results

### Basic properties of Hausdorff dimension

* `hausdorff_measure_of_lt_dimH`, `dimH_le_of_hausdorff_measure_ne_top`,
  `le_dimH_of_hausdorff_measure_eq_top`, `hausdorff_measure_of_dimH_lt`, `measure_zero_of_dimH_lt`,
  `le_dimH_of_hausdorff_measure_ne_zero`, `dimH_of_hausdorff_measure_ne_zero_ne_top`: various forms
  of the characteristic property of the Hausdorff dimension;
* `dimH_union`: the Hausdorff dimension of the union of two sets is the maximum of their Hausdorff
  dimensions.
* `dimH_Union`, `dimH_bUnion`, `dimH_sUnion`: the Hausdorff dimension of a countable union of sets
  is the supremum of their Hausdorff dimensions;
* `dimH_empty`, `dimH_singleton`, `set.subsingleton.dimH_zero`, `set.countable.dimH_zero` : `dimH s
  = 0` whenever `s` is countable;

### (Pre)images under (anti)lipschitz and Hölder continuous maps

* `holder_with.dimH_image_le` etc: if `f : X → Y` is Hölder continuous with exponent `r > 0`, then
  for any `s`, `dimH (f '' s) ≤ dimH s / r`. We prove versions of this statement for `holder_with`,
  `holder_on_with`, and locally Hölder maps, as well as for `set.image` and `set.range`.
* `lipschitz_with.dimH_image_le` etc: Lipschitz continuous maps do not increase the Hausdorff
  dimension of sets.
* for a map that is known to be both Lipschitz and antilipschitz (e.g., for an `isometry` or
  a `continuous_linear_equiv`) we also prove `dimH (f '' s) = dimH s`.

### Hausdorff measure in `ℝⁿ`

* `real.dimH_of_nonempty_interior`: if `s` is a set in a finite dimensional real vector space `E`
  with nonempty interior, then the Hausdorff dimension of `s` is equal to the dimension of `E`.
* `dense_compl_of_dimH_lt_finrank`: if `s` is a set in a finite dimensional real vector space `E`
  with Hausdorff dimension strictly less than the dimension of `E`, the `s` has a dense complement.
* `times_cont_diff.dense_compl_range_of_finrank_lt_finrank`: the complement to the range of a `C¹`
  smooth map is dense provided that the dimension of the domain is strictly less than the dimension
  of the codomain.

## Notations

We use the following notation localized in `measure_theory`. It is defined in
`measure_theory.measure.hausdorff`.

- `μH[d]` : `measure_theory.measure.hausdorff_measure d`

## Implementation notes

* The definition of `dimH` explicitly uses `borel X` as a measurable space structure. This way we
  can formulate lemmas about Hausdorff dimension without assuming that the environment has a
  `[measurable_space X]` instance that is equal but possibly not defeq to `borel X`.

  Lemma `dimH_def` unfolds this definition using whatever `[measurable_space X]` instance we have in
  the environment (as long as it is equal to `borel X`).

* The definition `dimH` is irreducible; use API lemmas or `dimH_def` instead.

## Tags

Hausdorff measure, Hausdorff dimension, dimension
-/


open_locale MeasureTheory Ennreal Nnreal TopologicalSpace

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace FiniteDimensional Filter

variable{ι X Y : Type _}[EmetricSpace X][EmetricSpace Y]

-- error in Topology.MetricSpace.HausdorffDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Hausdorff dimension of a set in an (e)metric space. -/
@[irreducible]
noncomputable
def dimH (s : set X) : «exprℝ≥0∞»() :=
by letI [] [] [":=", expr borel X]; exact [expr «expr⨆ , »((d : «exprℝ≥0»())
  (hd : «expr = »(@hausdorff_measure X _ _ ⟨rfl⟩ d s, «expr∞»())), d)]

/-!
### Basic properties
-/


section Measurable

variable[MeasurableSpace X][BorelSpace X]

/-- Unfold the definition of `dimH` using `[measurable_space X] [borel_space X]` from the
environment. -/
theorem dimH_def (s : Set X) : dimH s = ⨆(d :  ℝ≥0 )(hd : μH[d] s = ∞), d :=
  by 
    (
      obtain rfl : ‹MeasurableSpace X› = borel X := BorelSpace.measurable_eq)
    rw [dimH]

theorem hausdorff_measure_of_lt_dimH {s : Set X} {d :  ℝ≥0 } (h : «expr↑ » d < dimH s) : μH[d] s = ∞ :=
  by 
    simp only [dimH_def, lt_supr_iff] at h 
    rcases h with ⟨d', hsd', hdd'⟩
    rw [Ennreal.coe_lt_coe, ←Nnreal.coe_lt_coe] at hdd' 
    exact top_unique (hsd' ▸ hausdorff_measure_mono hdd'.le _)

theorem dimH_le {s : Set X} {d : ℝ≥0∞} (H : ∀ d' :  ℝ≥0 , μH[d'] s = ∞ → «expr↑ » d' ≤ d) : dimH s ≤ d :=
  (dimH_def s).trans_le$ bsupr_le H

theorem dimH_le_of_hausdorff_measure_ne_top {s : Set X} {d :  ℝ≥0 } (h : μH[d] s ≠ ∞) : dimH s ≤ d :=
  le_of_not_ltₓ$ mt hausdorff_measure_of_lt_dimH h

theorem le_dimH_of_hausdorff_measure_eq_top {s : Set X} {d :  ℝ≥0 } (h : μH[d] s = ∞) : «expr↑ » d ≤ dimH s :=
  by 
    rw [dimH_def]
    exact le_bsupr d h

theorem hausdorff_measure_of_dimH_lt {s : Set X} {d :  ℝ≥0 } (h : dimH s < d) : μH[d] s = 0 :=
  by 
    rw [dimH_def] at h 
    rcases Ennreal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hsd', hd'd⟩
    rw [Ennreal.coe_lt_coe, ←Nnreal.coe_lt_coe] at hd'd 
    exact (hausdorff_measure_zero_or_top hd'd s).resolve_right fun h => hsd'.not_le (le_bsupr d' h)

theorem measure_zero_of_dimH_lt {μ : Measureₓ X} {d :  ℝ≥0 } (h : μ ≪ μH[d]) {s : Set X} (hd : dimH s < d) : μ s = 0 :=
  h$ hausdorff_measure_of_dimH_lt hd

theorem le_dimH_of_hausdorff_measure_ne_zero {s : Set X} {d :  ℝ≥0 } (h : μH[d] s ≠ 0) : «expr↑ » d ≤ dimH s :=
  le_of_not_ltₓ$ mt hausdorff_measure_of_dimH_lt h

theorem dimH_of_hausdorff_measure_ne_zero_ne_top {d :  ℝ≥0 } {s : Set X} (h : μH[d] s ≠ 0) (h' : μH[d] s ≠ ∞) :
  dimH s = d :=
  le_antisymmₓ (dimH_le_of_hausdorff_measure_ne_top h') (le_dimH_of_hausdorff_measure_ne_zero h)

end Measurable

-- error in Topology.MetricSpace.HausdorffDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[mono #[]] theorem dimH_mono {s t : set X} (h : «expr ⊆ »(s, t)) : «expr ≤ »(dimH s, dimH t) :=
begin
  letI [] [] [":=", expr borel X],
  haveI [] [":", expr borel_space X] [":=", expr ⟨rfl⟩],
  exact [expr dimH_le (λ
    d hd, «expr $ »(le_dimH_of_hausdorff_measure_eq_top, «expr $ »(top_unique, «expr ▸ »(hd, measure_mono h))))]
end

theorem dimH_subsingleton {s : Set X} (h : s.subsingleton) : dimH s = 0 :=
  by 
    simp [dimH, h.measure_zero]

alias dimH_subsingleton ← Set.Subsingleton.dimH_zero

@[simp]
theorem dimH_empty : dimH (∅ : Set X) = 0 :=
  subsingleton_empty.dimH_zero

@[simp]
theorem dimH_singleton (x : X) : dimH ({x} : Set X) = 0 :=
  subsingleton_singleton.dimH_zero

-- error in Topology.MetricSpace.HausdorffDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem dimH_Union [encodable ι] (s : ι → set X) : «expr = »(dimH «expr⋃ , »((i), s i), «expr⨆ , »((i), dimH (s i))) :=
begin
  letI [] [] [":=", expr borel X],
  haveI [] [":", expr borel_space X] [":=", expr ⟨rfl⟩],
  refine [expr le_antisymm «expr $ »(dimH_le, λ
    d hd, _) «expr $ »(supr_le, λ i, «expr $ »(dimH_mono, subset_Union _ _))],
  contrapose ["!"] [ident hd],
  have [] [":", expr ∀ i, «expr = »(«exprμH[ ]»(d) (s i), 0)] [],
  from [expr λ i, hausdorff_measure_of_dimH_lt ((le_supr (λ i, dimH (s i)) i).trans_lt hd)],
  rw [expr measure_Union_null this] [],
  exact [expr ennreal.zero_ne_top]
end

-- error in Topology.MetricSpace.HausdorffDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem dimH_bUnion
{s : set ι}
(hs : countable s)
(t : ι → set X) : «expr = »(dimH «expr⋃ , »((i «expr ∈ » s), t i), «expr⨆ , »((i «expr ∈ » s), dimH (t i))) :=
begin
  haveI [] [] [":=", expr hs.to_encodable],
  rw ["[", expr bUnion_eq_Union, ",", expr dimH_Union, ",", "<-", expr supr_subtype'', "]"] []
end

@[simp]
theorem dimH_sUnion {S : Set (Set X)} (hS : countable S) : dimH (⋃₀S) = ⨆(s : _)(_ : s ∈ S), dimH s :=
  by 
    rw [sUnion_eq_bUnion, dimH_bUnion hS]

@[simp]
theorem dimH_union (s t : Set X) : dimH (s ∪ t) = max (dimH s) (dimH t) :=
  by 
    rw [union_eq_Union, dimH_Union, supr_bool_eq, cond, cond, Ennreal.sup_eq_max]

theorem dimH_countable {s : Set X} (hs : countable s) : dimH s = 0 :=
  bUnion_of_singleton s ▸
    by 
      simp only [dimH_bUnion hs, dimH_singleton, Ennreal.supr_zero_eq_zero]

alias dimH_countable ← Set.Countable.dimH_zero

theorem dimH_finite {s : Set X} (hs : finite s) : dimH s = 0 :=
  hs.countable.dimH_zero

alias dimH_finite ← Set.Finite.dimH_zero

@[simp]
theorem dimH_coe_finset (s : Finset X) : dimH (s : Set X) = 0 :=
  s.finite_to_set.dimH_zero

alias dimH_coe_finset ← Finset.dimH_zero

/-!
### Hausdorff dimension as the supremum of local Hausdorff dimensions
-/


section 

variable[second_countable_topology X]

/-- If `r` is less than the Hausdorff dimension of a set `s` in an (extended) metric space with
second countable topology, then there exists a point `x ∈ s` such that every neighborhood
`t` of `x` within `s` has Hausdorff dimension greater than `r`. -/
theorem exists_mem_nhds_within_lt_dimH_of_lt_dimH {s : Set X} {r : ℝ≥0∞} (h : r < dimH s) :
  ∃ (x : _)(_ : x ∈ s), ∀ t _ : t ∈ 𝓝[s] x, r < dimH t :=
  by 
    contrapose! h 
    choose! t htx htr using h 
    rcases countable_cover_nhds_within htx with ⟨S, hSs, hSc, hSU⟩
    calc dimH s ≤ dimH (⋃(x : _)(_ : x ∈ S), t x) := dimH_mono hSU _ = ⨆(x : _)(_ : x ∈ S), dimH (t x) :=
      dimH_bUnion hSc _ _ ≤ r := bsupr_le fun x hx => htr x (hSs hx)

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over `x ∈ s` of the limit superiors of `dimH t` along
`(𝓝[s] x).lift' powerset`. -/
theorem bsupr_limsup_dimH (s : Set X) : (⨆(x : _)(_ : x ∈ s), limsup ((𝓝[s] x).lift' powerset) dimH) = dimH s :=
  by 
    refine' le_antisymmₓ (bsupr_le$ fun x hx => _) _
    ·
      refine'
        Limsup_le_of_le
          (by 
            inferAutoParam)
          (eventually_map.2 _)
      exact eventually_lift'_powerset.2 ⟨s, self_mem_nhds_within, fun t => dimH_mono⟩
    ·
      refine' le_of_forall_ge_of_dense fun r hr => _ 
      rcases exists_mem_nhds_within_lt_dimH_of_lt_dimH hr with ⟨x, hxs, hxr⟩
      refine' le_bsupr_of_le x hxs _ 
      rw [limsup_eq]
      refine' le_Inf fun b hb => _ 
      rcases eventually_lift'_powerset.1 hb with ⟨t, htx, ht⟩
      exact (hxr t htx).le.trans (ht t subset.rfl)

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over all `x` of the limit superiors of `dimH t` along
`(𝓝[s] x).lift' powerset`. -/
theorem supr_limsup_dimH (s : Set X) : (⨆x, limsup ((𝓝[s] x).lift' powerset) dimH) = dimH s :=
  by 
    refine' le_antisymmₓ (supr_le$ fun x => _) _
    ·
      refine'
        Limsup_le_of_le
          (by 
            inferAutoParam)
          (eventually_map.2 _)
      exact eventually_lift'_powerset.2 ⟨s, self_mem_nhds_within, fun t => dimH_mono⟩
    ·
      rw [←bsupr_limsup_dimH]
      exact bsupr_le_supr _ _

end 

/-!
### Hausdorff dimension and Hölder continuity
-/


variable{C K r :  ℝ≥0 }{f : X → Y}{s t : Set X}

-- error in Topology.MetricSpace.HausdorffDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is a Hölder continuous map with exponent `r > 0`, then `dimH (f '' s) ≤ dimH s / r`. -/
theorem holder_on_with.dimH_image_le
(h : holder_on_with C r f s)
(hr : «expr < »(0, r)) : «expr ≤ »(dimH «expr '' »(f, s), «expr / »(dimH s, r)) :=
begin
  letI [] [] [":=", expr borel X],
  haveI [] [":", expr borel_space X] [":=", expr ⟨rfl⟩],
  letI [] [] [":=", expr borel Y],
  haveI [] [":", expr borel_space Y] [":=", expr ⟨rfl⟩],
  refine [expr dimH_le (λ d hd, _)],
  have [] [] [":=", expr h.hausdorff_measure_image_le hr d.coe_nonneg],
  rw ["[", expr hd, ",", expr ennreal.coe_rpow_of_nonneg _ d.coe_nonneg, ",", expr top_le_iff, "]"] ["at", ident this],
  have [ident Hrd] [":", expr «expr = »(«exprμH[ ]»((«expr * »(r, d) : «exprℝ≥0»())) s, «expr⊤»())] [],
  { contrapose [] [ident this],
    exact [expr ennreal.mul_ne_top ennreal.coe_ne_top this] },
  rw ["[", expr ennreal.le_div_iff_mul_le, ",", expr mul_comm, ",", "<-", expr ennreal.coe_mul, "]"] [],
  exacts ["[", expr le_dimH_of_hausdorff_measure_eq_top Hrd, ",", expr or.inl (mt ennreal.coe_eq_zero.1 hr.ne'), ",", expr or.inl ennreal.coe_ne_top, "]"]
end

namespace HolderWith

/-- If `f : X → Y` is Hölder continuous with a positive exponent `r`, then the Hausdorff dimension
of the image of a set `s` is at most `dimH s / r`. -/
theorem dimH_image_le (h : HolderWith C r f) (hr : 0 < r) (s : Set X) : dimH (f '' s) ≤ dimH s / r :=
  (h.holder_on_with s).dimH_image_le hr

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then the Hausdorff dimension of its
range is at most the Hausdorff dimension of its domain divided by `r`. -/
theorem dimH_range_le (h : HolderWith C r f) (hr : 0 < r) : dimH (range f) ≤ dimH (univ : Set X) / r :=
  @image_univ _ _ f ▸ h.dimH_image_le hr univ

end HolderWith

/-- If `s` is a set in a space `X` with second countable topology and `f : X → Y` is Hölder
continuous in a neighborhood within `s` of every point `x ∈ s` with the same positive exponent `r`
but possibly different coefficients, then the Hausdorff dimension of the image `f '' s` is at most
the Hausdorff dimension of `s` divided by `r`. -/
theorem dimH_image_le_of_locally_holder_on [second_countable_topology X] {r :  ℝ≥0 } {f : X → Y} (hr : 0 < r)
  {s : Set X} (hf : ∀ x _ : x ∈ s, ∃ (C :  ℝ≥0 )(t : _)(_ : t ∈ 𝓝[s] x), HolderOnWith C r f t) :
  dimH (f '' s) ≤ dimH s / r :=
  by 
    choose! C t htn hC using hf 
    rcases countable_cover_nhds_within htn with ⟨u, hus, huc, huU⟩
    replace huU := inter_eq_self_of_subset_left huU 
    rw [inter_bUnion] at huU 
    rw [←huU, image_bUnion, dimH_bUnion huc, dimH_bUnion huc]
    simp only [Ennreal.supr_div]
    exact bsupr_le_bsupr fun x hx => ((hC x (hus hx)).mono (inter_subset_right _ _)).dimH_image_le hr

/-- If `f : X → Y` is Hölder continuous in a neighborhood of every point `x : X` with the same
positive exponent `r` but possibly different coefficients, then the Hausdorff dimension of the range
of `f` is at most the Hausdorff dimension of `X` divided by `r`. -/
theorem dimH_range_le_of_locally_holder_on [second_countable_topology X] {r :  ℝ≥0 } {f : X → Y} (hr : 0 < r)
  (hf : ∀ x : X, ∃ (C :  ℝ≥0 )(s : _)(_ : s ∈ 𝓝 x), HolderOnWith C r f s) : dimH (range f) ≤ dimH (univ : Set X) / r :=
  by 
    rw [←image_univ]
    refine' dimH_image_le_of_locally_holder_on hr fun x _ => _ 
    simpa only [exists_prop, nhds_within_univ] using hf x

/-!
### Hausdorff dimension and Lipschitz continuity
-/


/-- If `f : X → Y` is Lipschitz continuous on `s`, then `dimH (f '' s) ≤ dimH s`. -/
theorem LipschitzOnWith.dimH_image_le (h : LipschitzOnWith K f s) : dimH (f '' s) ≤ dimH s :=
  by 
    simpa using h.holder_on_with.dimH_image_le zero_lt_one

namespace LipschitzWith

/-- If `f` is a Lipschitz continuous map, then `dimH (f '' s) ≤ dimH s`. -/
theorem dimH_image_le (h : LipschitzWith K f) (s : Set X) : dimH (f '' s) ≤ dimH s :=
  (h.lipschitz_on_with s).dimH_image_le

/-- If `f` is a Lipschitz continuous map, then the Hausdorff dimension of its range is at most the
Hausdorff dimension of its domain. -/
theorem dimH_range_le (h : LipschitzWith K f) : dimH (range f) ≤ dimH (univ : Set X) :=
  @image_univ _ _ f ▸ h.dimH_image_le univ

end LipschitzWith

-- error in Topology.MetricSpace.HausdorffDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `s` is a set in an extended metric space `X` with second countable topology and `f : X → Y`
is Lipschitz in a neighborhood within `s` of every point `x ∈ s`, then the Hausdorff dimension of
the image `f '' s` is at most the Hausdorff dimension of `s`. -/
theorem dimH_image_le_of_locally_lipschitz_on
[second_countable_topology X]
{f : X → Y}
{s : set X}
(hf : ∀
 x «expr ∈ » s, «expr∃ , »((C : «exprℝ≥0»())
  (t «expr ∈ » «expr𝓝[ ] »(s, x)), lipschitz_on_with C f t)) : «expr ≤ »(dimH «expr '' »(f, s), dimH s) :=
begin
  have [] [":", expr ∀
   x «expr ∈ » s, «expr∃ , »((C : «exprℝ≥0»()) (t «expr ∈ » «expr𝓝[ ] »(s, x)), holder_on_with C 1 f t)] [],
  by simpa [] [] ["only"] ["[", expr holder_on_with_one, "]"] [] ["using", expr hf],
  simpa [] [] ["only"] ["[", expr ennreal.coe_one, ",", expr ennreal.div_one, "]"] [] ["using", expr dimH_image_le_of_locally_holder_on zero_lt_one this]
end

/-- If `f : X → Y` is Lipschitz in a neighborhood of each point `x : X`, then the Hausdorff
dimension of `range f` is at most the Hausdorff dimension of `X`. -/
theorem dimH_range_le_of_locally_lipschitz_on [second_countable_topology X] {f : X → Y}
  (hf : ∀ x : X, ∃ (C :  ℝ≥0 )(s : _)(_ : s ∈ 𝓝 x), LipschitzOnWith C f s) : dimH (range f) ≤ dimH (univ : Set X) :=
  by 
    rw [←image_univ]
    refine' dimH_image_le_of_locally_lipschitz_on fun x _ => _ 
    simpa only [exists_prop, nhds_within_univ] using hf x

namespace AntilipschitzWith

-- error in Topology.MetricSpace.HausdorffDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dimH_preimage_le (hf : antilipschitz_with K f) (s : set Y) : «expr ≤ »(dimH «expr ⁻¹' »(f, s), dimH s) :=
begin
  letI [] [] [":=", expr borel X],
  haveI [] [":", expr borel_space X] [":=", expr ⟨rfl⟩],
  letI [] [] [":=", expr borel Y],
  haveI [] [":", expr borel_space Y] [":=", expr ⟨rfl⟩],
  refine [expr dimH_le (λ d hd, le_dimH_of_hausdorff_measure_eq_top _)],
  have [] [] [":=", expr hf.hausdorff_measure_preimage_le d.coe_nonneg s],
  rw ["[", expr hd, ",", expr top_le_iff, "]"] ["at", ident this],
  contrapose ["!"] [ident this],
  exact [expr ennreal.mul_ne_top (by simp [] [] [] [] [] []) this]
end

theorem le_dimH_image (hf : AntilipschitzWith K f) (s : Set X) : dimH s ≤ dimH (f '' s) :=
  calc dimH s ≤ dimH (f ⁻¹' (f '' s)) := dimH_mono (subset_preimage_image _ _)
    _ ≤ dimH (f '' s) := hf.dimH_preimage_le _
    

end AntilipschitzWith

/-!
### Isometries preserve Hausdorff dimension
-/


theorem Isometry.dimH_image (hf : Isometry f) (s : Set X) : dimH (f '' s) = dimH s :=
  le_antisymmₓ (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)

namespace Isometric

@[simp]
theorem dimH_image (e : X ≃ᵢ Y) (s : Set X) : dimH (e '' s) = dimH s :=
  e.isometry.dimH_image s

@[simp]
theorem dimH_preimage (e : X ≃ᵢ Y) (s : Set Y) : dimH (e ⁻¹' s) = dimH s :=
  by 
    rw [←e.image_symm, e.symm.dimH_image]

theorem dimH_univ (e : X ≃ᵢ Y) : dimH (univ : Set X) = dimH (univ : Set Y) :=
  by 
    rw [←e.dimH_preimage univ, preimage_univ]

end Isometric

namespace ContinuousLinearEquiv

variable{𝕜 E F : Type _}[NondiscreteNormedField 𝕜][NormedGroup E][NormedSpace 𝕜 E][NormedGroup F][NormedSpace 𝕜 F]

@[simp]
theorem dimH_image (e : E ≃L[𝕜] F) (s : Set E) : dimH (e '' s) = dimH s :=
  le_antisymmₓ (e.lipschitz.dimH_image_le s)$
    by 
      simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)

@[simp]
theorem dimH_preimage (e : E ≃L[𝕜] F) (s : Set F) : dimH (e ⁻¹' s) = dimH s :=
  by 
    rw [←e.image_symm_eq_preimage, e.symm.dimH_image]

theorem dimH_univ (e : E ≃L[𝕜] F) : dimH (univ : Set E) = dimH (univ : Set F) :=
  by 
    rw [←e.dimH_preimage, preimage_univ]

end ContinuousLinearEquiv

/-!
### Hausdorff dimension in a real vector space
-/


namespace Real

variable{E : Type _}[Fintype ι][NormedGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]

-- error in Topology.MetricSpace.HausdorffDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dimH_ball_pi
(x : ι → exprℝ())
{r : exprℝ()}
(hr : «expr < »(0, r)) : «expr = »(dimH (metric.ball x r), fintype.card ι) :=
begin
  casesI [expr is_empty_or_nonempty ι] [],
  { rwa ["[", expr dimH_subsingleton, ",", expr eq_comm, ",", expr nat.cast_eq_zero, ",", expr fintype.card_eq_zero_iff, "]"] [],
    exact [expr λ x _ y _, subsingleton.elim x y] },
  { rw ["<-", expr ennreal.coe_nat] [],
    have [] [":", expr «expr = »(«exprμH[ ]»(fintype.card ι) (metric.ball x r), ennreal.of_real «expr ^ »(«expr * »(2, r), fintype.card ι))] [],
    by rw ["[", expr hausdorff_measure_pi_real, ",", expr real.volume_pi_ball _ hr, "]"] [],
    refine [expr dimH_of_hausdorff_measure_ne_zero_ne_top _ _]; rw ["[", expr nnreal.coe_nat_cast, ",", expr this, "]"] [],
    { simp [] [] [] ["[", expr pow_pos (mul_pos zero_lt_two hr), "]"] [] [] },
    { exact [expr ennreal.of_real_ne_top] } }
end

theorem dimH_ball_pi_fin {n : ℕ} (x : Finₓ n → ℝ) {r : ℝ} (hr : 0 < r) : dimH (Metric.Ball x r) = n :=
  by 
    rw [dimH_ball_pi x hr, Fintype.card_fin]

theorem dimH_univ_pi (ι : Type _) [Fintype ι] : dimH (univ : Set (ι → ℝ)) = Fintype.card ι :=
  by 
    simp only [←Metric.Union_ball_nat_succ (0 : ι → ℝ), dimH_Union, dimH_ball_pi _ (Nat.cast_add_one_pos _), supr_const]

theorem dimH_univ_pi_fin (n : ℕ) : dimH (univ : Set (Finₓ n → ℝ)) = n :=
  by 
    rw [dimH_univ_pi, Fintype.card_fin]

-- error in Topology.MetricSpace.HausdorffDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dimH_of_mem_nhds {x : E} {s : set E} (h : «expr ∈ »(s, expr𝓝() x)) : «expr = »(dimH s, finrank exprℝ() E) :=
begin
  have [ident e] [":", expr «expr ≃L[ ] »(E, exprℝ(), fin (finrank exprℝ() E) → exprℝ())] [],
  from [expr continuous_linear_equiv.of_finrank_eq (finite_dimensional.finrank_fin_fun exprℝ()).symm],
  rw ["<-", expr e.dimH_image] [],
  refine [expr le_antisymm _ _],
  { exact [expr (dimH_mono (subset_univ _)).trans_eq (dimH_univ_pi_fin _)] },
  { have [] [":", expr «expr ∈ »(«expr '' »(e, s), expr𝓝() (e x))] [],
    by { rw ["<-", expr e.map_nhds_eq] [],
      exact [expr image_mem_map h] },
    rcases [expr metric.nhds_basis_ball.mem_iff.1 this, "with", "⟨", ident r, ",", ident hr0, ",", ident hr, "⟩"],
    simpa [] [] ["only"] ["[", expr dimH_ball_pi_fin (e x) hr0, "]"] [] ["using", expr dimH_mono hr] }
end

theorem dimH_of_nonempty_interior {s : Set E} (h : (Interior s).Nonempty) : dimH s = finrank ℝ E :=
  let ⟨x, hx⟩ := h 
  dimH_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)

variable(E)

theorem dimH_univ_eq_finrank : dimH (univ : Set E) = finrank ℝ E :=
  dimH_of_mem_nhds (@univ_mem _ (𝓝 0))

theorem dimH_univ : dimH (univ : Set ℝ) = 1 :=
  by 
    rw [dimH_univ_eq_finrank ℝ, FiniteDimensional.finrank_self, Nat.cast_one]

end Real

variable{E F : Type _}[NormedGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedGroup F][NormedSpace ℝ F]

theorem dense_compl_of_dimH_lt_finrank {s : Set E} (hs : dimH s < finrank ℝ E) : Dense («expr ᶜ» s) :=
  by 
    refine' fun x => mem_closure_iff_nhds.2 fun t ht => ne_empty_iff_nonempty.1$ fun he => hs.not_le _ 
    rw [←diff_eq, diff_eq_empty] at he 
    rw [←Real.dimH_of_mem_nhds ht]
    exact dimH_mono he

/-!
### Hausdorff dimension and `C¹`-smooth maps

`C¹`-smooth maps are locally Lipschitz continuous, hence they do not increase the Hausdorff
dimension of sets.
-/


/-- Let `f` be a function defined on a finite dimensional real normed space. If `f` is `C¹`-smooth
on a convex set `s`, then the Hausdorff dimension of `f '' s` is less than or equal to the Hausdorff
dimension of `s`.

TODO: do we actually need `convex ℝ s`? -/
theorem TimesContDiffOn.dimH_image_le {f : E → F} {s t : Set E} (hf : TimesContDiffOn ℝ 1 f s) (hc : Convex ℝ s)
  (ht : t ⊆ s) : dimH (f '' t) ≤ dimH t :=
  dimH_image_le_of_locally_lipschitz_on$
    fun x hx =>
      let ⟨C, u, hu, hf⟩ := (hf x (ht hx)).exists_lipschitz_on_with hc
      ⟨C, u, nhds_within_mono _ ht hu, hf⟩

/-- The Hausdorff dimension of the range of a `C¹`-smooth function defined on a finite dimensional
real normed space is at most the dimension of its domain as a vector space over `ℝ`. -/
theorem TimesContDiff.dimH_range_le {f : E → F} (h : TimesContDiff ℝ 1 f) : dimH (range f) ≤ finrank ℝ E :=
  calc dimH (range f) = dimH (f '' univ) :=
    by 
      rw [image_univ]
    _ ≤ dimH (univ : Set E) := h.times_cont_diff_on.dimH_image_le convex_univ subset.rfl 
    _ = finrank ℝ E := Real.dimH_univ_eq_finrank E
    

/-- A particular case of Sard's Theorem. Let `f : E → F` be a map between finite dimensional real
vector spaces. Suppose that `f` is `C¹` smooth on a convex set `s` of Hausdorff dimension strictly
less than the dimension of `F`. Then the complement of the image `f '' s` is dense in `F`. -/
theorem TimesContDiffOn.dense_compl_image_of_dimH_lt_finrank [FiniteDimensional ℝ F] {f : E → F} {s t : Set E}
  (h : TimesContDiffOn ℝ 1 f s) (hc : Convex ℝ s) (ht : t ⊆ s) (htF : dimH t < finrank ℝ F) :
  Dense («expr ᶜ» (f '' t)) :=
  dense_compl_of_dimH_lt_finrank$ (h.dimH_image_le hc ht).trans_lt htF

/-- A particular case of Sard's Theorem. If `f` is a `C¹` smooth map from a real vector space to a
real vector space `F` of strictly larger dimension, then the complement of the range of `f` is dense
in `F`. -/
theorem TimesContDiff.dense_compl_range_of_finrank_lt_finrank [FiniteDimensional ℝ F] {f : E → F}
  (h : TimesContDiff ℝ 1 f) (hEF : finrank ℝ E < finrank ℝ F) : Dense («expr ᶜ» (range f)) :=
  dense_compl_of_dimH_lt_finrank$ h.dimH_range_le.trans_lt$ Ennreal.coe_nat_lt_coe_nat.2 hEF

