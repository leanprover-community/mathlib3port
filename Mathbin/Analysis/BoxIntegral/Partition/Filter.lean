import Mathbin.Analysis.BoxIntegral.Partition.SubboxInduction 
import Mathbin.Analysis.BoxIntegral.Partition.Split

/-!
# Filters used in box-based integrals

First we define a structure `box_integral.integration_params`. This structure will be used as an
argument in the definition of `box_integral.integral` in order to use the same definition for a few
well-known definitions of integrals based on partitions of a rectangular box into subboxes (Riemann
integral, Henstock-Kurzweil integral, and McShane integral).

This structure holds three boolean values (see below), and encodes eight different sets of
parameters; only four of these values are used somewhere in `mathlib`. Three of them correspond to
the integration theories listed above, and one is a generalization of the one-dimensional
Henstock-Kurzweil integral such that the divergence theorem works without additional integrability
assumptions.

Finally, for each set of parameters `l : box_integral.integration_params` and a rectangular box
`I : box_integral.box ι`, we define several `filter`s that will be used either in the definition of
the corresponding integral, or in the proofs of its properties. We equip
`box_integral.integration_params` with a `bounded_order` structure such that larger
`integration_params` produce larger filters.

## Main definitions

### Integration parameters

The structure `box_integral.integration_params` has 3 boolean fields with the following meaning:

* `bRiemann`: the value `tt` means that the filter corresponds to a Riemann-style integral, i.e. in
  the definition of integrability we require a constant upper estimate `r` on the size of boxes of a
  tagged partition; the value `ff` means that the estimate may depend on the position of the tag.

* `bHenstock`: the value `tt` means that we require that each tag belongs to its own closed box; the
  value `ff` means that we only require that tags belong to the ambient box.

* `bDistortion`: the value `tt` means that `r` can depend on the maximal ratio of sides of the same
  box of a partition. Presence of this case make quite a few proofs harder but we can prove the
  divergence theorem only for the filter `⊥ = {bRiemann := ff, bHenstock := tt, bDistortion := tt}`.

### Well-known sets of parameters

Out of eight possible values of `box_integral.integration_params`, the following four are used in
the library.

* `box_integral.integration_params.Riemann` (`bRiemann = tt`, `bHenstock = tt`, `bDistortion = ff`):
  this value corresponds to the Riemann integral; in the corresponding filter, we require that the
  diameters of all boxes `J` of a tagged partition are bounded from above by a constant upper
  estimate that may not depend on the geometry of `J`, and each tag belongs to the corresponding
  closed box.

* `box_integral.integration_params.Henstock` (`bRiemann = ff`, `bHenstock = tt`,
  `bDistortion = ff`): this value corresponds to the most natural generalization of
  Henstock-Kurzweil integral to higher dimension; the only (but important!) difference between this
  theory and Riemann integral is that instead of a constant upper estimate on the size of all boxes
  of a partition, we require that the partition is *subordinate* to a possibly discontinuous
  function `r : (ι → ℝ) → {x : ℝ | 0 < x}`, i.e. each box `J` is included in a closed ball with
  center `π.tag J` and radius `r J`.

* `box_integral.integration_params.McShane` (`bRiemann = ff`, `bHenstock = ff`, `bDistortion = ff`):
  this value corresponds to the McShane integral; the only difference with the Henstock integral is
  that we allow tags to be outside of their boxes; the tags still have to be in the ambient closed
  box, and the partition still has to be subordinate to a function.

* `⊥` (`bRiemann = ff`, `bHenstock = tt`, `bDistortion = tt`): this is the least integration theory
  in our list, i.e., all functions integrable in any other theory is integrable in this one as well.
  This is a non-standard generalization of the Henstock-Kurzweil integral to higher dimension.
  In dimension one, it generates the same filter as `Henstock`. In higher dimension, this
  generalization defines an integration theory such that the divergence of any Fréchet
  differentiable function `f` is integrable, and its integral is equal to the sum of integrals of
  `f` over the faces of the box, taken with appropriate signs.

  A function `f` is `⊥`-integrable if for any `ε > 0` and `c : ℝ≥0` there exists
  `r : (ι → ℝ) → {x : ℝ | 0 < x}` such that for any tagged partition `π` subordinate to `r`, if each
  tag belongs to the corresponding closed box and for each box `J ∈ π`, the maximal ratio of its
  sides is less than or equal to `c`, then the integral sum of `f` over `π` is `ε`-close to the
  integral.

### Filters and predicates on `tagged_prepartition I`

For each value of `integration_params` and a rectangular box `I`, we define a few filters on
`tagged_prepartition I`. First, we define a predicate

```
structure box_integral.integration_params.mem_base_set (l : box_integral.integration_params)
  (I : box_integral.box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
  (π : box_integral.tagged_prepartition I) : Prop :=
```

This predicate says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs to the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equal to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c` that covers
  exactly `I \ π.Union`.

The last condition is always true for `c > 1`, see TODO section for more details.

Then we define a predicate `box_integral.integration_params.r_cond` on functions
`r : (ι → ℝ) → {x : ℝ | 0 < x}`. If `l.bRiemann`, then this predicate requires `r` to be a constant
function, otherwise it imposes no restrictions on `r`. We introduce this definition to prove a few
dot-notation lemmas: e.g., `box_integral.integration_params.r_cond.min` says that the pointwise
minimum of two functions that satisfy this condition satisfies this condition as well.

Then we define four filters on `box_integral.tagged_prepartition I`.

* `box_integral.integration_params.to_filter_distortion`: an auxiliary filter that takes parameters
  `(l : box_integral.integration_params) (I : box_integral.box ι) (c : ℝ≥0)` and returns the
  filter generated by all sets `{π | mem_base_set l I c r π}`, where `r` is a function satisfying
  the predicate `box_integral.integration_params.r_cond l`;

* `box_integral.integration_params.to_filter l I`: the supremum of `l.to_filter_distortion I c`
  over all `c : ℝ≥0`;

* `box_integral.integration_params.to_filter_distortion_Union l I c π₀`, where `π₀` is a
  prepartition of `I`: the infimum of `l.to_filter_distortion I c` and the principal filter
  generated by `{π | π.Union = π₀.Union}`;

* `box_integral.integration_params.to_filter_Union l I π₀`: the supremum of
  `l.to_filter_distortion_Union l I c π₀` over all `c : ℝ≥0`. This is the filter (in the case
  `π₀ = ⊤` is the one-box partition of `I`) used in the definition of the integral of a function
  over a box.

## Implementation details

* Later we define the integral of a function over a rectangular box as the limit (if it exists) of
  the integral sums along `box_integral.integration_params.to_filter_Union l I ⊤`. While it is
  possible to define the integral with a general filter on `box_integral.tagged_prepartition I` as a
  parameter, many lemmas (e.g., Sacks-Henstock lemma and most results about integrability of
  functions) require the filter to have a predictable structure. So, instead of adding assumptions
  about the filter here and there, we define this auxiliary type that can encode all integration
  theories we need in practice.

* While the definition of the integral only uses the filter
  `box_integral.integration_params.to_filter_Union l I ⊤` and partitions of a box, some lemmas
  (e.g., the Henstock-Sacks lemmas) are best formulated in terms of the predicate `mem_base_set` and
  other filters defined above.

* We use `bool` instead of `Prop` for the fields of `integration_params` in order to have decidable
  equality and inequalities.

## TODO

Currently, `box_integral.integration_params.mem_base_set` explicitly requires that there exists a
partition of the complement `I \ π.Union` with distortion `≤ c`. For `c > 1`, this condition is
always true but the proof of this fact requires more API about
`box_integral.prepartition.split_many`. We should formalize this fact, then either require `c > 1`
everywhere, or replace `≤ c` with `< c` so that we automatically get `c > 1` for a non-trivial
prepartition (and consider the special case `π = ⊥` separately if needed).

## Tags

integral, rectangular box, partition, filter
-/


open Set Function Filter Metric Finset Bool

open_locale Classical TopologicalSpace Filter Nnreal

noncomputable theory

namespace BoxIntegral

variable{ι :
    Type _}[Fintype ι]{I J : box ι}{c c₁ c₂ :  ℝ≥0 }{r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}{π π₁ π₂ : tagged_prepartition I}

open TaggedPrepartition

/-- An `integration_params` is a structure holding 3 boolean values used to define a filter to be
used in the definition of a box-integrable function.

* `bRiemann`: the value `tt` means that the filter corresponds to a Riemann-style integral, i.e. in
  the definition of integrability we require a constant upper estimate `r` on the size of boxes of a
  tagged partition; the value `ff` means that the estimate may depend on the position of the tag.

* `bHenstock`: the value `tt` means that we require that each tag belongs to its own closed box; the
  value `ff` means that we only require that tags belong to the ambient box.

* `bDistortion`: the value `tt` means that `r` can depend on the maximal ratio of sides of the same
  box of a partition. Presence of this case makes quite a few proofs harder but we can prove the
  divergence theorem only for the filter `⊥ = {bRiemann := ff, bHenstock := tt, bDistortion := tt}`.
-/
@[ext]
structure integration_params : Type where 
  (bRiemann bHenstock bDistortion : Bool)

variable{l l₁ l₂ : integration_params}

namespace IntegrationParams

/-- Auxiliary equivalence with a product type used to lift an order. -/
def equiv_prod : integration_params ≃ Bool × OrderDual Bool × OrderDual Bool :=
  { toFun := fun l => ⟨l.1, OrderDual.toDual l.2, OrderDual.toDual l.3⟩,
    invFun := fun l => ⟨l.1, OrderDual.ofDual l.2.1, OrderDual.ofDual l.2.2⟩, left_inv := fun ⟨a, b, c⟩ => rfl,
    right_inv := fun ⟨a, b, c⟩ => rfl }

instance  : PartialOrderₓ integration_params :=
  PartialOrderₓ.lift equiv_prod equiv_prod.Injective

/-- Auxiliary `order_iso` with a product type used to lift a `bounded_order` structure. -/
def iso_prod : integration_params ≃o Bool × OrderDual Bool × OrderDual Bool :=
  ⟨equiv_prod, fun ⟨x, y, z⟩ => Iff.rfl⟩

instance  : BoundedOrder integration_params :=
  iso_prod.symm.toGaloisInsertion.liftBoundedOrder

/-- The value `⊥` (`bRiemann = ff`, `bHenstock = tt`, `bDistortion = tt`) corresponds to a
generalization of the Henstock integral such that the Divergence theorem holds true without
additional integrability assumptions, see the module docstring for details. -/
instance  : Inhabited integration_params :=
  ⟨⊥⟩

instance  : DecidableRel (· ≤ · : integration_params → integration_params → Prop) :=
  fun _ _ => And.decidable

instance  : DecidableEq integration_params :=
  fun x y => decidableOfIff _ (ext_iff x y).symm

/-- The `box_integral.integration_params` corresponding to the Riemann integral. In the
corresponding filter, we require that the diameters of all boxes `J` of a tagged partition are
bounded from above by a constant upper estimate that may not depend on the geometry of `J`, and each
tag belongs to the corresponding closed box. -/
def Riemann : integration_params :=
  { bRiemann := tt, bHenstock := tt, bDistortion := ff }

/-- The `box_integral.integration_params` corresponding to the Henstock-Kurzweil integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r` and each tag belongs to the corresponding closed box. -/
def Henstock : integration_params :=
  ⟨ff, tt, ff⟩

/-- The `box_integral.integration_params` corresponding to the McShane integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r`; the tags may be outside of the corresponding closed box
(but still inside the ambient closed box `I.Icc`). -/
def McShane : integration_params :=
  ⟨ff, ff, ff⟩

theorem Henstock_le_Riemann : Henstock ≤ Riemann :=
  by 
    decide

theorem Henstock_le_McShane : Henstock ≤ McShane :=
  by 
    decide

/-- The predicate corresponding to a base set of the filter defined by an
`integration_params`. It says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs to the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equal to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c` that covers
  exactly `I \ π.Union`.

The last condition is automatically verified for partitions, and is used in the proof of the
Sacks-Henstock inequality to compare two prepartitions covering the same part of the box.

It is also automatically satisfied for any `c > 1`, see TODO section of the module docstring for
details. -/
@[protectProj]
structure
  mem_base_set(l : integration_params)(I : box ι)(c :  ℝ≥0 )(r : (ι → ℝ) → Ioi (0 : ℝ))(π : tagged_prepartition I) :
  Prop where 
  IsSubordinate : π.is_subordinate r 
  IsHenstock : l.bHenstock → π.is_Henstock 
  distortion_le : l.bDistortion → π.distortion ≤ c 
  exists_compl : l.bDistortion → ∃ π' : prepartition I, π'.Union = I \ π.Union ∧ π'.distortion ≤ c

/-- A predicate saying that in case `l.bRiemann = tt`, the function `r` is a constant. -/
def r_cond {ι : Type _} (l : integration_params) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  l.bRiemann → ∀ x, r x = r 0

/-- A set `s : set (tagged_prepartition I)` belongs to `l.to_filter_distortion I c` if there exists
a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tt`) such that `s` contains each
prepartition `π` such that `l.mem_base_set I c r π`. -/
def to_filter_distortion (l : integration_params) (I : box ι) (c :  ℝ≥0 ) : Filter (tagged_prepartition I) :=
  ⨅(r : (ι → ℝ) → Ioi (0 : ℝ))(hr : l.r_cond r), 𝓟 { π | l.mem_base_set I c r π }

/-- A set `s : set (tagged_prepartition I)` belongs to `l.to_filter I` if for any `c : ℝ≥0` there
exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tt`) such that
`s` contains each prepartition `π` such that `l.mem_base_set I c r π`. -/
def to_filter (l : integration_params) (I : box ι) : Filter (tagged_prepartition I) :=
  ⨆c :  ℝ≥0 , l.to_filter_distortion I c

/-- A set `s : set (tagged_prepartition I)` belongs to `l.to_filter_distortion_Union I c π₀` if
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tt`) such that `s`
contains each prepartition `π` such that `l.mem_base_set I c r π` and `π.Union = π₀.Union`. -/
def to_filter_distortion_Union (l : integration_params) (I : box ι) (c :  ℝ≥0 ) (π₀ : prepartition I) :=
  l.to_filter_distortion I c⊓𝓟 { π | π.Union = π₀.Union }

/-- A set `s : set (tagged_prepartition I)` belongs to `l.to_filter_Union I π₀` if for any `c : ℝ≥0`
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tt`) such that `s`
contains each prepartition `π` such that `l.mem_base_set I c r π` and `π.Union = π₀.Union`. -/
def to_filter_Union (l : integration_params) (I : box ι) (π₀ : prepartition I) :=
  ⨆c :  ℝ≥0 , l.to_filter_distortion_Union I c π₀

theorem r_cond_of_bRiemann_eq_ff {ι} (l : integration_params) (hl : l.bRiemann = ff) {r : (ι → ℝ) → Ioi (0 : ℝ)} :
  l.r_cond r :=
  by 
    simp [r_cond, hl]

theorem to_filter_inf_Union_eq (l : integration_params) (I : box ι) (π₀ : prepartition I) :
  l.to_filter I⊓𝓟 { π | π.Union = π₀.Union } = l.to_filter_Union I π₀ :=
  (supr_inf_principal _ _).symm

theorem mem_base_set.mono' (I : box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) {π : tagged_prepartition I}
  (hr : ∀ J (_ : J ∈ π), r₁ (π.tag J) ≤ r₂ (π.tag J)) (hπ : l₁.mem_base_set I c₁ r₁ π) : l₂.mem_base_set I c₂ r₂ π :=
  ⟨hπ.1.mono' hr, fun h₂ => hπ.2 (le_iff_imp.1 h.2.1 h₂), fun hD => (hπ.3 (le_iff_imp.1 h.2.2 hD)).trans hc,
    fun hD => (hπ.4 (le_iff_imp.1 h.2.2 hD)).imp$ fun π hπ => ⟨hπ.1, hπ.2.trans hc⟩⟩

@[mono]
theorem mem_base_set.mono (I : box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) {π : tagged_prepartition I}
  (hr : ∀ x (_ : x ∈ I.Icc), r₁ x ≤ r₂ x) (hπ : l₁.mem_base_set I c₁ r₁ π) : l₂.mem_base_set I c₂ r₂ π :=
  hπ.mono' I h hc$ fun J hJ => hr _$ π.tag_mem_Icc J

theorem mem_base_set.exists_common_compl (h₁ : l.mem_base_set I c₁ r₁ π₁) (h₂ : l.mem_base_set I c₂ r₂ π₂)
  (hU : π₁.Union = π₂.Union) :
  ∃ π : prepartition I,
    π.Union = I \ π₁.Union ∧ (l.bDistortion → π.distortion ≤ c₁) ∧ (l.bDistortion → π.distortion ≤ c₂) :=
  by 
    wlog (discharger := tactic.skip) hc : c₁ ≤ c₂ := le_totalₓ c₁ c₂ using c₁ c₂ r₁ r₂ π₁ π₂, c₂ c₁ r₂ r₁ π₂ π₁
    ·
      byCases' hD : (l.bDistortion : Prop)
      ·
        rcases h₁.4 hD with ⟨π, hπU, hπc⟩
        exact ⟨π, hπU, fun _ => hπc, fun _ => hπc.trans hc⟩
      ·
        exact ⟨π₁.to_prepartition.compl, π₁.to_prepartition.Union_compl, fun h => (hD h).elim, fun h => (hD h).elim⟩
    ·
      intro h₁ h₂ hU 
      simpa [hU, and_comm] using this h₂ h₁ hU.symm

protected theorem mem_base_set.union_compl_to_subordinate (hπ₁ : l.mem_base_set I c r₁ π₁)
  (hle : ∀ x (_ : x ∈ I.Icc), r₂ x ≤ r₁ x) {π₂ : prepartition I} (hU : π₂.Union = I \ π₁.Union)
  (hc : l.bDistortion → π₂.distortion ≤ c) : l.mem_base_set I c r₁ (π₁.union_compl_to_subordinate π₂ hU r₂) :=
  ⟨hπ₁.1.disjUnion ((π₂.is_subordinate_to_subordinate r₂).mono hle) _,
    fun h => (hπ₁.2 h).disjUnion (π₂.is_Henstock_to_subordinate _) _,
    fun h => (distortion_union_compl_to_subordinate _ _ _ _).trans_le (max_leₓ (hπ₁.3 h) (hc h)),
    fun _ =>
      ⟨⊥,
        by 
          simp ⟩⟩

-- error in Analysis.BoxIntegral.Partition.Filter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem mem_base_set.filter
(hπ : l.mem_base_set I c r π)
(p : box ι → exprProp()) : l.mem_base_set I c r (π.filter p) :=
begin
  refine [expr ⟨λ
    J
    hJ, hπ.1 J (π.mem_filter.1 hJ).1, λ
    hH J hJ, hπ.2 hH J (π.mem_filter.1 hJ).1, λ hD, (distortion_filter_le _ _).trans (hπ.3 hD), λ hD, _⟩],
  rcases [expr hπ.4 hD, "with", "⟨", ident π₁, ",", ident hπ₁U, ",", ident hc, "⟩"],
  set [] [ident π₂] [] [":="] [expr π.filter (λ J, «expr¬ »(p J))] [],
  have [] [":", expr disjoint π₁.Union π₂.Union] [],
  by simpa [] [] [] ["[", expr π₂, ",", expr hπ₁U, "]"] [] ["using", expr (disjoint_diff.mono_left sdiff_le).symm],
  refine [expr ⟨π₁.disj_union π₂.to_prepartition this, _, _⟩],
  { suffices [] [":", expr «expr = »(«expr ∪ »(«expr \ »(«expr↑ »(I), π.Union), «expr \ »(π.Union, (π.filter p).Union)), «expr \ »(«expr↑ »(I), (π.filter p).Union))],
    by simpa [] [] [] ["*"] [] [],
    have [] [":", expr «expr ⊆ »((π.filter p).Union, π.Union)] [],
    from [expr bUnion_subset_bUnion_left (finset.filter_subset _ _)],
    ext [] [ident x] [],
    fsplit,
    { rintro ["(", "⟨", ident hxI, ",", ident hxπ, "⟩", "|", "⟨", ident hxπ, ",", ident hxp, "⟩", ")"],
      exacts ["[", expr ⟨hxI, mt (@this x) hxπ⟩, ",", expr ⟨π.Union_subset hxπ, hxp⟩, "]"] },
    { rintro ["⟨", ident hxI, ",", ident hxp, "⟩"],
      by_cases [expr hxπ, ":", expr «expr ∈ »(x, π.Union)],
      exacts ["[", expr or.inr ⟨hxπ, hxp⟩, ",", expr or.inl ⟨hxI, hxπ⟩, "]"] } },
  { have [] [":", expr «expr ≤ »((π.filter (λ J, «expr¬ »(p J))).distortion, c)] [],
    from [expr (distortion_filter_le _ _).trans (hπ.3 hD)],
    simpa [] [] [] ["[", expr hc, "]"] [] [] }
end

theorem bUnion_tagged_mem_base_set {π : prepartition I} {πi : ∀ J, tagged_prepartition J}
  (h : ∀ J (_ : J ∈ π), l.mem_base_set J c r (πi J)) (hp : ∀ J (_ : J ∈ π), (πi J).IsPartition)
  (hc : l.bDistortion → π.compl.distortion ≤ c) : l.mem_base_set I c r (π.bUnion_tagged πi) :=
  by 
    refine'
      ⟨tagged_prepartition.is_subordinate_bUnion_tagged.2$ fun J hJ => (h J hJ).1,
        fun hH => tagged_prepartition.is_Henstock_bUnion_tagged.2$ fun J hJ => (h J hJ).2 hH, fun hD => _, fun hD => _⟩
    ·
      rw [prepartition.distortion_bUnion_tagged, Finset.sup_le_iff]
      exact fun J hJ => (h J hJ).3 hD
    ·
      refine' ⟨_, _, hc hD⟩
      rw [π.Union_compl, ←π.Union_bUnion_partition hp]
      rfl

@[mono]
theorem r_cond.mono {ι : Type _} {r : (ι → ℝ) → Ioi (0 : ℝ)} (h : l₁ ≤ l₂) (hr : l₂.r_cond r) : l₁.r_cond r :=
  fun hR => hr (le_iff_imp.1 h.1 hR)

theorem r_cond.min {ι : Type _} {r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)} (h₁ : l.r_cond r₁) (h₂ : l.r_cond r₂) :
  l.r_cond fun x => min (r₁ x) (r₂ x) :=
  fun hR x => congr_arg2 min (h₁ hR x) (h₂ hR x)

@[mono]
theorem to_filter_distortion_mono (I : box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) :
  l₁.to_filter_distortion I c₁ ≤ l₂.to_filter_distortion I c₂ :=
  infi_le_infi$
    fun r => infi_le_infi2$ fun hr => ⟨hr.mono h, principal_mono.2$ fun _ => mem_base_set.mono I h hc fun _ _ => le_rfl⟩

@[mono]
theorem to_filter_mono (I : box ι) {l₁ l₂ : integration_params} (h : l₁ ≤ l₂) : l₁.to_filter I ≤ l₂.to_filter I :=
  supr_le_supr$ fun c => to_filter_distortion_mono I h le_rfl

@[mono]
theorem to_filter_Union_mono (I : box ι) {l₁ l₂ : integration_params} (h : l₁ ≤ l₂) (π₀ : prepartition I) :
  l₁.to_filter_Union I π₀ ≤ l₂.to_filter_Union I π₀ :=
  supr_le_supr$ fun c => inf_le_inf_right _$ to_filter_distortion_mono _ h le_rfl

theorem to_filter_Union_congr (I : box ι) (l : integration_params) {π₁ π₂ : prepartition I} (h : π₁.Union = π₂.Union) :
  l.to_filter_Union I π₁ = l.to_filter_Union I π₂ :=
  by 
    simp only [to_filter_Union, to_filter_distortion_Union, h]

theorem has_basis_to_filter_distortion (l : integration_params) (I : box ι) (c :  ℝ≥0 ) :
  (l.to_filter_distortion I c).HasBasis l.r_cond fun r => { π | l.mem_base_set I c r π } :=
  has_basis_binfi_principal'
    (fun r₁ hr₁ r₂ hr₂ =>
      ⟨_, hr₁.min hr₂, fun _ => mem_base_set.mono _ le_rfl le_rfl fun x hx => min_le_leftₓ _ _,
        fun _ => mem_base_set.mono _ le_rfl le_rfl fun x hx => min_le_rightₓ _ _⟩)
    ⟨fun _ => ⟨1, @zero_lt_one ℝ _ _⟩, fun _ _ => rfl⟩

theorem has_basis_to_filter_distortion_Union (l : integration_params) (I : box ι) (c :  ℝ≥0 ) (π₀ : prepartition I) :
  (l.to_filter_distortion_Union I c π₀).HasBasis l.r_cond
    fun r => { π | l.mem_base_set I c r π ∧ π.Union = π₀.Union } :=
  (l.has_basis_to_filter_distortion I c).inf_principal _

-- error in Analysis.BoxIntegral.Partition.Filter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_basis_to_filter_Union
(l : integration_params)
(I : box ι)
(π₀ : prepartition I) : (l.to_filter_Union I π₀).has_basis (λ
 r : «exprℝ≥0»() → (ι → exprℝ()) → Ioi (0 : exprℝ()), ∀
 c, l.r_cond (r c)) (λ r, {π | «expr∃ , »((c), «expr ∧ »(l.mem_base_set I c (r c) π, «expr = »(π.Union, π₀.Union)))}) :=
have _ := λ c, l.has_basis_to_filter_distortion_Union I c π₀,
by simpa [] [] ["only"] ["[", expr set_of_and, ",", expr set_of_exists, "]"] [] ["using", expr has_basis_supr this]

-- error in Analysis.BoxIntegral.Partition.Filter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_basis_to_filter_Union_top
(l : integration_params)
(I : box ι) : (l.to_filter_Union I «expr⊤»()).has_basis (λ
 r : «exprℝ≥0»() → (ι → exprℝ()) → Ioi (0 : exprℝ()), ∀
 c, l.r_cond (r c)) (λ r, {π | «expr∃ , »((c), «expr ∧ »(l.mem_base_set I c (r c) π, π.is_partition))}) :=
by simpa [] [] ["only"] ["[", expr tagged_prepartition.is_partition_iff_Union_eq, ",", expr prepartition.Union_top, "]"] [] ["using", expr l.has_basis_to_filter_Union I «expr⊤»()]

-- error in Analysis.BoxIntegral.Partition.Filter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_basis_to_filter
(l : integration_params)
(I : box ι) : (l.to_filter I).has_basis (λ
 r : «exprℝ≥0»() → (ι → exprℝ()) → Ioi (0 : exprℝ()), ∀
 c, l.r_cond (r c)) (λ r, {π | «expr∃ , »((c), l.mem_base_set I c (r c) π)}) :=
by simpa [] [] ["only"] ["[", expr set_of_exists, "]"] [] ["using", expr has_basis_supr (l.has_basis_to_filter_distortion I)]

theorem tendsto_embed_box_to_filter_Union_top (l : integration_params) (h : I ≤ J) :
  tendsto (tagged_prepartition.embed_box I J h) (l.to_filter_Union I ⊤)
    (l.to_filter_Union J (prepartition.single J I h)) :=
  by 
    simp only [to_filter_Union, tendsto_supr]
    intro c 
    set π₀ := prepartition.single J I h 
    refine' le_supr_of_le (max c π₀.compl.distortion) _ 
    refine'
      ((l.has_basis_to_filter_distortion_Union I c ⊤).tendsto_iff (l.has_basis_to_filter_distortion_Union J _ _)).2
        fun r hr => _ 
    refine' ⟨r, hr, fun π hπ => _⟩
    rw [mem_set_of_eq, prepartition.Union_top] at hπ 
    refine' ⟨⟨hπ.1.1, hπ.1.2, fun hD => le_transₓ (hπ.1.3 hD) (le_max_leftₓ _ _), fun hD => _⟩, _⟩
    ·
      refine' ⟨_, π₀.Union_compl.trans _, le_max_rightₓ _ _⟩
      congr 1 
      exact (prepartition.Union_single h).trans hπ.2.symm
    ·
      exact hπ.2.trans (prepartition.Union_single _).symm

theorem exists_mem_base_set_le_Union_eq (l : integration_params) (π₀ : prepartition I) (hc₁ : π₀.distortion ≤ c)
  (hc₂ : π₀.compl.distortion ≤ c) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
  ∃ π, l.mem_base_set I c r π ∧ π.to_prepartition ≤ π₀ ∧ π.Union = π₀.Union :=
  by 
    rcases π₀.exists_tagged_le_is_Henstock_is_subordinate_Union_eq r with ⟨π, hle, hH, hr, hd, hU⟩
    refine' ⟨π, ⟨hr, fun _ => hH, fun _ => hd.trans_le hc₁, fun hD => ⟨π₀.compl, _, hc₂⟩⟩, ⟨hle, hU⟩⟩
    exact prepartition.compl_congr hU ▸ π.to_prepartition.Union_compl

-- error in Analysis.BoxIntegral.Partition.Filter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_mem_base_set_is_partition
(l : integration_params)
(I : box ι)
(hc : «expr ≤ »(I.distortion, c))
(r : (ι → exprℝ()) → Ioi (0 : exprℝ())) : «expr∃ , »((π), «expr ∧ »(l.mem_base_set I c r π, π.is_partition)) :=
begin
  rw ["<-", expr prepartition.distortion_top] ["at", ident hc],
  have [ident hc'] [":", expr «expr ≤ »((«expr⊤»() : prepartition I).compl.distortion, c)] [],
  by simp [] [] [] [] [] [],
  simpa [] [] [] ["[", expr is_partition_iff_Union_eq, "]"] [] ["using", expr l.exists_mem_base_set_le_Union_eq «expr⊤»() hc hc' r]
end

theorem to_filter_distortion_Union_ne_bot (l : integration_params) (I : box ι) (π₀ : prepartition I)
  (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) : (l.to_filter_distortion_Union I c π₀).ne_bot :=
  ((l.has_basis_to_filter_distortion I _).inf_principal _).ne_bot_iff.2$
    fun r hr => (l.exists_mem_base_set_le_Union_eq π₀ hc₁ hc₂ r).imp$ fun π hπ => ⟨hπ.1, hπ.2.2⟩

instance to_filter_distortion_Union_ne_bot' (l : integration_params) (I : box ι) (π₀ : prepartition I) :
  (l.to_filter_distortion_Union I (max π₀.distortion π₀.compl.distortion) π₀).ne_bot :=
  l.to_filter_distortion_Union_ne_bot I π₀ (le_max_leftₓ _ _) (le_max_rightₓ _ _)

instance to_filter_distortion_ne_bot (l : integration_params) (I : box ι) :
  (l.to_filter_distortion I I.distortion).ne_bot :=
  by 
    simpa using (l.to_filter_distortion_Union_ne_bot' I ⊤).mono inf_le_left

instance to_filter_ne_bot (l : integration_params) (I : box ι) : (l.to_filter I).ne_bot :=
  (l.to_filter_distortion_ne_bot I).mono$ le_supr _ _

instance to_filter_Union_ne_bot (l : integration_params) (I : box ι) (π₀ : prepartition I) :
  (l.to_filter_Union I π₀).ne_bot :=
  (l.to_filter_distortion_Union_ne_bot' I π₀).mono$ le_supr (fun c => l.to_filter_distortion_Union I c π₀) _

theorem eventually_is_partition (l : integration_params) (I : box ι) :
  ∀ᶠπ in l.to_filter_Union I ⊤, tagged_prepartition.is_partition π :=
  eventually_supr.2$
    fun c =>
      eventually_inf_principal.2$
        eventually_of_forall$ fun π h => π.is_partition_iff_Union_eq.2 (h.trans prepartition.Union_top)

end IntegrationParams

end BoxIntegral

