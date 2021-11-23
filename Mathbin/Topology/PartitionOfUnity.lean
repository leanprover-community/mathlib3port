import Mathbin.Algebra.BigOperators.Finprod 
import Mathbin.Topology.UrysohnsLemma 
import Mathbin.Topology.Paracompact 
import Mathbin.Topology.ShrinkingLemma 
import Mathbin.Topology.ContinuousFunction.Algebra 
import Mathbin.SetTheory.Ordinal

/-!
# Continuous partition of unity

In this file we define `partition_of_unity (ι X : Type*) [topological_space X] (s : set X := univ)`
to be a continuous partition of unity on `s` indexed by `ι`. More precisely, `f : partition_of_unity
ι X s` is a collection of continuous functions `f i : C(X, ℝ)`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* `∑ᶠ i, f i x = 1` for all `x ∈ s`;
* `∑ᶠ i, f i x ≤ 1` for all `x : X`.

In the case `s = univ` the last assumption follows from the previous one but it is convenient to
have this assumption in the case `s ≠ univ`.

We also define a bump function covering,
`bump_covering (ι X : Type*) [topological_space X] (s : set X := univ)`, to be a collection of
functions `f i : C(X, ℝ)`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* for each `x ∈ s` there exists `i : ι` such that `f i y = 1` in a neighborhood of `x`.

The term is motivated by the smooth case.

If `f` is a bump function covering indexed by a linearly ordered type, then
`g i x = f i x * ∏ᶠ j < i, (1 - f j x)` is a partition of unity, see
`bump_covering.to_partition_of_unity`. Note that only finitely many terms `1 - f j x` are not equal
to one, so this product is well-defined.

Note that `g i x = ∏ᶠ j ≤ i, (1 - f j x) - ∏ᶠ j < i, (1 - f j x)`, so most terms in the sum
`∑ᶠ i, g i x` cancel, and we get `∑ᶠ i, g i x = 1 - ∏ᶠ i, (1 - f i x)`, and the latter product
equals zero because one of `f i x` is equal to one.

We say that a partition of unity or a bump function covering `f` is *subordinate* to a family of
sets `U i`, `i : ι`, if the closure of the support of each `f i` is included in `U i`. We use
Urysohn's Lemma to prove that a locally finite open covering of a normal topological space admits a
subordinate bump function covering (hence, a subordinate partition of unity), see
`bump_covering.exists_is_subordinate_of_locally_finite`. If `X` is a paracompact space, then any
open covering admits a locally finite refinement, hence it admits a subordinate bump function
covering and a subordinate partition of unity, see `bump_covering.exists_is_subordinate`.

We also provide two slightly more general versions of these lemmas,
`bump_covering.exists_is_subordinate_of_locally_finite_of_prop` and
`bump_covering.exists_is_subordinate_of_prop`, to be used later in the construction of a smooth
partition of unity.

## Implementation notes

Most (if not all) books only define a partition of unity of the whole space. However, quite a few
proofs only deal with `f i` such that `closure (support (f i))` meets a specific closed subset, and
it is easier to formalize these proofs if we don't have other functions right away.

We use `well_ordering_rel j i` instead of `j < i` in the definition of
`bump_covering.to_partition_of_unity` to avoid a `[linear_order ι]` assumption. While
`well_ordering_rel j i` is a well order, not only a strict linear order, we never use this property.

## Tags

partition of unity, bump function, Urysohn's lemma, normal space, paracompact space
-/


universe u v

open Function Set Filter

open_locale BigOperators TopologicalSpace Classical

noncomputable theory

/-- A continuous partition of unity on a set `s : set X` is a collection of continuous functions
`f i` such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* the functions `f i` are nonnegative;
* the sum `∑ᶠ i, f i x` is equal to one for every `x ∈ s` and is less than or equal to one
  otherwise.

If `X` is a normal paracompact space, then `partition_of_unity.exists_is_subordinate` guarantees
that for every open covering `U : set (set X)` of `s` there exists a partition of unity that is
subordinate to `U`.
-/
structure PartitionOfUnity(ι X : Type _)[TopologicalSpace X](s : Set X := univ) where 
  toFun : ι → C(X, ℝ)
  locally_finite' : LocallyFinite fun i => support (to_fun i)
  nonneg' : 0 ≤ to_fun 
  sum_eq_one' : ∀ x _ : x ∈ s, (∑ᶠi, to_fun i x) = 1
  sum_le_one' : ∀ x, (∑ᶠi, to_fun i x) ≤ 1

/-- A `bump_covering ι X s` is an indexed family of functions `f i`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* for all `i`, `x` we have `0 ≤ f i x ≤ 1`;
* each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`.

One of the main use cases for a `bump_covering` is to define a `partition_of_unity`, see
`bump_covering.to_partition_of_unity`, but some proofs can directly use a `bump_covering` instead of
a `partition_of_unity`.

If `X` is a normal paracompact space, then `bump_covering.exists_is_subordinate` guarantees that for
every open covering `U : set (set X)` of `s` there exists a `bump_covering` of `s` that is
subordinate to `U`.
-/
structure BumpCovering(ι X : Type _)[TopologicalSpace X](s : Set X := univ) where 
  toFun : ι → C(X, ℝ)
  locally_finite' : LocallyFinite fun i => support (to_fun i)
  nonneg' : 0 ≤ to_fun 
  le_one' : to_fun ≤ 1 
  eventually_eq_one' : ∀ x _ : x ∈ s, ∃ i, to_fun i =ᶠ[𝓝 x] 1

variable{ι : Type u}{X : Type v}[TopologicalSpace X]

namespace PartitionOfUnity

variable{s : Set X}(f : PartitionOfUnity ι X s)

instance  : CoeFun (PartitionOfUnity ι X s) fun _ => ι → C(X, ℝ) :=
  ⟨to_fun⟩

protected theorem LocallyFinite : LocallyFinite fun i => support (f i) :=
  f.locally_finite'

theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

theorem sum_eq_one {x : X} (hx : x ∈ s) : (∑ᶠi, f i x) = 1 :=
  f.sum_eq_one' x hx

theorem sum_le_one (x : X) : (∑ᶠi, f i x) ≤ 1 :=
  f.sum_le_one' x

theorem sum_nonneg (x : X) : 0 ≤ ∑ᶠi, f i x :=
  finsum_nonneg$ fun i => f.nonneg i x

theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  (single_le_finsum i (f.locally_finite.point_finite x) fun j => f.nonneg j x).trans (f.sum_le_one x)

/-- A partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same type if
for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def is_subordinate (f : PartitionOfUnity ι X s) (U : ι → Set X) : Prop :=
  ∀ i, Closure (support (f i)) ⊆ U i

end PartitionOfUnity

namespace BumpCovering

variable{s : Set X}(f : BumpCovering ι X s)

instance  : CoeFun (BumpCovering ι X s) fun _ => ι → C(X, ℝ) :=
  ⟨to_fun⟩

protected theorem LocallyFinite : LocallyFinite fun i => support (f i) :=
  f.locally_finite'

protected theorem point_finite (x : X) : finite { i | f i x ≠ 0 } :=
  f.locally_finite.point_finite x

theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  f.le_one' i x

/-- A `bump_covering` that consists of a single function, uniformly equal to one, defined as an
example for `inhabited` instance. -/
protected def single (i : ι) (s : Set X) : BumpCovering ι X s :=
  { toFun := Pi.single i 1,
    locally_finite' :=
      fun x =>
        by 
          refine' ⟨univ, univ_mem, (finite_singleton i).Subset _⟩
          rintro j ⟨x, hx, -⟩
          contrapose! hx 
          rw [mem_singleton_iff] at hx 
          simp [hx],
    nonneg' := le_update_iff.2 ⟨fun x => zero_le_one, fun _ _ => le_rfl⟩,
    le_one' := update_le_iff.2 ⟨le_rfl, fun _ _ _ => zero_le_one⟩,
    eventually_eq_one' :=
      fun x _ =>
        ⟨i,
          by 
            simp ⟩ }

@[simp]
theorem coe_single (i : ι) (s : Set X) : «expr⇑ » (BumpCovering.single i s) = Pi.single i 1 :=
  rfl

instance  [Inhabited ι] : Inhabited (BumpCovering ι X s) :=
  ⟨BumpCovering.single (default ι) s⟩

/-- A collection of bump functions `f i` is subordinate to a family of sets `U i` indexed by the
same type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def is_subordinate (f : BumpCovering ι X s) (U : ι → Set X) : Prop :=
  ∀ i, Closure (support (f i)) ⊆ U i

theorem is_subordinate.mono {f : BumpCovering ι X s} {U V : ι → Set X} (hU : f.is_subordinate U) (hV : ∀ i, U i ⊆ V i) :
  f.is_subordinate V :=
  fun i => subset.trans (hU i) (hV i)

-- error in Topology.PartitionOfUnity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : locally_finite U` can be omitted, see
`bump_covering.exists_is_subordinate`. This version assumes that `p : (X → ℝ) → Prop` is a predicate
that satisfies Urysohn's lemma, and provides a `bump_covering` such that each function of the
covering satisfies `p`. -/
theorem exists_is_subordinate_of_locally_finite_of_prop
[normal_space X]
(p : (X → exprℝ()) → exprProp())
(h01 : ∀
 s
 t, is_closed s → is_closed t → disjoint s t → «expr∃ , »((f : «exprC( , )»(X, exprℝ())), «expr ∧ »(p f, «expr ∧ »(eq_on f 0 s, «expr ∧ »(eq_on f 1 t, ∀
     x, «expr ∈ »(f x, Icc (0 : exprℝ()) 1))))))
(hs : is_closed s)
(U : ι → set X)
(ho : ∀ i, is_open (U i))
(hf : locally_finite U)
(hU : «expr ⊆ »(s, «expr⋃ , »((i), U i))) : «expr∃ , »((f : bump_covering ι X s), «expr ∧ »(∀
  i, p (f i), f.is_subordinate U)) :=
begin
  rcases [expr exists_subset_Union_closure_subset hs ho (λ
    x _, hf.point_finite x) hU, "with", "⟨", ident V, ",", ident hsV, ",", ident hVo, ",", ident hVU, "⟩"],
  have [ident hVU'] [":", expr ∀ i, «expr ⊆ »(V i, U i)] [],
  from [expr λ i, subset.trans subset_closure (hVU i)],
  rcases [expr exists_subset_Union_closure_subset hs hVo (λ
    x
    _, (hf.subset hVU').point_finite x) hsV, "with", "⟨", ident W, ",", ident hsW, ",", ident hWo, ",", ident hWV, "⟩"],
  choose [] [ident f] [ident hfp, ident hf0, ident hf1, ident hf01] ["using", expr λ
   i, h01 _ _ «expr $ »(is_closed_compl_iff.2, hVo i) is_closed_closure «expr $ »(disjoint_right.2, λ
    x hx, not_not.2 (hWV i hx))],
  have [ident hsupp] [":", expr ∀ i, «expr ⊆ »(support (f i), V i)] [],
  from [expr λ i, support_subset_iff'.2 (hf0 i)],
  refine [expr ⟨⟨f, hf.subset (λ
      i, subset.trans (hsupp i) (hVU' i)), λ
     i x, (hf01 i x).1, λ i x, (hf01 i x).2, λ x hx, _⟩, hfp, λ i, subset.trans (closure_mono (hsupp i)) (hVU i)⟩],
  rcases [expr mem_Union.1 (hsW hx), "with", "⟨", ident i, ",", ident hi, "⟩"],
  exact [expr ⟨i, ((hf1 i).mono subset_closure).eventually_eq_of_mem ((hWo i).mem_nhds hi)⟩]
end

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : locally_finite U` can be omitted, see
`bump_covering.exists_is_subordinate`. -/
theorem exists_is_subordinate_of_locally_finite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
  (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃i, U i) : ∃ f : BumpCovering ι X s, f.is_subordinate U :=
  let ⟨f, _, hfU⟩ :=
    exists_is_subordinate_of_locally_finite_of_prop (fun _ => True)
      (fun s t hs ht hd => (exists_continuous_zero_one_of_closed hs ht hd).imp$ fun f hf => ⟨trivialₓ, hf⟩) hs U ho hf
      hU
  ⟨f, hfU⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. This version assumes that
`p : (X → ℝ) → Prop` is a predicate that satisfies Urysohn's lemma, and provides a
`bump_covering` such that each function of the covering satisfies `p`. -/
theorem exists_is_subordinate_of_prop [NormalSpace X] [ParacompactSpace X] (p : (X → ℝ) → Prop)
  (h01 :
    ∀ s t,
      IsClosed s →
        IsClosed t → Disjoint s t → ∃ f : C(X, ℝ), p f ∧ eq_on f 0 s ∧ eq_on f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
  (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃i, U i) :
  ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.is_subordinate U :=
  by 
    rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
    rcases exists_is_subordinate_of_locally_finite_of_prop p h01 hs V hVo hVf hsV with ⟨f, hfp, hf⟩
    exact ⟨f, hfp, hf.mono hVU⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. -/
theorem exists_is_subordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
  (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃i, U i) : ∃ f : BumpCovering ι X s, f.is_subordinate U :=
  by 
    rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
    rcases exists_is_subordinate_of_locally_finite hs V hVo hVf hsV with ⟨f, hf⟩
    exact ⟨f, hf.mono hVU⟩

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : X) (hx : x ∈ s) : ι :=
  (f.eventually_eq_one' x hx).some

theorem eventually_eq_one (x : X) (hx : x ∈ s) : f (f.ind x hx) =ᶠ[𝓝 x] 1 :=
  (f.eventually_eq_one' x hx).some_spec

theorem ind_apply (x : X) (hx : x ∈ s) : f (f.ind x hx) x = 1 :=
  (f.eventually_eq_one x hx).eq_of_nhds

/-- Partition of unity defined by a `bump_covering`. We use this auxiliary definition to prove some
properties of the new family of functions before bundling it into a `partition_of_unity`. Do not use
this definition, use `bump_function.to_partition_of_unity` instead.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals one, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `linear_order ι`, we use `well_ordering_rel` instead of `(<)`. -/
def to_pou_fun (i : ι) (x : X) : ℝ :=
  f i x*∏ᶠ(j : _)(hj : WellOrderingRel j i), 1 - f j x

theorem to_pou_fun_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.to_pou_fun i x = 0 :=
  by 
    rw [to_pou_fun, h, zero_mul]

theorem support_to_pou_fun_subset (i : ι) : support (f.to_pou_fun i) ⊆ support (f i) :=
  fun x => mt$ f.to_pou_fun_zero_of_zero

theorem to_pou_fun_eq_mul_prod (i : ι) (x : X) (t : Finset ι) (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
  f.to_pou_fun i x = f i x*∏j in t.filter fun j => WellOrderingRel j i, 1 - f j x :=
  by 
    refine' congr_argₓ _ (finprod_cond_eq_prod_of_cond_iff _ fun j hj => _)
    rw [Ne.def, sub_eq_self] at hj 
    rw [Finset.mem_filter, Iff.comm, and_iff_right_iff_imp]
    exact flip (ht j) hj

-- error in Topology.PartitionOfUnity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sum_to_pou_fun_eq
(x : X) : «expr = »(«expr∑ᶠ , »((i), f.to_pou_fun i x), «expr - »(1, «expr∏ᶠ , »((i), «expr - »(1, f i x)))) :=
begin
  set [] [ident s] [] [":="] [expr (f.point_finite x).to_finset] [],
  have [ident hs] [":", expr «expr = »((s : set ι), {i | «expr ≠ »(f i x, 0)})] [":=", expr finite.coe_to_finset _],
  have [ident A] [":", expr «expr ⊆ »(support (λ i, to_pou_fun f i x), s)] [],
  { rw [expr hs] [],
    exact [expr λ i hi, f.support_to_pou_fun_subset i hi] },
  have [ident B] [":", expr «expr ⊆ »(mul_support (λ i, «expr - »(1, f i x)), s)] [],
  { rw ["[", expr hs, ",", expr mul_support_one_sub, "]"] [],
    exact [expr λ i, id] },
  letI [] [":", expr linear_order ι] [":=", expr linear_order_of_STO' well_ordering_rel],
  rw ["[", expr finsum_eq_sum_of_support_subset _ A, ",", expr finprod_eq_prod_of_mul_support_subset _ B, ",", expr finset.prod_one_sub_ordered, ",", expr sub_sub_cancel, "]"] [],
  refine [expr finset.sum_congr rfl (λ i hi, _)],
  convert [] [expr f.to_pou_fun_eq_mul_prod _ _ _ (λ j hji hj, _)] [],
  rwa [expr finite.mem_to_finset] []
end

theorem exists_finset_to_pou_fun_eventually_eq (i : ι) (x : X) :
  ∃ t : Finset ι, f.to_pou_fun i =ᶠ[𝓝 x] f i*∏j in t.filter fun j => WellOrderingRel j i, 1 - f j :=
  by 
    rcases f.locally_finite x with ⟨U, hU, hf⟩
    use hf.to_finset 
    filterUpwards [hU]
    intro y hyU 
    simp only [Pi.mul_apply, Finset.prod_apply]
    apply to_pou_fun_eq_mul_prod 
    intro j hji hj 
    exact hf.mem_to_finset.2 ⟨y, ⟨hj, hyU⟩⟩

theorem continuous_to_pou_fun (i : ι) : Continuous (f.to_pou_fun i) :=
  by 
    refine' (f i).Continuous.mul$ continuous_finprod_cond (fun j _ => continuous_const.sub (f j).Continuous) _ 
    simp only [mul_support_one_sub]
    exact f.locally_finite

/-- The partition of unity defined by a `bump_covering`.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals one, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `linear_order ι`, we use `well_ordering_rel` instead of `(<)`. -/
def to_partition_of_unity : PartitionOfUnity ι X s :=
  { toFun := fun i => ⟨f.to_pou_fun i, f.continuous_to_pou_fun i⟩,
    locally_finite' := f.locally_finite.subset f.support_to_pou_fun_subset,
    nonneg' := fun i x => mul_nonneg (f.nonneg i x) (finprod_cond_nonneg$ fun j hj => sub_nonneg.2$ f.le_one j x),
    sum_eq_one' :=
      fun x hx =>
        by 
          simp only [ContinuousMap.coe_mk, sum_to_pou_fun_eq, sub_eq_self]
          apply finprod_eq_zero (fun i => 1 - f i x) (f.ind x hx)
          ·
            simp only [f.ind_apply x hx, sub_self]
          ·
            rw [mul_support_one_sub]
            exact f.point_finite x,
    sum_le_one' :=
      fun x =>
        by 
          simp only [ContinuousMap.coe_mk, sum_to_pou_fun_eq, sub_le_self_iff]
          exact finprod_nonneg fun i => sub_nonneg.2$ f.le_one i x }

theorem to_partition_of_unity_apply (i : ι) (x : X) :
  f.to_partition_of_unity i x = f i x*∏ᶠ(j : _)(hj : WellOrderingRel j i), 1 - f j x :=
  rfl

theorem to_partition_of_unity_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
  (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
  f.to_partition_of_unity i x = f i x*∏j in t.filter fun j => WellOrderingRel j i, 1 - f j x :=
  f.to_pou_fun_eq_mul_prod i x t ht

theorem exists_finset_to_partition_of_unity_eventually_eq (i : ι) (x : X) :
  ∃ t : Finset ι, f.to_partition_of_unity i =ᶠ[𝓝 x] f i*∏j in t.filter fun j => WellOrderingRel j i, 1 - f j :=
  f.exists_finset_to_pou_fun_eventually_eq i x

theorem to_partition_of_unity_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.to_partition_of_unity i x = 0 :=
  f.to_pou_fun_zero_of_zero h

theorem support_to_partition_of_unity_subset (i : ι) : support (f.to_partition_of_unity i) ⊆ support (f i) :=
  f.support_to_pou_fun_subset i

theorem sum_to_partition_of_unity_eq (x : X) : (∑ᶠi, f.to_partition_of_unity i x) = 1 - ∏ᶠi, 1 - f i x :=
  f.sum_to_pou_fun_eq x

theorem is_subordinate.to_partition_of_unity {f : BumpCovering ι X s} {U : ι → Set X} (h : f.is_subordinate U) :
  f.to_partition_of_unity.is_subordinate U :=
  fun i => subset.trans (closure_mono$ f.support_to_partition_of_unity_subset i) (h i)

end BumpCovering

namespace PartitionOfUnity

variable{s : Set X}

instance  [Inhabited ι] : Inhabited (PartitionOfUnity ι X s) :=
  ⟨(default (BumpCovering ι X s)).toPartitionOfUnity⟩

/-- If `X` is a normal topological space and `U` is a locally finite open covering of a closed set
`s`, then there exists a `partition_of_unity ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : locally_finite U` can be omitted, see
`bump_covering.exists_is_subordinate`. -/
theorem exists_is_subordinate_of_locally_finite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
  (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃i, U i) :
  ∃ f : PartitionOfUnity ι X s, f.is_subordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_is_subordinate_of_locally_finite hs U ho hf hU
  ⟨f.to_partition_of_unity, hf.to_partition_of_unity⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `partition_of_unity ι X s` that is subordinate to `U`. -/
theorem exists_is_subordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
  (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃i, U i) : ∃ f : PartitionOfUnity ι X s, f.is_subordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_is_subordinate hs U ho hU
  ⟨f.to_partition_of_unity, hf.to_partition_of_unity⟩

end PartitionOfUnity

