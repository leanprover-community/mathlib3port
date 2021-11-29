import Mathbin.Analysis.Convex.Combination 
import Mathbin.Analysis.Convex.Extreme

/-!
# Convex independence

This file defines convex independent families of points.

Convex independence is closely related to affine independence. In both cases, no point can be
written as a combination of others. When the combination is affine (that is, any coefficients), this
yields affine independence. When the combination is convex (that is, all coefficients are
nonnegative), then this yields convex independence. In particular, affine independence implies
convex independence.

## Main declarations

* `convex_independent p`: Convex independence of the indexed family `p : ι → E`. Every point of the
  family only belongs to convex hulls of sets of the family containing it.
* `convex_independent_iff_finset`: Carathéodory's theorem allows us to only check finsets to
  conclude convex independence.
* `convex.extreme_points_convex_independent`: Extreme points of a convex set are convex independent.

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Prove `affine_independent.convex_independent`. This requires some glue between `affine_combination`
and `finset.center_mass`.

## Tags

independence, convex position
-/


open_locale Affine BigOperators Classical

open Finset Function

variable{𝕜 E ι : Type _}

section OrderedSemiring

variable(𝕜)[OrderedSemiring 𝕜][AddCommGroupₓ E][Module 𝕜 E]{s t : Set E}

/-- An indexed family is said to be convex independent if every point only belongs to convex hulls
of sets containing it. -/
def ConvexIndependent (p : ι → E) : Prop :=
  ∀ (s : Set ι) (x : ι), p x ∈ convexHull 𝕜 (p '' s) → x ∈ s

variable{𝕜}

-- error in Analysis.Convex.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A family with at most one point is convex independent. -/
theorem subsingleton.convex_independent [subsingleton ι] (p : ι → E) : convex_independent 𝕜 p :=
λ s x hx, begin
  have [] [":", expr (convex_hull 𝕜 «expr '' »(p, s)).nonempty] [":=", expr ⟨p x, hx⟩],
  rw ["[", expr convex_hull_nonempty_iff, ",", expr set.nonempty_image_iff, "]"] ["at", ident this],
  rwa [expr subsingleton.mem_iff_nonempty] []
end

/-- A convex independent family is injective. -/
protected theorem ConvexIndependent.injective {p : ι → E} (hc : ConvexIndependent 𝕜 p) : Function.Injective p :=
  by 
    refine' fun i j hij => hc {j} i _ 
    rw [hij, Set.image_singleton, convex_hull_singleton]
    exact Set.mem_singleton _

/-- If a family is convex independent, so is any subfamily given by composition of an embedding into
index type with the original family. -/
theorem ConvexIndependent.comp_embedding {ι' : Type _} (f : ι' ↪ ι) {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
  ConvexIndependent 𝕜 (p ∘ f) :=
  by 
    intro s x hx 
    rw [←f.injective.mem_set_image]
    exact
      hc _ _
        (by 
          rwa [Set.image_image])

-- error in Analysis.Convex.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If a family is convex independent, so is any subfamily indexed by a subtype of the index type.
-/
protected
theorem convex_independent.subtype
{p : ι → E}
(hc : convex_independent 𝕜 p)
(s : set ι) : convex_independent 𝕜 (λ i : s, p i) :=
hc.comp_embedding (embedding.subtype _)

-- error in Analysis.Convex.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If an indexed family of points is convex independent, so is the corresponding set of points. -/
protected
theorem convex_independent.range
{p : ι → E}
(hc : convex_independent 𝕜 p) : convex_independent 𝕜 (λ x, x : set.range p → E) :=
begin
  let [ident f] [":", expr set.range p → ι] [":=", expr λ x, x.property.some],
  have [ident hf] [":", expr ∀ x, «expr = »(p (f x), x)] [":=", expr λ x, x.property.some_spec],
  let [ident fe] [":", expr «expr ↪ »(set.range p, ι)] [":=", expr ⟨f, λ
    x₁ x₂ he, subtype.ext «expr ▸ »(hf x₁, «expr ▸ »(hf x₂, «expr ▸ »(he, rfl)))⟩],
  convert [] [expr hc.comp_embedding fe] [],
  ext [] [] [],
  rw ["[", expr embedding.coe_fn_mk, ",", expr comp_app, ",", expr hf, "]"] []
end

/-- A subset of a convex independent set of points is convex independent as well. -/
protected theorem ConvexIndependent.mono {s t : Set E} (hc : ConvexIndependent 𝕜 (fun x => x : t → E)) (hs : s ⊆ t) :
  ConvexIndependent 𝕜 (fun x => x : s → E) :=
  hc.comp_embedding (s.embedding_of_subset t hs)

/-- The range of an injective indexed family of points is convex independent iff that family is. -/
theorem Function.Injective.convex_independent_iff_set {p : ι → E} (hi : Function.Injective p) :
  ConvexIndependent 𝕜 (fun x => x : Set.Range p → E) ↔ ConvexIndependent 𝕜 p :=
  ⟨fun hc =>
      hc.comp_embedding
        (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun x y h => hi (Subtype.mk_eq_mk.1 h)⟩ : ι ↪ Set.Range p),
    ConvexIndependent.range⟩

/-- If a family is convex independent, a point in the family is in the convex hull of some of the
points given by a subset of the index type if and only if the point's index is in this subset. -/
@[simp]
protected theorem ConvexIndependent.mem_convex_hull_iff {p : ι → E} (hc : ConvexIndependent 𝕜 p) (s : Set ι) (i : ι) :
  p i ∈ convexHull 𝕜 (p '' s) ↔ i ∈ s :=
  ⟨hc _ _, fun hi => subset_convex_hull 𝕜 _ (Set.mem_image_of_mem p hi)⟩

/-- If a family is convex independent, a point in the family is not in the convex hull of the other
points. See `convex_independent_set_iff_not_mem_convex_hull_diff` for the `set` version.  -/
theorem convex_independent_iff_not_mem_convex_hull_diff {p : ι → E} :
  ConvexIndependent 𝕜 p ↔ ∀ i s, p i ∉ convexHull 𝕜 (p '' (s \ {i})) :=
  by 
    refine' ⟨fun hc i s h => _, fun h s i hi => _⟩
    ·
      rw [hc.mem_convex_hull_iff] at h 
      exact h.2 (Set.mem_singleton _)
    ·
      byContra H 
      refine' h i s _ 
      rw [Set.diff_singleton_eq_self H]
      exact hi

theorem convex_independent_set_iff_inter_convex_hull_subset {s : Set E} :
  ConvexIndependent 𝕜 (fun x => x : s → E) ↔ ∀ t, t ⊆ s → s ∩ convexHull 𝕜 t ⊆ t :=
  by 
    split 
    ·
      rintro hc t h x ⟨hxs, hxt⟩
      refine' hc { x | «expr↑ » x ∈ t } ⟨x, hxs⟩ _ 
      rw [Subtype.coe_image_of_subset h]
      exact hxt
    ·
      intro hc t x h 
      rw [←subtype.coe_injective.mem_set_image]
      exact hc (t.image coeₓ) (Subtype.coe_image_subset s t) ⟨x.prop, h⟩

/-- If a set is convex independent, a point in the set is not in the convex hull of the other
points. See `convex_independent_iff_not_mem_convex_hull_diff` for the indexed family version.  -/
theorem convex_independent_set_iff_not_mem_convex_hull_diff {s : Set E} :
  ConvexIndependent 𝕜 (fun x => x : s → E) ↔ ∀ x (_ : x ∈ s), x ∉ convexHull 𝕜 (s \ {x}) :=
  by 
    rw [convex_independent_set_iff_inter_convex_hull_subset]
    split 
    ·
      rintro hs x hxs hx 
      exact (hs _ (Set.diff_subset _ _) ⟨hxs, hx⟩).2 (Set.mem_singleton _)
    ·
      rintro hs t ht x ⟨hxs, hxt⟩
      byContra h 
      exact hs _ hxs (convex_hull_mono (Set.subset_diff_singleton ht h) hxt)

end OrderedSemiring

section LinearOrderedField

variable[LinearOrderedField 𝕜][AddCommGroupₓ E][Module 𝕜 E]{s : Set E}

-- error in Analysis.Convex.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- To check convex independence, one only has to check finsets thanks to Carathéodory's theorem. -/
theorem convex_independent_iff_finset
{p : ι → E} : «expr ↔ »(convex_independent 𝕜 p, ∀
 (s : finset ι)
 (x : ι), «expr ∈ »(p x, convex_hull 𝕜 (s.image p : set E)) → «expr ∈ »(x, s)) :=
begin
  refine [expr ⟨λ hc s x hx, hc s x _, λ h s x hx, _⟩],
  { rwa [expr finset.coe_image] ["at", ident hx] },
  have [ident hp] [":", expr injective p] [],
  { rintro [ident a, ident b, ident hab],
    rw ["<-", expr mem_singleton] [],
    refine [expr h {b} a _],
    rw ["[", expr hab, ",", expr image_singleton, ",", expr coe_singleton, ",", expr convex_hull_singleton, "]"] [],
    exact [expr set.mem_singleton _] },
  rw [expr convex_hull_eq_union_convex_hull_finite_subsets] ["at", ident hx],
  simp_rw [expr set.mem_Union] ["at", ident hx],
  obtain ["⟨", ident t, ",", ident ht, ",", ident hx, "⟩", ":=", expr hx],
  rw ["<-", expr hp.mem_set_image] [],
  refine [expr ht _],
  suffices [] [":", expr «expr ∈ »(x, t.preimage p (hp.inj_on _))],
  { rwa ["[", expr mem_preimage, ",", "<-", expr mem_coe, "]"] ["at", ident this] },
  refine [expr h _ x _],
  rwa ["[", expr t.image_preimage p (hp.inj_on _), ",", expr filter_true_of_mem, "]"] [],
  { exact [expr λ y hy, s.image_subset_range p «expr $ »(ht, mem_coe.2 hy)] }
end

/-! ### Extreme points -/


theorem Convex.convex_independent_extreme_points (hs : Convex 𝕜 s) :
  ConvexIndependent 𝕜 (fun p => p : s.extreme_points 𝕜 → E) :=
  convex_independent_set_iff_not_mem_convex_hull_diff.2$
    fun x hx h =>
      (extreme_points_convex_hull_subset
            (inter_extreme_points_subset_extreme_points_of_subset
              (convex_hull_min ((Set.diff_subset _ _).trans extreme_points_subset) hs) ⟨h, hx⟩)).2
        (Set.mem_singleton _)

end LinearOrderedField

