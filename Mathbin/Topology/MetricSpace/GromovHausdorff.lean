import Mathbin.Topology.MetricSpace.Closeds 
import Mathbin.SetTheory.Cardinal 
import Mathbin.Topology.MetricSpace.GromovHausdorffRealized 
import Mathbin.Topology.MetricSpace.Completion 
import Mathbin.Topology.MetricSpace.Kuratowski

/-!
# Gromov-Hausdorff distance

This file defines the Gromov-Hausdorff distance on the space of nonempty compact metric spaces
up to isometry.

We introduce the space of all nonempty compact metric spaces, up to isometry,
called `GH_space`, and endow it with a metric space structure. The distance,
known as the Gromov-Hausdorff distance, is defined as follows: given two
nonempty compact spaces `X` and `Y`, their distance is the minimum Hausdorff distance
between all possible isometric embeddings of `X` and `Y` in all metric spaces.
To define properly the Gromov-Hausdorff space, we consider the non-empty
compact subsets of `ℓ^∞(ℝ)` up to isometry, which is a well-defined type,
and define the distance as the infimum of the Hausdorff distance over all
embeddings in `ℓ^∞(ℝ)`. We prove that this coincides with the previous description,
as all separable metric spaces embed isometrically into `ℓ^∞(ℝ)`, through an
embedding called the Kuratowski embedding.
To prove that we have a distance, we should show that if spaces can be coupled
to be arbitrarily close, then they are isometric. More generally, the Gromov-Hausdorff
distance is realized, i.e., there is a coupling for which the Hausdorff distance
is exactly the Gromov-Hausdorff distance. This follows from a compactness
argument, essentially following from Arzela-Ascoli.

## Main results

We prove the most important properties of the Gromov-Hausdorff space: it is a polish space,
i.e., it is complete and second countable. We also prove the Gromov compactness criterion.

-/


noncomputable theory

open_locale Classical TopologicalSpace

universe u v w

open Classical Set Function TopologicalSpace Filter Metric Quotientₓ

open BoundedContinuousFunction Nat Int kuratowskiEmbedding

open sum(inl inr)

attribute [local instance] metric_space_sum

namespace GromovHausdorff

section GHSpace

/-- Equivalence relation identifying two nonempty compact sets which are isometric -/
private def isometry_rel : nonempty_compacts ℓInftyℝ → nonempty_compacts ℓInftyℝ → Prop :=
  fun x y => Nonempty (x.val ≃ᵢ y.val)

/-- This is indeed an equivalence relation -/
private theorem is_equivalence_isometry_rel : Equivalenceₓ isometry_rel :=
  ⟨fun x => ⟨Isometric.refl _⟩, fun x y ⟨e⟩ => ⟨e.symm⟩, fun x y z ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- setoid instance identifying two isometric nonempty compact subspaces of ℓ^∞(ℝ) -/
instance isometry_rel.setoid : Setoidₓ (nonempty_compacts ℓInftyℝ) :=
  Setoidₓ.mk isometry_rel is_equivalence_isometry_rel

/-- The Gromov-Hausdorff space -/
def GH_space : Type :=
  Quotientₓ isometry_rel.setoid

/-- Map any nonempty compact type to `GH_space` -/
def to_GH_space (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] : GH_space :=
  «expr⟦ ⟧» (NonemptyCompacts.kuratowskiEmbedding X)

instance : Inhabited GH_space :=
  ⟨Quot.mk _
      ⟨{0},
        by 
          simp ⟩⟩

/-- A metric space representative of any abstract point in `GH_space` -/
@[nolint has_inhabited_instance]
def GH_space.rep (p : GH_space) : Type :=
  (Quot.out p).val

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_to_GH_space_iff
{X : Type u}
[metric_space X]
[compact_space X]
[nonempty X]
{p : nonempty_compacts ℓ_infty_ℝ} : «expr ↔ »(«expr = »(«expr⟦ ⟧»(p), to_GH_space X), «expr∃ , »((Ψ : X → ℓ_infty_ℝ), «expr ∧ »(isometry Ψ, «expr = »(range Ψ, p.val)))) :=
begin
  simp [] [] ["only"] ["[", expr to_GH_space, ",", expr quotient.eq, "]"] [] [],
  split,
  { assume [binders (h)],
    rcases [expr setoid.symm h, "with", "⟨", ident e, "⟩"],
    have [ident f] [] [":=", expr (Kuratowski_embedding.isometry X).isometric_on_range.trans e],
    use [expr λ x, f x],
    split,
    { apply [expr isometry_subtype_coe.comp f.isometry] },
    { rw ["[", expr range_comp, ",", expr f.range_eq_univ, ",", expr set.image_univ, ",", expr subtype.range_coe, "]"] [] } },
  { rintros ["⟨", ident Ψ, ",", "⟨", ident isomΨ, ",", ident rangeΨ, "⟩", "⟩"],
    have [ident f] [] [":=", expr ((Kuratowski_embedding.isometry X).isometric_on_range.symm.trans isomΨ.isometric_on_range).symm],
    have [ident E] [":", expr «expr = »(«expr ≃ᵢ »(range Ψ, (nonempty_compacts.Kuratowski_embedding X).val), «expr ≃ᵢ »(p.val, range (Kuratowski_embedding X)))] [],
    by { dunfold [ident nonempty_compacts.Kuratowski_embedding] [],
      rw ["[", expr rangeΨ, "]"] []; refl },
    have [ident g] [] [":=", expr cast E f],
    exact [expr ⟨g⟩] }
end

theorem eq_to_GH_space {p : nonempty_compacts ℓInftyℝ} : «expr⟦ ⟧» p = to_GH_space p.val :=
  by 
    refine' eq_to_GH_space_iff.2 ⟨(fun x => x : p.val → ℓInftyℝ), _, Subtype.range_coe⟩
    apply isometry_subtype_coe

section 

attribute [local reducible] GH_space.rep

instance rep_GH_space_metric_space {p : GH_space} : MetricSpace p.rep :=
  by 
    infer_instance

instance rep_GH_space_compact_space {p : GH_space} : CompactSpace p.rep :=
  by 
    infer_instance

instance rep_GH_space_nonempty {p : GH_space} : Nonempty p.rep :=
  by 
    infer_instance

end 

theorem GH_space.to_GH_space_rep (p : GH_space) : to_GH_space p.rep = p :=
  by 
    change to_GH_space (Quot.out p).val = p 
    rw [←eq_to_GH_space]
    exact Quot.out_eq p

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Two nonempty compact spaces have the same image in `GH_space` if and only if they are
isometric. -/
theorem to_GH_space_eq_to_GH_space_iff_isometric
{X : Type u}
[metric_space X]
[compact_space X]
[nonempty X]
{Y : Type v}
[metric_space Y]
[compact_space Y]
[nonempty Y] : «expr ↔ »(«expr = »(to_GH_space X, to_GH_space Y), nonempty «expr ≃ᵢ »(X, Y)) :=
⟨begin
   simp [] [] ["only"] ["[", expr to_GH_space, ",", expr quotient.eq, "]"] [] [],
   assume [binders (h)],
   rcases [expr h, "with", "⟨", ident e, "⟩"],
   have [ident I] [":", expr «expr = »(«expr ≃ᵢ »((nonempty_compacts.Kuratowski_embedding X).val, (nonempty_compacts.Kuratowski_embedding Y).val), «expr ≃ᵢ »(range (Kuratowski_embedding X), range (Kuratowski_embedding Y)))] [],
   by { dunfold [ident nonempty_compacts.Kuratowski_embedding] [],
     refl },
   have [ident e'] [] [":=", expr cast I e],
   have [ident f] [] [":=", expr (Kuratowski_embedding.isometry X).isometric_on_range],
   have [ident g] [] [":=", expr (Kuratowski_embedding.isometry Y).isometric_on_range.symm],
   have [ident h] [] [":=", expr (f.trans e').trans g],
   exact [expr ⟨h⟩]
 end, begin
   rintros ["⟨", ident e, "⟩"],
   simp [] [] ["only"] ["[", expr to_GH_space, ",", expr quotient.eq, "]"] [] [],
   have [ident f] [] [":=", expr (Kuratowski_embedding.isometry X).isometric_on_range.symm],
   have [ident g] [] [":=", expr (Kuratowski_embedding.isometry Y).isometric_on_range],
   have [ident h] [] [":=", expr (f.trans e).trans g],
   have [ident I] [":", expr «expr = »(«expr ≃ᵢ »(range (Kuratowski_embedding X), range (Kuratowski_embedding Y)), «expr ≃ᵢ »((nonempty_compacts.Kuratowski_embedding X).val, (nonempty_compacts.Kuratowski_embedding Y).val))] [],
   by { dunfold [ident nonempty_compacts.Kuratowski_embedding] [],
     refl },
   have [ident h'] [] [":=", expr cast I h],
   exact [expr ⟨h'⟩]
 end⟩

/-- Distance on `GH_space`: the distance between two nonempty compact spaces is the infimum
Hausdorff distance between isometric copies of the two spaces in a metric space. For the definition,
we only consider embeddings in `ℓ^∞(ℝ)`, but we will prove below that it works for all spaces. -/
instance : HasDist GH_space :=
  { dist :=
      fun x y =>
        Inf$
          (fun p : nonempty_compacts ℓInftyℝ × nonempty_compacts ℓInftyℝ => Hausdorff_dist p.1.val p.2.val) ''
            Set.Prod { a | «expr⟦ ⟧» a = x } { b | «expr⟦ ⟧» b = y } }

/-- The Gromov-Hausdorff distance between two nonempty compact metric spaces, equal by definition to
the distance of the equivalence classes of these spaces in the Gromov-Hausdorff space. -/
def GH_dist (X : Type u) (Y : Type v) [MetricSpace X] [Nonempty X] [CompactSpace X] [MetricSpace Y] [Nonempty Y]
  [CompactSpace Y] : ℝ :=
  dist (to_GH_space X) (to_GH_space Y)

theorem dist_GH_dist (p q : GH_space) : dist p q = GH_dist p.rep q.rep :=
  by 
    rw [GH_dist, p.to_GH_space_rep, q.to_GH_space_rep]

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Gromov-Hausdorff distance between two spaces is bounded by the Hausdorff distance
of isometric copies of the spaces, in any metric space. -/
theorem GH_dist_le_Hausdorff_dist
{X : Type u}
[metric_space X]
[compact_space X]
[nonempty X]
{Y : Type v}
[metric_space Y]
[compact_space Y]
[nonempty Y]
{γ : Type w}
[metric_space γ]
{Φ : X → γ}
{Ψ : Y → γ}
(ha : isometry Φ)
(hb : isometry Ψ) : «expr ≤ »(GH_dist X Y, Hausdorff_dist (range Φ) (range Ψ)) :=
begin
  rcases [expr exists_mem_of_nonempty X, "with", "⟨", ident xX, ",", "_", "⟩"],
  let [ident s] [":", expr set γ] [":=", expr «expr ∪ »(range Φ, range Ψ)],
  let [ident Φ'] [":", expr X → subtype s] [":=", expr λ y, ⟨Φ y, mem_union_left _ (mem_range_self _)⟩],
  let [ident Ψ'] [":", expr Y → subtype s] [":=", expr λ y, ⟨Ψ y, mem_union_right _ (mem_range_self _)⟩],
  have [ident IΦ'] [":", expr isometry Φ'] [":=", expr λ x y, ha x y],
  have [ident IΨ'] [":", expr isometry Ψ'] [":=", expr λ x y, hb x y],
  have [] [":", expr is_compact s] [],
  from [expr (is_compact_range ha.continuous).union (is_compact_range hb.continuous)],
  letI [] [":", expr metric_space (subtype s)] [":=", expr by apply_instance],
  haveI [] [":", expr compact_space (subtype s)] [":=", expr ⟨is_compact_iff_is_compact_univ.1 «expr‹ ›»(is_compact s)⟩],
  haveI [] [":", expr nonempty (subtype s)] [":=", expr ⟨Φ' xX⟩],
  have [ident ΦΦ'] [":", expr «expr = »(Φ, «expr ∘ »(subtype.val, Φ'))] [],
  by { funext [],
    refl },
  have [ident ΨΨ'] [":", expr «expr = »(Ψ, «expr ∘ »(subtype.val, Ψ'))] [],
  by { funext [],
    refl },
  have [] [":", expr «expr = »(Hausdorff_dist (range Φ) (range Ψ), Hausdorff_dist (range Φ') (range Ψ'))] [],
  { rw ["[", expr ΦΦ', ",", expr ΨΨ', ",", expr range_comp, ",", expr range_comp, "]"] [],
    exact [expr Hausdorff_dist_image isometry_subtype_coe] },
  rw [expr this] [],
  let [ident F] [] [":=", expr Kuratowski_embedding (subtype s)],
  have [] [":", expr «expr = »(Hausdorff_dist «expr '' »(F, range Φ') «expr '' »(F, range Ψ'), Hausdorff_dist (range Φ') (range Ψ'))] [":=", expr Hausdorff_dist_image (Kuratowski_embedding.isometry _)],
  rw ["<-", expr this] [],
  let [ident A] [":", expr nonempty_compacts ℓ_infty_ℝ] [":=", expr ⟨«expr '' »(F, range Φ'), ⟨(range_nonempty _).image _, (is_compact_range IΦ'.continuous).image (Kuratowski_embedding.isometry _).continuous⟩⟩],
  let [ident B] [":", expr nonempty_compacts ℓ_infty_ℝ] [":=", expr ⟨«expr '' »(F, range Ψ'), ⟨(range_nonempty _).image _, (is_compact_range IΨ'.continuous).image (Kuratowski_embedding.isometry _).continuous⟩⟩],
  have [ident AX] [":", expr «expr = »(«expr⟦ ⟧»(A), to_GH_space X)] [],
  { rw [expr eq_to_GH_space_iff] [],
    exact [expr ⟨λ x, F (Φ' x), ⟨(Kuratowski_embedding.isometry _).comp IΦ', by rw [expr range_comp] []⟩⟩] },
  have [ident BY] [":", expr «expr = »(«expr⟦ ⟧»(B), to_GH_space Y)] [],
  { rw [expr eq_to_GH_space_iff] [],
    exact [expr ⟨λ x, F (Ψ' x), ⟨(Kuratowski_embedding.isometry _).comp IΨ', by rw [expr range_comp] []⟩⟩] },
  refine [expr cInf_le ⟨0, begin
      simp [] [] [] ["[", expr lower_bounds, "]"] [] [],
      assume [binders (t _ _ _ _ ht)],
      rw ["<-", expr ht] [],
      exact [expr Hausdorff_dist_nonneg]
    end⟩ _],
  apply [expr (mem_image _ _ _).2],
  existsi [expr (⟨A, B⟩ : «expr × »(nonempty_compacts ℓ_infty_ℝ, nonempty_compacts ℓ_infty_ℝ))],
  simp [] [] [] ["[", expr AX, ",", expr BY, "]"] [] []
end

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The optimal coupling constructed above realizes exactly the Gromov-Hausdorff distance,
essentially by design. -/
theorem Hausdorff_dist_optimal
{X : Type u}
[metric_space X]
[compact_space X]
[nonempty X]
{Y : Type v}
[metric_space Y]
[compact_space Y]
[nonempty Y] : «expr = »(Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)), GH_dist X Y) :=
begin
  inhabit [expr X] [],
  inhabit [expr Y] [],
  have [ident A] [":", expr ∀
   p
   q : nonempty_compacts ℓ_infty_ℝ, «expr = »(«expr⟦ ⟧»(p), to_GH_space X) → «expr = »(«expr⟦ ⟧»(q), to_GH_space Y) → «expr < »(Hausdorff_dist p.val q.val, «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y))) → «expr ≤ »(Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)), Hausdorff_dist p.val q.val)] [],
  { assume [binders (p q hp hq bound)],
    rcases [expr eq_to_GH_space_iff.1 hp, "with", "⟨", ident Φ, ",", "⟨", ident Φisom, ",", ident Φrange, "⟩", "⟩"],
    rcases [expr eq_to_GH_space_iff.1 hq, "with", "⟨", ident Ψ, ",", "⟨", ident Ψisom, ",", ident Ψrange, "⟩", "⟩"],
    have [ident I] [":", expr «expr ≤ »(diam «expr ∪ »(range Φ, range Ψ), «expr + »(«expr + »(«expr * »(2, diam (univ : set X)), 1), «expr * »(2, diam (univ : set Y))))] [],
    { rcases [expr exists_mem_of_nonempty X, "with", "⟨", ident xX, ",", "_", "⟩"],
      have [] [":", expr «expr∃ , »((y «expr ∈ » range Ψ), «expr < »(dist (Φ xX) y, «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y))))] [],
      { rw [expr Ψrange] [],
        have [] [":", expr «expr ∈ »(Φ xX, p.val)] [":=", expr «expr ▸ »(Φrange, mem_range_self _)],
        exact [expr exists_dist_lt_of_Hausdorff_dist_lt this bound (Hausdorff_edist_ne_top_of_nonempty_of_bounded p.2.1 q.2.1 p.2.2.bounded q.2.2.bounded)] },
      rcases [expr this, "with", "⟨", ident y, ",", ident hy, ",", ident dy, "⟩"],
      rcases [expr mem_range.1 hy, "with", "⟨", ident z, ",", ident hzy, "⟩"],
      rw ["<-", expr hzy] ["at", ident dy],
      have [ident DΦ] [":", expr «expr = »(diam (range Φ), diam (univ : set X))] [":=", expr Φisom.diam_range],
      have [ident DΨ] [":", expr «expr = »(diam (range Ψ), diam (univ : set Y))] [":=", expr Ψisom.diam_range],
      calc
        «expr ≤ »(diam «expr ∪ »(range Φ, range Ψ), «expr + »(«expr + »(diam (range Φ), dist (Φ xX) (Ψ z)), diam (range Ψ))) : diam_union (mem_range_self _) (mem_range_self _)
        «expr ≤ »(..., «expr + »(«expr + »(diam (univ : set X), «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y))), diam (univ : set Y))) : by { rw ["[", expr DΦ, ",", expr DΨ, "]"] [],
          apply [expr add_le_add (add_le_add (le_refl _) (le_of_lt dy)) (le_refl _)] }
        «expr = »(..., «expr + »(«expr + »(«expr * »(2, diam (univ : set X)), 1), «expr * »(2, diam (univ : set Y)))) : by ring [] },
    let [ident f] [":", expr «expr ⊕ »(X, Y) → ℓ_infty_ℝ] [":=", expr λ x, match x with
     | inl y := Φ y
     | inr z := Ψ z end],
    let [ident F] [":", expr «expr × »(«expr ⊕ »(X, Y), «expr ⊕ »(X, Y)) → exprℝ()] [":=", expr λ
     p, dist (f p.1) (f p.2)],
    have [ident Fgood] [":", expr «expr ∈ »(F, candidates X Y)] [],
    { simp [] [] ["only"] ["[", expr candidates, ",", expr forall_const, ",", expr and_true, ",", expr add_comm, ",", expr eq_self_iff_true, ",", expr dist_eq_zero, ",", expr and_self, ",", expr set.mem_set_of_eq, "]"] [] [],
      repeat { split },
      { exact [expr λ x y, calc
           «expr = »(F (inl x, inl y), dist (Φ x) (Φ y)) : rfl
           «expr = »(..., dist x y) : Φisom.dist_eq x y] },
      { exact [expr λ x y, calc
           «expr = »(F (inr x, inr y), dist (Ψ x) (Ψ y)) : rfl
           «expr = »(..., dist x y) : Ψisom.dist_eq x y] },
      { exact [expr λ x y, dist_comm _ _] },
      { exact [expr λ x y z, dist_triangle _ _ _] },
      { exact [expr λ x y, calc
           «expr ≤ »(F (x, y), diam «expr ∪ »(range Φ, range Ψ)) : begin
             have [ident A] [":", expr ∀ z : «expr ⊕ »(X, Y), «expr ∈ »(f z, «expr ∪ »(range Φ, range Ψ))] [],
             { assume [binders (z)],
               cases [expr z] [],
               { apply [expr mem_union_left],
                 apply [expr mem_range_self] },
               { apply [expr mem_union_right],
                 apply [expr mem_range_self] } },
             refine [expr dist_le_diam_of_mem _ (A _) (A _)],
             rw ["[", expr Φrange, ",", expr Ψrange, "]"] [],
             exact [expr (p.2.2.union q.2.2).bounded]
           end
           «expr ≤ »(..., «expr + »(«expr + »(«expr * »(2, diam (univ : set X)), 1), «expr * »(2, diam (univ : set Y)))) : I] } },
    let [ident Fb] [] [":=", expr candidates_b_of_candidates F Fgood],
    have [] [":", expr «expr ≤ »(Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)), HD Fb)] [":=", expr Hausdorff_dist_optimal_le_HD _ _ (candidates_b_of_candidates_mem F Fgood)],
    refine [expr le_trans this (le_of_forall_le_of_dense (λ r hr, _))],
    have [ident I1] [":", expr ∀ x : X, «expr ≤ »(«expr⨅ , »((y), Fb (inl x, inr y)), r)] [],
    { assume [binders (x)],
      have [] [":", expr «expr ∈ »(f (inl x), p.val)] [],
      by { rw ["[", "<-", expr Φrange, "]"] [],
        apply [expr mem_range_self] },
      rcases [expr exists_dist_lt_of_Hausdorff_dist_lt this hr (Hausdorff_edist_ne_top_of_nonempty_of_bounded p.2.1 q.2.1 p.2.2.bounded q.2.2.bounded), "with", "⟨", ident z, ",", ident zq, ",", ident hz, "⟩"],
      have [] [":", expr «expr ∈ »(z, range Ψ)] [],
      by rwa ["[", "<-", expr Ψrange, "]"] ["at", ident zq],
      rcases [expr mem_range.1 this, "with", "⟨", ident y, ",", ident hy, "⟩"],
      calc
        «expr ≤ »(«expr⨅ , »((y), Fb (inl x, inr y)), Fb (inl x, inr y)) : cinfi_le (by simpa [] [] [] [] [] ["using", expr HD_below_aux1 0]) y
        «expr = »(..., dist (Φ x) (Ψ y)) : rfl
        «expr = »(..., dist (f (inl x)) z) : by rw [expr hy] []
        «expr ≤ »(..., r) : le_of_lt hz },
    have [ident I2] [":", expr ∀ y : Y, «expr ≤ »(«expr⨅ , »((x), Fb (inl x, inr y)), r)] [],
    { assume [binders (y)],
      have [] [":", expr «expr ∈ »(f (inr y), q.val)] [],
      by { rw ["[", "<-", expr Ψrange, "]"] [],
        apply [expr mem_range_self] },
      rcases [expr exists_dist_lt_of_Hausdorff_dist_lt' this hr (Hausdorff_edist_ne_top_of_nonempty_of_bounded p.2.1 q.2.1 p.2.2.bounded q.2.2.bounded), "with", "⟨", ident z, ",", ident zq, ",", ident hz, "⟩"],
      have [] [":", expr «expr ∈ »(z, range Φ)] [],
      by rwa ["[", "<-", expr Φrange, "]"] ["at", ident zq],
      rcases [expr mem_range.1 this, "with", "⟨", ident x, ",", ident hx, "⟩"],
      calc
        «expr ≤ »(«expr⨅ , »((x), Fb (inl x, inr y)), Fb (inl x, inr y)) : cinfi_le (by simpa [] [] [] [] [] ["using", expr HD_below_aux2 0]) x
        «expr = »(..., dist (Φ x) (Ψ y)) : rfl
        «expr = »(..., dist z (f (inr y))) : by rw [expr hx] []
        «expr ≤ »(..., r) : le_of_lt hz },
    simp [] [] [] ["[", expr HD, ",", expr csupr_le I1, ",", expr csupr_le I2, "]"] [] [] },
  have [ident B] [":", expr ∀
   p
   q : nonempty_compacts ℓ_infty_ℝ, «expr = »(«expr⟦ ⟧»(p), to_GH_space X) → «expr = »(«expr⟦ ⟧»(q), to_GH_space Y) → «expr ≤ »(Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)), Hausdorff_dist p.val q.val)] [],
  { assume [binders (p q hp hq)],
    by_cases [expr h, ":", expr «expr < »(Hausdorff_dist p.val q.val, «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y)))],
    { exact [expr A p q hp hq h] },
    { calc
        «expr ≤ »(Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)), HD (candidates_b_dist X Y)) : Hausdorff_dist_optimal_le_HD _ _ candidates_b_dist_mem_candidates_b
        «expr ≤ »(..., «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y))) : HD_candidates_b_dist_le
        «expr ≤ »(..., Hausdorff_dist p.val q.val) : not_lt.1 h } },
  refine [expr le_antisymm _ _],
  { apply [expr le_cInf],
    { refine [expr (set.nonempty.prod _ _).image _]; exact [expr ⟨_, rfl⟩] },
    { rintro [ident b, "⟨", "⟨", ident p, ",", ident q, "⟩", ",", "⟨", ident hp, ",", ident hq, "⟩", ",", ident rfl, "⟩"],
      exact [expr B p q hp hq] } },
  { exact [expr GH_dist_le_Hausdorff_dist (isometry_optimal_GH_injl X Y) (isometry_optimal_GH_injr X Y)] }
end

/-- The Gromov-Hausdorff distance can also be realized by a coupling in `ℓ^∞(ℝ)`, by embedding
the optimal coupling through its Kuratowski embedding. -/
theorem GH_dist_eq_Hausdorff_dist (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] (Y : Type v)
  [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
  ∃ Φ : X → ℓInftyℝ, ∃ Ψ : Y → ℓInftyℝ, Isometry Φ ∧ Isometry Ψ ∧ GH_dist X Y = Hausdorff_dist (range Φ) (range Ψ) :=
  by 
    let F := kuratowskiEmbedding (optimal_GH_coupling X Y)
    let Φ := F ∘ optimal_GH_injl X Y 
    let Ψ := F ∘ optimal_GH_injr X Y 
    refine' ⟨Φ, Ψ, _, _, _⟩
    ·
      exact (kuratowskiEmbedding.isometry _).comp (isometry_optimal_GH_injl X Y)
    ·
      exact (kuratowskiEmbedding.isometry _).comp (isometry_optimal_GH_injr X Y)
    ·
      rw [←image_univ, ←image_univ, image_comp F, image_univ, image_comp F (optimal_GH_injr X Y), image_univ,
        ←Hausdorff_dist_optimal]
      exact (Hausdorff_dist_image (kuratowskiEmbedding.isometry _)).symm

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Gromov-Hausdorff distance defines a genuine distance on the Gromov-Hausdorff space. -/
instance : metric_space GH_space :=
{ dist_self := λ x, begin
    rcases [expr exists_rep x, "with", "⟨", ident y, ",", ident hy, "⟩"],
    refine [expr le_antisymm _ _],
    { apply [expr cInf_le],
      { exact [expr ⟨0, by { rintro [ident b, "⟨", "⟨", ident u, ",", ident v, "⟩", ",", "⟨", ident hu, ",", ident hv, "⟩", ",", ident rfl, "⟩"],
            exact [expr Hausdorff_dist_nonneg] }⟩] },
      { simp [] [] [] [] [] [],
        existsi ["[", expr y, ",", expr y, "]"],
        simpa [] [] [] [] [] [] } },
    { apply [expr le_cInf],
      { exact [expr (nonempty.prod ⟨y, hy⟩ ⟨y, hy⟩).image _] },
      { rintro [ident b, "⟨", "⟨", ident u, ",", ident v, "⟩", ",", "⟨", ident hu, ",", ident hv, "⟩", ",", ident rfl, "⟩"],
        exact [expr Hausdorff_dist_nonneg] } }
  end,
  dist_comm := λ x y, begin
    have [ident A] [":", expr «expr = »(«expr '' »(λ
       p : «expr × »(nonempty_compacts ℓ_infty_ℝ, nonempty_compacts ℓ_infty_ℝ), Hausdorff_dist p.fst.val p.snd.val, set.prod {a | «expr = »(«expr⟦ ⟧»(a), x)} {b | «expr = »(«expr⟦ ⟧»(b), y)}), «expr '' »(«expr ∘ »(λ
        p : «expr × »(nonempty_compacts ℓ_infty_ℝ, nonempty_compacts ℓ_infty_ℝ), Hausdorff_dist p.fst.val p.snd.val, prod.swap), set.prod {a | «expr = »(«expr⟦ ⟧»(a), x)} {b | «expr = »(«expr⟦ ⟧»(b), y)}))] [":=", expr by { congr,
       funext [],
       simp [] [] [] [] [] [],
       rw [expr Hausdorff_dist_comm] [] }],
    simp [] [] ["only"] ["[", expr dist, ",", expr A, ",", expr image_comp, ",", expr image_swap_prod, "]"] [] []
  end,
  eq_of_dist_eq_zero := λ x y hxy, begin
    rcases [expr GH_dist_eq_Hausdorff_dist x.rep y.rep, "with", "⟨", ident Φ, ",", ident Ψ, ",", ident Φisom, ",", ident Ψisom, ",", ident DΦΨ, "⟩"],
    rw ["[", "<-", expr dist_GH_dist, ",", expr hxy, "]"] ["at", ident DΦΨ],
    have [] [":", expr «expr = »(range Φ, range Ψ)] [],
    { have [ident hΦ] [":", expr is_compact (range Φ)] [":=", expr is_compact_range Φisom.continuous],
      have [ident hΨ] [":", expr is_compact (range Ψ)] [":=", expr is_compact_range Ψisom.continuous],
      apply [expr (is_closed.Hausdorff_dist_zero_iff_eq _ _ _).1 DΦΨ.symm],
      { exact [expr hΦ.is_closed] },
      { exact [expr hΨ.is_closed] },
      { exact [expr Hausdorff_edist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _) hΦ.bounded hΨ.bounded] } },
    have [ident T] [":", expr «expr = »(«expr ≃ᵢ »(range Ψ, y.rep), «expr ≃ᵢ »(range Φ, y.rep))] [],
    by rw [expr this] [],
    have [ident eΨ] [] [":=", expr cast T Ψisom.isometric_on_range.symm],
    have [ident e] [] [":=", expr Φisom.isometric_on_range.trans eΨ],
    rw ["[", "<-", expr x.to_GH_space_rep, ",", "<-", expr y.to_GH_space_rep, ",", expr to_GH_space_eq_to_GH_space_iff_isometric, "]"] [],
    exact [expr ⟨e⟩]
  end,
  dist_triangle := λ x y z, begin
    let [ident X] [] [":=", expr x.rep],
    let [ident Y] [] [":=", expr y.rep],
    let [ident Z] [] [":=", expr z.rep],
    let [ident γ1] [] [":=", expr optimal_GH_coupling X Y],
    let [ident γ2] [] [":=", expr optimal_GH_coupling Y Z],
    let [ident Φ] [":", expr Y → γ1] [":=", expr optimal_GH_injr X Y],
    have [ident hΦ] [":", expr isometry Φ] [":=", expr isometry_optimal_GH_injr X Y],
    let [ident Ψ] [":", expr Y → γ2] [":=", expr optimal_GH_injl Y Z],
    have [ident hΨ] [":", expr isometry Ψ] [":=", expr isometry_optimal_GH_injl Y Z],
    let [ident γ] [] [":=", expr glue_space hΦ hΨ],
    letI [] [":", expr metric_space γ] [":=", expr metric.metric_space_glue_space hΦ hΨ],
    have [ident Comm] [":", expr «expr = »(«expr ∘ »(to_glue_l hΦ hΨ, optimal_GH_injr X Y), «expr ∘ »(to_glue_r hΦ hΨ, optimal_GH_injl Y Z))] [":=", expr to_glue_commute hΦ hΨ],
    calc
      «expr = »(dist x z, dist (to_GH_space X) (to_GH_space Z)) : by rw ["[", expr x.to_GH_space_rep, ",", expr z.to_GH_space_rep, "]"] []
      «expr ≤ »(..., Hausdorff_dist (range «expr ∘ »(to_glue_l hΦ hΨ, optimal_GH_injl X Y)) (range «expr ∘ »(to_glue_r hΦ hΨ, optimal_GH_injr Y Z))) : GH_dist_le_Hausdorff_dist ((to_glue_l_isometry hΦ hΨ).comp (isometry_optimal_GH_injl X Y)) ((to_glue_r_isometry hΦ hΨ).comp (isometry_optimal_GH_injr Y Z))
      «expr ≤ »(..., «expr + »(Hausdorff_dist (range «expr ∘ »(to_glue_l hΦ hΨ, optimal_GH_injl X Y)) (range «expr ∘ »(to_glue_l hΦ hΨ, optimal_GH_injr X Y)), Hausdorff_dist (range «expr ∘ »(to_glue_l hΦ hΨ, optimal_GH_injr X Y)) (range «expr ∘ »(to_glue_r hΦ hΨ, optimal_GH_injr Y Z)))) : begin
        refine [expr Hausdorff_dist_triangle (Hausdorff_edist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _) _ _)],
        { exact [expr (is_compact_range (isometry.continuous ((to_glue_l_isometry hΦ hΨ).comp (isometry_optimal_GH_injl X Y)))).bounded] },
        { exact [expr (is_compact_range (isometry.continuous ((to_glue_l_isometry hΦ hΨ).comp (isometry_optimal_GH_injr X Y)))).bounded] }
      end
      «expr = »(..., «expr + »(Hausdorff_dist «expr '' »(to_glue_l hΦ hΨ, range (optimal_GH_injl X Y)) «expr '' »(to_glue_l hΦ hΨ, range (optimal_GH_injr X Y)), Hausdorff_dist «expr '' »(to_glue_r hΦ hΨ, range (optimal_GH_injl Y Z)) «expr '' »(to_glue_r hΦ hΨ, range (optimal_GH_injr Y Z)))) : by simp [] [] ["only"] ["[", "<-", expr range_comp, ",", expr Comm, ",", expr eq_self_iff_true, ",", expr add_right_inj, "]"] [] []
      «expr = »(..., «expr + »(Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)), Hausdorff_dist (range (optimal_GH_injl Y Z)) (range (optimal_GH_injr Y Z)))) : by rw ["[", expr Hausdorff_dist_image (to_glue_l_isometry hΦ hΨ), ",", expr Hausdorff_dist_image (to_glue_r_isometry hΦ hΨ), "]"] []
      «expr = »(..., «expr + »(dist (to_GH_space X) (to_GH_space Y), dist (to_GH_space Y) (to_GH_space Z))) : by rw ["[", expr Hausdorff_dist_optimal, ",", expr Hausdorff_dist_optimal, ",", expr GH_dist, ",", expr GH_dist, "]"] []
      «expr = »(..., «expr + »(dist x y, dist y z)) : by rw ["[", expr x.to_GH_space_rep, ",", expr y.to_GH_space_rep, ",", expr z.to_GH_space_rep, "]"] []
  end }

end GHSpace

end GromovHausdorff

/-- In particular, nonempty compacts of a metric space map to `GH_space`. We register this
in the topological_space namespace to take advantage of the notation `p.to_GH_space`. -/
def TopologicalSpace.NonemptyCompacts.toGHSpace {X : Type u} [MetricSpace X] (p : nonempty_compacts X) :
  GromovHausdorff.GHSpace :=
  GromovHausdorff.toGHSpace p.val

open TopologicalSpace

namespace GromovHausdorff

section NonemptyCompacts

variable {X : Type u} [MetricSpace X]

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem GH_dist_le_nonempty_compacts_dist
(p q : nonempty_compacts X) : «expr ≤ »(dist p.to_GH_space q.to_GH_space, dist p q) :=
begin
  have [ident ha] [":", expr isometry (coe : p.val → X)] [":=", expr isometry_subtype_coe],
  have [ident hb] [":", expr isometry (coe : q.val → X)] [":=", expr isometry_subtype_coe],
  have [ident A] [":", expr «expr = »(dist p q, Hausdorff_dist p.val q.val)] [":=", expr rfl],
  have [ident I] [":", expr «expr = »(p.val, range (coe : p.val → X))] [],
  by simp [] [] [] [] [] [],
  have [ident J] [":", expr «expr = »(q.val, range (coe : q.val → X))] [],
  by simp [] [] [] [] [] [],
  rw ["[", expr I, ",", expr J, "]"] ["at", ident A],
  rw [expr A] [],
  exact [expr GH_dist_le_Hausdorff_dist ha hb]
end

theorem to_GH_space_lipschitz : LipschitzWith 1 (nonempty_compacts.to_GH_space : nonempty_compacts X → GH_space) :=
  LipschitzWith.mk_one GH_dist_le_nonempty_compacts_dist

theorem to_GH_space_continuous : Continuous (nonempty_compacts.to_GH_space : nonempty_compacts X → GH_space) :=
  to_GH_space_lipschitz.Continuous

end NonemptyCompacts

section 

variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y]
  [Nonempty Y]

attribute [local instance] Sum.topologicalSpace Sum.uniformSpace

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If there are subsets which are `ε₁`-dense and `ε₃`-dense in two spaces, and
isometric up to `ε₂`, then the Gromov-Hausdorff distance between the spaces is bounded by
`ε₁ + ε₂/2 + ε₃`. -/
theorem GH_dist_le_of_approx_subsets
{s : set X}
(Φ : s → Y)
{ε₁ ε₂ ε₃ : exprℝ()}
(hs : ∀ x : X, «expr∃ , »((y «expr ∈ » s), «expr ≤ »(dist x y, ε₁)))
(hs' : ∀ x : Y, «expr∃ , »((y : s), «expr ≤ »(dist x (Φ y), ε₃)))
(H : ∀
 x
 y : s, «expr ≤ »(«expr| |»(«expr - »(dist x y, dist (Φ x) (Φ y))), ε₂)) : «expr ≤ »(GH_dist X Y, «expr + »(«expr + »(ε₁, «expr / »(ε₂, 2)), ε₃)) :=
begin
  refine [expr le_of_forall_pos_le_add (λ δ δ0, _)],
  rcases [expr exists_mem_of_nonempty X, "with", "⟨", ident xX, ",", "_", "⟩"],
  rcases [expr hs xX, "with", "⟨", ident xs, ",", ident hxs, ",", ident Dxs, "⟩"],
  have [ident sne] [":", expr s.nonempty] [":=", expr ⟨xs, hxs⟩],
  letI [] [":", expr nonempty s] [":=", expr sne.to_subtype],
  have [] [":", expr «expr ≤ »(0, ε₂)] [":=", expr le_trans (abs_nonneg _) (H ⟨xs, hxs⟩ ⟨xs, hxs⟩)],
  have [] [":", expr ∀
   p
   q : s, «expr ≤ »(«expr| |»(«expr - »(dist p q, dist (Φ p) (Φ q))), «expr * »(2, «expr + »(«expr / »(ε₂, 2), δ)))] [":=", expr λ
   p q, calc
     «expr ≤ »(«expr| |»(«expr - »(dist p q, dist (Φ p) (Φ q))), ε₂) : H p q
     «expr ≤ »(..., «expr * »(2, «expr + »(«expr / »(ε₂, 2), δ))) : by linarith [] [] []],
  letI [] [":", expr metric_space «expr ⊕ »(X, Y)] [":=", expr glue_metric_approx (λ
    x : s, (x : X)) (λ x, Φ x) «expr + »(«expr / »(ε₂, 2), δ) (by linarith [] [] []) this],
  let [ident Fl] [] [":=", expr @sum.inl X Y],
  let [ident Fr] [] [":=", expr @sum.inr X Y],
  have [ident Il] [":", expr isometry Fl] [":=", expr isometry_emetric_iff_metric.2 (λ x y, rfl)],
  have [ident Ir] [":", expr isometry Fr] [":=", expr isometry_emetric_iff_metric.2 (λ x y, rfl)],
  have [] [":", expr «expr ≤ »(GH_dist X Y, Hausdorff_dist (range Fl) (range Fr))] [":=", expr GH_dist_le_Hausdorff_dist Il Ir],
  have [] [":", expr «expr ≤ »(Hausdorff_dist (range Fl) (range Fr), «expr + »(Hausdorff_dist (range Fl) «expr '' »(Fl, s), Hausdorff_dist «expr '' »(Fl, s) (range Fr)))] [],
  { have [ident B] [":", expr bounded (range Fl)] [":=", expr (is_compact_range Il.continuous).bounded],
    exact [expr Hausdorff_dist_triangle (Hausdorff_edist_ne_top_of_nonempty_of_bounded (range_nonempty _) (sne.image _) B (B.mono (image_subset_range _ _)))] },
  have [] [":", expr «expr ≤ »(Hausdorff_dist «expr '' »(Fl, s) (range Fr), «expr + »(Hausdorff_dist «expr '' »(Fl, s) «expr '' »(Fr, range Φ), Hausdorff_dist «expr '' »(Fr, range Φ) (range Fr)))] [],
  { have [ident B] [":", expr bounded (range Fr)] [":=", expr (is_compact_range Ir.continuous).bounded],
    exact [expr Hausdorff_dist_triangle' (Hausdorff_edist_ne_top_of_nonempty_of_bounded ((range_nonempty _).image _) (range_nonempty _) (bounded.mono (image_subset_range _ _) B) B)] },
  have [] [":", expr «expr ≤ »(Hausdorff_dist (range Fl) «expr '' »(Fl, s), ε₁)] [],
  { rw ["[", "<-", expr image_univ, ",", expr Hausdorff_dist_image Il, "]"] [],
    have [] [":", expr «expr ≤ »(0, ε₁)] [":=", expr le_trans dist_nonneg Dxs],
    refine [expr Hausdorff_dist_le_of_mem_dist this (λ
      x hx, hs x) (λ x hx, ⟨x, mem_univ _, by simpa [] [] [] [] [] []⟩)] },
  have [] [":", expr «expr ≤ »(Hausdorff_dist «expr '' »(Fl, s) «expr '' »(Fr, range Φ), «expr + »(«expr / »(ε₂, 2), δ))] [],
  { refine [expr Hausdorff_dist_le_of_mem_dist (by linarith [] [] []) _ _],
    { assume [binders (x' hx')],
      rcases [expr (set.mem_image _ _ _).1 hx', "with", "⟨", ident x, ",", "⟨", ident x_in_s, ",", ident xx', "⟩", "⟩"],
      rw ["<-", expr xx'] [],
      use ["[", expr Fr (Φ ⟨x, x_in_s⟩), ",", expr mem_image_of_mem Fr (mem_range_self _), "]"],
      exact [expr le_of_eq (glue_dist_glued_points (λ x : s, (x : X)) Φ «expr + »(«expr / »(ε₂, 2), δ) ⟨x, x_in_s⟩)] },
    { assume [binders (x' hx')],
      rcases [expr (set.mem_image _ _ _).1 hx', "with", "⟨", ident y, ",", "⟨", ident y_in_s', ",", ident yx', "⟩", "⟩"],
      rcases [expr mem_range.1 y_in_s', "with", "⟨", ident x, ",", ident xy, "⟩"],
      use ["[", expr Fl x, ",", expr mem_image_of_mem _ x.2, "]"],
      rw ["[", "<-", expr yx', ",", "<-", expr xy, ",", expr dist_comm, "]"] [],
      exact [expr le_of_eq (glue_dist_glued_points (@subtype.val X s) Φ «expr + »(«expr / »(ε₂, 2), δ) x)] } },
  have [] [":", expr «expr ≤ »(Hausdorff_dist «expr '' »(Fr, range Φ) (range Fr), ε₃)] [],
  { rw ["[", "<-", expr @image_univ _ _ Fr, ",", expr Hausdorff_dist_image Ir, "]"] [],
    rcases [expr exists_mem_of_nonempty Y, "with", "⟨", ident xY, ",", "_", "⟩"],
    rcases [expr hs' xY, "with", "⟨", ident xs', ",", ident Dxs', "⟩"],
    have [] [":", expr «expr ≤ »(0, ε₃)] [":=", expr le_trans dist_nonneg Dxs'],
    refine [expr Hausdorff_dist_le_of_mem_dist this (λ x hx, ⟨x, mem_univ _, by simpa [] [] [] [] [] []⟩) (λ x _, _)],
    rcases [expr hs' x, "with", "⟨", ident y, ",", ident Dy, "⟩"],
    exact [expr ⟨Φ y, mem_range_self _, Dy⟩] },
  linarith [] [] []
end

end 

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Gromov-Hausdorff space is second countable. -/ instance : second_countable_topology GH_space :=
begin
  refine [expr second_countable_of_countable_discretization (λ δ δpos, _)],
  let [ident ε] [] [":=", expr «expr * »(«expr / »(2, 5), δ)],
  have [ident εpos] [":", expr «expr < »(0, ε)] [":=", expr mul_pos (by norm_num [] []) δpos],
  have [] [":", expr ∀
   p : GH_space, «expr∃ , »((s : set p.rep), «expr ∧ »(finite s, «expr ⊆ »(univ, «expr⋃ , »((x «expr ∈ » s), ball x ε))))] [":=", expr λ
   p, by simpa [] [] [] [] [] ["using", expr finite_cover_balls_of_compact (@compact_univ p.rep _ _) εpos]],
  choose [] [ident s] [ident hs] ["using", expr this],
  have [] [":", expr ∀
   p : GH_space, ∀ t : set p.rep, finite t → «expr∃ , »((n : exprℕ()), «expr∃ , »((e : equiv t (fin n)), true))] [],
  { assume [binders (p t ht)],
    letI [] [":", expr fintype t] [":=", expr finite.fintype ht],
    exact [expr ⟨fintype.card t, fintype.equiv_fin t, trivial⟩] },
  choose [] [ident N] [ident e, ident hne] ["using", expr this],
  let [ident N] [] [":=", expr λ p : GH_space, N p (s p) (hs p).1],
  let [ident E] [] [":=", expr λ p : GH_space, e p (s p) (hs p).1],
  let [ident F] [":", expr GH_space → «exprΣ , »((n : exprℕ()), fin n → fin n → exprℤ())] [":=", expr λ
   p, ⟨N p, λ a b, «expr⌊ ⌋»(«expr * »(«expr ⁻¹»(ε), dist ((E p).symm a) ((E p).symm b)))⟩],
  refine [expr ⟨«exprΣ , »((n), fin n → fin n → exprℤ()), by apply_instance, F, λ p q hpq, _⟩],
  have [ident Npq] [":", expr «expr = »(N p, N q)] [":=", expr (sigma.mk.inj_iff.1 hpq).1],
  let [ident Ψ] [":", expr s p → s q] [":=", expr λ x, (E q).symm (fin.cast Npq (E p x))],
  let [ident Φ] [":", expr s p → q.rep] [":=", expr λ x, Ψ x],
  have [ident main] [":", expr «expr ≤ »(GH_dist p.rep q.rep, «expr + »(«expr + »(ε, «expr / »(ε, 2)), ε))] [],
  { refine [expr GH_dist_le_of_approx_subsets Φ _ _ _],
    show [expr ∀ x : p.rep, «expr∃ , »((y : p.rep) (H : «expr ∈ »(y, s p)), «expr ≤ »(dist x y, ε))],
    { assume [binders (x)],
      have [] [":", expr «expr ∈ »(x, «expr⋃ , »((y «expr ∈ » s p), ball y ε))] [":=", expr (hs p).2 (mem_univ _)],
      rcases [expr mem_bUnion_iff.1 this, "with", "⟨", ident y, ",", ident ys, ",", ident hy, "⟩"],
      exact [expr ⟨y, ys, le_of_lt hy⟩] },
    show [expr ∀ x : q.rep, «expr∃ , »((z : s p), «expr ≤ »(dist x (Φ z), ε))],
    { assume [binders (x)],
      have [] [":", expr «expr ∈ »(x, «expr⋃ , »((y «expr ∈ » s q), ball y ε))] [":=", expr (hs q).2 (mem_univ _)],
      rcases [expr mem_bUnion_iff.1 this, "with", "⟨", ident y, ",", ident ys, ",", ident hy, "⟩"],
      let [ident i] [":", expr exprℕ()] [":=", expr E q ⟨y, ys⟩],
      let [ident hi] [] [":=", expr (E q ⟨y, ys⟩).is_lt],
      have [ident ihi_eq] [":", expr «expr = »((⟨i, hi⟩ : fin (N q)), E q ⟨y, ys⟩)] [],
      by rw ["[", expr fin.ext_iff, ",", expr fin.coe_mk, "]"] [],
      have [ident hiq] [":", expr «expr < »(i, N q)] [":=", expr hi],
      have [ident hip] [":", expr «expr < »(i, N p)] [],
      { rwa [expr Npq.symm] ["at", ident hiq] },
      let [ident z] [] [":=", expr (E p).symm ⟨i, hip⟩],
      use [expr z],
      have [ident C1] [":", expr «expr = »(E p z, ⟨i, hip⟩)] [":=", expr (E p).apply_symm_apply ⟨i, hip⟩],
      have [ident C2] [":", expr «expr = »(fin.cast Npq ⟨i, hip⟩, ⟨i, hi⟩)] [":=", expr rfl],
      have [ident C3] [":", expr «expr = »((E q).symm ⟨i, hi⟩, ⟨y, ys⟩)] [],
      by { rw [expr ihi_eq] [],
        exact [expr (E q).symm_apply_apply ⟨y, ys⟩] },
      have [] [":", expr «expr = »(Φ z, y)] [":=", expr by { simp [] [] ["only"] ["[", expr Φ, ",", expr Ψ, "]"] [] [],
         rw ["[", expr C1, ",", expr C2, ",", expr C3, "]"] [],
         refl }],
      rw [expr this] [],
      exact [expr le_of_lt hy] },
    show [expr ∀ x y : s p, «expr ≤ »(«expr| |»(«expr - »(dist x y, dist (Φ x) (Φ y))), ε)],
    { assume [binders (x y)],
      have [] [":", expr «expr = »(dist (Φ x) (Φ y), dist (Ψ x) (Ψ y))] [":=", expr rfl],
      rw [expr this] [],
      let [ident i] [":", expr exprℕ()] [":=", expr E p x],
      have [ident hip] [":", expr «expr < »(i, N p)] [":=", expr (E p x).2],
      have [ident hiq] [":", expr «expr < »(i, N q)] [],
      by rwa [expr Npq] ["at", ident hip],
      have [ident i'] [":", expr «expr = »(i, E q (Ψ x))] [],
      by { simp [] [] [] ["[", expr Ψ, "]"] [] [] },
      let [ident j] [":", expr exprℕ()] [":=", expr E p y],
      have [ident hjp] [":", expr «expr < »(j, N p)] [":=", expr (E p y).2],
      have [ident hjq] [":", expr «expr < »(j, N q)] [],
      by rwa [expr Npq] ["at", ident hjp],
      have [ident j'] [":", expr «expr = »(j, (E q (Ψ y)).1)] [],
      by { simp [] [] [] ["[", expr Ψ, "]"] [] [] },
      have [] [":", expr «expr = »((F p).2 (E p x) (E p y), floor «expr * »(«expr ⁻¹»(ε), dist x y))] [],
      by simp [] [] ["only"] ["[", expr F, ",", expr (E p).symm_apply_apply, "]"] [] [],
      have [ident Ap] [":", expr «expr = »((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩, floor «expr * »(«expr ⁻¹»(ε), dist x y))] [],
      by { rw ["<-", expr this] [],
        congr; apply [expr (fin.ext_iff _ _).2]; refl },
      have [] [":", expr «expr = »((F q).2 (E q (Ψ x)) (E q (Ψ y)), floor «expr * »(«expr ⁻¹»(ε), dist (Ψ x) (Ψ y)))] [],
      by simp [] [] ["only"] ["[", expr F, ",", expr (E q).symm_apply_apply, "]"] [] [],
      have [ident Aq] [":", expr «expr = »((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩, floor «expr * »(«expr ⁻¹»(ε), dist (Ψ x) (Ψ y)))] [],
      by { rw ["<-", expr this] [],
        congr; apply [expr (fin.ext_iff _ _).2]; [exact [expr i'], exact [expr j']] },
      have [] [":", expr «expr = »((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩, (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩)] [],
      { revert [ident hiq, ident hjq],
        change [expr N q] ["with", expr (F q).1] [],
        generalize_hyp [] [":"] [expr «expr = »(F q, f)] ["at", ident hpq, "⊢"],
        subst [expr hpq],
        intros [],
        refl },
      rw ["[", expr Ap, ",", expr Aq, "]"] ["at", ident this],
      have [ident I] [] [":=", expr calc
         «expr = »(«expr * »(«expr| |»(«expr ⁻¹»(ε)), «expr| |»(«expr - »(dist x y, dist (Ψ x) (Ψ y)))), «expr| |»(«expr * »(«expr ⁻¹»(ε), «expr - »(dist x y, dist (Ψ x) (Ψ y))))) : (abs_mul _ _).symm
         «expr = »(..., «expr| |»(«expr - »(«expr * »(«expr ⁻¹»(ε), dist x y), «expr * »(«expr ⁻¹»(ε), dist (Ψ x) (Ψ y))))) : by { congr,
           ring [] }
         «expr ≤ »(..., 1) : le_of_lt (abs_sub_lt_one_of_floor_eq_floor this)],
      calc
        «expr = »(«expr| |»(«expr - »(dist x y, dist (Ψ x) (Ψ y))), «expr * »(«expr * »(ε, «expr ⁻¹»(ε)), «expr| |»(«expr - »(dist x y, dist (Ψ x) (Ψ y))))) : by rw ["[", expr mul_inv_cancel (ne_of_gt εpos), ",", expr one_mul, "]"] []
        «expr = »(..., «expr * »(ε, «expr * »(«expr| |»(«expr ⁻¹»(ε)), «expr| |»(«expr - »(dist x y, dist (Ψ x) (Ψ y)))))) : by rw ["[", expr abs_of_nonneg (le_of_lt (inv_pos.2 εpos)), ",", expr mul_assoc, "]"] []
        «expr ≤ »(..., «expr * »(ε, 1)) : mul_le_mul_of_nonneg_left I (le_of_lt εpos)
        «expr = »(..., ε) : mul_one _ } },
  calc
    «expr = »(dist p q, GH_dist p.rep q.rep) : dist_GH_dist p q
    «expr ≤ »(..., «expr + »(«expr + »(ε, «expr / »(ε, 2)), ε)) : main
    «expr = »(..., δ) : by { simp [] [] [] ["[", expr ε, "]"] [] [],
      ring [] }
end

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Compactness criterion: a closed set of compact metric spaces is compact if the spaces have
a uniformly bounded diameter, and for all `ε` the number of balls of radius `ε` required
to cover the spaces is uniformly bounded. This is an equivalence, but we only prove the
interesting direction that these conditions imply compactness. -/
theorem totally_bounded
{t : set GH_space}
{C : exprℝ()}
{u : exprℕ() → exprℝ()}
{K : exprℕ() → exprℕ()}
(ulim : tendsto u at_top (expr𝓝() 0))
(hdiam : ∀ p «expr ∈ » t, «expr ≤ »(diam (univ : set (GH_space.rep p)), C))
(hcov : ∀
 p «expr ∈ » t, ∀
 n : exprℕ(), «expr∃ , »((s : set (GH_space.rep p)), «expr ∧ »(«expr ≤ »(cardinal.mk s, K n), «expr ⊆ »(univ, «expr⋃ , »((x «expr ∈ » s), ball x (u n)))))) : totally_bounded t :=
begin
  refine [expr metric.totally_bounded_of_finite_discretization (λ δ δpos, _)],
  let [ident ε] [] [":=", expr «expr * »(«expr / »(1, 5), δ)],
  have [ident εpos] [":", expr «expr < »(0, ε)] [":=", expr mul_pos (by norm_num [] []) δpos],
  rcases [expr metric.tendsto_at_top.1 ulim ε εpos, "with", "⟨", ident n, ",", ident hn, "⟩"],
  have [ident u_le_ε] [":", expr «expr ≤ »(u n, ε)] [],
  { have [] [] [":=", expr hn n (le_refl _)],
    simp [] [] ["only"] ["[", expr real.dist_eq, ",", expr add_zero, ",", expr sub_eq_add_neg, ",", expr neg_zero, "]"] [] ["at", ident this],
    exact [expr le_of_lt (lt_of_le_of_lt (le_abs_self _) this)] },
  have [] [":", expr ∀
   p : GH_space, «expr∃ , »((s : set p.rep), «expr∃ , »((N «expr ≤ » K n), «expr∃ , »((E : equiv s (fin N)), «expr ∈ »(p, t) → «expr ⊆ »(univ, «expr⋃ , »((x «expr ∈ » s), ball x (u n))))))] [],
  { assume [binders (p)],
    by_cases [expr hp, ":", expr «expr ∉ »(p, t)],
    { have [] [":", expr nonempty (equiv («expr∅»() : set p.rep) (fin 0))] [],
      { rw ["<-", expr fintype.card_eq] [],
        simp [] [] [] [] [] [] },
      use ["[", expr «expr∅»(), ",", expr 0, ",", expr bot_le, ",", expr choice this, "]"] },
    { rcases [expr hcov _ (set.not_not_mem.1 hp) n, "with", "⟨", ident s, ",", "⟨", ident scard, ",", ident scover, "⟩", "⟩"],
      rcases [expr cardinal.lt_omega.1 (lt_of_le_of_lt scard (cardinal.nat_lt_omega _)), "with", "⟨", ident N, ",", ident hN, "⟩"],
      rw ["[", expr hN, ",", expr cardinal.nat_cast_le, "]"] ["at", ident scard],
      have [] [":", expr «expr = »(cardinal.mk s, cardinal.mk (fin N))] [],
      by rw ["[", expr hN, ",", expr cardinal.mk_fin, "]"] [],
      cases [expr quotient.exact this] ["with", ident E],
      use ["[", expr s, ",", expr N, ",", expr scard, ",", expr E, "]"],
      simp [] [] [] ["[", expr hp, ",", expr scover, "]"] [] [] } },
  choose [] [ident s] [ident N, ident hN, ident E, ident hs] ["using", expr this],
  let [ident M] [] [":=", expr «expr⌊ ⌋₊»(«expr * »(«expr ⁻¹»(ε), max C 0))],
  let [ident F] [":", expr GH_space → «exprΣ , »((k : fin (K n).succ), fin k → fin k → fin M.succ)] [":=", expr λ
   p, ⟨⟨N p, lt_of_le_of_lt (hN p) (nat.lt_succ_self _)⟩, λ
    a
    b, ⟨min M «expr⌊ ⌋₊»(«expr * »(«expr ⁻¹»(ε), dist ((E p).symm a) ((E p).symm b))), (min_le_left _ _).trans_lt (nat.lt_succ_self _)⟩⟩],
  refine [expr ⟨_, _, λ p, F p, _⟩],
  apply_instance,
  rintros ["⟨", ident p, ",", ident pt, "⟩", "⟨", ident q, ",", ident qt, "⟩", ident hpq],
  have [ident Npq] [":", expr «expr = »(N p, N q)] [":=", expr (fin.ext_iff _ _).1 (sigma.mk.inj_iff.1 hpq).1],
  let [ident Ψ] [":", expr s p → s q] [":=", expr λ x, (E q).symm (fin.cast Npq (E p x))],
  let [ident Φ] [":", expr s p → q.rep] [":=", expr λ x, Ψ x],
  have [ident main] [":", expr «expr ≤ »(GH_dist p.rep q.rep, «expr + »(«expr + »(ε, «expr / »(ε, 2)), ε))] [],
  { refine [expr GH_dist_le_of_approx_subsets Φ _ _ _],
    show [expr ∀ x : p.rep, «expr∃ , »((y : p.rep) (H : «expr ∈ »(y, s p)), «expr ≤ »(dist x y, ε))],
    { assume [binders (x)],
      have [] [":", expr «expr ∈ »(x, «expr⋃ , »((y «expr ∈ » s p), ball y (u n)))] [":=", expr hs p pt (mem_univ _)],
      rcases [expr mem_bUnion_iff.1 this, "with", "⟨", ident y, ",", ident ys, ",", ident hy, "⟩"],
      exact [expr ⟨y, ys, le_trans (le_of_lt hy) u_le_ε⟩] },
    show [expr ∀ x : q.rep, «expr∃ , »((z : s p), «expr ≤ »(dist x (Φ z), ε))],
    { assume [binders (x)],
      have [] [":", expr «expr ∈ »(x, «expr⋃ , »((y «expr ∈ » s q), ball y (u n)))] [":=", expr hs q qt (mem_univ _)],
      rcases [expr mem_bUnion_iff.1 this, "with", "⟨", ident y, ",", ident ys, ",", ident hy, "⟩"],
      let [ident i] [":", expr exprℕ()] [":=", expr E q ⟨y, ys⟩],
      let [ident hi] [] [":=", expr (E q ⟨y, ys⟩).2],
      have [ident ihi_eq] [":", expr «expr = »((⟨i, hi⟩ : fin (N q)), E q ⟨y, ys⟩)] [],
      by rw ["[", expr fin.ext_iff, ",", expr fin.coe_mk, "]"] [],
      have [ident hiq] [":", expr «expr < »(i, N q)] [":=", expr hi],
      have [ident hip] [":", expr «expr < »(i, N p)] [],
      { rwa [expr Npq.symm] ["at", ident hiq] },
      let [ident z] [] [":=", expr (E p).symm ⟨i, hip⟩],
      use [expr z],
      have [ident C1] [":", expr «expr = »(E p z, ⟨i, hip⟩)] [":=", expr (E p).apply_symm_apply ⟨i, hip⟩],
      have [ident C2] [":", expr «expr = »(fin.cast Npq ⟨i, hip⟩, ⟨i, hi⟩)] [":=", expr rfl],
      have [ident C3] [":", expr «expr = »((E q).symm ⟨i, hi⟩, ⟨y, ys⟩)] [],
      by { rw [expr ihi_eq] [],
        exact [expr (E q).symm_apply_apply ⟨y, ys⟩] },
      have [] [":", expr «expr = »(Φ z, y)] [":=", expr by { simp [] [] ["only"] ["[", expr Φ, ",", expr Ψ, "]"] [] [],
         rw ["[", expr C1, ",", expr C2, ",", expr C3, "]"] [],
         refl }],
      rw [expr this] [],
      exact [expr le_trans (le_of_lt hy) u_le_ε] },
    show [expr ∀ x y : s p, «expr ≤ »(«expr| |»(«expr - »(dist x y, dist (Φ x) (Φ y))), ε)],
    { assume [binders (x y)],
      have [] [":", expr «expr = »(dist (Φ x) (Φ y), dist (Ψ x) (Ψ y))] [":=", expr rfl],
      rw [expr this] [],
      let [ident i] [":", expr exprℕ()] [":=", expr E p x],
      have [ident hip] [":", expr «expr < »(i, N p)] [":=", expr (E p x).2],
      have [ident hiq] [":", expr «expr < »(i, N q)] [],
      by rwa [expr Npq] ["at", ident hip],
      have [ident i'] [":", expr «expr = »(i, E q (Ψ x))] [],
      by { simp [] [] [] ["[", expr Ψ, "]"] [] [] },
      let [ident j] [":", expr exprℕ()] [":=", expr E p y],
      have [ident hjp] [":", expr «expr < »(j, N p)] [":=", expr (E p y).2],
      have [ident hjq] [":", expr «expr < »(j, N q)] [],
      by rwa [expr Npq] ["at", ident hjp],
      have [ident j'] [":", expr «expr = »(j, E q (Ψ y))] [],
      by { simp [] [] [] ["[", expr Ψ, "]"] [] [] },
      have [ident Ap] [":", expr «expr = »(((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1, «expr⌊ ⌋₊»(«expr * »(«expr ⁻¹»(ε), dist x y)))] [":=", expr calc
         «expr = »(((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1, ((F p).2 (E p x) (E p y)).1) : by { congr; apply [expr (fin.ext_iff _ _).2]; refl }
         «expr = »(..., min M «expr⌊ ⌋₊»(«expr * »(«expr ⁻¹»(ε), dist x y))) : by simp [] [] ["only"] ["[", expr F, ",", expr (E p).symm_apply_apply, "]"] [] []
         «expr = »(..., «expr⌊ ⌋₊»(«expr * »(«expr ⁻¹»(ε), dist x y))) : begin
           refine [expr min_eq_right (nat.floor_mono _)],
           refine [expr mul_le_mul_of_nonneg_left (le_trans _ (le_max_left _ _)) (inv_pos.2 εpos).le],
           change [expr «expr ≤ »(dist (x : p.rep) y, C)] [] [],
           refine [expr le_trans (dist_le_diam_of_mem compact_univ.bounded (mem_univ _) (mem_univ _)) _],
           exact [expr hdiam p pt]
         end],
      have [ident Aq] [":", expr «expr = »(((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1, «expr⌊ ⌋₊»(«expr * »(«expr ⁻¹»(ε), dist (Ψ x) (Ψ y))))] [":=", expr calc
         «expr = »(((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1, ((F q).2 (E q (Ψ x)) (E q (Ψ y))).1) : by { congr; apply [expr (fin.ext_iff _ _).2]; [exact [expr i'], exact [expr j']] }
         «expr = »(..., min M «expr⌊ ⌋₊»(«expr * »(«expr ⁻¹»(ε), dist (Ψ x) (Ψ y)))) : by simp [] [] ["only"] ["[", expr F, ",", expr (E q).symm_apply_apply, "]"] [] []
         «expr = »(..., «expr⌊ ⌋₊»(«expr * »(«expr ⁻¹»(ε), dist (Ψ x) (Ψ y)))) : begin
           refine [expr min_eq_right (nat.floor_mono _)],
           refine [expr mul_le_mul_of_nonneg_left (le_trans _ (le_max_left _ _)) (inv_pos.2 εpos).le],
           change [expr «expr ≤ »(dist (Ψ x : q.rep) (Ψ y), C)] [] [],
           refine [expr le_trans (dist_le_diam_of_mem compact_univ.bounded (mem_univ _) (mem_univ _)) _],
           exact [expr hdiam q qt]
         end],
      have [] [":", expr «expr = »(((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1, ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1)] [],
      { revert [ident hiq, ident hjq],
        change [expr N q] ["with", expr (F q).1] [],
        generalize_hyp [] [":"] [expr «expr = »(F q, f)] ["at", ident hpq, "⊢"],
        subst [expr hpq],
        intros [],
        refl },
      have [] [":", expr «expr = »(«expr⌊ ⌋»(«expr * »(«expr ⁻¹»(ε), dist x y)), «expr⌊ ⌋»(«expr * »(«expr ⁻¹»(ε), dist (Ψ x) (Ψ y))))] [],
      { rw ["[", expr Ap, ",", expr Aq, "]"] ["at", ident this],
        have [ident D] [":", expr «expr ≤ »(0, «expr⌊ ⌋»(«expr * »(«expr ⁻¹»(ε), dist x y)))] [":=", expr floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg)],
        have [ident D'] [":", expr «expr ≤ »(0, «expr⌊ ⌋»(«expr * »(«expr ⁻¹»(ε), dist (Ψ x) (Ψ y))))] [":=", expr floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg)],
        rw ["[", "<-", expr int.to_nat_of_nonneg D, ",", "<-", expr int.to_nat_of_nonneg D', ",", expr int.floor_to_nat, ",", expr int.floor_to_nat, ",", expr this, "]"] [] },
      have [ident I] [] [":=", expr calc
         «expr = »(«expr * »(«expr| |»(«expr ⁻¹»(ε)), «expr| |»(«expr - »(dist x y, dist (Ψ x) (Ψ y)))), «expr| |»(«expr * »(«expr ⁻¹»(ε), «expr - »(dist x y, dist (Ψ x) (Ψ y))))) : (abs_mul _ _).symm
         «expr = »(..., «expr| |»(«expr - »(«expr * »(«expr ⁻¹»(ε), dist x y), «expr * »(«expr ⁻¹»(ε), dist (Ψ x) (Ψ y))))) : by { congr,
           ring [] }
         «expr ≤ »(..., 1) : le_of_lt (abs_sub_lt_one_of_floor_eq_floor this)],
      calc
        «expr = »(«expr| |»(«expr - »(dist x y, dist (Ψ x) (Ψ y))), «expr * »(«expr * »(ε, «expr ⁻¹»(ε)), «expr| |»(«expr - »(dist x y, dist (Ψ x) (Ψ y))))) : by rw ["[", expr mul_inv_cancel (ne_of_gt εpos), ",", expr one_mul, "]"] []
        «expr = »(..., «expr * »(ε, «expr * »(«expr| |»(«expr ⁻¹»(ε)), «expr| |»(«expr - »(dist x y, dist (Ψ x) (Ψ y)))))) : by rw ["[", expr abs_of_nonneg (le_of_lt (inv_pos.2 εpos)), ",", expr mul_assoc, "]"] []
        «expr ≤ »(..., «expr * »(ε, 1)) : mul_le_mul_of_nonneg_left I (le_of_lt εpos)
        «expr = »(..., ε) : mul_one _ } },
  calc
    «expr = »(dist p q, GH_dist p.rep q.rep) : dist_GH_dist p q
    «expr ≤ »(..., «expr + »(«expr + »(ε, «expr / »(ε, 2)), ε)) : main
    «expr = »(..., «expr / »(δ, 2)) : by { simp [] [] [] ["[", expr ε, "]"] [] [],
      ring [] }
    «expr < »(..., δ) : half_lt_self δpos
end

section Complete

variable (X : ℕ → Type) [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)]

/-- Auxiliary structure used to glue metric spaces below, recording an isometric embedding
of a type `A` in another metric space. -/
structure aux_gluing_struct (A : Type) [MetricSpace A] : Type 1 where 
  Space : Type 
  metric : MetricSpace space 
  embed : A → space 
  isom : Isometry embed

instance (A : Type) [MetricSpace A] : Inhabited (aux_gluing_struct A) :=
  ⟨{ Space := A,
      metric :=
        by 
          infer_instance,
      embed := id, isom := fun x y => rfl }⟩

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Auxiliary sequence of metric spaces, containing copies of `X 0`, ..., `X n`, where each
`X i` is glued to `X (i+1)` in an optimal way. The space at step `n+1` is obtained from the space
at step `n` by adding `X (n+1)`, glued in an optimal way to the `X n` already sitting there. -/
def aux_gluing (n : exprℕ()) : aux_gluing_struct (X n) :=
nat.rec_on n { space := X 0,
  metric := by apply_instance,
  embed := id,
  isom := λ
  x
  y, rfl } (λ
 n
 Y, by letI [] [":", expr metric_space Y.space] [":=", expr Y.metric]; exact [expr { space := glue_space Y.isom (isometry_optimal_GH_injl (X n) (X «expr + »(n, 1))),
    metric := by apply_instance,
    embed := «expr ∘ »(to_glue_r Y.isom (isometry_optimal_GH_injl (X n) (X «expr + »(n, 1))), optimal_GH_injr (X n) (X «expr + »(n, 1))),
    isom := (to_glue_r_isometry _ _).comp (isometry_optimal_GH_injr (X n) (X «expr + »(n, 1))) }])

-- error in Topology.MetricSpace.GromovHausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Gromov-Hausdorff space is complete. -/ instance : complete_space GH_space :=
begin
  have [] [":", expr ∀ n : exprℕ(), «expr < »(0, «expr ^ »(«expr / »((1 : exprℝ()), 2), n))] [],
  by { apply [expr pow_pos],
    norm_num [] [] },
  refine [expr metric.complete_of_convergent_controlled_sequences (λ
    n, «expr ^ »(«expr / »(1, 2), n)) this (λ u hu, _)],
  let [ident X] [] [":=", expr λ n, (u n).rep],
  let [ident Y] [] [":=", expr aux_gluing X],
  letI [] [":", expr ∀ n, metric_space (Y n).space] [":=", expr λ n, (Y n).metric],
  have [ident E] [":", expr ∀
   n : exprℕ(), «expr = »(glue_space (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ)), (Y n.succ).space)] [":=", expr λ
   n, by { simp [] [] [] ["[", expr Y, ",", expr aux_gluing, "]"] [] [],
     refl }],
  let [ident c] [] [":=", expr λ n, cast (E n)],
  have [ident ic] [":", expr ∀ n, isometry (c n)] [":=", expr λ n x y, rfl],
  let [ident f] [":", expr ∀
   n, (Y n).space → (Y n.succ).space] [":=", expr λ
   n, «expr ∘ »(c n, to_glue_l (aux_gluing X n).isom (isometry_optimal_GH_injl (X n) (X n.succ)))],
  have [ident I] [":", expr ∀ n, isometry (f n)] [],
  { assume [binders (n)],
    apply [expr isometry.comp],
    { assume [binders (x y)],
      refl },
    { apply [expr to_glue_l_isometry] } },
  let [ident Z0] [] [":=", expr metric.inductive_limit I],
  let [ident Z] [] [":=", expr uniform_space.completion Z0],
  let [ident Φ] [] [":=", expr to_inductive_limit I],
  let [ident coeZ] [] [":=", expr (coe : Z0 → Z)],
  let [ident X2] [] [":=", expr λ n, range «expr ∘ »(coeZ, «expr ∘ »(Φ n, (Y n).embed))],
  have [ident isom] [":", expr ∀ n, isometry «expr ∘ »(coeZ, «expr ∘ »(Φ n, (Y n).embed))] [],
  { assume [binders (n)],
    apply [expr isometry.comp completion.coe_isometry _],
    apply [expr isometry.comp _ (Y n).isom],
    apply [expr to_inductive_limit_isometry] },
  have [ident D2] [":", expr ∀ n, «expr < »(Hausdorff_dist (X2 n) (X2 n.succ), «expr ^ »(«expr / »(1, 2), n))] [],
  { assume [binders (n)],
    have [ident X2n] [":", expr «expr = »(X2 n, range «expr ∘ »(«expr ∘ »(coeZ, «expr ∘ »(Φ n.succ, «expr ∘ »(c n, to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ))))), optimal_GH_injl (X n) (X n.succ)))] [],
    { change [expr «expr = »(X2 n, range «expr ∘ »(coeZ, «expr ∘ »(Φ n.succ, «expr ∘ »(c n, «expr ∘ »(to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ)), optimal_GH_injl (X n) (X n.succ))))))] [] [],
      simp [] [] ["only"] ["[", expr X2, ",", expr Φ, "]"] [] [],
      rw ["[", "<-", expr to_inductive_limit_commute I, "]"] [],
      simp [] [] ["only"] ["[", expr f, "]"] [] [],
      rw ["<-", expr to_glue_commute] [] },
    rw [expr range_comp] ["at", ident X2n],
    have [ident X2nsucc] [":", expr «expr = »(X2 n.succ, range «expr ∘ »(«expr ∘ »(coeZ, «expr ∘ »(Φ n.succ, «expr ∘ »(c n, to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ))))), optimal_GH_injr (X n) (X n.succ)))] [],
    by refl,
    rw [expr range_comp] ["at", ident X2nsucc],
    rw ["[", expr X2n, ",", expr X2nsucc, ",", expr Hausdorff_dist_image, ",", expr Hausdorff_dist_optimal, ",", "<-", expr dist_GH_dist, "]"] [],
    { exact [expr hu n n n.succ (le_refl n) (le_succ n)] },
    { apply [expr isometry.comp completion.coe_isometry _],
      apply [expr isometry.comp _ ((ic n).comp (to_glue_r_isometry _ _))],
      apply [expr to_inductive_limit_isometry] } },
  let [ident X3] [":", expr exprℕ() → nonempty_compacts Z] [":=", expr λ
   n, ⟨X2 n, ⟨range_nonempty _, is_compact_range (isom n).continuous⟩⟩],
  have [] [":", expr cauchy_seq X3] [],
  { refine [expr cauchy_seq_of_le_geometric «expr / »(1, 2) 1 (by norm_num [] []) (λ n, _)],
    rw [expr one_mul] [],
    exact [expr le_of_lt (D2 n)] },
  rcases [expr cauchy_seq_tendsto_of_complete this, "with", "⟨", ident L, ",", ident hL, "⟩"],
  have [ident M] [":", expr tendsto (λ
    n, (X3 n).to_GH_space) at_top (expr𝓝() L.to_GH_space)] [":=", expr tendsto.comp (to_GH_space_continuous.tendsto _) hL],
  have [] [":", expr ∀ n, «expr = »((X3 n).to_GH_space, u n)] [],
  { assume [binders (n)],
    rw ["[", expr nonempty_compacts.to_GH_space, ",", "<-", expr (u n).to_GH_space_rep, ",", expr to_GH_space_eq_to_GH_space_iff_isometric, "]"] [],
    constructor,
    convert [] [expr (isom n).isometric_on_range.symm] [] },
  exact [expr ⟨L.to_GH_space, by simpa [] [] [] ["[", expr this, "]"] [] ["using", expr M]⟩]
end

end Complete

end GromovHausdorff

