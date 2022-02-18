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


noncomputable section

open_locale Classical TopologicalSpace Ennreal

local notation "ℓ_infty_ℝ" => lp (fun n : ℕ => ℝ) ∞

universe u v w

open Classical Set Function TopologicalSpace Filter Metric Quotientₓ

open BoundedContinuousFunction Nat Int kuratowskiEmbedding

open sum (inl inr)

attribute [local instance] metric_space_sum

namespace GromovHausdorff

section GHSpace

/-- Equivalence relation identifying two nonempty compact sets which are isometric -/
private def isometry_rel : NonemptyCompacts ℓ_infty_ℝ → NonemptyCompacts ℓ_infty_ℝ → Prop := fun x y =>
  Nonempty (x.val ≃ᵢ y.val)

/-- This is indeed an equivalence relation -/
private theorem is_equivalence_isometry_rel : Equivalenceₓ IsometryRel :=
  ⟨fun x => ⟨Isometric.refl _⟩, fun x y ⟨e⟩ => ⟨e.symm⟩, fun x y z ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- setoid instance identifying two isometric nonempty compact subspaces of ℓ^∞(ℝ) -/
instance isometry_rel.setoid : Setoidₓ (NonemptyCompacts ℓ_infty_ℝ) :=
  Setoidₓ.mk IsometryRel is_equivalence_isometry_rel

/-- The Gromov-Hausdorff space -/
def GH_space : Type :=
  Quotientₓ IsometryRel.setoid

/-- Map any nonempty compact type to `GH_space` -/
def to_GH_space (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] : GHSpace :=
  ⟦NonemptyCompacts.kuratowskiEmbedding X⟧

instance : Inhabited GHSpace :=
  ⟨Quot.mk _
      ⟨{0}, by
        simp ⟩⟩

/-- A metric space representative of any abstract point in `GH_space` -/
@[nolint has_inhabited_instance]
def GH_space.rep (p : GHSpace) : Type :=
  (Quot.out p).val

theorem eq_to_GH_space_iff {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {p : NonemptyCompacts ℓ_infty_ℝ} :
    ⟦p⟧ = toGHSpace X ↔ ∃ Ψ : X → ℓ_infty_ℝ, Isometry Ψ ∧ Range Ψ = p.val := by
  simp only [to_GH_space, Quotientₓ.eq]
  refine' ⟨fun h => _, _⟩
  · rcases Setoidₓ.symm h with ⟨e⟩
    have f := (kuratowskiEmbedding.isometry X).isometricOnRange.trans e
    use fun x => f x, isometry_subtype_coe.comp f.isometry
    rw [range_comp, f.range_eq_univ, Set.image_univ, Subtype.range_coe]
    
  · rintro ⟨Ψ, ⟨isomΨ, rangeΨ⟩⟩
    have f := ((kuratowskiEmbedding.isometry X).isometricOnRange.symm.trans isomΨ.isometric_on_range).symm
    have E : (range Ψ ≃ᵢ (NonemptyCompacts.kuratowskiEmbedding X).val) = (p.val ≃ᵢ range (kuratowskiEmbedding X)) := by
      dunfold NonemptyCompacts.kuratowskiEmbedding
      rw [rangeΨ] <;> rfl
    exact ⟨cast E f⟩
    

theorem eq_to_GH_space {p : NonemptyCompacts ℓ_infty_ℝ} : ⟦p⟧ = toGHSpace p.val :=
  eq_to_GH_space_iff.2 ⟨fun x => x, isometry_subtype_coe, Subtype.range_coe⟩

section

attribute [local reducible] GH_space.rep

instance rep_GH_space_metric_space {p : GHSpace} : MetricSpace p.rep := by
  infer_instance

instance rep_GH_space_compact_space {p : GHSpace} : CompactSpace p.rep := by
  infer_instance

instance rep_GH_space_nonempty {p : GHSpace} : Nonempty p.rep := by
  infer_instance

end

theorem GH_space.to_GH_space_rep (p : GHSpace) : toGHSpace p.rep = p := by
  change to_GH_space (Quot.out p).val = p
  rw [← eq_to_GH_space]
  exact Quot.out_eq p

/-- Two nonempty compact spaces have the same image in `GH_space` if and only if they are
isometric. -/
theorem to_GH_space_eq_to_GH_space_iff_isometric {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v}
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : toGHSpace X = toGHSpace Y ↔ Nonempty (X ≃ᵢ Y) :=
  ⟨by
    simp only [to_GH_space, Quotientₓ.eq]
    rintro ⟨e⟩
    have I :
      ((NonemptyCompacts.kuratowskiEmbedding X).val ≃ᵢ (NonemptyCompacts.kuratowskiEmbedding Y).val) =
        (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) :=
      by
      dunfold NonemptyCompacts.kuratowskiEmbedding
      rfl
    have f := (kuratowskiEmbedding.isometry X).isometricOnRange
    have g := (kuratowskiEmbedding.isometry Y).isometricOnRange.symm
    exact ⟨f.trans <| (cast I e).trans g⟩, by
    rintro ⟨e⟩
    simp only [to_GH_space, Quotientₓ.eq]
    have f := (kuratowskiEmbedding.isometry X).isometricOnRange.symm
    have g := (kuratowskiEmbedding.isometry Y).isometricOnRange
    have I :
      (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) =
        ((NonemptyCompacts.kuratowskiEmbedding X).val ≃ᵢ (NonemptyCompacts.kuratowskiEmbedding Y).val) :=
      by
      dunfold NonemptyCompacts.kuratowskiEmbedding
      rfl
    exact ⟨cast I ((f.trans e).trans g)⟩⟩

/-- Distance on `GH_space`: the distance between two nonempty compact spaces is the infimum
Hausdorff distance between isometric copies of the two spaces in a metric space. For the definition,
we only consider embeddings in `ℓ^∞(ℝ)`, but we will prove below that it works for all spaces. -/
instance : HasDist GHSpace where
  dist := fun x y =>
    Inf <|
      (fun p : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ => hausdorffDist p.1.val p.2.val) ''
        ({ a | ⟦a⟧ = x } ×ˢ { b | ⟦b⟧ = y })

/-- The Gromov-Hausdorff distance between two nonempty compact metric spaces, equal by definition to
the distance of the equivalence classes of these spaces in the Gromov-Hausdorff space. -/
def GH_dist (X : Type u) (Y : Type v) [MetricSpace X] [Nonempty X] [CompactSpace X] [MetricSpace Y] [Nonempty Y]
    [CompactSpace Y] : ℝ :=
  dist (toGHSpace X) (toGHSpace Y)

theorem dist_GH_dist (p q : GHSpace) : dist p q = gHDist p.rep q.rep := by
  rw [GH_dist, p.to_GH_space_rep, q.to_GH_space_rep]

/-- The Gromov-Hausdorff distance between two spaces is bounded by the Hausdorff distance
of isometric copies of the spaces, in any metric space. -/
theorem GH_dist_le_Hausdorff_dist {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v}
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {γ : Type w} [MetricSpace γ] {Φ : X → γ} {Ψ : Y → γ} (ha : Isometry Φ)
    (hb : Isometry Ψ) : gHDist X Y ≤ hausdorffDist (Range Φ) (Range Ψ) := by
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩
  let s : Set γ := range Φ ∪ range Ψ
  let Φ' : X → Subtype s := fun y => ⟨Φ y, mem_union_left _ (mem_range_self _)⟩
  let Ψ' : Y → Subtype s := fun y => ⟨Ψ y, mem_union_right _ (mem_range_self _)⟩
  have IΦ' : Isometry Φ' := fun x y => ha x y
  have IΨ' : Isometry Ψ' := fun x y => hb x y
  have : IsCompact s := (is_compact_range ha.continuous).union (is_compact_range hb.continuous)
  let this' : MetricSpace (Subtype s) := by
    infer_instance
  have : CompactSpace (Subtype s) := ⟨is_compact_iff_is_compact_univ.1 ‹IsCompact s›⟩
  have : Nonempty (Subtype s) := ⟨Φ' xX⟩
  have ΦΦ' : Φ = Subtype.val ∘ Φ' := by
    funext
    rfl
  have ΨΨ' : Ψ = Subtype.val ∘ Ψ' := by
    funext
    rfl
  have : Hausdorff_dist (range Φ) (range Ψ) = Hausdorff_dist (range Φ') (range Ψ') := by
    rw [ΦΦ', ΨΨ', range_comp, range_comp]
    exact Hausdorff_dist_image isometry_subtype_coe
  rw [this]
  let F := kuratowskiEmbedding (Subtype s)
  have : Hausdorff_dist (F '' range Φ') (F '' range Ψ') = Hausdorff_dist (range Φ') (range Ψ') :=
    Hausdorff_dist_image (kuratowskiEmbedding.isometry _)
  rw [← this]
  let A : nonempty_compacts ℓ_infty_ℝ :=
    ⟨F '' range Φ',
      ⟨(range_nonempty _).Image _, (is_compact_range IΦ'.continuous).Image (kuratowskiEmbedding.isometry _).Continuous⟩⟩
  let B : nonempty_compacts ℓ_infty_ℝ :=
    ⟨F '' range Ψ',
      ⟨(range_nonempty _).Image _, (is_compact_range IΨ'.continuous).Image (kuratowskiEmbedding.isometry _).Continuous⟩⟩
  have AX : ⟦A⟧ = to_GH_space X := by
    rw [eq_to_GH_space_iff]
    exact
      ⟨fun x => F (Φ' x),
        ⟨(kuratowskiEmbedding.isometry _).comp IΦ', by
          rw [range_comp]⟩⟩
  have BY : ⟦B⟧ = to_GH_space Y := by
    rw [eq_to_GH_space_iff]
    exact
      ⟨fun x => F (Ψ' x),
        ⟨(kuratowskiEmbedding.isometry _).comp IΨ', by
          rw [range_comp]⟩⟩
  refine'
    cInf_le
      ⟨0, by
        simp [LowerBounds]
        intro t _ _ _ _ ht
        rw [← ht]
        exact Hausdorff_dist_nonneg⟩
      _
  apply (mem_image _ _ _).2
  exists (⟨A, B⟩ : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ)
  simp [AX, BY]

/-- The optimal coupling constructed above realizes exactly the Gromov-Hausdorff distance,
essentially by design. -/
theorem Hausdorff_dist_optimal {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y]
    [CompactSpace Y] [Nonempty Y] :
    hausdorffDist (Range (optimalGHInjl X Y)) (Range (optimalGHInjr X Y)) = gHDist X Y := by
  inhabit X
  inhabit Y
  have A :
    ∀ p q : nonempty_compacts ℓ_infty_ℝ,
      ⟦p⟧ = to_GH_space X →
        ⟦q⟧ = to_GH_space Y →
          Hausdorff_dist p.val q.val < diam (univ : Set X) + 1 + diam (univ : Set Y) →
            Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) ≤ Hausdorff_dist p.val q.val :=
    by
    intro p q hp hq bound
    rcases eq_to_GH_space_iff.1 hp with ⟨Φ, ⟨Φisom, Φrange⟩⟩
    rcases eq_to_GH_space_iff.1 hq with ⟨Ψ, ⟨Ψisom, Ψrange⟩⟩
    have I : diam (range Φ ∪ range Ψ) ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by
      rcases exists_mem_of_nonempty X with ⟨xX, _⟩
      have : ∃ y ∈ range Ψ, dist (Φ xX) y < diam (univ : Set X) + 1 + diam (univ : Set Y) := by
        rw [Ψrange]
        have : Φ xX ∈ p.val := Φrange ▸ mem_range_self _
        exact
          exists_dist_lt_of_Hausdorff_dist_lt this bound
            (Hausdorff_edist_ne_top_of_nonempty_of_bounded p.2.1 q.2.1 p.2.2.Bounded q.2.2.Bounded)
      rcases this with ⟨y, hy, dy⟩
      rcases mem_range.1 hy with ⟨z, hzy⟩
      rw [← hzy] at dy
      have DΦ : diam (range Φ) = diam (univ : Set X) := Φisom.diam_range
      have DΨ : diam (range Ψ) = diam (univ : Set Y) := Ψisom.diam_range
      calc diam (range Φ ∪ range Ψ) ≤ diam (range Φ) + dist (Φ xX) (Ψ z) + diam (range Ψ) :=
          diam_union (mem_range_self _)
            (mem_range_self
              _)_ ≤ diam (univ : Set X) + (diam (univ : Set X) + 1 + diam (univ : Set Y)) + diam (univ : Set Y) :=
          by
          rw [DΦ, DΨ]
          apply
            add_le_add (add_le_add le_rfl (le_of_ltₓ dy))
              le_rfl _ = 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) :=
          by
          ring
    let f : Sum X Y → ℓ_infty_ℝ := fun x =>
      match x with
      | inl y => Φ y
      | inr z => Ψ z
    let F : Sum X Y × Sum X Y → ℝ := fun p => dist (f p.1) (f p.2)
    have Fgood : F ∈ candidates X Y := by
      simp only [candidates, forall_const, and_trueₓ, add_commₓ, eq_self_iff_true, dist_eq_zero, and_selfₓ,
        Set.mem_set_of_eq]
      repeat'
        constructor
      · exact fun x y =>
          calc
            F (inl x, inl y) = dist (Φ x) (Φ y) := rfl
            _ = dist x y := Φisom.dist_eq x y
            
        
      · exact fun x y =>
          calc
            F (inr x, inr y) = dist (Ψ x) (Ψ y) := rfl
            _ = dist x y := Ψisom.dist_eq x y
            
        
      · exact fun x y => dist_comm _ _
        
      · exact fun x y z => dist_triangle _ _ _
        
      · exact fun x y =>
          calc
            F (x, y) ≤ diam (range Φ ∪ range Ψ) := by
              have A : ∀ z : Sum X Y, f z ∈ range Φ ∪ range Ψ := by
                intro z
                cases z
                · apply mem_union_left
                  apply mem_range_self
                  
                · apply mem_union_right
                  apply mem_range_self
                  
              refine' dist_le_diam_of_mem _ (A _) (A _)
              rw [Φrange, Ψrange]
              exact (p.2.2.union q.2.2).Bounded
            _ ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := I
            
        
    let Fb := candidates_b_of_candidates F Fgood
    have : Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) ≤ HD Fb :=
      Hausdorff_dist_optimal_le_HD _ _ (candidates_b_of_candidates_mem F Fgood)
    refine' le_transₓ this (le_of_forall_le_of_dense fun r hr => _)
    have I1 : ∀ x : X, (⨅ y, Fb (inl x, inr y)) ≤ r := by
      intro x
      have : f (inl x) ∈ p.val := by
        rw [← Φrange]
        apply mem_range_self
      rcases exists_dist_lt_of_Hausdorff_dist_lt this hr
          (Hausdorff_edist_ne_top_of_nonempty_of_bounded p.2.1 q.2.1 p.2.2.Bounded q.2.2.Bounded) with
        ⟨z, zq, hz⟩
      have : z ∈ range Ψ := by
        rwa [← Ψrange] at zq
      rcases mem_range.1 this with ⟨y, hy⟩
      calc (⨅ y, Fb (inl x, inr y)) ≤ Fb (inl x, inr y) :=
          cinfi_le
            (by
              simpa using HD_below_aux1 0)
            y _ = dist (Φ x) (Ψ y) :=
          rfl _ = dist (f (inl x)) z := by
          rw [hy]_ ≤ r := le_of_ltₓ hz
    have I2 : ∀ y : Y, (⨅ x, Fb (inl x, inr y)) ≤ r := by
      intro y
      have : f (inr y) ∈ q.val := by
        rw [← Ψrange]
        apply mem_range_self
      rcases exists_dist_lt_of_Hausdorff_dist_lt' this hr
          (Hausdorff_edist_ne_top_of_nonempty_of_bounded p.2.1 q.2.1 p.2.2.Bounded q.2.2.Bounded) with
        ⟨z, zq, hz⟩
      have : z ∈ range Φ := by
        rwa [← Φrange] at zq
      rcases mem_range.1 this with ⟨x, hx⟩
      calc (⨅ x, Fb (inl x, inr y)) ≤ Fb (inl x, inr y) :=
          cinfi_le
            (by
              simpa using HD_below_aux2 0)
            x _ = dist (Φ x) (Ψ y) :=
          rfl _ = dist z (f (inr y)) := by
          rw [hx]_ ≤ r := le_of_ltₓ hz
    simp [HD, csupr_le I1, csupr_le I2]
  have B :
    ∀ p q : nonempty_compacts ℓ_infty_ℝ,
      ⟦p⟧ = to_GH_space X →
        ⟦q⟧ = to_GH_space Y →
          Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) ≤ Hausdorff_dist p.val q.val :=
    by
    intro p q hp hq
    by_cases' h : Hausdorff_dist p.val q.val < diam (univ : Set X) + 1 + diam (univ : Set Y)
    · exact A p q hp hq h
      
    · calc Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) ≤ HD (candidates_b_dist X Y) :=
          Hausdorff_dist_optimal_le_HD _ _
            candidates_b_dist_mem_candidates_b _ ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
          HD_candidates_b_dist_le _ ≤ Hausdorff_dist p.val q.val := not_ltₓ.1 h
      
  refine' le_antisymmₓ _ _
  · apply le_cInf
    · refine' (Set.Nonempty.prod _ _).Image _ <;> exact ⟨_, rfl⟩
      
    · rintro b ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩
      exact B p q hp hq
      
    
  · exact GH_dist_le_Hausdorff_dist (isometry_optimal_GH_injl X Y) (isometry_optimal_GH_injr X Y)
    

/-- The Gromov-Hausdorff distance can also be realized by a coupling in `ℓ^∞(ℝ)`, by embedding
the optimal coupling through its Kuratowski embedding. -/
theorem GH_dist_eq_Hausdorff_dist (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] (Y : Type v)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    ∃ Φ : X → ℓ_infty_ℝ,
      ∃ Ψ : Y → ℓ_infty_ℝ, Isometry Φ ∧ Isometry Ψ ∧ gHDist X Y = hausdorffDist (Range Φ) (Range Ψ) :=
  by
  let F := kuratowskiEmbedding (optimal_GH_coupling X Y)
  let Φ := F ∘ optimal_GH_injl X Y
  let Ψ := F ∘ optimal_GH_injr X Y
  refine' ⟨Φ, Ψ, _, _, _⟩
  · exact (kuratowskiEmbedding.isometry _).comp (isometry_optimal_GH_injl X Y)
    
  · exact (kuratowskiEmbedding.isometry _).comp (isometry_optimal_GH_injr X Y)
    
  · rw [← image_univ, ← image_univ, image_comp F, image_univ, image_comp F (optimal_GH_injr X Y), image_univ, ←
      Hausdorff_dist_optimal]
    exact (Hausdorff_dist_image (kuratowskiEmbedding.isometry _)).symm
    

/-- The Gromov-Hausdorff distance defines a genuine distance on the Gromov-Hausdorff space. -/
instance : MetricSpace GHSpace where
  dist_self := fun x => by
    rcases exists_rep x with ⟨y, hy⟩
    refine' le_antisymmₓ _ _
    · apply cInf_le
      · exact
          ⟨0, by
            rintro b ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
            exact Hausdorff_dist_nonneg⟩
        
      · simp
        exists y, y
        simpa
        
      
    · apply le_cInf
      · exact (nonempty.prod ⟨y, hy⟩ ⟨y, hy⟩).Image _
        
      · rintro b ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
        exact Hausdorff_dist_nonneg
        
      
  dist_comm := fun x y => by
    have A :
      (fun p : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ => Hausdorff_dist p.fst.val p.snd.val) ''
          ({ a | ⟦a⟧ = x } ×ˢ { b | ⟦b⟧ = y }) =
        (fun p : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ => Hausdorff_dist p.fst.val p.snd.val) ∘
            Prod.swap ''
          ({ a | ⟦a⟧ = x } ×ˢ { b | ⟦b⟧ = y }) :=
      by
      congr
      funext
      simp
      rw [Hausdorff_dist_comm]
    simp only [dist, A, image_comp, image_swap_prod]
  eq_of_dist_eq_zero := fun x y hxy => by
    rcases GH_dist_eq_Hausdorff_dist x.rep y.rep with ⟨Φ, Ψ, Φisom, Ψisom, DΦΨ⟩
    rw [← dist_GH_dist, hxy] at DΦΨ
    have : range Φ = range Ψ := by
      have hΦ : IsCompact (range Φ) := is_compact_range Φisom.continuous
      have hΨ : IsCompact (range Ψ) := is_compact_range Ψisom.continuous
      apply (IsClosed.Hausdorff_dist_zero_iff_eq _ _ _).1 DΦΨ.symm
      · exact hΦ.is_closed
        
      · exact hΨ.is_closed
        
      · exact Hausdorff_edist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _) hΦ.bounded hΨ.bounded
        
    have T : (range Ψ ≃ᵢ y.rep) = (range Φ ≃ᵢ y.rep) := by
      rw [this]
    have eΨ := cast T Ψisom.isometric_on_range.symm
    have e := Φisom.isometric_on_range.trans eΨ
    rw [← x.to_GH_space_rep, ← y.to_GH_space_rep, to_GH_space_eq_to_GH_space_iff_isometric]
    exact ⟨e⟩
  dist_triangle := fun x y z => by
    let X := x.rep
    let Y := y.rep
    let Z := z.rep
    let γ1 := optimal_GH_coupling X Y
    let γ2 := optimal_GH_coupling Y Z
    let Φ : Y → γ1 := optimal_GH_injr X Y
    have hΦ : Isometry Φ := isometry_optimal_GH_injr X Y
    let Ψ : Y → γ2 := optimal_GH_injl Y Z
    have hΨ : Isometry Ψ := isometry_optimal_GH_injl Y Z
    let γ := glue_space hΦ hΨ
    let this' : MetricSpace γ := Metric.metricSpaceGlueSpace hΦ hΨ
    have Comm : to_glue_l hΦ hΨ ∘ optimal_GH_injr X Y = to_glue_r hΦ hΨ ∘ optimal_GH_injl Y Z := to_glue_commute hΦ hΨ
    calc dist x z = dist (to_GH_space X) (to_GH_space Z) := by
        rw [x.to_GH_space_rep,
          z.to_GH_space_rep]_ ≤
          Hausdorff_dist (range (to_glue_l hΦ hΨ ∘ optimal_GH_injl X Y))
            (range (to_glue_r hΦ hΨ ∘ optimal_GH_injr Y Z)) :=
        GH_dist_le_Hausdorff_dist ((to_glue_l_isometry hΦ hΨ).comp (isometry_optimal_GH_injl X Y))
          ((to_glue_r_isometry hΦ hΨ).comp
            (isometry_optimal_GH_injr Y
              Z))_ ≤
          Hausdorff_dist (range (to_glue_l hΦ hΨ ∘ optimal_GH_injl X Y))
              (range (to_glue_l hΦ hΨ ∘ optimal_GH_injr X Y)) +
            Hausdorff_dist (range (to_glue_l hΦ hΨ ∘ optimal_GH_injr X Y))
              (range (to_glue_r hΦ hΨ ∘ optimal_GH_injr Y Z)) :=
        by
        refine'
          Hausdorff_dist_triangle
            (Hausdorff_edist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _) _ _)
        · exact
            (is_compact_range
                (Isometry.continuous ((to_glue_l_isometry hΦ hΨ).comp (isometry_optimal_GH_injl X Y)))).Bounded
          
        · exact
            (is_compact_range
                (Isometry.continuous ((to_glue_l_isometry hΦ hΨ).comp (isometry_optimal_GH_injr X Y)))).Bounded
          _ =
          Hausdorff_dist (to_glue_l hΦ hΨ '' range (optimal_GH_injl X Y))
              (to_glue_l hΦ hΨ '' range (optimal_GH_injr X Y)) +
            Hausdorff_dist (to_glue_r hΦ hΨ '' range (optimal_GH_injl Y Z))
              (to_glue_r hΦ hΨ '' range (optimal_GH_injr Y Z)) :=
        by
        simp only [← range_comp, Comm, eq_self_iff_true,
          add_right_injₓ]_ =
          Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) +
            Hausdorff_dist (range (optimal_GH_injl Y Z)) (range (optimal_GH_injr Y Z)) :=
        by
        rw [Hausdorff_dist_image (to_glue_l_isometry hΦ hΨ),
          Hausdorff_dist_image
            (to_glue_r_isometry hΦ
              hΨ)]_ = dist (to_GH_space X) (to_GH_space Y) + dist (to_GH_space Y) (to_GH_space Z) :=
        by
        rw [Hausdorff_dist_optimal, Hausdorff_dist_optimal, GH_dist, GH_dist]_ = dist x y + dist y z := by
        rw [x.to_GH_space_rep, y.to_GH_space_rep, z.to_GH_space_rep]

end GHSpace

end GromovHausdorff

/-- In particular, nonempty compacts of a metric space map to `GH_space`. We register this
in the topological_space namespace to take advantage of the notation `p.to_GH_space`. -/
def TopologicalSpace.NonemptyCompacts.toGHSpace {X : Type u} [MetricSpace X] (p : NonemptyCompacts X) :
    GromovHausdorff.GHSpace :=
  GromovHausdorff.toGHSpace p.val

open TopologicalSpace

namespace GromovHausdorff

section NonemptyCompacts

variable {X : Type u} [MetricSpace X]

theorem GH_dist_le_nonempty_compacts_dist (p q : NonemptyCompacts X) : dist p.toGHSpace q.toGHSpace ≤ dist p q := by
  have ha : Isometry (coe : p.val → X) := isometry_subtype_coe
  have hb : Isometry (coe : q.val → X) := isometry_subtype_coe
  have A : dist p q = Hausdorff_dist p.val q.val := rfl
  have I : p.val = range (coe : p.val → X) := by
    simp
  have J : q.val = range (coe : q.val → X) := by
    simp
  rw [I, J] at A
  rw [A]
  exact GH_dist_le_Hausdorff_dist ha hb

theorem to_GH_space_lipschitz : LipschitzWith 1 (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  LipschitzWith.mk_one GH_dist_le_nonempty_compacts_dist

theorem to_GH_space_continuous : Continuous (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  to_GH_space_lipschitz.Continuous

end NonemptyCompacts

section

variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y]
  [Nonempty Y]

attribute [local instance] Sum.topologicalSpace Sum.uniformSpace

/-- If there are subsets which are `ε₁`-dense and `ε₃`-dense in two spaces, and
isometric up to `ε₂`, then the Gromov-Hausdorff distance between the spaces is bounded by
`ε₁ + ε₂/2 + ε₃`. -/
theorem GH_dist_le_of_approx_subsets {s : Set X} (Φ : s → Y) {ε₁ ε₂ ε₃ : ℝ} (hs : ∀ x : X, ∃ y ∈ s, dist x y ≤ ε₁)
    (hs' : ∀ x : Y, ∃ y : s, dist x (Φ y) ≤ ε₃) (H : ∀ x y : s, abs (dist x y - dist (Φ x) (Φ y)) ≤ ε₂) :
    gHDist X Y ≤ ε₁ + ε₂ / 2 + ε₃ := by
  refine' le_of_forall_pos_le_add fun δ δ0 => _
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩
  rcases hs xX with ⟨xs, hxs, Dxs⟩
  have sne : s.nonempty := ⟨xs, hxs⟩
  let this' : Nonempty s := sne.to_subtype
  have : 0 ≤ ε₂ := le_transₓ (abs_nonneg _) (H ⟨xs, hxs⟩ ⟨xs, hxs⟩)
  have : ∀ p q : s, abs (dist p q - dist (Φ p) (Φ q)) ≤ 2 * (ε₂ / 2 + δ) := fun p q =>
    calc
      abs (dist p q - dist (Φ p) (Φ q)) ≤ ε₂ := H p q
      _ ≤ 2 * (ε₂ / 2 + δ) := by
        linarith
      
  let this' : MetricSpace (Sum X Y) :=
    glue_metric_approx (fun x : s => (x : X)) (fun x => Φ x) (ε₂ / 2 + δ)
      (by
        linarith)
      this
  let Fl := @Sum.inl X Y
  let Fr := @Sum.inr X Y
  have Il : Isometry Fl := isometry_emetric_iff_metric.2 fun x y => rfl
  have Ir : Isometry Fr := isometry_emetric_iff_metric.2 fun x y => rfl
  have : GH_dist X Y ≤ Hausdorff_dist (range Fl) (range Fr) := GH_dist_le_Hausdorff_dist Il Ir
  have :
    Hausdorff_dist (range Fl) (range Fr) ≤ Hausdorff_dist (range Fl) (Fl '' s) + Hausdorff_dist (Fl '' s) (range Fr) :=
    have B : bounded (range Fl) := (is_compact_range Il.continuous).Bounded
    Hausdorff_dist_triangle
      (Hausdorff_edist_ne_top_of_nonempty_of_bounded (range_nonempty _) (sne.image _) B
        (B.mono (image_subset_range _ _)))
  have :
    Hausdorff_dist (Fl '' s) (range Fr) ≤
      Hausdorff_dist (Fl '' s) (Fr '' range Φ) + Hausdorff_dist (Fr '' range Φ) (range Fr) :=
    have B : bounded (range Fr) := (is_compact_range Ir.continuous).Bounded
    Hausdorff_dist_triangle'
      (Hausdorff_edist_ne_top_of_nonempty_of_bounded ((range_nonempty _).Image _) (range_nonempty _)
        (bounded.mono (image_subset_range _ _) B) B)
  have : Hausdorff_dist (range Fl) (Fl '' s) ≤ ε₁ := by
    rw [← image_univ, Hausdorff_dist_image Il]
    have : 0 ≤ ε₁ := le_transₓ dist_nonneg Dxs
    refine'
      Hausdorff_dist_le_of_mem_dist this (fun x hx => hs x) fun x hx =>
        ⟨x, mem_univ _, by
          simpa⟩
  have : Hausdorff_dist (Fl '' s) (Fr '' range Φ) ≤ ε₂ / 2 + δ := by
    refine'
      Hausdorff_dist_le_of_mem_dist
        (by
          linarith)
        _ _
    · intro x' hx'
      rcases(Set.mem_image _ _ _).1 hx' with ⟨x, ⟨x_in_s, xx'⟩⟩
      rw [← xx']
      use Fr (Φ ⟨x, x_in_s⟩), mem_image_of_mem Fr (mem_range_self _)
      exact le_of_eqₓ (glue_dist_glued_points (fun x : s => (x : X)) Φ (ε₂ / 2 + δ) ⟨x, x_in_s⟩)
      
    · intro x' hx'
      rcases(Set.mem_image _ _ _).1 hx' with ⟨y, ⟨y_in_s', yx'⟩⟩
      rcases mem_range.1 y_in_s' with ⟨x, xy⟩
      use Fl x, mem_image_of_mem _ x.2
      rw [← yx', ← xy, dist_comm]
      exact le_of_eqₓ (glue_dist_glued_points (@Subtype.val X s) Φ (ε₂ / 2 + δ) x)
      
  have : Hausdorff_dist (Fr '' range Φ) (range Fr) ≤ ε₃ := by
    rw [← @image_univ _ _ Fr, Hausdorff_dist_image Ir]
    rcases exists_mem_of_nonempty Y with ⟨xY, _⟩
    rcases hs' xY with ⟨xs', Dxs'⟩
    have : 0 ≤ ε₃ := le_transₓ dist_nonneg Dxs'
    refine'
      Hausdorff_dist_le_of_mem_dist this
        (fun x hx =>
          ⟨x, mem_univ _, by
            simpa⟩)
        fun x _ => _
    rcases hs' x with ⟨y, Dy⟩
    exact ⟨Φ y, mem_range_self _, Dy⟩
  linarith

end

/-- The Gromov-Hausdorff space is second countable. -/
instance : SecondCountableTopology GHSpace := by
  refine' second_countable_of_countable_discretization fun δ δpos => _
  let ε := 2 / 5 * δ
  have εpos : 0 < ε :=
    mul_pos
      (by
        norm_num)
      δpos
  have : ∀ p : GH_space, ∃ s : Set p.rep, finite s ∧ univ ⊆ ⋃ x ∈ s, ball x ε := fun p => by
    simpa using finite_cover_balls_of_compact (@compact_univ p.rep _ _) εpos
  choose s hs using this
  have : ∀ p : GH_space, ∀ t : Set p.rep, finite t → ∃ n : ℕ, ∃ e : Equivₓ t (Finₓ n), True := by
    intro p t ht
    let this' : Fintype t := finite.fintype ht
    exact ⟨Fintype.card t, Fintype.equivFin t, trivialₓ⟩
  choose N e hne using this
  let N := fun p : GH_space => N p (s p) (hs p).1
  let E := fun p : GH_space => e p (s p) (hs p).1
  let F : GH_space → Σ n : ℕ, Finₓ n → Finₓ n → ℤ := fun p =>
    ⟨N p, fun a b => ⌊ε⁻¹ * dist ((E p).symm a) ((E p).symm b)⌋⟩
  refine'
    ⟨Σ n, Finₓ n → Finₓ n → ℤ, by
      infer_instance, F, fun p q hpq => _⟩
  have Npq : N p = N q := (Sigma.mk.inj_iff.1 hpq).1
  let Ψ : s p → s q := fun x => (E q).symm (Finₓ.cast Npq ((E p) x))
  let Φ : s p → q.rep := fun x => Ψ x
  have main : GH_dist p.rep q.rep ≤ ε + ε / 2 + ε := by
    refine' GH_dist_le_of_approx_subsets Φ _ _ _
    show ∀ x : p.rep, ∃ (y : p.rep)(H : y ∈ s p), dist x y ≤ ε
    · intro x
      have : x ∈ ⋃ y ∈ s p, ball y ε := (hs p).2 (mem_univ _)
      rcases mem_Union₂.1 this with ⟨y, ys, hy⟩
      exact ⟨y, ys, le_of_ltₓ hy⟩
      
    show ∀ x : q.rep, ∃ z : s p, dist x (Φ z) ≤ ε
    · intro x
      have : x ∈ ⋃ y ∈ s q, ball y ε := (hs q).2 (mem_univ _)
      rcases mem_Union₂.1 this with ⟨y, ys, hy⟩
      let i : ℕ := E q ⟨y, ys⟩
      let hi := ((E q) ⟨y, ys⟩).is_lt
      have ihi_eq : (⟨i, hi⟩ : Finₓ (N q)) = (E q) ⟨y, ys⟩ := by
        rw [Finₓ.ext_iff, Finₓ.coe_mk]
      have hiq : i < N q := hi
      have hip : i < N p := by
        rwa [Npq.symm] at hiq
      let z := (E p).symm ⟨i, hip⟩
      use z
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩
      have C2 : Finₓ.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩ := by
        rw [ihi_eq]
        exact (E q).symm_apply_apply ⟨y, ys⟩
      have : Φ z = y := by
        simp only [Φ, Ψ]
        rw [C1, C2, C3]
        rfl
      rw [this]
      exact le_of_ltₓ hy
      
    show ∀ x y : s p, abs (dist x y - dist (Φ x) (Φ y)) ≤ ε
    · intro x y
      have : dist (Φ x) (Φ y) = dist (Ψ x) (Ψ y) := rfl
      rw [this]
      let i : ℕ := E p x
      have hip : i < N p := ((E p) x).2
      have hiq : i < N q := by
        rwa [Npq] at hip
      have i' : i = (E q) (Ψ x) := by
        simp [Ψ]
      let j : ℕ := E p y
      have hjp : j < N p := ((E p) y).2
      have hjq : j < N q := by
        rwa [Npq] at hjp
      have j' : j = ((E q) (Ψ y)).1 := by
        simp [Ψ]
      have : (F p).2 ((E p) x) ((E p) y) = floor (ε⁻¹ * dist x y) := by
        simp only [F, (E p).symm_apply_apply]
      have Ap : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = floor (ε⁻¹ * dist x y) := by
        rw [← this]
        congr <;> apply (Finₓ.ext_iff _ _).2 <;> rfl
      have : (F q).2 ((E q) (Ψ x)) ((E q) (Ψ y)) = floor (ε⁻¹ * dist (Ψ x) (Ψ y)) := by
        simp only [F, (E q).symm_apply_apply]
      have Aq : (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩ = floor (ε⁻¹ * dist (Ψ x) (Ψ y)) := by
        rw [← this]
        congr <;> apply (Finₓ.ext_iff _ _).2 <;> [exact i', exact j']
      have : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩ := by
        revert hiq hjq
        change N q with (F q).1
        generalize F q = f  at hpq⊢
        subst hpq
        intros
        rfl
      rw [Ap, Aq] at this
      have I :=
        calc
          abs ε⁻¹ * abs (dist x y - dist (Ψ x) (Ψ y)) = abs (ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))) := (abs_mul _ _).symm
          _ = abs (ε⁻¹ * dist x y - ε⁻¹ * dist (Ψ x) (Ψ y)) := by
            congr
            ring
          _ ≤ 1 := le_of_ltₓ (abs_sub_lt_one_of_floor_eq_floor this)
          
      calc abs (dist x y - dist (Ψ x) (Ψ y)) = ε * ε⁻¹ * abs (dist x y - dist (Ψ x) (Ψ y)) := by
          rw [mul_inv_cancel (ne_of_gtₓ εpos), one_mulₓ]_ = ε * (abs ε⁻¹ * abs (dist x y - dist (Ψ x) (Ψ y))) := by
          rw [abs_of_nonneg (le_of_ltₓ (inv_pos.2 εpos)), mul_assoc]_ ≤ ε * 1 :=
          mul_le_mul_of_nonneg_left I (le_of_ltₓ εpos)_ = ε := mul_oneₓ _
      
  calc dist p q = GH_dist p.rep q.rep := dist_GH_dist p q _ ≤ ε + ε / 2 + ε := main _ = δ := by
      simp [ε]
      ring

/-- Compactness criterion: a closed set of compact metric spaces is compact if the spaces have
a uniformly bounded diameter, and for all `ε` the number of balls of radius `ε` required
to cover the spaces is uniformly bounded. This is an equivalence, but we only prove the
interesting direction that these conditions imply compactness. -/
theorem TotallyBounded {t : Set GHSpace} {C : ℝ} {u : ℕ → ℝ} {K : ℕ → ℕ} (ulim : Tendsto u atTop (𝓝 0))
    (hdiam : ∀, ∀ p ∈ t, ∀, diam (Univ : Set (GHSpace.Rep p)) ≤ C)
    (hcov : ∀, ∀ p ∈ t, ∀, ∀ n : ℕ, ∃ s : Set (GHSpace.Rep p), Cardinal.mk s ≤ K n ∧ univ ⊆ ⋃ x ∈ s, Ball x (u n)) :
    TotallyBounded t := by
  refine' Metric.totally_bounded_of_finite_discretization fun δ δpos => _
  let ε := 1 / 5 * δ
  have εpos : 0 < ε :=
    mul_pos
      (by
        norm_num)
      δpos
  rcases Metric.tendsto_at_top.1 ulim ε εpos with ⟨n, hn⟩
  have u_le_ε : u n ≤ ε := by
    have := hn n le_rfl
    simp only [Real.dist_eq, add_zeroₓ, sub_eq_add_neg, neg_zero] at this
    exact le_of_ltₓ (lt_of_le_of_ltₓ (le_abs_self _) this)
  have : ∀ p : GH_space, ∃ s : Set p.rep, ∃ N ≤ K n, ∃ E : Equivₓ s (Finₓ N), p ∈ t → univ ⊆ ⋃ x ∈ s, ball x (u n) := by
    intro p
    by_cases' hp : p ∉ t
    · have : Nonempty (Equivₓ (∅ : Set p.rep) (Finₓ 0)) := by
        rw [← Fintype.card_eq]
        simp
      use ∅, 0, bot_le, choice this
      
    · rcases hcov _ (Set.not_not_mem.1 hp) n with ⟨s, ⟨scard, scover⟩⟩
      rcases Cardinal.lt_omega.1 (lt_of_le_of_ltₓ scard (Cardinal.nat_lt_omega _)) with ⟨N, hN⟩
      rw [hN, Cardinal.nat_cast_le] at scard
      have : Cardinal.mk s = Cardinal.mk (Finₓ N) := by
        rw [hN, Cardinal.mk_fin]
      cases' Quotientₓ.exact this with E
      use s, N, scard, E
      simp [hp, scover]
      
  choose s N hN E hs using this
  let M := ⌊ε⁻¹ * max C 0⌋₊
  let F : GH_space → Σ k : Finₓ (K n).succ, Finₓ k → Finₓ k → Finₓ M.succ := fun p =>
    ⟨⟨N p, lt_of_le_of_ltₓ (hN p) (Nat.lt_succ_selfₓ _)⟩, fun a b =>
      ⟨min M ⌊ε⁻¹ * dist ((E p).symm a) ((E p).symm b)⌋₊, (min_le_leftₓ _ _).trans_lt (Nat.lt_succ_selfₓ _)⟩⟩
  refine' ⟨_, _, fun p => F p, _⟩
  infer_instance
  rintro ⟨p, pt⟩ ⟨q, qt⟩ hpq
  have Npq : N p = N q := (Finₓ.ext_iff _ _).1 (Sigma.mk.inj_iff.1 hpq).1
  let Ψ : s p → s q := fun x => (E q).symm (Finₓ.cast Npq ((E p) x))
  let Φ : s p → q.rep := fun x => Ψ x
  have main : GH_dist p.rep q.rep ≤ ε + ε / 2 + ε := by
    refine' GH_dist_le_of_approx_subsets Φ _ _ _
    show ∀ x : p.rep, ∃ (y : p.rep)(H : y ∈ s p), dist x y ≤ ε
    · intro x
      have : x ∈ ⋃ y ∈ s p, ball y (u n) := (hs p pt) (mem_univ _)
      rcases mem_Union₂.1 this with ⟨y, ys, hy⟩
      exact ⟨y, ys, le_transₓ (le_of_ltₓ hy) u_le_ε⟩
      
    show ∀ x : q.rep, ∃ z : s p, dist x (Φ z) ≤ ε
    · intro x
      have : x ∈ ⋃ y ∈ s q, ball y (u n) := (hs q qt) (mem_univ _)
      rcases mem_Union₂.1 this with ⟨y, ys, hy⟩
      let i : ℕ := E q ⟨y, ys⟩
      let hi := ((E q) ⟨y, ys⟩).2
      have ihi_eq : (⟨i, hi⟩ : Finₓ (N q)) = (E q) ⟨y, ys⟩ := by
        rw [Finₓ.ext_iff, Finₓ.coe_mk]
      have hiq : i < N q := hi
      have hip : i < N p := by
        rwa [Npq.symm] at hiq
      let z := (E p).symm ⟨i, hip⟩
      use z
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩
      have C2 : Finₓ.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩ := by
        rw [ihi_eq]
        exact (E q).symm_apply_apply ⟨y, ys⟩
      have : Φ z = y := by
        simp only [Φ, Ψ]
        rw [C1, C2, C3]
        rfl
      rw [this]
      exact le_transₓ (le_of_ltₓ hy) u_le_ε
      
    show ∀ x y : s p, abs (dist x y - dist (Φ x) (Φ y)) ≤ ε
    · intro x y
      have : dist (Φ x) (Φ y) = dist (Ψ x) (Ψ y) := rfl
      rw [this]
      let i : ℕ := E p x
      have hip : i < N p := ((E p) x).2
      have hiq : i < N q := by
        rwa [Npq] at hip
      have i' : i = (E q) (Ψ x) := by
        simp [Ψ]
      let j : ℕ := E p y
      have hjp : j < N p := ((E p) y).2
      have hjq : j < N q := by
        rwa [Npq] at hjp
      have j' : j = (E q) (Ψ y) := by
        simp [Ψ]
      have Ap : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ⌊ε⁻¹ * dist x y⌋₊ :=
        calc
          ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F p).2 ((E p) x) ((E p) y)).1 := by
            congr <;> apply (Finₓ.ext_iff _ _).2 <;> rfl
          _ = min M ⌊ε⁻¹ * dist x y⌋₊ := by
            simp only [F, (E p).symm_apply_apply]
          _ = ⌊ε⁻¹ * dist x y⌋₊ := by
            refine' min_eq_rightₓ (Nat.floor_mono _)
            refine' mul_le_mul_of_nonneg_left (le_transₓ _ (le_max_leftₓ _ _)) (inv_pos.2 εpos).le
            change dist (x : p.rep) y ≤ C
            refine' le_transₓ (dist_le_diam_of_mem compact_univ.bounded (mem_univ _) (mem_univ _)) _
            exact hdiam p pt
          
      have Aq : ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ :=
        calc
          ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = ((F q).2 ((E q) (Ψ x)) ((E q) (Ψ y))).1 := by
            congr <;> apply (Finₓ.ext_iff _ _).2 <;> [exact i', exact j']
          _ = min M ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ := by
            simp only [F, (E q).symm_apply_apply]
          _ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ := by
            refine' min_eq_rightₓ (Nat.floor_mono _)
            refine' mul_le_mul_of_nonneg_left (le_transₓ _ (le_max_leftₓ _ _)) (inv_pos.2 εpos).le
            change dist (Ψ x : q.rep) (Ψ y) ≤ C
            refine' le_transₓ (dist_le_diam_of_mem compact_univ.bounded (mem_univ _) (mem_univ _)) _
            exact hdiam q qt
          
      have : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 := by
        revert hiq hjq
        change N q with (F q).1
        generalize F q = f  at hpq⊢
        subst hpq
        intros
        rfl
      have : ⌊ε⁻¹ * dist x y⌋ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ := by
        rw [Ap, Aq] at this
        have D : 0 ≤ ⌊ε⁻¹ * dist x y⌋ := floor_nonneg.2 (mul_nonneg (le_of_ltₓ (inv_pos.2 εpos)) dist_nonneg)
        have D' : 0 ≤ ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ := floor_nonneg.2 (mul_nonneg (le_of_ltₓ (inv_pos.2 εpos)) dist_nonneg)
        rw [← Int.to_nat_of_nonneg D, ← Int.to_nat_of_nonneg D', Int.floor_to_nat, Int.floor_to_nat, this]
      have I :=
        calc
          abs ε⁻¹ * abs (dist x y - dist (Ψ x) (Ψ y)) = abs (ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))) := (abs_mul _ _).symm
          _ = abs (ε⁻¹ * dist x y - ε⁻¹ * dist (Ψ x) (Ψ y)) := by
            congr
            ring
          _ ≤ 1 := le_of_ltₓ (abs_sub_lt_one_of_floor_eq_floor this)
          
      calc abs (dist x y - dist (Ψ x) (Ψ y)) = ε * ε⁻¹ * abs (dist x y - dist (Ψ x) (Ψ y)) := by
          rw [mul_inv_cancel (ne_of_gtₓ εpos), one_mulₓ]_ = ε * (abs ε⁻¹ * abs (dist x y - dist (Ψ x) (Ψ y))) := by
          rw [abs_of_nonneg (le_of_ltₓ (inv_pos.2 εpos)), mul_assoc]_ ≤ ε * 1 :=
          mul_le_mul_of_nonneg_left I (le_of_ltₓ εpos)_ = ε := mul_oneₓ _
      
  calc dist p q = GH_dist p.rep q.rep := dist_GH_dist p q _ ≤ ε + ε / 2 + ε := main _ = δ / 2 := by
      simp [ε]
      ring _ < δ := half_lt_self δpos

section Complete

variable (X : ℕ → Type) [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)]

/-- Auxiliary structure used to glue metric spaces below, recording an isometric embedding
of a type `A` in another metric space. -/
structure aux_gluing_struct (A : Type) [MetricSpace A] : Type 1 where
  Space : Type
  metric : MetricSpace space
  embed : A → space
  isom : Isometry embed

instance (A : Type) [MetricSpace A] : Inhabited (AuxGluingStruct A) :=
  ⟨{ Space := A,
      metric := by
        infer_instance,
      embed := id, isom := fun x y => rfl }⟩

/-- Auxiliary sequence of metric spaces, containing copies of `X 0`, ..., `X n`, where each
`X i` is glued to `X (i+1)` in an optimal way. The space at step `n+1` is obtained from the space
at step `n` by adding `X (n+1)`, glued in an optimal way to the `X n` already sitting there. -/
def aux_gluing (n : ℕ) : AuxGluingStruct (X n) :=
  Nat.recOn n
    { Space := X 0,
      metric := by
        infer_instance,
      embed := id, isom := fun x y => rfl }
    fun n Y => by
    let this' : MetricSpace Y.space := Y.metric <;>
      exact
        { Space := glue_space Y.isom (isometry_optimal_GH_injl (X n) (X (n + 1))),
          metric := by
            infer_instance,
          embed := to_glue_r Y.isom (isometry_optimal_GH_injl (X n) (X (n + 1))) ∘ optimal_GH_injr (X n) (X (n + 1)),
          isom := (to_glue_r_isometry _ _).comp (isometry_optimal_GH_injr (X n) (X (n + 1))) }

/-- The Gromov-Hausdorff space is complete. -/
instance : CompleteSpace GHSpace := by
  have : ∀ n : ℕ, 0 < ((1 : ℝ) / 2) ^ n := by
    apply pow_pos
    norm_num
  refine' Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2) ^ n) this fun u hu => _
  let X := fun n => (u n).rep
  let Y := aux_gluing X
  let this' : ∀ n, MetricSpace (Y n).Space := fun n => (Y n).metric
  have E : ∀ n : ℕ, glue_space (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ)) = (Y n.succ).Space := fun n => by
    simp [Y, aux_gluing]
    rfl
  let c := fun n => cast (E n)
  have ic : ∀ n, Isometry (c n) := fun n x y => rfl
  let f : ∀ n, (Y n).Space → (Y n.succ).Space := fun n =>
    c n ∘ to_glue_l (aux_gluing X n).isom (isometry_optimal_GH_injl (X n) (X n.succ))
  have I : ∀ n, Isometry (f n) := by
    intro n
    apply Isometry.comp
    · intro x y
      rfl
      
    · apply to_glue_l_isometry
      
  let Z0 := Metric.InductiveLimit I
  let Z := UniformSpace.Completion Z0
  let Φ := to_inductive_limit I
  let coeZ := (coe : Z0 → Z)
  let X2 := fun n => range (coeZ ∘ Φ n ∘ (Y n).embed)
  have isom : ∀ n, Isometry (coeZ ∘ Φ n ∘ (Y n).embed) := by
    intro n
    apply Isometry.comp completion.coe_isometry _
    apply Isometry.comp _ (Y n).isom
    apply to_inductive_limit_isometry
  have D2 : ∀ n, Hausdorff_dist (X2 n) (X2 n.succ) < (1 / 2) ^ n := by
    intro n
    have X2n :
      X2 n =
        range
          ((coeZ ∘ Φ n.succ ∘ c n ∘ to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ))) ∘
            optimal_GH_injl (X n) (X n.succ)) :=
      by
      change
        X2 n =
          range
            (coeZ ∘
              Φ n.succ ∘
                c n ∘
                  to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ)) ∘ optimal_GH_injl (X n) (X n.succ))
      simp only [X2, Φ]
      rw [← to_inductive_limit_commute I]
      simp only [f]
      rw [← to_glue_commute]
    rw [range_comp] at X2n
    have X2nsucc :
      X2 n.succ =
        range
          ((coeZ ∘ Φ n.succ ∘ c n ∘ to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ))) ∘
            optimal_GH_injr (X n) (X n.succ)) :=
      by
      rfl
    rw [range_comp] at X2nsucc
    rw [X2n, X2nsucc, Hausdorff_dist_image, Hausdorff_dist_optimal, ← dist_GH_dist]
    · exact hu n n n.succ (le_reflₓ n) (le_succ n)
      
    · apply Isometry.comp completion.coe_isometry _
      apply Isometry.comp _ ((ic n).comp (to_glue_r_isometry _ _))
      apply to_inductive_limit_isometry
      
  let X3 : ℕ → nonempty_compacts Z := fun n => ⟨X2 n, ⟨range_nonempty _, is_compact_range (isom n).Continuous⟩⟩
  have : CauchySeq X3 := by
    refine'
      cauchy_seq_of_le_geometric (1 / 2) 1
        (by
          norm_num)
        fun n => _
    rw [one_mulₓ]
    exact le_of_ltₓ (D2 n)
  rcases cauchy_seq_tendsto_of_complete this with ⟨L, hL⟩
  have M : tendsto (fun n => (X3 n).toGHSpace) at_top (𝓝 L.to_GH_space) :=
    tendsto.comp (to_GH_space_continuous.tendsto _) hL
  have : ∀ n, (X3 n).toGHSpace = u n := by
    intro n
    rw [nonempty_compacts.to_GH_space, ← (u n).to_GH_space_rep, to_GH_space_eq_to_GH_space_iff_isometric]
    constructor
    convert (isom n).isometricOnRange.symm
  exact
    ⟨L.to_GH_space, by
      simpa [this] using M⟩

end Complete

end GromovHausdorff

