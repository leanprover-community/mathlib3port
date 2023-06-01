/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Yury Kudryashov

! This file was ported from Lean 3 source module topology.alexandroff
! leanprover-community/mathlib commit ac34df03f74e6f797efd6991df2e3b7f7d8d33e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Option
import Mathbin.Topology.Separation
import Mathbin.Topology.Sets.Opens

/-!
# The Alexandroff Compactification

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct the Alexandroff compactification (the one-point compactification) of an arbitrary
topological space `X` and prove some properties inherited from `X`.

## Main definitions

* `alexandroff`: the Alexandroff compactification, we use coercion for the canonical embedding
  `X → alexandroff X`; when `X` is already compact, the compactification adds an isolated point
  to the space.
* `alexandroff.infty`: the extra point

## Main results

* The topological structure of `alexandroff X`
* The connectedness of `alexandroff X` for a noncompact, preconnected `X`
* `alexandroff X` is `T₀` for a T₀ space `X`
* `alexandroff X` is `T₁` for a T₁ space `X`
* `alexandroff X` is normal if `X` is a locally compact Hausdorff space

## Tags

one-point compactification, compactness
-/


open Set Filter

open scoped Classical Topology Filter

/-!
### Definition and basic properties

In this section we define `alexandroff X` to be the disjoint union of `X` and `∞`, implemented as
`option X`. Then we restate some lemmas about `option X` for `alexandroff X`.
-/


variable {X : Type _}

#print OnePoint /-
/-- The Alexandroff extension of an arbitrary topological space `X` -/
def OnePoint (X : Type _) :=
  Option X
#align alexandroff OnePoint
-/

/-- The repr uses the notation from the `alexandroff` locale. -/
instance [Repr X] : Repr (OnePoint X) :=
  ⟨fun o =>
    match o with
    | none => "∞"
    | some a => "↑" ++ repr a⟩

namespace OnePoint

#print OnePoint.infty /-
/-- The point at infinity -/
def infty : OnePoint X :=
  none
#align alexandroff.infty OnePoint.infty
-/

-- mathport name: alexandroff.infty
scoped notation "∞" => OnePoint.infty

instance : CoeTC X (OnePoint X) :=
  ⟨Option.some⟩

instance : Inhabited (OnePoint X) :=
  ⟨∞⟩

instance [Fintype X] : Fintype (OnePoint X) :=
  Option.fintype

#print OnePoint.infinite /-
instance infinite [Infinite X] : Infinite (OnePoint X) :=
  Option.infinite
#align alexandroff.infinite OnePoint.infinite
-/

#print OnePoint.coe_injective /-
theorem coe_injective : Function.Injective (coe : X → OnePoint X) :=
  Option.some_injective X
#align alexandroff.coe_injective OnePoint.coe_injective
-/

#print OnePoint.coe_eq_coe /-
@[norm_cast]
theorem coe_eq_coe {x y : X} : (x : OnePoint X) = y ↔ x = y :=
  coe_injective.eq_iff
#align alexandroff.coe_eq_coe OnePoint.coe_eq_coe
-/

#print OnePoint.coe_ne_infty /-
@[simp]
theorem coe_ne_infty (x : X) : (x : OnePoint X) ≠ ∞ :=
  fun.
#align alexandroff.coe_ne_infty OnePoint.coe_ne_infty
-/

#print OnePoint.infty_ne_coe /-
@[simp]
theorem infty_ne_coe (x : X) : ∞ ≠ (x : OnePoint X) :=
  fun.
#align alexandroff.infty_ne_coe OnePoint.infty_ne_coe
-/

#print OnePoint.rec /-
/-- Recursor for `alexandroff` using the preferred forms `∞` and `↑x`. -/
@[elab_as_elim]
protected def rec (C : OnePoint X → Sort _) (h₁ : C ∞) (h₂ : ∀ x : X, C x) :
    ∀ z : OnePoint X, C z :=
  Option.rec h₁ h₂
#align alexandroff.rec OnePoint.rec
-/

theorem isCompl_range_coe_infty : IsCompl (range (coe : X → OnePoint X)) {∞} :=
  isCompl_range_some_none X
#align alexandroff.is_compl_range_coe_infty OnePoint.isCompl_range_coe_infty

@[simp]
theorem range_coe_union_infty : range (coe : X → OnePoint X) ∪ {∞} = univ :=
  range_some_union_none X
#align alexandroff.range_coe_union_infty OnePoint.range_coe_union_infty

@[simp]
theorem range_coe_inter_infty : range (coe : X → OnePoint X) ∩ {∞} = ∅ :=
  range_some_inter_none X
#align alexandroff.range_coe_inter_infty OnePoint.range_coe_inter_infty

@[simp]
theorem compl_range_coe : range (coe : X → OnePoint X)ᶜ = {∞} :=
  compl_range_some X
#align alexandroff.compl_range_coe OnePoint.compl_range_coe

theorem compl_infty : ({∞}ᶜ : Set (OnePoint X)) = range (coe : X → OnePoint X) :=
  (@isCompl_range_coe_infty X).symm.compl_eq
#align alexandroff.compl_infty OnePoint.compl_infty

theorem compl_image_coe (s : Set X) : (coe '' s : Set (OnePoint X))ᶜ = coe '' sᶜ ∪ {∞} := by
  rw [coe_injective.compl_image_eq, compl_range_coe]
#align alexandroff.compl_image_coe OnePoint.compl_image_coe

#print OnePoint.ne_infty_iff_exists /-
theorem ne_infty_iff_exists {x : OnePoint X} : x ≠ ∞ ↔ ∃ y : X, (y : OnePoint X) = x := by
  induction x using OnePoint.rec <;> simp
#align alexandroff.ne_infty_iff_exists OnePoint.ne_infty_iff_exists
-/

#print OnePoint.canLift /-
instance canLift : CanLift (OnePoint X) X coe fun x => x ≠ ∞ :=
  WithTop.canLift
#align alexandroff.can_lift OnePoint.canLift
-/

#print OnePoint.not_mem_range_coe_iff /-
theorem not_mem_range_coe_iff {x : OnePoint X} : x ∉ range (coe : X → OnePoint X) ↔ x = ∞ := by
  rw [← mem_compl_iff, compl_range_coe, mem_singleton_iff]
#align alexandroff.not_mem_range_coe_iff OnePoint.not_mem_range_coe_iff
-/

#print OnePoint.infty_not_mem_range_coe /-
theorem infty_not_mem_range_coe : ∞ ∉ range (coe : X → OnePoint X) :=
  not_mem_range_coe_iff.2 rfl
#align alexandroff.infty_not_mem_range_coe OnePoint.infty_not_mem_range_coe
-/

#print OnePoint.infty_not_mem_image_coe /-
theorem infty_not_mem_image_coe {s : Set X} : ∞ ∉ (coe : X → OnePoint X) '' s :=
  not_mem_subset (image_subset_range _ _) infty_not_mem_range_coe
#align alexandroff.infty_not_mem_image_coe OnePoint.infty_not_mem_image_coe
-/

#print OnePoint.coe_preimage_infty /-
@[simp]
theorem coe_preimage_infty : (coe : X → OnePoint X) ⁻¹' {∞} = ∅ := by ext; simp
#align alexandroff.coe_preimage_infty OnePoint.coe_preimage_infty
-/

/-!
### Topological space structure on `alexandroff X`

We define a topological space structure on `alexandroff X` so that `s` is open if and only if

* `coe ⁻¹' s` is open in `X`;
* if `∞ ∈ s`, then `(coe ⁻¹' s)ᶜ` is compact.

Then we reformulate this definition in a few different ways, and prove that
`coe : X → alexandroff X` is an open embedding. If `X` is not a compact space, then we also prove
that `coe` has dense range, so it is a dense embedding.
-/


variable [TopologicalSpace X]

instance : TopologicalSpace (OnePoint X)
    where
  IsOpen s :=
    (∞ ∈ s → IsCompact (((coe : X → OnePoint X) ⁻¹' s)ᶜ)) ∧ IsOpen ((coe : X → OnePoint X) ⁻¹' s)
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro ⟨hms, hs⟩ ⟨hmt, ht⟩
    refine' ⟨_, hs.inter ht⟩
    rintro ⟨hms', hmt'⟩
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  isOpen_sUnion S ho :=
    by
    suffices IsOpen (coe ⁻¹' ⋃₀ S : Set X) by
      refine' ⟨_, this⟩
      rintro ⟨s, hsS : s ∈ S, hs : ∞ ∈ s⟩
      refine' isCompact_of_isClosed_subset ((ho s hsS).1 hs) this.is_closed_compl _
      exact compl_subset_compl.mpr (preimage_mono <| subset_sUnion_of_mem hsS)
    rw [preimage_sUnion]
    exact isOpen_biUnion fun s hs => (ho s hs).2

variable {s : Set (OnePoint X)} {t : Set X}

theorem isOpen_def :
    IsOpen s ↔ (∞ ∈ s → IsCompact ((coe ⁻¹' s : Set X)ᶜ)) ∧ IsOpen (coe ⁻¹' s : Set X) :=
  Iff.rfl
#align alexandroff.is_open_def OnePoint.isOpen_def

theorem isOpen_iff_of_mem' (h : ∞ ∈ s) :
    IsOpen s ↔ IsCompact ((coe ⁻¹' s : Set X)ᶜ) ∧ IsOpen (coe ⁻¹' s : Set X) := by
  simp [is_open_def, h]
#align alexandroff.is_open_iff_of_mem' OnePoint.isOpen_iff_of_mem'

theorem isOpen_iff_of_mem (h : ∞ ∈ s) :
    IsOpen s ↔ IsClosed ((coe ⁻¹' s : Set X)ᶜ) ∧ IsCompact ((coe ⁻¹' s : Set X)ᶜ) := by
  simp only [is_open_iff_of_mem' h, isClosed_compl_iff, and_comm]
#align alexandroff.is_open_iff_of_mem OnePoint.isOpen_iff_of_mem

theorem isOpen_iff_of_not_mem (h : ∞ ∉ s) : IsOpen s ↔ IsOpen (coe ⁻¹' s : Set X) := by
  simp [is_open_def, h]
#align alexandroff.is_open_iff_of_not_mem OnePoint.isOpen_iff_of_not_mem

theorem isClosed_iff_of_mem (h : ∞ ∈ s) : IsClosed s ↔ IsClosed (coe ⁻¹' s : Set X) :=
  by
  have : ∞ ∉ sᶜ := fun H => H h
  rw [← isOpen_compl_iff, is_open_iff_of_not_mem this, ← isOpen_compl_iff, preimage_compl]
#align alexandroff.is_closed_iff_of_mem OnePoint.isClosed_iff_of_mem

theorem isClosed_iff_of_not_mem (h : ∞ ∉ s) :
    IsClosed s ↔ IsClosed (coe ⁻¹' s : Set X) ∧ IsCompact (coe ⁻¹' s : Set X) := by
  rw [← isOpen_compl_iff, is_open_iff_of_mem (mem_compl h), ← preimage_compl, compl_compl]
#align alexandroff.is_closed_iff_of_not_mem OnePoint.isClosed_iff_of_not_mem

@[simp]
theorem isOpen_image_coe {s : Set X} : IsOpen (coe '' s : Set (OnePoint X)) ↔ IsOpen s := by
  rw [is_open_iff_of_not_mem infty_not_mem_image_coe, preimage_image_eq _ coe_injective]
#align alexandroff.is_open_image_coe OnePoint.isOpen_image_coe

theorem isOpen_compl_image_coe {s : Set X} :
    IsOpen ((coe '' s : Set (OnePoint X))ᶜ) ↔ IsClosed s ∧ IsCompact s :=
  by
  rw [is_open_iff_of_mem, ← preimage_compl, compl_compl, preimage_image_eq _ coe_injective]
  exact infty_not_mem_image_coe
#align alexandroff.is_open_compl_image_coe OnePoint.isOpen_compl_image_coe

@[simp]
theorem isClosed_image_coe {s : Set X} :
    IsClosed (coe '' s : Set (OnePoint X)) ↔ IsClosed s ∧ IsCompact s := by
  rw [← isOpen_compl_iff, is_open_compl_image_coe]
#align alexandroff.is_closed_image_coe OnePoint.isClosed_image_coe

/-- An open set in `alexandroff X` constructed from a closed compact set in `X` -/
def opensOfCompl (s : Set X) (h₁ : IsClosed s) (h₂ : IsCompact s) :
    TopologicalSpace.Opens (OnePoint X) :=
  ⟨(coe '' s)ᶜ, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩
#align alexandroff.opens_of_compl OnePoint.opensOfCompl

#print OnePoint.infty_mem_opensOfCompl /-
theorem infty_mem_opensOfCompl {s : Set X} (h₁ : IsClosed s) (h₂ : IsCompact s) :
    ∞ ∈ opensOfCompl s h₁ h₂ :=
  mem_compl infty_not_mem_image_coe
#align alexandroff.infty_mem_opens_of_compl OnePoint.infty_mem_opensOfCompl
-/

@[continuity]
theorem continuous_coe : Continuous (coe : X → OnePoint X) :=
  continuous_def.mpr fun s hs => hs.right
#align alexandroff.continuous_coe OnePoint.continuous_coe

theorem isOpenMap_coe : IsOpenMap (coe : X → OnePoint X) := fun s => isOpen_image_coe.2
#align alexandroff.is_open_map_coe OnePoint.isOpenMap_coe

theorem openEmbedding_coe : OpenEmbedding (coe : X → OnePoint X) :=
  openEmbedding_of_continuous_injective_open continuous_coe coe_injective isOpenMap_coe
#align alexandroff.open_embedding_coe OnePoint.openEmbedding_coe

theorem isOpen_range_coe : IsOpen (range (coe : X → OnePoint X)) :=
  openEmbedding_coe.open_range
#align alexandroff.is_open_range_coe OnePoint.isOpen_range_coe

theorem isClosed_infty : IsClosed ({∞} : Set (OnePoint X)) := by
  rw [← compl_range_coe, isClosed_compl_iff]; exact is_open_range_coe
#align alexandroff.is_closed_infty OnePoint.isClosed_infty

theorem nhds_coe_eq (x : X) : 𝓝 ↑x = map (coe : X → OnePoint X) (𝓝 x) :=
  (openEmbedding_coe.map_nhds_eq x).symm
#align alexandroff.nhds_coe_eq OnePoint.nhds_coe_eq

theorem nhdsWithin_coe_image (s : Set X) (x : X) :
    𝓝[coe '' s] (x : OnePoint X) = map coe (𝓝[s] x) :=
  (openEmbedding_coe.toEmbedding.map_nhdsWithin_eq _ _).symm
#align alexandroff.nhds_within_coe_image OnePoint.nhdsWithin_coe_image

theorem nhdsWithin_coe (s : Set (OnePoint X)) (x : X) : 𝓝[s] ↑x = map coe (𝓝[coe ⁻¹' s] x) :=
  (openEmbedding_coe.map_nhdsWithin_preimage_eq _ _).symm
#align alexandroff.nhds_within_coe OnePoint.nhdsWithin_coe

theorem comap_coe_nhds (x : X) : comap (coe : X → OnePoint X) (𝓝 x) = 𝓝 x :=
  (openEmbedding_coe.to_inducing.nhds_eq_comap x).symm
#align alexandroff.comap_coe_nhds OnePoint.comap_coe_nhds

/-- If `x` is not an isolated point of `X`, then `x : alexandroff X` is not an isolated point
of `alexandroff X`. -/
instance nhdsWithin_compl_coe_neBot (x : X) [h : NeBot (𝓝[≠] x)] : NeBot (𝓝[≠] (x : OnePoint X)) :=
  by simpa [nhds_within_coe, preimage, coe_eq_coe] using h.map coe
#align alexandroff.nhds_within_compl_coe_ne_bot OnePoint.nhdsWithin_compl_coe_neBot

theorem nhdsWithin_compl_infty_eq : 𝓝[≠] (∞ : OnePoint X) = map coe (coclosedCompact X) :=
  by
  refine' (nhdsWithin_basis_open ∞ _).ext (has_basis_coclosed_compact.map _) _ _
  · rintro s ⟨hs, hso⟩
    refine' ⟨_, (is_open_iff_of_mem hs).mp hso, _⟩
    simp
  · rintro s ⟨h₁, h₂⟩
    refine' ⟨_, ⟨mem_compl infty_not_mem_image_coe, is_open_compl_image_coe.2 ⟨h₁, h₂⟩⟩, _⟩
    simp [compl_image_coe, ← diff_eq, subset_preimage_image]
#align alexandroff.nhds_within_compl_infty_eq OnePoint.nhdsWithin_compl_infty_eq

/-- If `X` is a non-compact space, then `∞` is not an isolated point of `alexandroff X`. -/
instance nhdsWithin_compl_infty_neBot [NoncompactSpace X] : NeBot (𝓝[≠] (∞ : OnePoint X)) := by
  rw [nhds_within_compl_infty_eq]; infer_instance
#align alexandroff.nhds_within_compl_infty_ne_bot OnePoint.nhdsWithin_compl_infty_neBot

instance (priority := 900) nhdsWithin_compl_neBot [∀ x : X, NeBot (𝓝[≠] x)] [NoncompactSpace X]
    (x : OnePoint X) : NeBot (𝓝[≠] x) :=
  OnePoint.rec _ OnePoint.nhdsWithin_compl_infty_neBot
    (fun y => OnePoint.nhdsWithin_compl_coe_neBot y) x
#align alexandroff.nhds_within_compl_ne_bot OnePoint.nhdsWithin_compl_neBot

theorem nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map coe (coclosedCompact X) ⊔ pure ∞ := by
  rw [← nhds_within_compl_infty_eq, nhdsWithin_compl_singleton_sup_pure]
#align alexandroff.nhds_infty_eq OnePoint.nhds_infty_eq

theorem hasBasis_nhds_infty :
    (𝓝 (∞ : OnePoint X)).HasBasis (fun s : Set X => IsClosed s ∧ IsCompact s) fun s =>
      coe '' sᶜ ∪ {∞} :=
  by
  rw [nhds_infty_eq]
  exact (has_basis_coclosed_compact.map _).sup_pure _
#align alexandroff.has_basis_nhds_infty OnePoint.hasBasis_nhds_infty

@[simp]
theorem comap_coe_nhds_infty : comap (coe : X → OnePoint X) (𝓝 ∞) = coclosedCompact X := by
  simp [nhds_infty_eq, comap_sup, comap_map coe_injective]
#align alexandroff.comap_coe_nhds_infty OnePoint.comap_coe_nhds_infty

theorem le_nhds_infty {f : Filter (OnePoint X)} :
    f ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → coe '' sᶜ ∪ {∞} ∈ f := by
  simp only [has_basis_nhds_infty.ge_iff, and_imp]
#align alexandroff.le_nhds_infty OnePoint.le_nhds_infty

theorem ultrafilter_le_nhds_infty {f : Ultrafilter (OnePoint X)} :
    (f : Filter (OnePoint X)) ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → coe '' s ∉ f := by
  simp only [le_nhds_infty, ← compl_image_coe, Ultrafilter.mem_coe,
    Ultrafilter.compl_mem_iff_not_mem]
#align alexandroff.ultrafilter_le_nhds_infty OnePoint.ultrafilter_le_nhds_infty

theorem tendsto_nhds_infty' {α : Type _} {f : OnePoint X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto (f ∘ coe) (coclosedCompact X) l := by
  simp [nhds_infty_eq, and_comm']
#align alexandroff.tendsto_nhds_infty' OnePoint.tendsto_nhds_infty'

theorem tendsto_nhds_infty {α : Type _} {f : OnePoint X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔
      ∀ s ∈ l, f ∞ ∈ s ∧ ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ coe) (tᶜ) s :=
  tendsto_nhds_infty'.trans <| by
    simp only [tendsto_pure_left, has_basis_coclosed_compact.tendsto_left_iff, forall_and,
      and_assoc', exists_prop]
#align alexandroff.tendsto_nhds_infty OnePoint.tendsto_nhds_infty

theorem continuousAt_infty' {Y : Type _} [TopologicalSpace Y] {f : OnePoint X → Y} :
    ContinuousAt f ∞ ↔ Tendsto (f ∘ coe) (coclosedCompact X) (𝓝 (f ∞)) :=
  tendsto_nhds_infty'.trans <| and_iff_right (tendsto_pure_nhds _ _)
#align alexandroff.continuous_at_infty' OnePoint.continuousAt_infty'

theorem continuousAt_infty {Y : Type _} [TopologicalSpace Y] {f : OnePoint X → Y} :
    ContinuousAt f ∞ ↔
      ∀ s ∈ 𝓝 (f ∞), ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ coe) (tᶜ) s :=
  continuousAt_infty'.trans <| by
    simp only [has_basis_coclosed_compact.tendsto_left_iff, exists_prop, and_assoc']
#align alexandroff.continuous_at_infty OnePoint.continuousAt_infty

theorem continuousAt_coe {Y : Type _} [TopologicalSpace Y] {f : OnePoint X → Y} {x : X} :
    ContinuousAt f x ↔ ContinuousAt (f ∘ coe) x := by
  rw [ContinuousAt, nhds_coe_eq, tendsto_map'_iff, ContinuousAt]
#align alexandroff.continuous_at_coe OnePoint.continuousAt_coe

/-- If `X` is not a compact space, then the natural embedding `X → alexandroff X` has dense range.
-/
theorem denseRange_coe [NoncompactSpace X] : DenseRange (coe : X → OnePoint X) :=
  by
  rw [DenseRange, ← compl_infty]
  exact dense_compl_singleton _
#align alexandroff.dense_range_coe OnePoint.denseRange_coe

theorem denseEmbedding_coe [NoncompactSpace X] : DenseEmbedding (coe : X → OnePoint X) :=
  { openEmbedding_coe with dense := denseRange_coe }
#align alexandroff.dense_embedding_coe OnePoint.denseEmbedding_coe

@[simp]
theorem specializes_coe {x y : X} : (x : OnePoint X) ⤳ y ↔ x ⤳ y :=
  openEmbedding_coe.to_inducing.specializes_iff
#align alexandroff.specializes_coe OnePoint.specializes_coe

@[simp]
theorem inseparable_coe {x y : X} : Inseparable (x : OnePoint X) y ↔ Inseparable x y :=
  openEmbedding_coe.to_inducing.inseparable_iff
#align alexandroff.inseparable_coe OnePoint.inseparable_coe

theorem not_specializes_infty_coe {x : X} : ¬Specializes ∞ (x : OnePoint X) :=
  isClosed_infty.not_specializes rfl (coe_ne_infty x)
#align alexandroff.not_specializes_infty_coe OnePoint.not_specializes_infty_coe

theorem not_inseparable_infty_coe {x : X} : ¬Inseparable ∞ (x : OnePoint X) := fun h =>
  not_specializes_infty_coe h.Specializes
#align alexandroff.not_inseparable_infty_coe OnePoint.not_inseparable_infty_coe

theorem not_inseparable_coe_infty {x : X} : ¬Inseparable (x : OnePoint X) ∞ := fun h =>
  not_specializes_infty_coe h.specializes'
#align alexandroff.not_inseparable_coe_infty OnePoint.not_inseparable_coe_infty

theorem inseparable_iff {x y : OnePoint X} :
    Inseparable x y ↔ x = ∞ ∧ y = ∞ ∨ ∃ x' : X, x = x' ∧ ∃ y' : X, y = y' ∧ Inseparable x' y' := by
  induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
    simp [not_inseparable_infty_coe, not_inseparable_coe_infty, coe_eq_coe]
#align alexandroff.inseparable_iff OnePoint.inseparable_iff

/-!
### Compactness and separation properties

In this section we prove that `alexandroff X` is a compact space; it is a T₀ (resp., T₁) space if
the original space satisfies the same separation axiom. If the original space is a locally compact
Hausdorff space, then `alexandroff X` is a normal (hence, T₃ and Hausdorff) space.

Finally, if the original space `X` is *not* compact and is a preconnected space, then
`alexandroff X` is a connected space.
-/


/-- For any topological space `X`, its one point compactification is a compact space. -/
instance : CompactSpace (OnePoint X)
    where isCompact_univ :=
    by
    have : tendsto (coe : X → OnePoint X) (cocompact X) (𝓝 ∞) :=
      by
      rw [nhds_infty_eq]
      exact (tendsto_map.mono_left cocompact_le_coclosed_compact).mono_right le_sup_left
    convert← this.is_compact_insert_range_of_cocompact continuous_coe
    exact insert_none_range_some X

/-- The one point compactification of a `t0_space` space is a `t0_space`. -/
instance [T0Space X] : T0Space (OnePoint X) :=
  by
  refine' ⟨fun x y hxy => _⟩
  rcases inseparable_iff.1 hxy with (⟨rfl, rfl⟩ | ⟨x, rfl, y, rfl, h⟩)
  exacts [rfl, congr_arg coe h.eq]

/-- The one point compactification of a `t1_space` space is a `t1_space`. -/
instance [T1Space X] : T1Space (OnePoint X)
    where t1 z := by
    induction z using OnePoint.rec
    · exact is_closed_infty
    · rw [← image_singleton, is_closed_image_coe]
      exact ⟨isClosed_singleton, isCompact_singleton⟩

/-- The one point compactification of a locally compact Hausdorff space is a normal (hence,
Hausdorff and regular) topological space. -/
instance [LocallyCompactSpace X] [T2Space X] : NormalSpace (OnePoint X) :=
  by
  have key :
    ∀ z : X, ∃ u v : Set (OnePoint X), IsOpen u ∧ IsOpen v ∧ ↑z ∈ u ∧ ∞ ∈ v ∧ Disjoint u v :=
    by
    intro z
    rcases exists_open_with_compact_closure z with ⟨u, hu, huy', Hu⟩
    exact
      ⟨coe '' u, (coe '' closure u)ᶜ, is_open_image_coe.2 hu,
        is_open_compl_image_coe.2 ⟨isClosed_closure, Hu⟩, mem_image_of_mem _ huy',
        mem_compl infty_not_mem_image_coe, (image_subset _ subset_closure).disjoint_compl_right⟩
  refine' @normalOfCompactT2 _ _ _ ⟨fun x y hxy => _⟩
  induction x using OnePoint.rec <;> induction y using OnePoint.rec
  · exact (hxy rfl).elim
  · rcases key y with ⟨u, v, hu, hv, hxu, hyv, huv⟩
    exact ⟨v, u, hv, hu, hyv, hxu, huv.symm⟩
  · exact key x
  · exact separated_by_openEmbedding open_embedding_coe (mt coe_eq_coe.mpr hxy)

/-- If `X` is not a compact space, then `alexandroff X` is a connected space. -/
instance [PreconnectedSpace X] [NoncompactSpace X] : ConnectedSpace (OnePoint X)
    where
  to_preconnectedSpace := denseEmbedding_coe.to_denseInducing.PreconnectedSpace
  to_nonempty := inferInstance

/-- If `X` is an infinite type with discrete topology (e.g., `ℕ`), then the identity map from
`cofinite_topology (alexandroff X)` to `alexandroff X` is not continuous. -/
theorem not_continuous_cofiniteTopology_of_symm [Infinite X] [DiscreteTopology X] :
    ¬Continuous (@CofiniteTopology.of (OnePoint X)).symm :=
  by
  inhabit X
  simp only [continuous_iff_continuousAt, ContinuousAt, not_forall]
  use CofiniteTopology.of ↑(default : X)
  simpa [nhds_coe_eq, nhds_discrete, CofiniteTopology.nhds_eq] using
    (finite_singleton ((default : X) : OnePoint X)).infinite_compl
#align alexandroff.not_continuous_cofinite_topology_of_symm OnePoint.not_continuous_cofiniteTopology_of_symm

end OnePoint

#print Continuous.homeoOfEquivCompactToT2.t1_counterexample /-
/-- A concrete counterexample shows that  `continuous.homeo_of_equiv_compact_to_t2`
cannot be generalized from `t2_space` to `t1_space`.

Let `α = alexandroff ℕ` be the one-point compactification of `ℕ`, and let `β` be the same space
`alexandroff ℕ` with the cofinite topology.  Then `α` is compact, `β` is T1, and the identity map
`id : α → β` is a continuous equivalence that is not a homeomorphism.
-/
theorem Continuous.homeoOfEquivCompactToT2.t1_counterexample :
    ∃ (α β : Type) (Iα : TopologicalSpace α) (Iβ : TopologicalSpace β),
      CompactSpace α ∧ T1Space β ∧ ∃ f : α ≃ β, Continuous f ∧ ¬Continuous f.symm :=
  ⟨OnePoint ℕ, CofiniteTopology (OnePoint ℕ), inferInstance, inferInstance, inferInstance,
    inferInstance, CofiniteTopology.of, CofiniteTopology.continuous_of,
    OnePoint.not_continuous_cofiniteTopology_of_symm⟩
#align continuous.homeo_of_equiv_compact_to_t2.t1_counterexample Continuous.homeoOfEquivCompactToT2.t1_counterexample
-/

