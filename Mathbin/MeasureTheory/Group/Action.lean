import Mathbin.MeasureTheory.Group.MeasurableEquiv 
import Mathbin.MeasureTheory.Measure.Regular 
import Mathbin.Dynamics.Ergodic.MeasurePreserving 
import Mathbin.Dynamics.Minimal

/-!
# Measures invariant under group actions

A measure `μ : measure α` is said to be *invariant* under an action of a group `G` if scalar
multiplication by `c : G` is a measure preserving map for all `c`. In this file we define a
typeclass for measures invariant under action of an (additive or multiplicative) group and prove
some basic properties of such measures.
-/


open_locale Ennreal Nnreal Pointwise TopologicalSpace

open MeasureTheory MeasureTheory.Measure Set Function

namespace MeasureTheory

variable {G M α : Type _}

/-- A measure `μ : measure α` is invariant under an additive action of `M` on `α` if for any
measurable set `s : set α` and `c : M`, the measure of its preimage under `λ x, c +ᵥ x` is equal to
the measure of `s`. -/
class vadd_invariant_measure (M α : Type _) [HasVadd M α] {_ : MeasurableSpace α} (μ : Measureₓ α) : Prop where 
  measure_preimage_vadd{} : ∀ c : M ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c +ᵥ x) ⁻¹' s) = μ s

/-- A measure `μ : measure α` is invariant under a multiplicative action of `M` on `α` if for any
measurable set `s : set α` and `c : M`, the measure of its preimage under `λ x, c • x` is equal to
the measure of `s`. -/
@[toAdditive]
class smul_invariant_measure (M α : Type _) [HasScalar M α] {_ : MeasurableSpace α} (μ : Measureₓ α) : Prop where 
  measure_preimage_smul{} : ∀ c : M ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c • x) ⁻¹' s) = μ s

namespace SmulInvariantMeasure

@[toAdditive]
instance zero [MeasurableSpace α] [HasScalar M α] : smul_invariant_measure M α 0 :=
  ⟨fun _ _ _ => rfl⟩

variable [HasScalar M α] {m : MeasurableSpace α} {μ ν : Measureₓ α}

@[toAdditive]
instance add [smul_invariant_measure M α μ] [smul_invariant_measure M α ν] : smul_invariant_measure M α (μ+ν) :=
  ⟨fun c s hs => show (_+_) = _+_ from congr_arg2ₓ (·+·) (measure_preimage_smul μ c hs) (measure_preimage_smul ν c hs)⟩

@[toAdditive]
instance smul [smul_invariant_measure M α μ] (c : ℝ≥0∞) : smul_invariant_measure M α (c • μ) :=
  ⟨fun a s hs => show c • _ = c • _ from congr_argₓ ((· • ·) c) (measure_preimage_smul μ a hs)⟩

@[toAdditive]
instance smul_nnreal [smul_invariant_measure M α μ] (c :  ℝ≥0 ) : smul_invariant_measure M α (c • μ) :=
  smul_invariant_measure.smul c

end SmulInvariantMeasure

variable (G) {m : MeasurableSpace α} [Groupₓ G] [MulAction G α] [MeasurableSpace G] [HasMeasurableSmul G α] (c : G)
  (μ : Measureₓ α)

/-- Equivalent definitions of a measure invariant under a multiplicative action of a group.

- 0: `smul_invariant_measure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under scalar
     multiplication by `c` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c • s` of `s` under
     scalar multiplication by `c` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, scalar multiplication by `c` maps `μ` to `μ`;

- 6: for any `c : G`, scalar multiplication by `c` is a measure preserving map. -/
@[toAdditive]
theorem smul_invariant_measure_tfae :
  tfae
    [smul_invariant_measure G α μ, ∀ c : G s, MeasurableSet s → μ ((· • ·) c ⁻¹' s) = μ s,
      ∀ c : G s, MeasurableSet s → μ (c • s) = μ s, ∀ c : G s, μ ((· • ·) c ⁻¹' s) = μ s, ∀ c : G s, μ (c • s) = μ s,
      ∀ c : G, measure.map ((· • ·) c) μ = μ, ∀ c : G, measure_preserving ((· • ·) c) μ μ] :=
  by 
    tfaeHave 1 ↔ 2 
    exact ⟨fun h => h.1, fun h => ⟨h⟩⟩
    tfaeHave 2 → 6 
    exact
      fun H c =>
        ext
          fun s hs =>
            by 
              rw [map_apply (measurable_const_smul c) hs, H _ _ hs]
    tfaeHave 6 → 7 
    exact fun H c => ⟨measurable_const_smul c, H c⟩
    tfaeHave 7 → 4 
    exact fun H c => (H c).measure_preimage_emb (measurable_embedding_const_smul c)
    tfaeHave 4 → 5 
    exact
      fun H c s =>
        by 
          rw [←preimage_smul_inv]
          apply H 
    tfaeHave 5 → 3 
    exact fun H c s hs => H c s 
    tfaeHave 3 → 2
    ·
      intro H c s hs 
      rw [preimage_smul]
      exact H (c⁻¹) s hs 
    tfaeFinish

/-- Equivalent definitions of a measure invariant under an additive action of a group.

- 0: `vadd_invariant_measure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under
     vector addition `(+ᵥ) c` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c +ᵥ s` of `s` under
     vector addition `(+ᵥ) c` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, vector addition of `c` maps `μ` to `μ`;

- 6: for any `c : G`, vector addition of `c` is a measure preserving map. -/
add_decl_doc vadd_invariant_measure_tfae

variable {G} [smul_invariant_measure G α μ]

@[toAdditive]
theorem measure_preserving_smul : measure_preserving ((· • ·) c) μ μ :=
  ((smul_invariant_measure_tfae G μ).out 0 6).mp ‹_› c

@[simp, toAdditive]
theorem map_smul : map ((· • ·) c) μ = μ :=
  (measure_preserving_smul c μ).map_eq

@[simp, toAdditive]
theorem measure_preimage_smul (s : Set α) : μ ((· • ·) c ⁻¹' s) = μ s :=
  ((smul_invariant_measure_tfae G μ).out 0 3).mp ‹_› c s

@[simp, toAdditive]
theorem measure_smul_set (s : Set α) : μ (c • s) = μ s :=
  ((smul_invariant_measure_tfae G μ).out 0 4).mp ‹_› c s

section IsMinimal

variable (G) {μ} [TopologicalSpace G] [TopologicalSpace α] [HasContinuousSmul G α] [MulAction.IsMinimal G α]
  {K U : Set α}

/-- If measure `μ` is invariant under a group action and is nonzero on a compact set `K`, then it is
positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0` instead of
`μ K ≠ 0`, see `measure_theory.measure_is_open_pos_of_smul_invariant_of_ne_zero`. -/
@[toAdditive]
theorem measure_is_open_pos_of_smul_invariant_of_compact_ne_zero (hK : IsCompact K) (hμK : μ K ≠ 0) (hU : IsOpen U)
  (hne : U.nonempty) : 0 < μ U :=
  let ⟨t, ht⟩ := hK.exists_finite_cover_smul G hU hne 
  pos_iff_ne_zero.2$
    fun hμU =>
      hμK$
        measure_mono_null ht$
          (measure_bUnion_null_iff t.countable_to_set).2$
            fun _ _ =>
              by 
                rwa [measure_smul_set]

/-- If measure `μ` is invariant under an additive group action and is nonzero on a compact set `K`,
then it is positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0`
instead of `μ K ≠ 0`, see `measure_theory.measure_is_open_pos_of_vadd_invariant_of_ne_zero`. -/
add_decl_doc measure_is_open_pos_of_vadd_invariant_of_compact_ne_zero

@[toAdditive]
theorem is_locally_finite_measure_of_smul_invariant (hU : IsOpen U) (hne : U.nonempty) (hμU : μ U ≠ ∞) :
  is_locally_finite_measure μ :=
  ⟨fun x =>
      let ⟨g, hg⟩ := hU.exists_smul_mem G x hne
      ⟨(· • ·) g ⁻¹' U, (hU.preimage (continuous_id.const_smul _)).mem_nhds hg,
        Ne.lt_top$
          by 
            rwa [measure_preimage_smul]⟩⟩

variable [measure.regular μ]

@[toAdditive]
theorem measure_is_open_pos_of_smul_invariant_of_ne_zero (hμ : μ ≠ 0) (hU : IsOpen U) (hne : U.nonempty) : 0 < μ U :=
  let ⟨K, hK, hμK⟩ := regular.exists_compact_not_null.mpr hμ 
  measure_is_open_pos_of_smul_invariant_of_compact_ne_zero G hK hμK hU hne

@[toAdditive]
theorem measure_pos_iff_nonempty_of_smul_invariant (hμ : μ ≠ 0) (hU : IsOpen U) : 0 < μ U ↔ U.nonempty :=
  ⟨fun h => nonempty_of_measure_ne_zero h.ne', measure_is_open_pos_of_smul_invariant_of_ne_zero G hμ hU⟩

include G

@[toAdditive]
theorem measure_eq_zero_iff_eq_empty_of_smul_invariant (hμ : μ ≠ 0) (hU : IsOpen U) : μ U = 0 ↔ U = ∅ :=
  by 
    rw [←not_iff_not, ←Ne.def, ←pos_iff_ne_zero, measure_pos_iff_nonempty_of_smul_invariant G hμ hU,
      ←ne_empty_iff_nonempty]

end IsMinimal

end MeasureTheory

