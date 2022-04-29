/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.MeasureTheory.Measure.Regular
import Mathbin.MeasureTheory.Group.MeasurableEquiv
import Mathbin.MeasureTheory.Measure.OpenPos

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: measures that are left or right invariant w.r.t. multiplication.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
* We define a class `is_haar_measure μ`, requiring that the measure `μ` is left-invariant, finite
  on compact sets, and positive on open sets.

We also give analogues of all these notions in the additive world.
-/


noncomputable section

open Ennreal Pointwise BigOperators

open Inv Set Function MeasureTheory.Measure

variable {G : Type _} [MeasurableSpace G]

namespace MeasureTheory

namespace Measureₓ

/-- A measure `μ` on a measurable additive group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself. -/
class IsAddLeftInvariant [Add G] (μ : Measure G) : Prop where
  map_add_left_eq_self : ∀ g : G, map ((· + ·) g) μ = μ

/-- A measure `μ` on a measurable group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself. -/
@[to_additive]
class IsMulLeftInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_left_eq_self : ∀ g : G, map ((· * ·) g) μ = μ

/-- A measure `μ` on a measurable additive group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself. -/
class IsAddRightInvariant [Add G] (μ : Measure G) : Prop where
  map_add_right_eq_self : ∀ g : G, map (· + g) μ = μ

/-- A measure `μ` on a measurable group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself. -/
@[to_additive]
class IsMulRightInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_right_eq_self : ∀ g : G, map (· * g) μ = μ

end Measureₓ

open Measureₓ

section Mul

variable [Mul G] {μ : Measure G}

@[to_additive]
theorem map_mul_left_eq_self (μ : Measure G) [IsMulLeftInvariant μ] (g : G) : map ((· * ·) g) μ = μ :=
  IsMulLeftInvariant.map_mul_left_eq_self g

@[to_additive]
theorem map_mul_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ :=
  IsMulRightInvariant.map_mul_right_eq_self g

/-- An alternative way to prove that `μ` is left invariant under multiplication. -/
@[to_additive "An alternative way to prove that `μ` is left invariant under addition."]
theorem forall_measure_preimage_mul_iff [HasMeasurableMul G] (μ : Measure G) :
    (∀ g : G A : Set G, MeasurableSet A → μ ((fun h => g * h) ⁻¹' A) = μ A) ↔ IsMulLeftInvariant μ := by
  trans ∀ g, map ((· * ·) g) μ = μ
  · simp_rw [measure.ext_iff]
    refine' forall_congrₓ fun g => forall_congrₓ fun A => forall_congrₓ fun hA => _
    rw [map_apply (measurable_const_mul g) hA]
    
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

/-- An alternative way to prove that `μ` is left invariant under multiplication. -/
@[to_additive "An alternative way to prove that `μ` is left invariant under addition."]
theorem forall_measure_preimage_mul_right_iff [HasMeasurableMul G] (μ : Measure G) :
    (∀ g : G A : Set G, MeasurableSet A → μ ((fun h => h * g) ⁻¹' A) = μ A) ↔ IsMulRightInvariant μ := by
  trans ∀ g, map (· * g) μ = μ
  · simp_rw [measure.ext_iff]
    refine' forall_congrₓ fun g => forall_congrₓ fun A => forall_congrₓ fun hA => _
    rw [map_apply (measurable_mul_const g) hA]
    
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[to_additive]
instance [IsMulLeftInvariant μ] (c : ℝ≥0∞) : IsMulLeftInvariant (c • μ) :=
  ⟨fun g => by
    rw [map_smul, map_mul_left_eq_self]⟩

@[to_additive]
instance [IsMulRightInvariant μ] (c : ℝ≥0∞) : IsMulRightInvariant (c • μ) :=
  ⟨fun g => by
    rw [map_smul, map_mul_right_eq_self]⟩

end Mul

section Groupₓ

variable [Groupₓ G]

@[to_additive]
theorem map_div_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) : map (· / g) μ = μ := by
  simp_rw [div_eq_mul_inv, map_mul_right_eq_self μ g⁻¹]

variable [HasMeasurableMul G]

/-- We shorten this from `measure_preimage_mul_left`, since left invariant is the preferred option
  for measures in this formalization. -/
@[simp,
  to_additive
      "We shorten this from `measure_preimage_add_left`, since left invariant is the\npreferred option for measures in this formalization."]
theorem measure_preimage_mul (μ : Measure G) [IsMulLeftInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => g * h) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => g * h) ⁻¹' A) = map (fun h => g * h) μ A := ((MeasurableEquiv.mulLeft g).map_apply A).symm
    _ = μ A := by
      rw [map_mul_left_eq_self μ g]
    

@[simp, to_additive]
theorem measure_preimage_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => h * g) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => h * g) ⁻¹' A) = map (fun h => h * g) μ A := ((MeasurableEquiv.mulRight g).map_apply A).symm
    _ = μ A := by
      rw [map_mul_right_eq_self μ g]
    

end Groupₓ

namespace Measureₓ

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive "The measure `A ↦ μ (- A)`, where `- A` is the pointwise negation of `A`."]
protected def inv [Inv G] (μ : Measure G) : Measure G :=
  Measure.map inv μ

/-- A measure is invariant under negation if `- μ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (- A) = μ A`, where `- A` is the pointwise negation of `A`. -/
class IsNegInvariant [Neg G] (μ : Measure G) : Prop where
  neg_eq_self : μ.neg = μ

/-- A measure is invariant under inversion if `μ⁻¹ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (A⁻¹) = μ A`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive]
class IsInvInvariant [Inv G] (μ : Measure G) : Prop where
  inv_eq_self : μ.inv = μ

section Inv

variable [Inv G]

@[simp, to_additive]
theorem inv_eq_self (μ : Measure G) [IsInvInvariant μ] : μ.inv = μ :=
  is_inv_invariant.inv_eq_self

@[simp, to_additive]
theorem map_inv_eq_self (μ : Measure G) [IsInvInvariant μ] : map Inv.inv μ = μ :=
  is_inv_invariant.inv_eq_self

end Inv

section HasInvolutiveInv

variable [HasInvolutiveInv G] [HasMeasurableInv G]

@[simp, to_additive]
theorem inv_apply (μ : Measure G) (s : Set G) : μ.inv s = μ s⁻¹ :=
  (MeasurableEquiv.inv G).map_apply s

@[simp, to_additive]
protected theorem inv_inv (μ : Measure G) : μ.inv.inv = μ :=
  (MeasurableEquiv.inv G).map_symm_map

@[simp, to_additive]
theorem measure_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) : μ A⁻¹ = μ A := by
  rw [← inv_apply, inv_eq_self]

@[to_additive]
theorem measure_preimage_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) : μ (Inv.inv ⁻¹' A) = μ A :=
  μ.measure_inv A

@[to_additive]
instance (μ : Measure G) [SigmaFinite μ] : SigmaFinite μ.inv :=
  (MeasurableEquiv.inv G).sigma_finite_map ‹_›

end HasInvolutiveInv

section mul_inv

variable [Groupₓ G] [HasMeasurableMul G] [HasMeasurableInv G] {μ : Measure G}

@[to_additive]
instance [IsMulLeftInvariant μ] : IsMulRightInvariant μ.inv := by
  constructor
  intro g
  conv_rhs => rw [← map_mul_left_eq_self μ g⁻¹]
  simp_rw [measure.inv, map_map (measurable_mul_const g) measurable_inv,
    map_map measurable_inv (measurable_const_mul g⁻¹), Function.comp, mul_inv_rev, inv_invₓ]

@[to_additive]
instance [IsMulRightInvariant μ] : IsMulLeftInvariant μ.inv := by
  constructor
  intro g
  conv_rhs => rw [← map_mul_right_eq_self μ g⁻¹]
  simp_rw [measure.inv, map_map (measurable_const_mul g) measurable_inv,
    map_map measurable_inv (measurable_mul_const g⁻¹), Function.comp, mul_inv_rev, inv_invₓ]

@[to_additive]
theorem map_div_left_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    map (fun t => g / t) μ = μ := by
  simp_rw [div_eq_mul_inv]
  conv_rhs => rw [← map_mul_left_eq_self μ g, ← map_inv_eq_self μ]
  exact (map_map (measurable_const_mul g) measurable_inv).symm

@[to_additive]
theorem map_mul_right_inv_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    map (fun t => (g * t)⁻¹) μ = μ := by
  conv_rhs => rw [← map_inv_eq_self μ, ← map_mul_left_eq_self μ g]
  exact (map_map measurable_inv (measurable_const_mul g)).symm

end mul_inv

end Measureₓ

section TopologicalGroup

variable [TopologicalSpace G] [BorelSpace G] {μ : Measure G}

variable [Groupₓ G] [TopologicalGroup G]

@[to_additive]
instance Measure.Regular.inv [T2Space G] [Regular μ] : Regular μ.inv :=
  Regular.map (Homeomorph.inv G)

@[to_additive]
theorem regular_inv_iff [T2Space G] : μ.inv.regular ↔ μ.regular := by
  constructor
  · intro h
    rw [← μ.inv_inv]
    exact measure.regular.inv
    
  · intro h
    exact measure.regular.inv
    

variable [IsMulLeftInvariant μ]

/-- If a left-invariant measure gives positive mass to a compact set, then it gives positive mass to
any open set. -/
@[to_additive
      "If a left-invariant measure gives positive mass to a compact set, then it gives\npositive mass to any open set."]
theorem is_open_pos_measure_of_mul_left_invariant_of_compact (K : Set G) (hK : IsCompact K) (h : μ K ≠ 0) :
    IsOpenPosMeasure μ := by
  refine' ⟨fun U hU hne => _⟩
  contrapose! h
  rw [← nonpos_iff_eq_zero]
  rw [← hU.interior_eq] at hne
  obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃ (g : G) (H : g ∈ t), (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK hne
  calc μ K ≤ μ (⋃ (g : G) (H : g ∈ t), (fun h : G => g * h) ⁻¹' U) :=
      measure_mono hKt _ ≤ ∑ g in t, μ ((fun h : G => g * h) ⁻¹' U) := measure_bUnion_finset_le _ _ _ = 0 := by
      simp [measure_preimage_mul, h]

/-- A nonzero left-invariant regular measure gives positive mass to any open set. -/
@[to_additive "A nonzero left-invariant regular measure gives positive mass to any open set."]
theorem is_open_pos_measure_of_mul_left_invariant_of_regular [Regular μ] (h₀ : μ ≠ 0) : IsOpenPosMeasure μ :=
  let ⟨K, hK, h2K⟩ := Regular.exists_compact_not_null.mpr h₀
  is_open_pos_measure_of_mul_left_invariant_of_compact K hK h2K

@[to_additive]
theorem null_iff_of_is_mul_left_invariant [Regular μ] {s : Set G} (hs : IsOpen s) : μ s = 0 ↔ s = ∅ ∨ μ = 0 := by
  by_cases' h3μ : μ = 0
  · simp [h3μ]
    
  · have := is_open_pos_measure_of_mul_left_invariant_of_regular h3μ
    simp only [h3μ, or_falseₓ, hs.measure_eq_zero_iff μ]
    

@[to_additive]
theorem measure_ne_zero_iff_nonempty_of_is_mul_left_invariant [Regular μ] (hμ : μ ≠ 0) {s : Set G} (hs : IsOpen s) :
    μ s ≠ 0 ↔ s.Nonempty := by
  simpa [null_iff_of_is_mul_left_invariant hs, hμ] using ne_empty_iff_nonempty

@[to_additive]
theorem measure_pos_iff_nonempty_of_is_mul_left_invariant [Regular μ] (h3μ : μ ≠ 0) {s : Set G} (hs : IsOpen s) :
    0 < μ s ↔ s.Nonempty :=
  pos_iff_ne_zero.trans <| measure_ne_zero_iff_nonempty_of_is_mul_left_invariant h3μ hs

/-- If a left-invariant measure gives finite mass to a nonempty open set, then it gives finite mass
to any compact set. -/
@[to_additive
      "If a left-invariant measure gives finite mass to a nonempty open set, then it gives\nfinite mass to any compact set."]
theorem measure_lt_top_of_is_compact_of_is_mul_left_invariant (U : Set G) (hU : IsOpen U) (h'U : U.Nonempty)
    (h : μ U ≠ ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ := by
  rw [← hU.interior_eq] at h'U
  obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃ (g : G) (H : g ∈ t), (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U
  calc μ K ≤ μ (⋃ (g : G) (H : g ∈ t), (fun h : G => g * h) ⁻¹' U) :=
      measure_mono hKt _ ≤ ∑ g in t, μ ((fun h : G => g * h) ⁻¹' U) :=
      measure_bUnion_finset_le _ _ _ = Finset.card t * μ U := by
      simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]_ < ∞ :=
      Ennreal.mul_lt_top Ennreal.coe_nat_ne_top h

/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then
it gives finite mass to any compact set. -/
@[to_additive
      "If a left-invariant measure gives finite mass to a set with nonempty interior, then\nit gives finite mass to any compact set."]
theorem measure_lt_top_of_is_compact_of_is_mul_left_invariant' {U : Set G} (hU : (Interior U).Nonempty) (h : μ U ≠ ∞)
    {K : Set G} (hK : IsCompact K) : μ K < ∞ :=
  measure_lt_top_of_is_compact_of_is_mul_left_invariant (Interior U) is_open_interior hU
    ((measure_mono interior_subset).trans_lt (lt_top_iff_ne_top.2 h)).Ne hK

end TopologicalGroup

section CommGroupₓ

variable [CommGroupₓ G]

/-- In an abelian group every left invariant measure is also right-invariant.
  We don't declare the converse as an instance, since that would loop type-class inference, and
  we use `is_mul_left_invariant` as default hypotheses in abelian groups. -/
@[to_additive
      "In an abelian additive group every left invariant measure is also\nright-invariant. We don't declare the converse as an instance, since that would loop type-class\ninference, and we use `is_add_left_invariant` as default hypotheses in abelian groups."]
instance (priority := 100) IsMulLeftInvariant.is_mul_right_invariant {μ : Measure G} [IsMulLeftInvariant μ] :
    IsMulRightInvariant μ :=
  ⟨fun g => by
    simp_rw [mul_comm, map_mul_left_eq_self]⟩

end CommGroupₓ

section Haar

namespace Measureₓ

/-- A measure on an additive group is an additive Haar measure if it is left-invariant, and gives
finite mass to compact sets and positive mass to open sets. -/
class IsAddHaarMeasure {G : Type _} [AddGroupₓ G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) extends
  IsFiniteMeasureOnCompacts μ, IsAddLeftInvariant μ, IsOpenPosMeasure μ : Prop

/-- A measure on a group is a Haar measure if it is left-invariant, and gives finite mass to compact
sets and positive mass to open sets. -/
@[to_additive]
class IsHaarMeasure {G : Type _} [Groupₓ G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) extends
  IsFiniteMeasureOnCompacts μ, IsMulLeftInvariant μ, IsOpenPosMeasure μ : Prop

/-- Record that a Haar measure on a locally compact space is locally finite. This is needed as the
fact that a measure which is finite on compacts is locally finite is not registered as an instance,
to avoid an instance loop.

See Note [lower instance priority]. -/
@[to_additive
      "Record that an additive Haar measure on a locally compact space is\nlocally finite. This is needed as the fact that a measure which is finite on compacts is locally\nfinite is not registered as an instance, to avoid an instance loop.\n\nSee Note [lower instance priority]"]
instance (priority := 100) is_locally_finite_measure_of_is_haar_measure {G : Type _} [Groupₓ G] [MeasurableSpace G]
    [TopologicalSpace G] [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] : IsLocallyFiniteMeasure μ :=
  is_locally_finite_measure_of_is_finite_measure_on_compacts

section

variable [Groupₓ G] [TopologicalSpace G] (μ : Measure G) [IsHaarMeasure μ]

@[simp, to_additive]
theorem haar_singleton [TopologicalGroup G] [BorelSpace G] (g : G) : μ {g} = μ {(1 : G)} := by
  convert measure_preimage_mul μ g⁻¹ _
  simp only [mul_oneₓ, preimage_mul_left_singleton, inv_invₓ]

@[to_additive MeasureTheory.Measure.IsAddHaarMeasure.smul]
theorem IsHaarMeasure.smul {c : ℝ≥0∞} (cpos : c ≠ 0) (ctop : c ≠ ∞) : IsHaarMeasure (c • μ) :=
  { lt_top_of_is_compact := fun K hK => Ennreal.mul_lt_top ctop hK.measure_lt_top.Ne,
    to_is_open_pos_measure := is_open_pos_measure_smul μ cpos }

/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is a Haar measure. -/
@[to_additive
      "If a left-invariant measure gives positive mass to some compact set with nonempty\ninterior, then it is an additive Haar measure."]
theorem is_haar_measure_of_is_compact_nonempty_interior [TopologicalGroup G] [BorelSpace G] (μ : Measure G)
    [IsMulLeftInvariant μ] (K : Set G) (hK : IsCompact K) (h'K : (Interior K).Nonempty) (h : μ K ≠ 0) (h' : μ K ≠ ∞) :
    IsHaarMeasure μ :=
  { lt_top_of_is_compact := fun L hL => measure_lt_top_of_is_compact_of_is_mul_left_invariant' h'K h' hL,
    to_is_open_pos_measure := is_open_pos_measure_of_mul_left_invariant_of_compact K hK h }

/-- The image of a Haar measure under a group homomorphism which is also a homeomorphism is again
a Haar measure. -/
@[to_additive
      "The image of an additive Haar measure under an additive group homomorphism which is\nalso a homeomorphism is again an additive Haar measure."]
theorem is_haar_measure_map [BorelSpace G] [TopologicalGroup G] {H : Type _} [Groupₓ H] [TopologicalSpace H]
    [MeasurableSpace H] [BorelSpace H] [T2Space H] [TopologicalGroup H] (f : G ≃* H) (hf : Continuous f)
    (hfsymm : Continuous f.symm) : IsHaarMeasure (Measure.map f μ) :=
  { to_is_mul_left_invariant := by
      constructor
      intro h
      rw [map_map (continuous_mul_left h).Measurable hf.measurable]
      conv_rhs => rw [← map_mul_left_eq_self μ (f.symm h)]
      rw [map_map hf.measurable (continuous_mul_left _).Measurable]
      congr 2
      ext y
      simp only [MulEquiv.apply_symm_apply, comp_app, MulEquiv.map_mul],
    lt_top_of_is_compact := by
      intro K hK
      rw [map_apply hf.measurable hK.measurable_set]
      have : f.symm '' K = f ⁻¹' K := Equivₓ.image_eq_preimage _ _
      rw [← this]
      exact IsCompact.measure_lt_top (hK.image hfsymm),
    to_is_open_pos_measure := hf.is_open_pos_measure_map f.Surjective }

/-- A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority] -/
@[to_additive "A Haar measure on a σ-compact space is σ-finite.\n\nSee Note [lower instance priority]"]
instance (priority := 100) IsHaarMeasure.sigma_finite [SigmaCompactSpace G] : SigmaFinite μ :=
  ⟨⟨{ Set := CompactCovering G, set_mem := fun n => mem_univ _,
        Finite := fun n => IsCompact.measure_lt_top <| is_compact_compact_covering G n,
        spanning := Union_compact_covering G }⟩⟩

open TopologicalSpace

open Filter

/-- If the neutral element of a group is not isolated, then a Haar measure on this group has
no atoms.

The additive version of this instance applies in particular to show that an additive Haar measure on
a nontrivial finite-dimensional real vector space has no atom. -/
@[to_additive
      "If the zero element of an additive group is not isolated, then an\nadditive Haar measure on this group has no atoms.\n\nThis applies in particular to show that an additive Haar measure on a nontrivial finite-dimensional\nreal vector space has no atom."]
instance (priority := 100) IsHaarMeasure.has_no_atoms [TopologicalGroup G] [BorelSpace G] [T1Space G]
    [LocallyCompactSpace G] [(𝓝[≠] (1 : G)).ne_bot] (μ : Measure G) [μ.IsHaarMeasure] : HasNoAtoms μ := by
  suffices H : μ {(1 : G)} ≤ 0
  · constructor
    simp [le_bot_iff.1 H]
    
  obtain ⟨K, K_compact, K_int⟩ : ∃ K : Set G, IsCompact K ∧ (1 : G) ∈ Interior K := by
    rcases exists_compact_subset is_open_univ (mem_univ (1 : G)) with ⟨K, hK⟩
    exact ⟨K, hK.1, hK.2.1⟩
  have K_inf : Set.Infinite K := infinite_of_mem_nhds (1 : G) (mem_interior_iff_mem_nhds.1 K_int)
  have μKlt : μ K ≠ ∞ := K_compact.measure_lt_top.ne
  have I : ∀ n : ℕ, μ {(1 : G)} ≤ μ K / n := by
    intro n
    obtain ⟨t, tK, tn⟩ : ∃ t : Finset G, ↑t ⊆ K ∧ t.card = n := K_inf.exists_subset_card_eq n
    have A : μ t ≤ μ K := measure_mono tK
    have B : μ t = n * μ {(1 : G)} := by
      rw [← bUnion_of_singleton ↑t]
      change μ (⋃ x ∈ t, {x}) = n * μ {1}
      rw [@measure_bUnion_finset G G _ μ t fun i => {i}]
      · simp only [tn, Finset.sum_const, nsmul_eq_mul, haar_singleton]
        
      · intro x hx y hy xy
        simp only [on_fun, xy.symm, mem_singleton_iff, not_false_iff, disjoint_singleton_right]
        
      · intro b hb
        exact measurable_set_singleton b
        
    rw [B] at A
    rwa [Ennreal.le_div_iff_mul_le _ (Or.inr μKlt), mul_comm]
    right
    apply (measure_pos_of_nonempty_interior μ ⟨_, K_int⟩).ne'
  have J : tendsto (fun n : ℕ => μ K / n) at_top (𝓝 (μ K / ∞)) :=
    Ennreal.Tendsto.const_div Ennreal.tendsto_nat_nhds_top (Or.inr μKlt)
  simp only [Ennreal.div_top] at J
  exact ge_of_tendsto' J I

/- The above instance applies in particular to show that an additive Haar measure on a nontrivial
finite-dimensional real vector space has no atom. -/
example {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] : HasNoAtoms μ := by
  infer_instance

end

end Measureₓ

end Haar

end MeasureTheory

