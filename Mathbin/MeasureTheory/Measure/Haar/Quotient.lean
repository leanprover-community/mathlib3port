/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import MeasureTheory.Measure.Haar.Basic
import MeasureTheory.Group.FundamentalDomain
import Algebra.Group.Opposite

#align_import measure_theory.measure.haar.quotient from "leanprover-community/mathlib"@"3b52265189f3fb43aa631edffce5d060fafaf82f"

/-!
# Haar quotient measure

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup of a group `G` on `G` itself.

## Main results

* `measure_theory.is_fundamental_domain.smul_invariant_measure_map `: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both
  left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure
  on `G ⧸ Γ`.

* `measure_theory.is_fundamental_domain.is_mul_left_invariant_map `: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a left-invariant
  measure on `G ⧸ Γ`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/


noncomputable section

open Set MeasureTheory TopologicalSpace MeasureTheory.Measure QuotientGroup

open scoped Pointwise MeasureTheory Topology BigOperators NNReal ENNReal

variable {G : Type _} [Group G] [MeasurableSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {μ : Measure G} {Γ : Subgroup G}

#print QuotientGroup.measurableSMul /-
/-- Measurability of the action of the topological group `G` on the left-coset space `G/Γ`. -/
@[to_additive
      "Measurability of the action of the additive topological group `G` on the left-coset\n  space `G/Γ`."]
instance QuotientGroup.measurableSMul [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] :
    MeasurableSMul G (G ⧸ Γ)
    where
  measurable_const_smul g := (continuous_const_smul g).Measurable
  measurable_smul_const x := (QuotientGroup.continuous_smul₁ x).Measurable
#align quotient_group.has_measurable_smul QuotientGroup.measurableSMul
#align quotient_add_group.has_measurable_vadd QuotientAddGroup.measurableVAdd
-/

variable {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ.opEquiv 𝓕 μ)

variable [Countable Γ] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

#print MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map /-
/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. -/
@[to_additive
      "The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and\n  right-invariant measure on an additive topological group `G` to a fundamental domain `𝓕` is a\n  `G`-invariant measure on `G ⧸ Γ`."]
theorem MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] :
    SMulInvariantMeasure G (G ⧸ Γ) (Measure.map QuotientGroup.mk (μ.restrict 𝓕)) :=
  {
    measure_preimage_smul := by
      let π : G → G ⧸ Γ := QuotientGroup.mk
      have meas_π : Measurable π := continuous_quotient_mk.measurable
      have 𝓕meas : null_measurable_set 𝓕 μ := h𝓕.null_measurable_set
      intro g A hA
      have meas_πA : MeasurableSet (π ⁻¹' A) := measurableSet_preimage meas_π hA
      rw [measure.map_apply meas_π hA,
        measure.map_apply meas_π (measurableSet_preimage (measurable_const_smul g) hA),
        measure.restrict_apply₀' 𝓕meas, measure.restrict_apply₀' 𝓕meas]
      set π_preA := π ⁻¹' A
      have : QuotientGroup.mk ⁻¹' ((fun x : G ⧸ Γ => g • x) ⁻¹' A) = Mul.mul g ⁻¹' π_preA := by
        ext1; simp
      rw [this]
      have : μ (Mul.mul g ⁻¹' π_preA ∩ 𝓕) = μ (π_preA ∩ Mul.mul g⁻¹ ⁻¹' 𝓕) :=
        by
        trans μ (Mul.mul g ⁻¹' (π_preA ∩ Mul.mul g⁻¹ ⁻¹' 𝓕))
        · rw [preimage_inter]
          congr
          rw [← preimage_comp, comp_mul_left, mul_left_inv]
          ext
          simp
        rw [measure_preimage_mul]
      rw [this]
      have h𝓕_translate_fundom : is_fundamental_domain Γ.opposite (g • 𝓕) μ := h𝓕.smul_of_comm g
      rw [h𝓕.measure_set_eq h𝓕_translate_fundom meas_πA, ← preimage_smul_inv]; rfl
      rintro ⟨γ, γ_in_Γ⟩
      ext
      have : π (x * MulOpposite.unop γ) = π x := by simpa [QuotientGroup.eq'] using γ_in_Γ
      simp [(· • ·), this] }
#align measure_theory.is_fundamental_domain.smul_invariant_measure_map MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map
#align measure_theory.is_add_fundamental_domain.vadd_invariant_measure_map MeasureTheory.IsAddFundamentalDomain.vaddInvariantMeasure_map
-/

#print MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map /-
/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
@[to_additive
      "Assuming `Γ` is a normal subgroup of an additive topological group `G`, the\n  pushforward to the quotient group `G ⧸ Γ` of the restriction of a both left- and right-invariant\n  measure on `G` to a fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`."]
theorem MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map [Subgroup.Normal Γ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] :
    (Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕)).IsMulLeftInvariant :=
  {
    map_mul_left_eq_self := by
      intro x
      apply measure.ext
      intro A hA
      obtain ⟨x₁, _⟩ := @Quotient.exists_rep _ (QuotientGroup.leftRel Γ) x
      haveI := h𝓕.smul_invariant_measure_map
      convert measure_preimage_smul x₁ ((measure.map QuotientGroup.mk) (μ.restrict 𝓕)) A using 1
      rw [← h, measure.map_apply]
      · rfl
      · exact measurable_const_mul _
      · exact hA }
#align measure_theory.is_fundamental_domain.is_mul_left_invariant_map MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map
#align measure_theory.is_add_fundamental_domain.is_add_left_invariant_map MeasureTheory.IsAddFundamentalDomain.isAddLeftInvariant_map
-/

#print MeasureTheory.IsFundamentalDomain.map_restrict_quotient /-
/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on `G ⧸ Γ`. -/
@[to_additive
      "Given a normal subgroup `Γ` of an additive topological group `G` with Haar measure\n  `μ`, which is also right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward\n  to the quotient group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on\n  `G ⧸ Γ`."]
theorem MeasureTheory.IsFundamentalDomain.map_restrict_quotient [T2Space (G ⧸ Γ)]
    [SecondCountableTopology (G ⧸ Γ)] (K : PositiveCompacts (G ⧸ Γ)) [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure μ] [μ.IsMulRightInvariant] (h𝓕_finite : μ 𝓕 < ⊤) :
    Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕) =
      μ (𝓕 ∩ QuotientGroup.mk' Γ ⁻¹' K) • MeasureTheory.Measure.haarMeasure K :=
  by
  let π : G →* G ⧸ Γ := QuotientGroup.mk' Γ
  have meas_π : Measurable π := continuous_quotient_mk.measurable
  have 𝓕meas : null_measurable_set 𝓕 μ := h𝓕.null_measurable_set
  haveI : is_finite_measure (μ.restrict 𝓕) :=
    ⟨by rw [measure.restrict_apply₀' 𝓕meas, univ_inter]; exact h𝓕_finite⟩
  -- the measure is left-invariant, so by the uniqueness of Haar measure it's enough to show that
  -- it has the stated size on the reference compact set `K`.
  haveI : (measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕)).IsMulLeftInvariant :=
    h𝓕.is_mul_left_invariant_map
  rw [measure.haar_measure_unique (measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕)) K,
    measure.map_apply meas_π, measure.restrict_apply₀' 𝓕meas, inter_comm]
  exact K.is_compact.measurable_set
#align measure_theory.is_fundamental_domain.map_restrict_quotient MeasureTheory.IsFundamentalDomain.map_restrict_quotient
#align measure_theory.is_add_fundamental_domain.map_restrict_quotient MeasureTheory.IsAddFundamentalDomain.map_restrict_quotient
-/

#print MeasurePreservingQuotientGroup.mk' /-
/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is
  measure-preserving between appropriate multiples of Haar measure on `G` and `G ⧸ Γ`. -/
@[to_additive MeasurePreservingQuotientAddGroup.mk'
      "Given a normal subgroup `Γ` of an additive\n  topological group `G` with Haar measure `μ`, which is also right-invariant, and a finite volume\n  fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is measure-preserving between appropriate\n  multiples of Haar measure on `G` and `G ⧸ Γ`."]
theorem MeasurePreservingQuotientGroup.mk' [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)]
    (K : PositiveCompacts (G ⧸ Γ)) [Subgroup.Normal Γ] [MeasureTheory.Measure.IsHaarMeasure μ]
    [μ.IsMulRightInvariant] (h𝓕_finite : μ 𝓕 < ⊤) (c : ℝ≥0)
    (h : μ (𝓕 ∩ QuotientGroup.mk' Γ ⁻¹' K) = c) :
    MeasurePreserving (QuotientGroup.mk' Γ) (μ.restrict 𝓕)
      (c • MeasureTheory.Measure.haarMeasure K) :=
  { Measurable := continuous_quotient_mk'.Measurable
    map_eq := by rw [h𝓕.map_restrict_quotient K h𝓕_finite, h] <;> rfl }
#align measure_preserving_quotient_group.mk' MeasurePreservingQuotientGroup.mk'
#align measure_preserving_quotient_add_group.mk' MeasurePreservingQuotientAddGroup.mk'
-/

section

local notation "μ_𝓕" => Measure.map (@QuotientGroup.mk G _ Γ) (μ.restrict 𝓕)

/-- The `ess_sup` of a function `g` on the quotient space `G ⧸ Γ` with respect to the pushforward
  of the restriction, `μ_𝓕`, of a right-invariant measure `μ` to a fundamental domain `𝓕`, is the
  same as the `ess_sup` of `g`'s lift to the universal cover `G` with respect to `μ`. -/
@[to_additive
      "The `ess_sup` of a function `g` on the additive quotient space `G ⧸ Γ` with respect\n  to the pushforward of the restriction, `μ_𝓕`, of a right-invariant measure `μ` to a fundamental\n  domain `𝓕`, is the same as the `ess_sup` of `g`'s lift to the universal cover `G` with respect\n  to `μ`."]
theorem essSup_comp_quotient_group_mk [μ.IsMulRightInvariant] {g : G ⧸ Γ → ℝ≥0∞}
    (g_ae_measurable : AEMeasurable g μ_𝓕) : essSup g μ_𝓕 = essSup (fun x : G => g x) μ :=
  by
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := continuous_quotient_mk.measurable
  rw [essSup_map_measure g_ae_measurable hπ.ae_measurable]
  refine' h𝓕.ess_sup_measure_restrict _
  rintro ⟨γ, hγ⟩ x
  dsimp
  congr 1
  exact QuotientGroup.mk_mul_of_mem x hγ
#align ess_sup_comp_quotient_group_mk essSup_comp_quotient_group_mk
#align ess_sup_comp_quotient_add_group_mk ess_sup_comp_quotient_add_group_mk

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ∈ »(_, s)]] -/
#print MeasureTheory.IsFundamentalDomain.absolutelyContinuous_map /-
/-- Given a quotient space `G ⧸ Γ` where `Γ` is `countable`, and the restriction,
  `μ_𝓕`, of a right-invariant measure `μ` on `G` to a fundamental domain `𝓕`, a set
  in the quotient which has `μ_𝓕`-measure zero, also has measure zero under the
  folding of `μ` under the quotient. Note that, if `Γ` is infinite, then the folded map
  will take the value `∞` on any open set in the quotient! -/
@[to_additive
      "Given an additive quotient space `G ⧸ Γ` where `Γ` is `countable`, and the\n  restriction, `μ_𝓕`, of a right-invariant measure `μ` on `G` to a fundamental domain `𝓕`, a set\n  in the quotient which has `μ_𝓕`-measure zero, also has measure zero under the\n  folding of `μ` under the quotient. Note that, if `Γ` is infinite, then the folded map\n  will take the value `∞` on any open set in the quotient!"]
theorem MeasureTheory.IsFundamentalDomain.absolutelyContinuous_map [μ.IsMulRightInvariant] :
    map (QuotientGroup.mk : G → G ⧸ Γ) μ ≪ map (QuotientGroup.mk : G → G ⧸ Γ) (μ.restrict 𝓕) :=
  by
  set π : G → G ⧸ Γ := QuotientGroup.mk
  have meas_π : Measurable π := continuous_quotient_mk.measurable
  apply absolutely_continuous.mk
  intro s s_meas hs
  rw [map_apply meas_π s_meas] at hs ⊢
  rw [measure.restrict_apply] at hs
  apply h𝓕.measure_zero_of_invariant _ _ hs
  · intro γ
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, mem_preimage, mem_preimage]
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ∈ »(_, s)]]"
    convert QuotientGroup.mk_mul_of_mem g γ⁻¹.2
  exact measurableSet_preimage meas_π s_meas
#align measure_theory.is_fundamental_domain.absolutely_continuous_map MeasureTheory.IsFundamentalDomain.absolutelyContinuous_map
#align measure_theory.is_add_fundamental_domain.absolutely_continuous_map MeasureTheory.IsAddFundamentalDomain.absolutelyContinuous_map
-/

attribute [-instance] Quotient.instMeasurableSpace

#print QuotientGroup.integral_eq_integral_automorphize /-
/-- This is a simple version of the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the
  integral of a function `f` on `G` with respect to a right-invariant measure `μ` is equal to the
  integral over the quotient `G ⧸ Γ` of the automorphization of `f`. -/
@[to_additive
      "This is a simple version of the **Unfolding Trick**: Given a subgroup `Γ` of an\n  additive  group `G`, the integral of a function `f` on `G` with respect to a right-invariant\n  measure `μ` is equal to the integral over the quotient `G ⧸ Γ` of the automorphization of `f`."]
theorem QuotientGroup.integral_eq_integral_automorphize {E : Type _} [NormedAddCommGroup E]
    [CompleteSpace E] [NormedSpace ℝ E] [μ.IsMulRightInvariant] {f : G → E} (hf₁ : Integrable f μ)
    (hf₂ : AEStronglyMeasurable (automorphize f) μ_𝓕) :
    ∫ x : G, f x ∂μ = ∫ x : G ⧸ Γ, automorphize f x ∂μ_𝓕 :=
  calc
    ∫ x : G, f x ∂μ = ∑' γ : Γ.opEquiv, ∫ x in 𝓕, f (γ • x) ∂μ := h𝓕.integral_eq_tsum'' f hf₁
    _ = ∫ x in 𝓕, ∑' γ : Γ.opEquiv, f (γ • x) ∂μ :=
      by
      rw [integral_tsum]
      ·
        exact fun i =>
          (hf₁.1.comp_quasiMeasurePreserving
              (measure_preserving_smul i μ).QuasiMeasurePreserving).restrict
      · rw [← h𝓕.lintegral_eq_tsum'' fun x => ‖f x‖₊]
        exact ne_of_lt hf₁.2
    _ = ∫ x : G ⧸ Γ, automorphize f x ∂μ_𝓕 :=
      (integral_map continuous_quotient_mk'.AEMeasurable hf₂).symm
#align quotient_group.integral_eq_integral_automorphize QuotientGroup.integral_eq_integral_automorphize
-/

/-- This is the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the integral of a
  function `f` on `G` times the lift to `G` of a function `g` on the quotient `G ⧸ Γ` with respect
  to a right-invariant measure `μ` on `G`, is equal to the integral over the quotient of the
  automorphization of `f` times `g`. -/
theorem QuotientGroup.integral_hMul_eq_integral_automorphize_hMul {K : Type _} [NormedField K]
    [CompleteSpace K] [NormedSpace ℝ K] [μ.IsMulRightInvariant] {f : G → K} (f_ℒ_1 : Integrable f μ)
    {g : G ⧸ Γ → K} (hg : AEStronglyMeasurable g μ_𝓕)
    (g_ℒ_infinity : essSup (fun x => ↑‖g x‖₊) μ_𝓕 ≠ ∞)
    (F_ae_measurable : AEStronglyMeasurable (QuotientGroup.automorphize f) μ_𝓕) :
    ∫ x : G, g (x : G ⧸ Γ) * f x ∂μ = ∫ x : G ⧸ Γ, g x * QuotientGroup.automorphize f x ∂μ_𝓕 :=
  by
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have H₀ : QuotientGroup.automorphize (g ∘ π * f) = g * QuotientGroup.automorphize f :=
    QuotientGroup.automorphize_smul_left f g
  calc
    ∫ x : G, g (π x) * f x ∂μ = ∫ x : G ⧸ Γ, QuotientGroup.automorphize (g ∘ π * f) x ∂μ_𝓕 := _
    _ = ∫ x : G ⧸ Γ, g x * QuotientGroup.automorphize f x ∂μ_𝓕 := by simp [H₀]
  have meas_π : Measurable π := continuous_quotient_mk.measurable
  have H₁ : integrable (g ∘ π * f) μ :=
    by
    have : ae_strongly_measurable (fun x : G => g (x : G ⧸ Γ)) μ :=
      by
      refine' (ae_strongly_measurable_of_absolutely_continuous _ _ hg).comp_measurable meas_π
      exact h𝓕.absolutely_continuous_map
    refine' integrable.ess_sup_smul f_ℒ_1 this _
    · have hg' : ae_strongly_measurable (fun x => ↑‖g x‖₊) μ_𝓕 :=
        (ennreal.continuous_coe.comp continuous_nnnorm).comp_aestronglyMeasurable hg
      rw [← essSup_comp_quotient_group_mk h𝓕 hg'.ae_measurable]
      exact g_ℒ_infinity
  have H₂ : ae_strongly_measurable (QuotientGroup.automorphize (g ∘ π * f)) μ_𝓕 :=
    by
    simp_rw [H₀]
    exact hg.mul F_ae_measurable
  apply QuotientGroup.integral_eq_integral_automorphize h𝓕 H₁ H₂
#align quotient_group.integral_mul_eq_integral_automorphize_mul QuotientGroup.integral_hMul_eq_integral_automorphize_hMul

end

section

variable {G' : Type _} [AddGroup G'] [MeasurableSpace G'] [TopologicalSpace G']
  [TopologicalAddGroup G'] [BorelSpace G'] {μ' : Measure G'} {Γ' : AddSubgroup G'} [Countable Γ']
  [MeasurableSpace (G' ⧸ Γ')] [BorelSpace (G' ⧸ Γ')] {𝓕' : Set G'}

local notation "μ_𝓕" => Measure.map (@QuotientAddGroup.mk G' _ Γ') (μ'.restrict 𝓕')

/-- This is the **Unfolding Trick**: Given an additive subgroup `Γ'` of an additive group `G'`, the
  integral of a function `f` on `G'` times the lift to `G'` of a function `g` on the quotient
  `G' ⧸ Γ'` with respect to a right-invariant measure `μ` on `G'`, is equal to the integral over
  the quotient of the automorphization of `f` times `g`. -/
theorem quotientAddGroup.integral_hMul_eq_integral_automorphize_hMul {K : Type _} [NormedField K]
    [CompleteSpace K] [NormedSpace ℝ K] [μ'.IsAddRightInvariant] {f : G' → K}
    (f_ℒ_1 : Integrable f μ') {g : G' ⧸ Γ' → K} (hg : AEStronglyMeasurable g μ_𝓕)
    (g_ℒ_infinity : essSup (fun x => ↑‖g x‖₊) μ_𝓕 ≠ ∞)
    (F_ae_measurable : AEStronglyMeasurable (quotientAddGroup.automorphize f) μ_𝓕)
    (h𝓕 : IsAddFundamentalDomain Γ'.opEquiv 𝓕' μ') :
    ∫ x : G', g (x : G' ⧸ Γ') * f x ∂μ' =
      ∫ x : G' ⧸ Γ', g x * quotientAddGroup.automorphize f x ∂μ_𝓕 :=
  by
  let π : G' → G' ⧸ Γ' := QuotientAddGroup.mk
  have H₀ : quotientAddGroup.automorphize (g ∘ π * f) = g * quotientAddGroup.automorphize f :=
    quotientAddGroup.automorphize_smul_left f g
  calc
    ∫ x : G', g (π x) * f x ∂μ' = ∫ x : G' ⧸ Γ', quotientAddGroup.automorphize (g ∘ π * f) x ∂μ_𝓕 :=
      _
    _ = ∫ x : G' ⧸ Γ', g x * quotientAddGroup.automorphize f x ∂μ_𝓕 := by simp [H₀]
  have meas_π : Measurable π := continuous_quotient_mk.measurable
  have H₁ : integrable (g ∘ π * f) μ' :=
    by
    have : ae_strongly_measurable (fun x : G' => g (x : G' ⧸ Γ')) μ' :=
      by
      refine' (ae_strongly_measurable_of_absolutely_continuous _ _ hg).comp_measurable meas_π
      exact h𝓕.absolutely_continuous_map
    refine' integrable.ess_sup_smul f_ℒ_1 this _
    · have hg' : ae_strongly_measurable (fun x => ↑‖g x‖₊) μ_𝓕 :=
        (ennreal.continuous_coe.comp continuous_nnnorm).comp_aestronglyMeasurable hg
      rw [← ess_sup_comp_quotient_add_group_mk h𝓕 hg'.ae_measurable]
      exact g_ℒ_infinity
  have H₂ : ae_strongly_measurable (quotientAddGroup.automorphize (g ∘ π * f)) μ_𝓕 :=
    by
    simp_rw [H₀]
    exact hg.mul F_ae_measurable
  apply quotientAddGroup.integral_eq_integral_automorphize h𝓕 H₁ H₂
#align quotient_add_group.integral_mul_eq_integral_automorphize_mul quotientAddGroup.integral_hMul_eq_integral_automorphize_hMul

end

attribute [to_additive QuotientGroup.integral_hMul_eq_integral_automorphize_hMul]
  quotientAddGroup.integral_hMul_eq_integral_automorphize_hMul

