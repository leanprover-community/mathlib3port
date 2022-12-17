/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module measure_theory.group.fundamental_domain
! leanprover-community/mathlib commit 11bb0c9152e5d14278fb0ac5e0be6d50e2c8fa05
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Group.Action
import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Fundamental domain of a group action

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.
-/


open Ennreal Pointwise TopologicalSpace Nnreal Ennreal MeasureTheory

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Filter

namespace MeasureTheory

/-- A measurable set `s` is a *fundamental domain* for an additive action of an additive group `G`
on a measurable space `α` with respect to a measure `α` if the sets `g +ᵥ s`, `g : G`, are pairwise
a.e. disjoint and cover the whole space. -/
@[protect_proj]
structure IsAddFundamentalDomain (G : Type _) {α : Type _} [Zero G] [VAdd G α] [MeasurableSpace α]
  (s : Set α) (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  NullMeasurableSet : NullMeasurableSet s μ
  ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s
  AeDisjoint : Pairwise <| (AeDisjoint μ on fun g : G => g +ᵥ s)
#align measure_theory.is_add_fundamental_domain MeasureTheory.IsAddFundamentalDomain

/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `α` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[protect_proj, to_additive is_add_fundamental_domain]
structure IsFundamentalDomain (G : Type _) {α : Type _} [One G] [HasSmul G α] [MeasurableSpace α]
  (s : Set α) (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  NullMeasurableSet : NullMeasurableSet s μ
  ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s
  AeDisjoint : Pairwise <| (AeDisjoint μ on fun g : G => g • s)
#align measure_theory.is_fundamental_domain MeasureTheory.IsFundamentalDomain

variable {G H α β E : Type _}

namespace IsFundamentalDomain

variable [Group G] [Group H] [MulAction G α] [MeasurableSpace α] [MulAction H β] [MeasurableSpace β]
  [NormedAddCommGroup E] {s t : Set α} {μ : Measure α}

/-- If for each `x : α`, exactly one of `g • x`, `g : G`, belongs to a measurable set `s`, then `s`
is a fundamental domain for the action of `G` on `α`. -/
@[to_additive
      "If for each `x : α`, exactly one of `g +ᵥ x`, `g : G`, belongs to a measurable set\n`s`, then `s` is a fundamental domain for the additive action of `G` on `α`."]
theorem mk' (h_meas : NullMeasurableSet s μ) (h_exists : ∀ x : α, ∃! g : G, g • x ∈ s) :
    IsFundamentalDomain G s μ :=
  { NullMeasurableSet := h_meas
    ae_covers := eventually_of_forall fun x => (h_exists x).exists
    AeDisjoint := fun a b hab =>
      Disjoint.aeDisjoint <|
        disjoint_left.2 fun x hxa hxb => by
          rw [mem_smul_set_iff_inv_smul_mem] at hxa hxb
          exact hab (inv_injective <| (h_exists x).unique hxa hxb) }
#align measure_theory.is_fundamental_domain.mk' MeasureTheory.IsFundamentalDomain.mk'

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (g «expr ≠ » (1 : G)) -/
/-- For `s` to be a fundamental domain, it's enough to check `ae_disjoint (g • s) s` for `g ≠ 1`. -/
@[to_additive
      "For `s` to be a fundamental domain, it's enough to check `ae_disjoint (g +ᵥ s) s` for\n`g ≠ 0`."]
theorem mk'' (h_meas : NullMeasurableSet s μ) (h_ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s)
    (h_ae_disjoint : ∀ (g) (_ : g ≠ (1 : G)), AeDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving ((· • ·) g : α → α) μ μ) : IsFundamentalDomain G s μ :=
  { NullMeasurableSet := h_meas
    ae_covers := h_ae_covers
    AeDisjoint := pairwise_ae_disjoint_of_ae_disjoint_forall_ne_one h_ae_disjoint h_qmp }
#align measure_theory.is_fundamental_domain.mk'' MeasureTheory.IsFundamentalDomain.mk''

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (g «expr ≠ » (1 : G)) -/
/-- If a measurable space has a finite measure `μ` and a countable group `G` acts
quasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient
to check that its translates `g • s` are (almost) disjoint and that the sum `∑' g, μ (g • s)` is
sufficiently large. -/
@[to_additive MeasureTheory.IsAddFundamentalDomain.mkOfMeasureUnivLe
      "\nIf a measurable space has a finite measure `μ` and a countable additive group `G` acts\nquasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient\nto check that its translates `g +ᵥ s` are (almost) disjoint and that the sum `∑' g, μ (g +ᵥ s)` is\nsufficiently large."]
theorem mkOfMeasureUnivLe [IsFiniteMeasure μ] [Countable G] (h_meas : NullMeasurableSet s μ)
    (h_ae_disjoint : ∀ (g) (_ : g ≠ (1 : G)), AeDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving ((· • ·) g : α → α) μ μ)
    (h_measure_univ_le : μ (univ : Set α) ≤ ∑' g : G, μ (g • s)) : IsFundamentalDomain G s μ :=
  have ae_disjoint : Pairwise (AeDisjoint μ on fun g : G => g • s) :=
    pairwise_ae_disjoint_of_ae_disjoint_forall_ne_one h_ae_disjoint h_qmp
  { NullMeasurableSet := h_meas
    AeDisjoint
    ae_covers := by
      replace h_meas : ∀ g : G, null_measurable_set (g • s) μ := fun g => by
        rw [← inv_inv g, ← preimage_smul]
        exact h_meas.preimage (h_qmp g⁻¹)
      have h_meas' : null_measurable_set { a | ∃ g : G, g • a ∈ s } μ := by
        rw [← Union_smul_eq_set_of_exists]
        exact null_measurable_set.Union h_meas
      rw [ae_iff_measure_eq h_meas', ← Union_smul_eq_set_of_exists]
      refine' le_antisymm (measure_mono <| subset_univ _) _
      rw [measure_Union₀ ae_disjoint h_meas]
      exact h_measure_univ_le }
#align
  measure_theory.is_fundamental_domain.mk_of_measure_univ_le MeasureTheory.IsFundamentalDomain.mkOfMeasureUnivLe

@[to_additive]
theorem Union_smul_ae_eq (h : IsFundamentalDomain G s μ) : (⋃ g : G, g • s) =ᵐ[μ] univ :=
  eventually_eq_univ.2 <|
    h.ae_covers.mono fun x ⟨g, hg⟩ => mem_Union.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩
#align
  measure_theory.is_fundamental_domain.Union_smul_ae_eq MeasureTheory.IsFundamentalDomain.Union_smul_ae_eq

@[to_additive]
theorem mono (h : IsFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ) :
    IsFundamentalDomain G s ν :=
  ⟨h.1.monoAc hle, hle h.2, h.AeDisjoint.mono fun a b hab => hle hab⟩
#align measure_theory.is_fundamental_domain.mono MeasureTheory.IsFundamentalDomain.mono

@[to_additive]
theorem preimageOfEquiv {ν : Measure β} (h : IsFundamentalDomain G s μ) {f : β → α}
    (hf : QuasiMeasurePreserving f ν μ) {e : G → H} (he : Bijective e)
    (hef : ∀ g, Semiconj f ((· • ·) (e g)) ((· • ·) g)) : IsFundamentalDomain H (f ⁻¹' s) ν :=
  { NullMeasurableSet := h.NullMeasurableSet.Preimage hf
    ae_covers := (hf.ae h.ae_covers).mono fun x ⟨g, hg⟩ => ⟨e g, by rwa [mem_preimage, hef g x]⟩
    AeDisjoint := fun a b hab => by 
      lift e to G ≃ H using he
      have : (e.symm a⁻¹)⁻¹ ≠ (e.symm b⁻¹)⁻¹ := by simp [hab]
      convert (h.ae_disjoint this).Preimage hf using 1
      simp only [← preimage_smul_inv, preimage_preimage, ← hef _ _, e.apply_symm_apply, inv_inv] }
#align
  measure_theory.is_fundamental_domain.preimage_of_equiv MeasureTheory.IsFundamentalDomain.preimageOfEquiv

@[to_additive]
theorem imageOfEquiv {ν : Measure β} (h : IsFundamentalDomain G s μ) (f : α ≃ β)
    (hf : QuasiMeasurePreserving f.symm ν μ) (e : H ≃ G)
    (hef : ∀ g, Semiconj f ((· • ·) (e g)) ((· • ·) g)) : IsFundamentalDomain H (f '' s) ν := by
  rw [f.image_eq_preimage]
  refine' h.preimage_of_equiv hf e.symm.bijective fun g x => _
  rcases f.surjective x with ⟨x, rfl⟩
  rw [← hef _ _, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]
#align
  measure_theory.is_fundamental_domain.image_of_equiv MeasureTheory.IsFundamentalDomain.imageOfEquiv

@[to_additive]
theorem pairwise_ae_disjoint_of_ac {ν} (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    Pairwise fun g₁ g₂ : G => AeDisjoint ν (g₁ • s) (g₂ • s) :=
  h.AeDisjoint.mono fun g₁ g₂ H => hν H
#align
  measure_theory.is_fundamental_domain.pairwise_ae_disjoint_of_ac MeasureTheory.IsFundamentalDomain.pairwise_ae_disjoint_of_ac

@[to_additive]
theorem smulOfComm {G' : Type _} [Group G'] [MulAction G' α] [MeasurableSpace G']
    [HasMeasurableSmul G' α] [SmulInvariantMeasure G' α μ] [SMulCommClass G' G α]
    (h : IsFundamentalDomain G s μ) (g : G') : IsFundamentalDomain G (g • s) μ :=
  h.imageOfEquiv (MulAction.toPerm g) (measurePreservingSmul _ _).QuasiMeasurePreserving
      (Equiv.refl _) <|
    smul_comm g
#align
  measure_theory.is_fundamental_domain.smul_of_comm MeasureTheory.IsFundamentalDomain.smulOfComm

variable [MeasurableSpace G] [HasMeasurableSmul G α] [SmulInvariantMeasure G α μ]

@[to_additive]
theorem nullMeasurableSetSmul (h : IsFundamentalDomain G s μ) (g : G) :
    NullMeasurableSet (g • s) μ :=
  h.NullMeasurableSet.smul g
#align
  measure_theory.is_fundamental_domain.null_measurable_set_smul MeasureTheory.IsFundamentalDomain.nullMeasurableSetSmul

@[to_additive]
theorem restrict_restrict (h : IsFundamentalDomain G s μ) (g : G) (t : Set α) :
    (μ.restrict t).restrict (g • s) = μ.restrict (g • s ∩ t) :=
  restrict_restrict₀ ((h.nullMeasurableSetSmul g).mono restrict_le_self)
#align
  measure_theory.is_fundamental_domain.restrict_restrict MeasureTheory.IsFundamentalDomain.restrict_restrict

@[to_additive]
theorem smul (h : IsFundamentalDomain G s μ) (g : G) : IsFundamentalDomain G (g • s) μ :=
  (h.imageOfEquiv (MulAction.toPerm g) (measurePreservingSmul _ _).QuasiMeasurePreserving
      ⟨fun g' => g⁻¹ * g' * g, fun g' => g * g' * g⁻¹, fun g' => by simp [mul_assoc], fun g' => by
        simp [mul_assoc]⟩)
    fun g' x => by simp [smul_smul, mul_assoc]
#align measure_theory.is_fundamental_domain.smul MeasureTheory.IsFundamentalDomain.smul

variable [Countable G] {ν : Measure α}

@[to_additive]
theorem sum_restrict_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    (Sum fun g : G => ν.restrict (g • s)) = ν := by
  rw [←
    restrict_Union_ae (h.ae_disjoint.mono fun i j h => hν h) fun g =>
      (h.null_measurable_set_smul g).monoAc hν,
    restrict_congr_set (hν h.Union_smul_ae_eq), restrict_univ]
#align
  measure_theory.is_fundamental_domain.sum_restrict_of_ac MeasureTheory.IsFundamentalDomain.sum_restrict_of_ac

@[to_additive]
theorem lintegral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂ν) = ∑' g : G, ∫⁻ x in g • s, f x ∂ν := by
  rw [← lintegral_sum_measure, h.sum_restrict_of_ac hν]
#align
  measure_theory.is_fundamental_domain.lintegral_eq_tsum_of_ac MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum_of_ac

@[to_additive]
theorem sum_restrict (h : IsFundamentalDomain G s μ) : (Sum fun g : G => μ.restrict (g • s)) = μ :=
  h.sum_restrict_of_ac (refl _)
#align
  measure_theory.is_fundamental_domain.sum_restrict MeasureTheory.IsFundamentalDomain.sum_restrict

@[to_additive]
theorem lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂μ) = ∑' g : G, ∫⁻ x in g • s, f x ∂μ :=
  h.lintegral_eq_tsum_of_ac (refl _) f
#align
  measure_theory.is_fundamental_domain.lintegral_eq_tsum MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum

@[to_additive]
theorem set_lintegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    (∫⁻ x in t, f x ∂μ) = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :=
  calc
    (∫⁻ x in t, f x ∂μ) = ∑' g : G, ∫⁻ x in g • s, f x ∂μ.restrict t :=
      h.lintegral_eq_tsum_of_ac restrict_le_self.AbsolutelyContinuous _
    _ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := by simp only [h.restrict_restrict, inter_comm]
    
#align
  measure_theory.is_fundamental_domain.set_lintegral_eq_tsum' MeasureTheory.IsFundamentalDomain.set_lintegral_eq_tsum'

@[to_additive]
theorem set_lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    (∫⁻ x in t, f x ∂μ) = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    (∫⁻ x in t, f x ∂μ) = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := h.set_lintegral_eq_tsum' f t
    _ = ∑' g : G, ∫⁻ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
      tsum_congr fun g =>
        ((measurePreservingSmul g⁻¹ μ).set_lintegral_comp_emb (measurableEmbeddingConstSmul _) _
            _).symm
    
#align
  measure_theory.is_fundamental_domain.set_lintegral_eq_tsum MeasureTheory.IsFundamentalDomain.set_lintegral_eq_tsum

@[to_additive]
theorem measure_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Set α) :
    ν t = ∑' g : G, ν (t ∩ g • s) := by
  have H : ν.restrict t ≪ μ := Measure.restrict_le_self.AbsolutelyContinuous.trans hν
  simpa only [set_lintegral_one, Pi.one_def,
    measure.restrict_apply₀ ((h.null_measurable_set_smul _).monoAc H), inter_comm] using
    h.lintegral_eq_tsum_of_ac H 1
#align
  measure_theory.is_fundamental_domain.measure_eq_tsum_of_ac MeasureTheory.IsFundamentalDomain.measure_eq_tsum_of_ac

@[to_additive]
theorem measure_eq_tsum' (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (t ∩ g • s) :=
  h.measure_eq_tsum_of_ac AbsolutelyContinuous.rfl t
#align
  measure_theory.is_fundamental_domain.measure_eq_tsum' MeasureTheory.IsFundamentalDomain.measure_eq_tsum'

@[to_additive]
theorem measure_eq_tsum (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (g • t ∩ s) := by
  simpa only [set_lintegral_one] using h.set_lintegral_eq_tsum (fun _ => 1) t
#align
  measure_theory.is_fundamental_domain.measure_eq_tsum MeasureTheory.IsFundamentalDomain.measure_eq_tsum

@[to_additive]
theorem measure_zero_of_invariant (h : IsFundamentalDomain G s μ) (t : Set α)
    (ht : ∀ g : G, g • t = t) (hts : μ (t ∩ s) = 0) : μ t = 0 := by
  simp [measure_eq_tsum h, ht, hts]
#align
  measure_theory.is_fundamental_domain.measure_zero_of_invariant MeasureTheory.IsFundamentalDomain.measure_zero_of_invariant

/-- Given a measure space with an action of a finite group `G`, the measure of any `G`-invariant set
is determined by the measure of its intersection with a fundamental domain for the action of `G`. -/
@[to_additive measure_eq_card_smul_of_vadd_ae_eq_self
      "Given a measure space with an action of a\nfinite additive group `G`, the measure of any `G`-invariant set is determined by the measure of its\nintersection with a fundamental domain for the action of `G`."]
theorem measure_eq_card_smul_of_smul_ae_eq_self [Finite G] (h : IsFundamentalDomain G s μ)
    (t : Set α) (ht : ∀ g : G, (g • t : Set α) =ᵐ[μ] t) : μ t = Nat.card G • μ (t ∩ s) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [h.measure_eq_tsum]
  replace ht : ∀ g : G, (g • t ∩ s : Set α) =ᵐ[μ] (t ∩ s : Set α) := fun g =>
    ae_eq_set_inter (ht g) (ae_eq_refl s)
  simp_rw [measure_congr (ht _), tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card,
    Finset.card_univ]
#align
  measure_theory.is_fundamental_domain.measure_eq_card_smul_of_smul_ae_eq_self MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self

@[to_additive]
protected theorem set_lintegral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    (f : α → ℝ≥0∞) (hf : ∀ (g : G) (x), f (g • x) = f x) :
    (∫⁻ x in s, f x ∂μ) = ∫⁻ x in t, f x ∂μ :=
  calc
    (∫⁻ x in s, f x ∂μ) = ∑' g : G, ∫⁻ x in s ∩ g • t, f x ∂μ := ht.set_lintegral_eq_tsum' _ _
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
    _ = ∫⁻ x in t, f x ∂μ := (hs.set_lintegral_eq_tsum _ _).symm
    
#align
  measure_theory.is_fundamental_domain.set_lintegral_eq MeasureTheory.IsFundamentalDomain.set_lintegral_eq

@[to_additive]
theorem measure_set_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {A : Set α}
    (hA₀ : MeasurableSet A) (hA : ∀ g : G, (fun x => g • x) ⁻¹' A = A) : μ (A ∩ s) = μ (A ∩ t) := by
  have : (∫⁻ x in s, A.indicator 1 x ∂μ) = ∫⁻ x in t, A.indicator 1 x ∂μ := by
    refine' hs.set_lintegral_eq ht (Set.indicator A fun _ => 1) _
    intro g x
    convert (Set.indicator_comp_right fun x : α => g • x).symm
    rw [hA g]
  simpa [measure.restrict_apply hA₀, lintegral_indicator _ hA₀] using this
#align
  measure_theory.is_fundamental_domain.measure_set_eq MeasureTheory.IsFundamentalDomain.measure_set_eq

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[to_additive
      "If `s` and `t` are two fundamental domains of the same action, then their measures\nare equal."]
protected theorem measure_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) :
    μ s = μ t := by
  simpa only [set_lintegral_one] using hs.set_lintegral_eq ht (fun _ => 1) fun _ _ => rfl
#align measure_theory.is_fundamental_domain.measure_eq MeasureTheory.IsFundamentalDomain.measure_eq

@[to_additive]
protected theorem ae_strongly_measurable_on_iff {β : Type _} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → β} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    AeStronglyMeasurable f (μ.restrict s) ↔ AeStronglyMeasurable f (μ.restrict t) :=
  calc
    AeStronglyMeasurable f (μ.restrict s) ↔
        AeStronglyMeasurable f (measure.sum fun g : G => μ.restrict (g • t ∩ s)) :=
      by
      simp only [← ht.restrict_restrict,
        ht.sum_restrict_of_ac restrict_le_self.absolutely_continuous]
    _ ↔ ∀ g : G, AeStronglyMeasurable f (μ.restrict (g • (g⁻¹ • s ∩ t))) := by
      simp only [smul_set_inter, inter_comm, smul_inv_smul, ae_strongly_measurable_sum_measure_iff]
    _ ↔ ∀ g : G, AeStronglyMeasurable f (μ.restrict (g⁻¹ • (g⁻¹⁻¹ • s ∩ t))) :=
      inv_surjective.forall
    _ ↔ ∀ g : G, AeStronglyMeasurable f (μ.restrict (g⁻¹ • (g • s ∩ t))) := by simp only [inv_inv]
    _ ↔ ∀ g : G, AeStronglyMeasurable f (μ.restrict (g • s ∩ t)) := by
      refine' forall_congr' fun g => _
      have he : MeasurableEmbedding ((· • ·) g⁻¹ : α → α) := measurableEmbeddingConstSmul _
      rw [← image_smul, ←
        ((measure_preserving_smul g⁻¹ μ).restrictImageEmb he _).ae_strongly_measurable_comp_iff he]
      simp only [(· ∘ ·), hf]
    _ ↔ AeStronglyMeasurable f (μ.restrict t) := by
      simp only [← ae_strongly_measurable_sum_measure_iff, ← hs.restrict_restrict,
        hs.sum_restrict_of_ac restrict_le_self.absolutely_continuous]
    
#align
  measure_theory.is_fundamental_domain.ae_strongly_measurable_on_iff MeasureTheory.IsFundamentalDomain.ae_strongly_measurable_on_iff

@[to_additive]
protected theorem has_finite_integral_on_iff (hs : IsFundamentalDomain G s μ)
    (ht : IsFundamentalDomain G t μ) {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    HasFiniteIntegral f (μ.restrict s) ↔ HasFiniteIntegral f (μ.restrict t) := by
  dsimp only [has_finite_integral]
  rw [hs.set_lintegral_eq ht]
  intro g x; rw [hf]
#align
  measure_theory.is_fundamental_domain.has_finite_integral_on_iff MeasureTheory.IsFundamentalDomain.has_finite_integral_on_iff

@[to_additive]
protected theorem integrable_on_iff (hs : IsFundamentalDomain G s μ)
    (ht : IsFundamentalDomain G t μ) {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  and_congr (hs.ae_strongly_measurable_on_iff ht hf) (hs.has_finite_integral_on_iff ht hf)
#align
  measure_theory.is_fundamental_domain.integrable_on_iff MeasureTheory.IsFundamentalDomain.integrable_on_iff

variable [NormedSpace ℝ E] [CompleteSpace E]

@[to_additive]
protected theorem set_integral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) : (∫ x in s, f x ∂μ) = ∫ x in t, f x ∂μ := by
  by_cases hfs : integrable_on f s μ
  · have hft : integrable_on f t μ := by rwa [ht.integrable_on_iff hs hf]
    have hac : ∀ {u}, μ.restrict u ≪ μ := fun u => restrict_le_self.absolutely_continuous
    calc
      (∫ x in s, f x ∂μ) = ∫ x in ⋃ g : G, g • t, f x ∂μ.restrict s := by
        rw [restrict_congr_set (hac ht.Union_smul_ae_eq), restrict_univ]
      _ = ∑' g : G, ∫ x in g • t, f x ∂μ.restrict s :=
        integral_Union_ae (fun g => (ht.null_measurable_set_smul g).monoAc hac)
          (ht.pairwise_ae_disjoint_of_ac hac) hfs.integrable.integrable_on
      _ = ∑' g : G, ∫ x in s ∩ g • t, f x ∂μ := by simp only [ht.restrict_restrict, inter_comm]
      _ = ∑' g : G, ∫ x in s ∩ g⁻¹ • t, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
      _ = ∑' g : G, ∫ x in g⁻¹ • (g • s ∩ t), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
      _ = ∑' g : G, ∫ x in g • s ∩ t, f (g⁻¹ • x) ∂μ :=
        tsum_congr fun g =>
          (measure_preserving_smul g⁻¹ μ).set_integral_image_emb (measurableEmbeddingConstSmul _) _
            _
      _ = ∑' g : G, ∫ x in g • s, f x ∂μ.restrict t := by simp only [hf, hs.restrict_restrict]
      _ = ∫ x in ⋃ g : G, g • s, f x ∂μ.restrict t :=
        (integral_Union_ae (fun g => (hs.null_measurable_set_smul g).monoAc hac)
            (hs.ae_disjoint.mono fun i j h => hac h) hft.integrable.integrable_on).symm
      _ = ∫ x in t, f x ∂μ := by rw [restrict_congr_set (hac hs.Union_smul_ae_eq), restrict_univ]
      
  · rw [integral_undef hfs, integral_undef]
    rwa [hs.integrable_on_iff ht hf] at hfs
#align
  measure_theory.is_fundamental_domain.set_integral_eq MeasureTheory.IsFundamentalDomain.set_integral_eq

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` such that the sets `g • t ∩ s` are pairwise a.e.-disjoint
has measure at most `μ s`. -/
@[to_additive
      "If the additive action of a countable group `G` admits an invariant measure `μ` with\na fundamental domain `s`, then every null-measurable set `t` such that the sets `g +ᵥ t ∩ s` are\npairwise a.e.-disjoint has measure at most `μ s`."]
theorem measure_le_of_pairwise_disjoint (hs : IsFundamentalDomain G s μ)
    (ht : NullMeasurableSet t μ) (hd : Pairwise (AeDisjoint μ on fun g : G => g • t ∩ s)) :
    μ t ≤ μ s :=
  calc
    μ t = ∑' g : G, μ (g • t ∩ s) := hs.measure_eq_tsum t
    _ = μ (⋃ g : G, g • t ∩ s) :=
      Eq.symm <| (measure_Union₀ hd) fun g => (ht.smul _).inter hs.NullMeasurableSet
    _ ≤ μ s := measure_mono (Union_subset fun g => inter_subset_right _ _)
    
#align
  measure_theory.is_fundamental_domain.measure_le_of_pairwise_disjoint MeasureTheory.IsFundamentalDomain.measure_le_of_pairwise_disjoint

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » t) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (g «expr ≠ » (1 : G)) -/
/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` of measure strictly greater than `μ s` contains two
points `x y` such that `g • x = y` for some `g ≠ 1`. -/
@[to_additive
      "If the additive action of a countable group `G` admits an invariant measure `μ` with\na fundamental domain `s`, then every null-measurable set `t` of measure strictly greater than `μ s`\ncontains two points `x y` such that `g +ᵥ x = y` for some `g ≠ 0`."]
theorem exists_ne_one_smul_eq (hs : IsFundamentalDomain G s μ) (htm : NullMeasurableSet t μ)
    (ht : μ s < μ t) : ∃ (x y : _)(_ : x ∈ t)(_ : y ∈ t)(g : _)(_ : g ≠ (1 : G)), g • x = y := by
  contrapose! ht
  refine' hs.measure_le_of_pairwise_disjoint htm (Pairwise.ae_disjoint fun g₁ g₂ hne => _)
  dsimp [Function.onFun]
  refine' (Disjoint.inf_left _ _).inf_right _
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  refine' ht x hx y hy (g₂⁻¹ * g₁) (mt inv_mul_eq_one.1 hne.symm) _
  rw [mul_smul, ← hxy, inv_smul_smul]
#align
  measure_theory.is_fundamental_domain.exists_ne_one_smul_eq MeasureTheory.IsFundamentalDomain.exists_ne_one_smul_eq

/-- If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant
  measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s` is the same as
  that of `f` on all of its domain. -/
@[to_additive
      "If `f` is invariant under the action of a countable additive group `G`, and `μ` is a\n`G`-invariant measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s` is\nthe same as that of `f` on all of its domain."]
theorem ess_sup_measure_restrict (hs : IsFundamentalDomain G s μ) {f : α → ℝ≥0∞}
    (hf : ∀ γ : G, ∀ x : α, f (γ • x) = f x) : essSup f (μ.restrict s) = essSup f μ := by
  refine' le_antisymm (ess_sup_mono_measure' measure.restrict_le_self) _
  rw [ess_sup_eq_Inf (μ.restrict s) f, ess_sup_eq_Inf μ f]
  refine' Inf_le_Inf _
  rintro a (ha : (μ.restrict s) { x : α | a < f x } = 0)
  rw [measure.restrict_apply₀' hs.null_measurable_set] at ha
  refine' measure_zero_of_invariant hs _ _ ha
  intro γ
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  simp only [mem_set_of_eq, hf γ⁻¹ x]
#align
  measure_theory.is_fundamental_domain.ess_sup_measure_restrict MeasureTheory.IsFundamentalDomain.ess_sup_measure_restrict

end IsFundamentalDomain

end MeasureTheory

