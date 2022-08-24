/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.MeasureTheory.Measure.HaarLebesgue
import Mathbin.MeasureTheory.Covering.Besicovitch

/-!
# Satellite configurations for Besicovitch covering lemma in vector spaces

The Besicovitch covering theorem ensures that, in a nice metric space, there exists a number `N`
such that, from any family of balls with bounded radii, one can extract `N` families, each made of
disjoint balls, covering together all the centers of the initial family.

A key tool in the proof of this theorem is the notion of a satellite configuration, i.e., a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This is a technical notion, but it shows
up naturally in the proof of the Besicovitch theorem (which goes through a greedy algorithm): to
ensure that in the end one needs at most `N` families of balls, the crucial property of the
underlying metric space is that there should be no satellite configuration of `N + 1` points.

This file is devoted to the study of this property in vector spaces: we prove the main result
of [Füredi and Loeb, On the best constant for the Besicovitch covering theorem][furedi-loeb1994],
which shows that the optimal such `N` in a vector space coincides with the maximal number
of points one can put inside the unit ball of radius `2` under the condition that their distances
are bounded below by `1`.
In particular, this number is bounded by `5 ^ dim` by a straightforward measure argument.

## Main definitions and results

* `multiplicity E` is the maximal number of points one can put inside the unit ball
  of radius `2` in the vector space `E`, under the condition that their distances
  are bounded below by `1`.
* `multiplicity_le E` shows that `multiplicity E ≤ 5 ^ (dim E)`.
* `good_τ E` is a constant `> 1`, but close enough to `1` that satellite configurations
  with this parameter `τ` are not worst than for `τ = 1`.
* `is_empty_satellite_config_multiplicity` is the main theorem, saying that there are
  no satellite configurations of `(multiplicity E) + 1` points, for the parameter `good_τ E`.
-/


universe u

open Metric Set FiniteDimensional MeasureTheory Filter Finₓ

open Ennreal TopologicalSpace

noncomputable section

namespace Besicovitch

variable {E : Type _} [NormedAddCommGroup E]

namespace SatelliteConfig

variable [NormedSpace ℝ E] {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ)

/-- Rescaling a satellite configuration in a vector space, to put the basepoint at `0` and the base
radius at `1`. -/
def centerAndRescale : SatelliteConfig E N τ where
  c := fun i => (a.R (last N))⁻¹ • (a.c i - a.c (last N))
  R := fun i => (a.R (last N))⁻¹ * a.R i
  rpos := fun i => mul_pos (inv_pos.2 (a.rpos _)) (a.rpos _)
  h := fun i j hij => by
    rcases a.h i j hij with (H | H)
    · left
      constructor
      · rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le)]
        refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
        rw [dist_eq_norm] at H
        convert H.1 using 2
        abel
        
      · rw [← mul_assoc, mul_comm τ, mul_assoc]
        refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
        exact H.2
        
      
    · right
      constructor
      · rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le)]
        refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
        rw [dist_eq_norm] at H
        convert H.1 using 2
        abel
        
      · rw [← mul_assoc, mul_comm τ, mul_assoc]
        refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
        exact H.2
        
      
  hlast := fun i hi => by
    have H := a.hlast i hi
    constructor
    · rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le)]
      refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
      rw [dist_eq_norm] at H
      convert H.1 using 2
      abel
      
    · rw [← mul_assoc, mul_comm τ, mul_assoc]
      refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
      exact H.2
      
  inter := fun i hi => by
    have H := a.inter i hi
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le), ← mul_addₓ]
    refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
    rw [dist_eq_norm] at H
    convert H using 2
    abel

theorem center_and_rescale_center : a.centerAndRescale.c (last N) = 0 := by
  simp [satellite_config.center_and_rescale]

theorem center_and_rescale_radius {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ) : a.centerAndRescale.R (last N) = 1 := by
  simp [satellite_config.center_and_rescale, inv_mul_cancel (a.rpos _).ne']

end SatelliteConfig

/-! ### Disjoint balls of radius close to `1` in the radius `2` ball. -/


/-- The maximum cardinality of a `1`-separated set in the ball of radius `2`. This is also the
optimal number of families in the Besicovitch covering theorem. -/
def multiplicity (E : Type _) [NormedAddCommGroup E] :=
  sup { N | ∃ s : Finset E, s.card = N ∧ (∀ c ∈ s, ∥c∥ ≤ 2) ∧ ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ∥c - d∥ }

section

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `borelize #[[expr E]]
/-- Any `1`-separated set in the ball of radius `2` has cardinality at most `5 ^ dim`. This is
useful to show that the supremum in the definition of `besicovitch.multiplicity E` is
well behaved. -/
theorem card_le_of_separated (s : Finset E) (hs : ∀ c ∈ s, ∥c∥ ≤ 2) (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ∥c - d∥) :
    s.card ≤ 5 ^ finrank ℝ E := by
  trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `borelize #[[expr E]]"
  let μ : Measureₓ E := measure.add_haar
  let δ : ℝ := (1 : ℝ) / 2
  let ρ : ℝ := (5 : ℝ) / 2
  have ρpos : 0 < ρ := by
    norm_num[ρ]
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert h c hc d hd hcd
    norm_num
  have A_subset : A ⊆ ball (0 : E) ρ := by
    refine' Union₂_subset fun x hx => _
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 2 := by
        rw [dist_zero_right]
        exact add_le_add le_rflₓ (hs x hx)
      _ = 5 / 2 := by
        norm_num[δ]
      
  have I :
    (s.card : ℝ≥0∞) * Ennreal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      Ennreal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * Ennreal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_bUnion_finset D fun c hc => measurable_set_ball]
        have I : 0 < δ := by
          norm_num[δ]
        simp only [μ.add_haar_ball_of_pos _ I, one_div, one_pow, Finset.sum_const, nsmul_eq_mul, div_pow, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono A_subset
      _ = Ennreal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.add_haar_ball_of_pos _ ρpos]
      
  have J : (s.card : ℝ≥0∞) * Ennreal.ofReal (δ ^ finrank ℝ E) ≤ Ennreal.ofReal (ρ ^ finrank ℝ E) :=
    (Ennreal.mul_le_mul_right (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) ≤ (5 : ℝ) ^ finrank ℝ E := by
    simpa [Ennreal.to_real_mul, div_eq_mul_inv] using Ennreal.to_real_le_of_le_of_real (pow_nonneg ρpos.le _) J
  exact_mod_cast K

theorem multiplicity_le : multiplicity E ≤ 5 ^ finrank ℝ E := by
  apply cSup_le
  · refine'
      ⟨0,
        ⟨∅, by
          simp ⟩⟩
    
  · rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2
    

theorem card_le_multiplicity {s : Finset E} (hs : ∀ c ∈ s, ∥c∥ ≤ 2) (h's : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ∥c - d∥) :
    s.card ≤ multiplicity E := by
  apply le_cSup
  · refine' ⟨5 ^ finrank ℝ E, _⟩
    rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2
    
  · simp only [mem_set_of_eq, Ne.def]
    exact ⟨s, rfl, hs, h's⟩
    

variable (E)

/-- If `δ` is small enough, a `(1-δ)`-separated set in the ball of radius `2` also has cardinality
at most `multiplicity E`. -/
theorem exists_good_δ :
    ∃ δ : ℝ,
      0 < δ ∧
        δ < 1 ∧
          ∀ s : Finset E, (∀ c ∈ s, ∥c∥ ≤ 2) → (∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 - δ ≤ ∥c - d∥) → s.card ≤ multiplicity E :=
  by
  /- This follows from a compactness argument: otherwise, one could extract a converging
    subsequence, to obtain a `1`-separated set in the ball of radius `2` with cardinality
    `N = multiplicity E + 1`. To formalize this, we work with functions `fin N → E`.
     -/
  classical
  by_contra' h
  set N := multiplicity E + 1 with hN
  have : ∀ δ : ℝ, 0 < δ → ∃ f : Finₓ N → E, (∀ i : Finₓ N, ∥f i∥ ≤ 2) ∧ ∀ i j, i ≠ j → 1 - δ ≤ ∥f i - f j∥ := by
    intro δ hδ
    rcases lt_or_leₓ δ 1 with (hδ' | hδ')
    · rcases h δ hδ hδ' with ⟨s, hs, h's, s_card⟩
      obtain ⟨f, f_inj, hfs⟩ : ∃ f : Finₓ N → E, Function.Injective f ∧ range f ⊆ ↑s := by
        have : Fintype.card (Finₓ N) ≤ s.card := by
          simp only [Fintype.card_fin]
          exact s_card
        rcases Function.Embedding.exists_of_card_le_finset this with ⟨f, hf⟩
        exact ⟨f, f.injective, hf⟩
      simp only [range_subset_iff, Finset.mem_coe] at hfs
      refine' ⟨f, fun i => hs _ (hfs i), fun i j hij => h's _ (hfs i) _ (hfs j) (f_inj.ne hij)⟩
      
    · exact
        ⟨fun i => 0, fun i => by
          simp , fun i j hij => by
          simpa only [norm_zero, sub_nonpos, sub_self] ⟩
      
  -- For `δ > 0`, `F δ` is a function from `fin N` to the ball of radius `2` for which two points
  -- in the image are separated by `1 - δ`.
  choose! F hF using this
  -- Choose a converging subsequence when `δ → 0`.
  have : ∃ f : Finₓ N → E, (∀ i : Finₓ N, ∥f i∥ ≤ 2) ∧ ∀ i j, i ≠ j → 1 ≤ ∥f i - f j∥ := by
    obtain ⟨u, u_mono, zero_lt_u, hu⟩ :
      ∃ u : ℕ → ℝ, (∀ m n : ℕ, m < n → u n < u m) ∧ (∀ n : ℕ, 0 < u n) ∧ Filter.Tendsto u Filter.atTop (𝓝 0) :=
      exists_seq_strict_anti_tendsto (0 : ℝ)
    have A : ∀ n, F (u n) ∈ closed_ball (0 : Finₓ N → E) 2 := by
      intro n
      simp only [pi_norm_le_iff zero_le_two, mem_closed_ball, dist_zero_right, (hF (u n) (zero_lt_u n)).left,
        forall_const]
    obtain ⟨f, fmem, φ, φ_mono, hf⟩ :
      ∃ f ∈ closed_ball (0 : Finₓ N → E) 2, ∃ φ : ℕ → ℕ, StrictMono φ ∧ tendsto ((F ∘ u) ∘ φ) at_top (𝓝 f) :=
      IsCompact.tendsto_subseq (is_compact_closed_ball _ _) A
    refine' ⟨f, fun i => _, fun i j hij => _⟩
    · simp only [pi_norm_le_iff zero_le_two, mem_closed_ball, dist_zero_right] at fmem
      exact fmem i
      
    · have A : tendsto (fun n => ∥F (u (φ n)) i - F (u (φ n)) j∥) at_top (𝓝 ∥f i - f j∥) :=
        ((hf.apply i).sub (hf.apply j)).norm
      have B : tendsto (fun n => 1 - u (φ n)) at_top (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (hu.comp φ_mono.tendsto_at_top)
      rw [sub_zero] at B
      exact le_of_tendsto_of_tendsto' B A fun n => (hF (u (φ n)) (zero_lt_u _)).2 i j hij
      
  rcases this with ⟨f, hf, h'f⟩
  -- the range of `f` contradicts the definition of `multiplicity E`.
  have finj : Function.Injective f := by
    intro i j hij
    by_contra
    have : 1 ≤ ∥f i - f j∥ := h'f i j h
    simp only [hij, norm_zero, sub_self] at this
    exact lt_irreflₓ _ (this.trans_lt zero_lt_one)
  let s := Finset.image f Finset.univ
  have s_card : s.card = N := by
    rw [Finset.card_image_of_injective _ finj]
    exact Finset.card_fin N
  have hs : ∀ c ∈ s, ∥c∥ ≤ 2 := by
    simp only [hf, forall_apply_eq_imp_iff', forall_const, forall_exists_index, Finset.mem_univ, Finset.mem_image]
  have h's : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ∥c - d∥ := by
    simp only [s, forall_apply_eq_imp_iff', forall_exists_index, Finset.mem_univ, Finset.mem_image, Ne.def,
      exists_true_left, forall_apply_eq_imp_iff', forall_true_left]
    intro i j hij
    have : i ≠ j := fun h => by
      rw [h] at hij
      exact hij rfl
    exact h'f i j this
  have : s.card ≤ multiplicity E := card_le_multiplicity hs h's
  rw [s_card, hN] at this
  exact lt_irreflₓ _ ((Nat.lt_succ_selfₓ (multiplicity E)).trans_le this)

/-- A small positive number such that any `1 - δ`-separated set in the ball of radius `2` has
cardinality at most `besicovitch.multiplicity E`. -/
def goodδ : ℝ :=
  (exists_good_δ E).some

theorem good_δ_lt_one : goodδ E < 1 :=
  (exists_good_δ E).some_spec.2.1

/-- A number `τ > 1`, but chosen close enough to `1` so that the construction in the Besicovitch
covering theorem using this parameter `τ` will give the smallest possible number of covering
families. -/
def goodτ : ℝ :=
  1 + goodδ E / 4

theorem one_lt_good_τ : 1 < goodτ E := by
  dsimp' [good_τ, good_δ]
  linarith [(exists_good_δ E).some_spec.1]

variable {E}

theorem card_le_multiplicity_of_δ {s : Finset E} (hs : ∀ c ∈ s, ∥c∥ ≤ 2)
    (h's : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 - goodδ E ≤ ∥c - d∥) : s.card ≤ multiplicity E :=
  (Classical.some_spec (exists_good_δ E)).2.2 s hs h's

theorem le_multiplicity_of_δ_of_fin {n : ℕ} (f : Finₓ n → E) (h : ∀ i, ∥f i∥ ≤ 2)
    (h' : ∀ i j, i ≠ j → 1 - goodδ E ≤ ∥f i - f j∥) : n ≤ multiplicity E := by
  classical
  have finj : Function.Injective f := by
    intro i j hij
    by_contra
    have : 1 - good_δ E ≤ ∥f i - f j∥ := h' i j h
    simp only [hij, norm_zero, sub_self] at this
    linarith [good_δ_lt_one E]
  let s := Finset.image f Finset.univ
  have s_card : s.card = n := by
    rw [Finset.card_image_of_injective _ finj]
    exact Finset.card_fin n
  have hs : ∀ c ∈ s, ∥c∥ ≤ 2 := by
    simp only [h, forall_apply_eq_imp_iff', forall_const, forall_exists_index, Finset.mem_univ, Finset.mem_image,
      implies_true_iff]
  have h's : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 - good_δ E ≤ ∥c - d∥ := by
    simp only [s, forall_apply_eq_imp_iff', forall_exists_index, Finset.mem_univ, Finset.mem_image, Ne.def,
      exists_true_left, forall_apply_eq_imp_iff', forall_true_left]
    intro i j hij
    have : i ≠ j := fun h => by
      rw [h] at hij
      exact hij rfl
    exact h' i j this
  have : s.card ≤ multiplicity E := card_le_multiplicity_of_δ hs h's
  rwa [s_card] at this

end

namespace SatelliteConfig

/-!
### Relating satellite configurations to separated points in the ball of radius `2`.

We prove that the number of points in a satellite configuration is bounded by the maximal number
of `1`-separated points in the ball of radius `2`. For this, start from a satellite congifuration
`c`. Without loss of generality, one can assume that the last ball is centered at `0` and of
radius `1`. Define `c' i = c i` if `∥c i∥ ≤ 2`, and `c' i = (2/∥c i∥) • c i` if `∥c i∥ > 2`.
It turns out that these points are `1 - δ`-separated, where `δ` is arbitrarily small if `τ` is
close enough to `1`. The number of such configurations is bounded by `multiplicity E` if `δ` is
suitably small.

To check that the points `c' i` are `1 - δ`-separated, one treats separately the cases where
both `∥c i∥` and `∥c j∥` are `≤ 2`, where one of them is `≤ 2` and the other one is `> 2`, and
where both of them are `> 2`.
-/


theorem exists_normalized_aux1 {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ) (lastr : a.R (last N) = 1) (hτ : 1 ≤ τ)
    (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4) (hδ2 : δ ≤ 1) (i j : Finₓ N.succ) (inej : i ≠ j) : 1 - δ ≤ ∥a.c i - a.c j∥ := by
  have ah : ∀ i j, i ≠ j → a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ * a.r i ∨ a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ * a.r j :=
    by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 ≤ δ := by
    linarith only [hτ, hδ1]
  have D : 0 ≤ 1 - δ / 4 := by
    linarith only [hδ2]
  have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ
  have I : (1 - δ / 4) * τ ≤ 1 :=
    calc
      (1 - δ / 4) * τ ≤ (1 - δ / 4) * (1 + δ / 4) := mul_le_mul_of_nonneg_left hδ1 D
      _ = 1 - δ ^ 2 / 16 := by
        ring
      _ ≤ 1 := by
        linarith only [sq_nonneg δ]
      
  have J : 1 - δ ≤ 1 - δ / 4 := by
    linarith only [δnonneg]
  have K : 1 - δ / 4 ≤ τ⁻¹ := by
    rw [inv_eq_one_div, le_div_iff τpos]
    exact I
  suffices L : τ⁻¹ ≤ ∥a.c i - a.c j∥
  · linarith only [J, K, L]
    
  have hτ' : ∀ k, τ⁻¹ ≤ a.r k := by
    intro k
    rw [inv_eq_one_div, div_le_iff τpos, ← lastr, mul_comm]
    exact a.hlast' k hτ
  rcases ah i j inej with (H | H)
  · apply le_transₓ _ H.1
    exact hτ' i
    
  · rw [norm_sub_rev]
    apply le_transₓ _ H.1
    exact hτ' j
    

variable [NormedSpace ℝ E]

theorem exists_normalized_aux2 {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ) (lastc : a.c (last N) = 0)
    (lastr : a.R (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4) (hδ2 : δ ≤ 1) (i j : Finₓ N.succ)
    (inej : i ≠ j) (hi : ∥a.c i∥ ≤ 2) (hj : 2 < ∥a.c j∥) : 1 - δ ≤ ∥a.c i - (2 / ∥a.c j∥) • a.c j∥ := by
  have ah : ∀ i j, i ≠ j → a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ * a.r i ∨ a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ * a.r j :=
    by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 ≤ δ := by
    linarith only [hτ, hδ1]
  have D : 0 ≤ 1 - δ / 4 := by
    linarith only [hδ2]
  have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ
  have hcrj : ∥a.c j∥ ≤ a.r j + 1 := by
    simpa only [lastc, lastr, dist_zero_right] using a.inter' j
  have I : a.r i ≤ 2 := by
    rcases lt_or_leₓ i (last N) with (H | H)
    · apply (a.hlast i H).1.trans
      simpa only [dist_eq_norm, lastc, sub_zero] using hi
      
    · have : i = last N := top_le_iff.1 H
      rw [this, lastr]
      exact one_le_two
      
  have J : (1 - δ / 4) * τ ≤ 1 :=
    calc
      (1 - δ / 4) * τ ≤ (1 - δ / 4) * (1 + δ / 4) := mul_le_mul_of_nonneg_left hδ1 D
      _ = 1 - δ ^ 2 / 16 := by
        ring
      _ ≤ 1 := by
        linarith only [sq_nonneg δ]
      
  have A : a.r j - δ ≤ ∥a.c i - a.c j∥ := by
    rcases ah j i inej.symm with (H | H)
    · rw [norm_sub_rev]
      linarith [H.1]
      
    have C : a.r j ≤ 4 :=
      calc
        a.r j ≤ τ * a.r i := H.2
        _ ≤ τ * 2 := mul_le_mul_of_nonneg_left I τpos.le
        _ ≤ 5 / 4 * 2 :=
          mul_le_mul_of_nonneg_right
            (by
              linarith only [hδ1, hδ2])
            zero_le_two
        _ ≤ 4 := by
          norm_num
        
    calc
      a.r j - δ ≤ a.r j - a.r j / 4 * δ := by
        refine' sub_le_sub le_rflₓ _
        refine' mul_le_of_le_one_left δnonneg _
        linarith only [C]
      _ = (1 - δ / 4) * a.r j := by
        ring
      _ ≤ (1 - δ / 4) * (τ * a.r i) := mul_le_mul_of_nonneg_left H.2 D
      _ ≤ 1 * a.r i := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right J (a.rpos _).le
      _ ≤ ∥a.c i - a.c j∥ := by
        rw [one_mulₓ]
        exact H.1
      
  set d := (2 / ∥a.c j∥) • a.c j with hd
  have : a.r j - δ ≤ ∥a.c i - d∥ + (a.r j - 1) :=
    calc
      a.r j - δ ≤ ∥a.c i - a.c j∥ := A
      _ ≤ ∥a.c i - d∥ + ∥d - a.c j∥ := by
        simp only [← dist_eq_norm, dist_triangle]
      _ ≤ ∥a.c i - d∥ + (a.r j - 1) := by
        apply add_le_add_left
        have A : 0 ≤ 1 - 2 / ∥a.c j∥ := by
          simpa [div_le_iff (zero_le_two.trans_lt hj)] using hj.le
        rw [← one_smul ℝ (a.c j), hd, ← sub_smul, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg A, sub_mul]
        field_simp [(zero_le_two.trans_lt hj).ne']
        linarith only [hcrj]
      
  linarith only [this]

theorem exists_normalized_aux3 {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ) (lastc : a.c (last N) = 0)
    (lastr : a.R (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4) (i j : Finₓ N.succ) (inej : i ≠ j)
    (hi : 2 < ∥a.c i∥) (hij : ∥a.c i∥ ≤ ∥a.c j∥) : 1 - δ ≤ ∥(2 / ∥a.c i∥) • a.c i - (2 / ∥a.c j∥) • a.c j∥ := by
  have ah : ∀ i j, i ≠ j → a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ * a.r i ∨ a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ * a.r j :=
    by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 ≤ δ := by
    linarith only [hτ, hδ1]
  have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ
  have hcrj : ∥a.c j∥ ≤ a.r j + 1 := by
    simpa only [lastc, lastr, dist_zero_right] using a.inter' j
  have A : a.r i ≤ ∥a.c i∥ := by
    have : i < last N := by
      apply lt_top_iff_ne_top.2
      intro iN
      change i = last N at iN
      rw [iN, lastc, norm_zero] at hi
      exact lt_irreflₓ _ (zero_le_two.trans_lt hi)
    convert (a.hlast i this).1
    rw [dist_eq_norm, lastc, sub_zero]
  have hj : 2 < ∥a.c j∥ := hi.trans_le hij
  set s := ∥a.c i∥ with hs
  have spos : 0 < s := zero_lt_two.trans hi
  set d := (s / ∥a.c j∥) • a.c j with hd
  have I : ∥a.c j - a.c i∥ ≤ ∥a.c j∥ - s + ∥d - a.c i∥ :=
    calc
      ∥a.c j - a.c i∥ ≤ ∥a.c j - d∥ + ∥d - a.c i∥ := by
        simp [← dist_eq_norm, dist_triangle]
      _ = ∥a.c j∥ - ∥a.c i∥ + ∥d - a.c i∥ := by
        nth_rw 0[← one_smul ℝ (a.c j)]
        rw [add_left_injₓ, hd, ← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg, sub_mul, one_mulₓ,
          div_mul_cancel _ (zero_le_two.trans_lt hj).ne']
        rwa [sub_nonneg, div_le_iff (zero_lt_two.trans hj), one_mulₓ]
      
  have J : a.r j - ∥a.c j - a.c i∥ ≤ s / 2 * δ :=
    calc
      a.r j - ∥a.c j - a.c i∥ ≤ s * (τ - 1) := by
        rcases ah j i inej.symm with (H | H)
        · calc
            a.r j - ∥a.c j - a.c i∥ ≤ 0 := sub_nonpos.2 H.1
            _ ≤ s * (τ - 1) := mul_nonneg spos.le (sub_nonneg.2 hτ)
            
          
        · rw [norm_sub_rev] at H
          calc
            a.r j - ∥a.c j - a.c i∥ ≤ τ * a.r i - a.r i := sub_le_sub H.2 H.1
            _ = a.r i * (τ - 1) := by
              ring
            _ ≤ s * (τ - 1) := mul_le_mul_of_nonneg_right A (sub_nonneg.2 hτ)
            
          
      _ ≤ s * (δ / 2) :=
        mul_le_mul_of_nonneg_left
          (by
            linarith only [δnonneg, hδ1])
          spos.le
      _ = s / 2 * δ := by
        ring
      
  have invs_nonneg : 0 ≤ 2 / s := div_nonneg zero_le_two (zero_le_two.trans hi.le)
  calc
    1 - δ = 2 / s * (s / 2 - s / 2 * δ) := by
      field_simp [spos.ne']
      ring
    _ ≤ 2 / s * ∥d - a.c i∥ :=
      mul_le_mul_of_nonneg_left
        (by
          linarith only [hcrj, I, J, hi])
        invs_nonneg
    _ = ∥(2 / s) • a.c i - (2 / ∥a.c j∥) • a.c j∥ := by
      conv_lhs => rw [norm_sub_rev, ← abs_of_nonneg invs_nonneg]
      rw [← Real.norm_eq_abs, ← norm_smul, smul_sub, hd, smul_smul]
      congr 3
      field_simp [spos.ne']
    

theorem exists_normalized {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ) (lastc : a.c (last N) = 0)
    (lastr : a.R (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4) (hδ2 : δ ≤ 1) :
    ∃ c' : Finₓ N.succ → E, (∀ n, ∥c' n∥ ≤ 2) ∧ ∀ i j, i ≠ j → 1 - δ ≤ ∥c' i - c' j∥ := by
  let c' : Finₓ N.succ → E := fun i => if ∥a.c i∥ ≤ 2 then a.c i else (2 / ∥a.c i∥) • a.c i
  have norm_c'_le : ∀ i, ∥c' i∥ ≤ 2 := by
    intro i
    simp only [c']
    split_ifs
    · exact h
      
    by_cases' hi : ∥a.c i∥ = 0 <;> field_simp [norm_smul, hi]
  refine' ⟨c', fun n => norm_c'_le n, fun i j inej => _⟩
  -- up to exchanging `i` and `j`, one can assume `∥c i∥ ≤ ∥c j∥`.
  wlog (discharger := tactic.skip) hij : ∥a.c i∥ ≤ ∥a.c j∥ := le_totalₓ ∥a.c i∥ ∥a.c j∥ using i j, j i
  swap
  · intro i_ne_j
    rw [norm_sub_rev]
    exact this i_ne_j.symm
    
  rcases le_or_ltₓ ∥a.c j∥ 2 with (Hj | Hj)
  -- case `∥c j∥ ≤ 2` (and therefore also `∥c i∥ ≤ 2`)
  · simp_rw [c', Hj, hij.trans Hj, if_true]
    exact exists_normalized_aux1 a lastr hτ δ hδ1 hδ2 i j inej
    
  -- case `2 < ∥c j∥`
  · have H'j : ∥a.c j∥ ≤ 2 ↔ False := by
      simpa only [not_leₓ, iff_falseₓ] using Hj
    rcases le_or_ltₓ ∥a.c i∥ 2 with (Hi | Hi)
    · -- case `∥c i∥ ≤ 2`
      simp_rw [c', Hi, if_true, H'j, if_false]
      exact exists_normalized_aux2 a lastc lastr hτ δ hδ1 hδ2 i j inej Hi Hj
      
    · -- case `2 < ∥c i∥`
      have H'i : ∥a.c i∥ ≤ 2 ↔ False := by
        simpa only [not_leₓ, iff_falseₓ] using Hi
      simp_rw [c', H'i, if_false, H'j, if_false]
      exact exists_normalized_aux3 a lastc lastr hτ δ hδ1 i j inej Hi hij
      
    

end SatelliteConfig

variable (E) [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a normed vector space `E`, there can be no satellite configuration with `multiplicity E + 1`
points and the parameter `good_τ E`. This will ensure that in the inductive construction to get
the Besicovitch covering families, there will never be more than `multiplicity E` nonempty
families. -/
theorem is_empty_satellite_config_multiplicity : IsEmpty (SatelliteConfig E (multiplicity E) (goodτ E)) :=
  ⟨by
    intro a
    let b := a.center_and_rescale
    rcases b.exists_normalized a.center_and_rescale_center a.center_and_rescale_radius (one_lt_good_τ E).le (good_δ E)
        le_rflₓ (good_δ_lt_one E).le with
      ⟨c', c'_le_two, hc'⟩
    exact lt_irreflₓ _ ((Nat.lt_succ_selfₓ _).trans_le (le_multiplicity_of_δ_of_fin c' c'_le_two hc'))⟩

instance (priority := 100) : HasBesicovitchCovering E :=
  ⟨⟨multiplicity E, goodτ E, one_lt_good_τ E, is_empty_satellite_config_multiplicity E⟩⟩

end Besicovitch

