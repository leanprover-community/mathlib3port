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

open_locale Ennreal TopologicalSpace

noncomputable theory

namespace Besicovitch

variable{E : Type _}[NormedGroup E]

namespace SatelliteConfig

variable[NormedSpace ℝ E]{N : ℕ}{τ : ℝ}(a : satellite_config E N τ)

/-- Rescaling a satellite configuration in a vector space, to put the basepoint at `0` and the base
radius at `1`. -/
def center_and_rescale : satellite_config E N τ :=
  { c := fun i => a.r (last N)⁻¹ • (a.c i - a.c (last N)), R := fun i => a.r (last N)⁻¹*a.r i,
    rpos := fun i => mul_pos (inv_pos.2 (a.rpos _)) (a.rpos _),
    h :=
      fun i j hij =>
        by 
          rcases a.h i j hij with (H | H)
          ·
            left 
            split 
            ·
              rw [dist_eq_norm, ←smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le)]
              refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
              rw [dist_eq_norm] at H 
              convert H.1 using 2
              abel
            ·
              rw [←mul_assocₓ, mul_commₓ τ, mul_assocₓ]
              refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
              exact H.2
          ·
            right 
            split 
            ·
              rw [dist_eq_norm, ←smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le)]
              refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
              rw [dist_eq_norm] at H 
              convert H.1 using 2
              abel
            ·
              rw [←mul_assocₓ, mul_commₓ τ, mul_assocₓ]
              refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
              exact H.2,
    hlast :=
      fun i hi =>
        by 
          have H := a.hlast i hi 
          split 
          ·
            rw [dist_eq_norm, ←smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le)]
            refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
            rw [dist_eq_norm] at H 
            convert H.1 using 2
            abel
          ·
            rw [←mul_assocₓ, mul_commₓ τ, mul_assocₓ]
            refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
            exact H.2,
    inter :=
      fun i hi =>
        by 
          have H := a.inter i hi 
          rw [dist_eq_norm, ←smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le),
            ←mul_addₓ]
          refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
          rw [dist_eq_norm] at H 
          convert H using 2
          abel }

theorem center_and_rescale_center : a.center_and_rescale.c (last N) = 0 :=
  by 
    simp [satellite_config.center_and_rescale]

theorem center_and_rescale_radius {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) : a.center_and_rescale.r (last N) = 1 :=
  by 
    simp [satellite_config.center_and_rescale, inv_mul_cancel (a.rpos _).ne']

end SatelliteConfig

/-! ### Disjoint balls of radius close to `1` in the radius `2` ball. -/


/-- The maximum cardinality of a `1`-separated set in the ball of radius `2`. This is also the
optimal number of families in the Besicovitch covering theorem. -/
def multiplicity (E : Type _) [NormedGroup E] :=
  Sup { N | ∃ s : Finset E, s.card = N ∧ (∀ c _ : c ∈ s, ∥c∥ ≤ 2) ∧ ∀ c _ : c ∈ s, ∀ d _ : d ∈ s, c ≠ d → 1 ≤ ∥c - d∥ }

section 

variable[NormedSpace ℝ E][FiniteDimensional ℝ E]

/-- Any `1`-separated set in the ball of radius `2` has cardinality at most `5 ^ dim`. This is
useful to show that the supremum in the definition of `besicovitch.multiplicity E` is
well behaved. -/
theorem card_le_of_separated (s : Finset E) (hs : ∀ c _ : c ∈ s, ∥c∥ ≤ 2)
  (h : ∀ c _ : c ∈ s d _ : d ∈ s, c ≠ d → 1 ≤ ∥c - d∥) : s.card ≤ (5^finrank ℝ E) :=
  by 
    letI this : MeasurableSpace E := borel E 
    letI this : BorelSpace E := ⟨rfl⟩
    let μ : Measureₓ E := measure.add_haar 
    let δ : ℝ := (1 : ℝ) / 2
    let ρ : ℝ := (5 : ℝ) / 2
    have ρpos : 0 < ρ :=
      by 
        normNum [ρ]
    set A := ⋃(c : _)(_ : c ∈ s), ball (c : E) δ with hA 
    have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ)
    ·
      rintro c hc d hd hcd 
      apply ball_disjoint_ball 
      rw [dist_eq_norm]
      convert h c hc d hd hcd 
      normNum 
    have A_subset : A ⊆ ball (0 : E) ρ
    ·
      refine' bUnion_subset fun x hx => _ 
      apply ball_subset_ball' 
      calc (δ+dist x 0) ≤ δ+2 :=
        by 
          rw [dist_zero_right]
          exact add_le_add le_rfl (hs x hx)_ = 5 / 2 :=
        by 
          normNum [δ]
    have I :
      (((s.card : ℝ≥0∞)*Ennreal.ofReal (δ^finrank ℝ E))*μ (ball 0 1)) ≤ Ennreal.ofReal (ρ^finrank ℝ E)*μ (ball 0 1) :=
      calc (((s.card : ℝ≥0∞)*Ennreal.ofReal (δ^finrank ℝ E))*μ (ball 0 1)) = μ A :=
        by 
          rw [hA, measure_bUnion_finset D fun c hc => measurable_set_ball]
          have I : 0 < δ
          ·
            normNum [δ]
          simp only [μ.add_haar_ball_of_pos _ I, one_div, one_pow, Finset.sum_const, nsmul_eq_mul, div_pow, mul_assocₓ]
        _ ≤ μ (ball (0 : E) ρ) := measure_mono A_subset 
        _ = Ennreal.ofReal (ρ^finrank ℝ E)*μ (ball 0 1) :=
        by 
          simp only [μ.add_haar_ball_of_pos _ ρpos]
        
    have J : ((s.card : ℝ≥0∞)*Ennreal.ofReal (δ^finrank ℝ E)) ≤ Ennreal.ofReal (ρ^finrank ℝ E) :=
      (Ennreal.mul_le_mul_right (μ.add_haar_ball_pos _ zero_lt_one).ne' (μ.add_haar_ball_lt_top _ _).Ne).1 I 
    have K : (s.card : ℝ) ≤ ((5 : ℝ)^finrank ℝ E)
    ·
      simpa [Ennreal.to_real_mul, div_eq_mul_inv] using Ennreal.to_real_le_of_le_of_real (pow_nonneg ρpos.le _) J 
    exactModCast K

theorem multiplicity_le : multiplicity E ≤ (5^finrank ℝ E) :=
  by 
    apply cSup_le
    ·
      refine'
        ⟨0,
          ⟨∅,
            by 
              simp ⟩⟩
    ·
      rintro _ ⟨s, ⟨rfl, h⟩⟩
      exact Besicovitch.card_le_of_separated s h.1 h.2

theorem card_le_multiplicity {s : Finset E} (hs : ∀ c _ : c ∈ s, ∥c∥ ≤ 2)
  (h's : ∀ c _ : c ∈ s d _ : d ∈ s, c ≠ d → 1 ≤ ∥c - d∥) : s.card ≤ multiplicity E :=
  by 
    apply le_cSup
    ·
      refine' ⟨5^finrank ℝ E, _⟩
      rintro _ ⟨s, ⟨rfl, h⟩⟩
      exact Besicovitch.card_le_of_separated s h.1 h.2
    ·
      simp only [mem_set_of_eq, Ne.def]
      exact ⟨s, rfl, hs, h's⟩

variable(E)

-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- If `δ` is small enough, a `(1-δ)`-separated set in the ball of radius `2` also has cardinality
at most `multiplicity E`. -/
theorem exists_good_δ : «expr∃ , »((δ : exprℝ()), «expr ∧ »(«expr < »(0, δ), «expr ∧ »(«expr < »(δ, 1), ∀
   s : finset E, ∀
   c «expr ∈ » s, «expr ≤ »(«expr∥ ∥»(c), 2) → ∀
   (c «expr ∈ » s)
   (d «expr ∈ » s), «expr ≠ »(c, d) → «expr ≤ »(«expr - »(1, δ), «expr∥ ∥»(«expr - »(c, d))) → «expr ≤ »(s.card, multiplicity E)))) :=
begin
  classical,
  by_contradiction [ident h],
  push_neg ["at", ident h],
  set [] [ident N] [] [":="] [expr «expr + »(multiplicity E, 1)] ["with", ident hN],
  have [] [":", expr ∀
   δ : exprℝ(), «expr < »(0, δ) → «expr∃ , »((f : fin N → E), «expr ∧ »(∀
     i : fin N, «expr ≤ »(«expr∥ ∥»(f i), 2), ∀
     i j, «expr ≠ »(i, j) → «expr ≤ »(«expr - »(1, δ), «expr∥ ∥»(«expr - »(f i, f j)))))] [],
  { assume [binders (δ hδ)],
    rcases [expr lt_or_le δ 1, "with", ident hδ', "|", ident hδ'],
    { rcases [expr h δ hδ hδ', "with", "⟨", ident s, ",", ident hs, ",", ident h's, ",", ident s_card, "⟩"],
      obtain ["⟨", ident f, ",", ident f_inj, ",", ident hfs, "⟩", ":", expr «expr∃ , »((f : fin N → E), «expr ∧ »(function.injective f, «expr ⊆ »(range f, «expr↑ »(s))))],
      { have [] [":", expr «expr ≤ »(fintype.card (fin N), s.card)] [],
        { simp [] [] ["only"] ["[", expr fintype.card_fin, "]"] [] [],
          exact [expr s_card] },
        rcases [expr function.embedding.exists_of_card_le_finset this, "with", "⟨", ident f, ",", ident hf, "⟩"],
        exact [expr ⟨f, f.injective, hf⟩] },
      simp [] [] ["only"] ["[", expr range_subset_iff, ",", expr finset.mem_coe, "]"] [] ["at", ident hfs],
      refine [expr ⟨f, λ i, hs _ (hfs i), λ i j hij, h's _ (hfs i) _ (hfs j) (f_inj.ne hij)⟩] },
    { exact [expr ⟨λ
        i, 0, λ
        i, by simp [] [] [] [] [] [], λ
        i
        j
        hij, by simpa [] [] ["only"] ["[", expr norm_zero, ",", expr sub_nonpos, ",", expr sub_self, "]"] [] []⟩] } },
  choose ["!"] [ident F] [ident hF] ["using", expr this],
  have [] [":", expr «expr∃ , »((f : fin N → E), «expr ∧ »(∀
     i : fin N, «expr ≤ »(«expr∥ ∥»(f i), 2), ∀
     i j, «expr ≠ »(i, j) → «expr ≤ »(1, «expr∥ ∥»(«expr - »(f i, f j)))))] [],
  { obtain ["⟨", ident u, ",", ident u_mono, ",", ident zero_lt_u, ",", ident hu, "⟩", ":", expr «expr∃ , »((u : exprℕ() → exprℝ()), «expr ∧ »(∀
       m
       n : exprℕ(), «expr < »(m, n) → «expr < »(u n, u m), «expr ∧ »(∀
        n : exprℕ(), «expr < »(0, u n), filter.tendsto u filter.at_top (expr𝓝() 0)))), ":=", expr exists_seq_strict_anti_tendsto (0 : exprℝ())],
    have [ident A] [":", expr ∀ n, «expr ∈ »(F (u n), closed_ball (0 : fin N → E) 2)] [],
    { assume [binders (n)],
      simp [] [] ["only"] ["[", expr pi_norm_le_iff zero_le_two, ",", expr mem_closed_ball, ",", expr dist_zero_right, ",", expr (hF (u n) (zero_lt_u n)).left, ",", expr forall_const, "]"] [] [] },
    obtain ["⟨", ident f, ",", ident fmem, ",", ident φ, ",", ident φ_mono, ",", ident hf, "⟩", ":", expr «expr∃ , »((f «expr ∈ » closed_ball (0 : fin N → E) 2)
      (φ : exprℕ() → exprℕ()), «expr ∧ »(strict_mono φ, tendsto «expr ∘ »(«expr ∘ »(F, u), φ) at_top (expr𝓝() f))), ":=", expr is_compact.tendsto_subseq (proper_space.is_compact_closed_ball _ _) A],
    refine [expr ⟨f, λ i, _, λ i j hij, _⟩],
    { simp [] [] ["only"] ["[", expr pi_norm_le_iff zero_le_two, ",", expr mem_closed_ball, ",", expr dist_zero_right, "]"] [] ["at", ident fmem],
      exact [expr fmem i] },
    { have [ident A] [":", expr tendsto (λ
        n, «expr∥ ∥»(«expr - »(F (u (φ n)) i, F (u (φ n)) j))) at_top (expr𝓝() «expr∥ ∥»(«expr - »(f i, f j)))] [":=", expr ((hf.apply i).sub (hf.apply j)).norm],
      have [ident B] [":", expr tendsto (λ
        n, «expr - »(1, u (φ n))) at_top (expr𝓝() «expr - »(1, 0))] [":=", expr tendsto_const_nhds.sub (hu.comp φ_mono.tendsto_at_top)],
      rw [expr sub_zero] ["at", ident B],
      exact [expr le_of_tendsto_of_tendsto' B A (λ n, (hF (u (φ n)) (zero_lt_u _)).2 i j hij)] } },
  rcases [expr this, "with", "⟨", ident f, ",", ident hf, ",", ident h'f, "⟩"],
  have [ident finj] [":", expr function.injective f] [],
  { assume [binders (i j hij)],
    by_contra [],
    have [] [":", expr «expr ≤ »(1, «expr∥ ∥»(«expr - »(f i, f j)))] [":=", expr h'f i j h],
    simp [] [] ["only"] ["[", expr hij, ",", expr norm_zero, ",", expr sub_self, "]"] [] ["at", ident this],
    exact [expr lt_irrefl _ (this.trans_lt zero_lt_one)] },
  let [ident s] [] [":=", expr finset.image f finset.univ],
  have [ident s_card] [":", expr «expr = »(s.card, N)] [],
  by { rw [expr finset.card_image_of_injective _ finj] [],
    exact [expr finset.card_fin N] },
  have [ident hs] [":", expr ∀ c «expr ∈ » s, «expr ≤ »(«expr∥ ∥»(c), 2)] [],
  by simp [] [] ["only"] ["[", expr hf, ",", expr forall_apply_eq_imp_iff', ",", expr forall_const, ",", expr forall_exists_index, ",", expr finset.mem_univ, ",", expr finset.mem_image, "]"] [] [],
  have [ident h's] [":", expr ∀
   (c «expr ∈ » s)
   (d «expr ∈ » s), «expr ≠ »(c, d) → «expr ≤ »(1, «expr∥ ∥»(«expr - »(c, d)))] [],
  { simp [] [] ["only"] ["[", expr s, ",", expr forall_apply_eq_imp_iff', ",", expr forall_exists_index, ",", expr finset.mem_univ, ",", expr finset.mem_image, ",", expr ne.def, ",", expr exists_true_left, ",", expr forall_apply_eq_imp_iff', ",", expr forall_true_left, "]"] [] [],
    assume [binders (i j hij)],
    have [] [":", expr «expr ≠ »(i, j)] [":=", expr λ h, by { rw [expr h] ["at", ident hij], exact [expr hij rfl] }],
    exact [expr h'f i j this] },
  have [] [":", expr «expr ≤ »(s.card, multiplicity E)] [":=", expr card_le_multiplicity hs h's],
  rw ["[", expr s_card, ",", expr hN, "]"] ["at", ident this],
  exact [expr lt_irrefl _ ((nat.lt_succ_self (multiplicity E)).trans_le this)]
end

/-- A small positive number such that any `1 - δ`-separated set in the ball of radius `2` has
cardinality at most `besicovitch.multiplicity E`. -/
def good_δ : ℝ :=
  (exists_good_δ E).some

theorem good_δ_lt_one : good_δ E < 1 :=
  (exists_good_δ E).some_spec.2.1

/-- A number `τ > 1`, but chosen close enough to `1` so that the construction in the Besicovitch
covering theorem using this parameter `τ` will give the smallest possible number of covering
families. -/
def good_τ : ℝ :=
  1+good_δ E / 4

theorem one_lt_good_τ : 1 < good_τ E :=
  by 
    dsimp [good_τ, good_δ]
    linarith [(exists_good_δ E).some_spec.1]

variable{E}

theorem card_le_multiplicity_of_δ {s : Finset E} (hs : ∀ c _ : c ∈ s, ∥c∥ ≤ 2)
  (h's : ∀ c _ : c ∈ s d _ : d ∈ s, c ≠ d → 1 - good_δ E ≤ ∥c - d∥) : s.card ≤ multiplicity E :=
  (Classical.some_spec (exists_good_δ E)).2.2 s hs h's

-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem le_multiplicity_of_δ_of_fin
{n : exprℕ()}
(f : fin n → E)
(h : ∀ i, «expr ≤ »(«expr∥ ∥»(f i), 2))
(h' : ∀
 i
 j, «expr ≠ »(i, j) → «expr ≤ »(«expr - »(1, good_δ E), «expr∥ ∥»(«expr - »(f i, f j)))) : «expr ≤ »(n, multiplicity E) :=
begin
  classical,
  have [ident finj] [":", expr function.injective f] [],
  { assume [binders (i j hij)],
    by_contra [],
    have [] [":", expr «expr ≤ »(«expr - »(1, good_δ E), «expr∥ ∥»(«expr - »(f i, f j)))] [":=", expr h' i j h],
    simp [] [] ["only"] ["[", expr hij, ",", expr norm_zero, ",", expr sub_self, "]"] [] ["at", ident this],
    linarith [] [] ["[", expr good_δ_lt_one E, "]"] },
  let [ident s] [] [":=", expr finset.image f finset.univ],
  have [ident s_card] [":", expr «expr = »(s.card, n)] [],
  by { rw [expr finset.card_image_of_injective _ finj] [],
    exact [expr finset.card_fin n] },
  have [ident hs] [":", expr ∀ c «expr ∈ » s, «expr ≤ »(«expr∥ ∥»(c), 2)] [],
  by simp [] [] ["only"] ["[", expr h, ",", expr forall_apply_eq_imp_iff', ",", expr forall_const, ",", expr forall_exists_index, ",", expr finset.mem_univ, ",", expr finset.mem_image, ",", expr implies_true_iff, "]"] [] [],
  have [ident h's] [":", expr ∀
   (c «expr ∈ » s)
   (d «expr ∈ » s), «expr ≠ »(c, d) → «expr ≤ »(«expr - »(1, good_δ E), «expr∥ ∥»(«expr - »(c, d)))] [],
  { simp [] [] ["only"] ["[", expr s, ",", expr forall_apply_eq_imp_iff', ",", expr forall_exists_index, ",", expr finset.mem_univ, ",", expr finset.mem_image, ",", expr ne.def, ",", expr exists_true_left, ",", expr forall_apply_eq_imp_iff', ",", expr forall_true_left, "]"] [] [],
    assume [binders (i j hij)],
    have [] [":", expr «expr ≠ »(i, j)] [":=", expr λ h, by { rw [expr h] ["at", ident hij], exact [expr hij rfl] }],
    exact [expr h' i j this] },
  have [] [":", expr «expr ≤ »(s.card, multiplicity E)] [":=", expr card_le_multiplicity_of_δ hs h's],
  rwa ["[", expr s_card, "]"] ["at", ident this]
end

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
both `∥c i∥` and `∥c j∥` are `≤ 2`, where one of them is `≤ 2` and the other one is `` > 2`, and
where both of them are `> 2`.
-/


theorem exists_normalized_aux1 {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ)
  (δ : ℝ) (hδ1 : τ ≤ 1+δ / 4) (hδ2 : δ ≤ 1) (i j : Finₓ N.succ) (inej : i ≠ j) : 1 - δ ≤ ∥a.c i - a.c j∥ :=
  by 
    have ah : ∀ i j, i ≠ j → (a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ*a.r i) ∨ a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ*a.r j
    ·
      simpa only [dist_eq_norm] using a.h 
    have δnonneg : 0 ≤ δ :=
      by 
        linarith only [hτ, hδ1]
    have D : 0 ≤ 1 - δ / 4
    ·
      linarith only [hδ2]
    have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ 
    have I : ((1 - δ / 4)*τ) ≤ 1 :=
      calc ((1 - δ / 4)*τ) ≤ (1 - δ / 4)*1+δ / 4 := mul_le_mul_of_nonneg_left hδ1 D 
        _ = 1 - (δ^2) / 16 :=
        by 
          ring 
        _ ≤ 1 :=
        by 
          linarith only [sq_nonneg δ]
        
    have J : 1 - δ ≤ 1 - δ / 4
    ·
      linarith only [δnonneg]
    have K : 1 - δ / 4 ≤ τ⁻¹
    ·
      ·
        rw [inv_eq_one_div, le_div_iff τpos]
        exact I 
    suffices L : τ⁻¹ ≤ ∥a.c i - a.c j∥
    ·
      linarith only [J, K, L]
    have hτ' : ∀ k, τ⁻¹ ≤ a.r k
    ·
      intro k 
      rw [inv_eq_one_div, div_le_iff τpos, ←lastr, mul_commₓ]
      exact a.hlast' k hτ 
    rcases ah i j inej with (H | H)
    ·
      apply le_transₓ _ H.1 
      exact hτ' i
    ·
      rw [norm_sub_rev]
      apply le_transₓ _ H.1 
      exact hτ' j

variable[NormedSpace ℝ E]

theorem exists_normalized_aux2 {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) (lastc : a.c (last N) = 0)
  (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1+δ / 4) (hδ2 : δ ≤ 1) (i j : Finₓ N.succ) (inej : i ≠ j)
  (hi : ∥a.c i∥ ≤ 2) (hj : 2 < ∥a.c j∥) : 1 - δ ≤ ∥a.c i - (2 / ∥a.c j∥) • a.c j∥ :=
  by 
    have ah : ∀ i j, i ≠ j → (a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ*a.r i) ∨ a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ*a.r j
    ·
      simpa only [dist_eq_norm] using a.h 
    have δnonneg : 0 ≤ δ :=
      by 
        linarith only [hτ, hδ1]
    have D : 0 ≤ 1 - δ / 4
    ·
      linarith only [hδ2]
    have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ 
    have hcrj : ∥a.c j∥ ≤ a.r j+1
    ·
      simpa only [lastc, lastr, dist_zero_right] using a.inter' j 
    have I : a.r i ≤ 2
    ·
      rcases lt_or_leₓ i (last N) with (H | H)
      ·
        apply (a.hlast i H).1.trans 
        simpa only [dist_eq_norm, lastc, sub_zero] using hi
      ·
        have  : i = last N := top_le_iff.1 H 
        rw [this, lastr]
        exact one_le_two 
    have J : ((1 - δ / 4)*τ) ≤ 1 :=
      calc ((1 - δ / 4)*τ) ≤ (1 - δ / 4)*1+δ / 4 := mul_le_mul_of_nonneg_left hδ1 D 
        _ = 1 - (δ^2) / 16 :=
        by 
          ring 
        _ ≤ 1 :=
        by 
          linarith only [sq_nonneg δ]
        
    have A : a.r j - δ ≤ ∥a.c i - a.c j∥
    ·
      rcases ah j i inej.symm with (H | H)
      ·
        rw [norm_sub_rev]
        linarith [H.1]
      have C : a.r j ≤ 4 :=
        calc a.r j ≤ τ*a.r i := H.2
          _ ≤ τ*2 := mul_le_mul_of_nonneg_left I τpos.le 
          _ ≤ (5 / 4)*2 :=
          mul_le_mul_of_nonneg_right
            (by 
              linarith only [hδ1, hδ2])
            zero_le_two 
          _ ≤ 4 :=
          by 
            normNum 
          
      calc a.r j - δ ≤ a.r j - (a.r j / 4)*δ :=
        by 
          refine' sub_le_sub le_rfl _ 
          refine' mul_le_of_le_one_left δnonneg _ 
          linarith only [C]_ = (1 - δ / 4)*a.r j :=
        by 
          ring _ ≤ (1 - δ / 4)*τ*a.r i :=
        mul_le_mul_of_nonneg_left H.2 D _ ≤ 1*a.r i :=
        by 
          rw [←mul_assocₓ]
          apply mul_le_mul_of_nonneg_right J (a.rpos _).le _ ≤ ∥a.c i - a.c j∥ :=
        by 
          rw [one_mulₓ]
          exact H.1
    set d := (2 / ∥a.c j∥) • a.c j with hd 
    have  : a.r j - δ ≤ ∥a.c i - d∥+a.r j - 1 :=
      calc a.r j - δ ≤ ∥a.c i - a.c j∥ := A 
        _ ≤ ∥a.c i - d∥+∥d - a.c j∥ :=
        by 
          simp only [←dist_eq_norm, dist_triangle]
        _ ≤ ∥a.c i - d∥+a.r j - 1 :=
        by 
          apply add_le_add_left 
          have A : 0 ≤ 1 - 2 / ∥a.c j∥
          ·
            simpa [div_le_iff (zero_le_two.trans_lt hj)] using hj.le 
          rw [←one_smul ℝ (a.c j), hd, ←sub_smul, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg A, sub_mul]
          fieldSimp [(zero_le_two.trans_lt hj).ne']
          linarith only [hcrj]
        
    linarith only [this]

theorem exists_normalized_aux3 {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) (lastc : a.c (last N) = 0)
  (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1+δ / 4) (i j : Finₓ N.succ) (inej : i ≠ j)
  (hi : 2 < ∥a.c i∥) (hij : ∥a.c i∥ ≤ ∥a.c j∥) : 1 - δ ≤ ∥(2 / ∥a.c i∥) • a.c i - (2 / ∥a.c j∥) • a.c j∥ :=
  by 
    have ah : ∀ i j, i ≠ j → (a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ*a.r i) ∨ a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ*a.r j
    ·
      simpa only [dist_eq_norm] using a.h 
    have δnonneg : 0 ≤ δ :=
      by 
        linarith only [hτ, hδ1]
    have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ 
    have hcrj : ∥a.c j∥ ≤ a.r j+1
    ·
      simpa only [lastc, lastr, dist_zero_right] using a.inter' j 
    have A : a.r i ≤ ∥a.c i∥
    ·
      have  : i < last N
      ·
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
    have I : ∥a.c j - a.c i∥ ≤ (∥a.c j∥ - s)+∥d - a.c i∥ :=
      calc ∥a.c j - a.c i∥ ≤ ∥a.c j - d∥+∥d - a.c i∥ :=
        by 
          simp [←dist_eq_norm, dist_triangle]
        _ = (∥a.c j∥ - ∥a.c i∥)+∥d - a.c i∥ :=
        by 
          nthRw 0[←one_smul ℝ (a.c j)]
          rw [add_left_injₓ, hd, ←sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg, sub_mul, one_mulₓ,
            div_mul_cancel _ (zero_le_two.trans_lt hj).ne']
          rwa [sub_nonneg, div_le_iff (zero_lt_two.trans hj), one_mulₓ]
        
    have J : a.r j - ∥a.c j - a.c i∥ ≤ (s / 2)*δ :=
      calc a.r j - ∥a.c j - a.c i∥ ≤ s*τ - 1 :=
        by 
          rcases ah j i inej.symm with (H | H)
          ·
            calc a.r j - ∥a.c j - a.c i∥ ≤ 0 := sub_nonpos.2 H.1_ ≤ s*τ - 1 := mul_nonneg spos.le (sub_nonneg.2 hτ)
          ·
            rw [norm_sub_rev] at H 
            calc a.r j - ∥a.c j - a.c i∥ ≤ (τ*a.r i) - a.r i := sub_le_sub H.2 H.1_ = a.r i*τ - 1 :=
              by 
                ring _ ≤ s*τ - 1 :=
              mul_le_mul_of_nonneg_right A (sub_nonneg.2 hτ)
        _ ≤ s*δ / 2 :=
        mul_le_mul_of_nonneg_left
          (by 
            linarith only [δnonneg, hδ1])
          spos.le 
        _ = (s / 2)*δ :=
        by 
          ring 
        
    have invs_nonneg : 0 ≤ 2 / s := div_nonneg zero_le_two (zero_le_two.trans hi.le)
    calc 1 - δ = (2 / s)*s / 2 - (s / 2)*δ :=
      by 
        fieldSimp [spos.ne']
        ring _ ≤ (2 / s)*∥d - a.c i∥ :=
      mul_le_mul_of_nonneg_left
        (by 
          linarith only [hcrj, I, J, hi])
        invs_nonneg _ = ∥(2 / s) • a.c i - (2 / ∥a.c j∥) • a.c j∥ :=
      by 
        convLHS => rw [norm_sub_rev, ←abs_of_nonneg invs_nonneg]
        rw [←Real.norm_eq_abs, ←norm_smul, smul_sub, hd, smul_smul]
        congr 3
        fieldSimp [spos.ne']

theorem exists_normalized {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) (lastc : a.c (last N) = 0)
  (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1+δ / 4) (hδ2 : δ ≤ 1) :
  ∃ c' : Finₓ N.succ → E, (∀ n, ∥c' n∥ ≤ 2) ∧ ∀ i j, i ≠ j → 1 - δ ≤ ∥c' i - c' j∥ :=
  by 
    let c' : Finₓ N.succ → E := fun i => if ∥a.c i∥ ≤ 2 then a.c i else (2 / ∥a.c i∥) • a.c i 
    have norm_c'_le : ∀ i, ∥c' i∥ ≤ 2
    ·
      intro i 
      simp only [c']
      splitIfs
      ·
        exact h 
      byCases' hi : ∥a.c i∥ = 0 <;> fieldSimp [norm_smul, hi]
    refine' ⟨c', fun n => norm_c'_le n, fun i j inej => _⟩
    wlog (discharger := tactic.skip) hij : ∥a.c i∥ ≤ ∥a.c j∥ := le_totalₓ ∥a.c i∥ ∥a.c j∥ using i j, j i 
    swap
    ·
      intro i_ne_j 
      rw [norm_sub_rev]
      exact this i_ne_j.symm 
    rcases le_or_ltₓ ∥a.c j∥ 2 with (Hj | Hj)
    ·
      simpRw [c', Hj, hij.trans Hj, if_true]
      exact exists_normalized_aux1 a lastr hτ δ hδ1 hδ2 i j inej
    ·
      have H'j : ∥a.c j∥ ≤ 2 ↔ False
      ·
        simpa only [not_leₓ, iff_falseₓ] using Hj 
      rcases le_or_ltₓ ∥a.c i∥ 2 with (Hi | Hi)
      ·
        simpRw [c', Hi, if_true, H'j, if_false]
        exact exists_normalized_aux2 a lastc lastr hτ δ hδ1 hδ2 i j inej Hi Hj
      ·
        have H'i : ∥a.c i∥ ≤ 2 ↔ False
        ·
          simpa only [not_leₓ, iff_falseₓ] using Hi 
        simpRw [c', H'i, if_false, H'j, if_false]
        exact exists_normalized_aux3 a lastc lastr hτ δ hδ1 i j inej Hi hij

end SatelliteConfig

variable(E)[NormedSpace ℝ E][FiniteDimensional ℝ E]

/-- In a normed vector space `E`, there can be no satellite configuration with `multiplicity E + 1`
points and the parameter `good_τ E`. This will ensure that in the inductive construction to get
the Besicovitch covering families, there will never be more than `multiplicity E` nonempty
families. -/
theorem is_empty_satellite_config_multiplicity : IsEmpty (satellite_config E (multiplicity E) (good_τ E)) :=
  ⟨by 
      intro a 
      let b := a.center_and_rescale 
      rcases
        b.exists_normalized a.center_and_rescale_center a.center_and_rescale_radius (one_lt_good_τ E).le (good_δ E)
          le_rfl (good_δ_lt_one E).le with
        ⟨c', c'_le_two, hc'⟩
      exact lt_irreflₓ _ ((Nat.lt_succ_selfₓ _).trans_le (le_multiplicity_of_δ_of_fin c' c'_le_two hc'))⟩

instance (priority := 100) : HasBesicovitchCovering E :=
  ⟨⟨multiplicity E, good_τ E, one_lt_good_τ E, is_empty_satellite_config_multiplicity E⟩⟩

end Besicovitch

