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

variable {E : Type _} [NormedGroup E]

namespace SatelliteConfig

variable [NormedSpace ℝ E] {N : ℕ} {τ : ℝ} (a : satellite_config E N τ)

-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Rescaling a satellite configuration in a vector space, to put the basepoint at `0` and the base
radius at `1`. -/ def center_and_rescale : satellite_config E N τ :=
{ c := λ i, «expr • »(«expr ⁻¹»(a.r (last N)), «expr - »(a.c i, a.c (last N))),
  r := λ i, «expr * »(«expr ⁻¹»(a.r (last N)), a.r i),
  rpos := λ i, mul_pos (inv_pos.2 (a.rpos _)) (a.rpos _),
  h := λ i j hij, begin
    rcases [expr a.h i j hij, "with", ident H, "|", ident H],
    { left,
      split,
      { rw ["[", expr dist_eq_norm, ",", "<-", expr smul_sub, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg (inv_nonneg.2 (a.rpos _).le), "]"] [],
        refine [expr mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)],
        rw ["[", expr dist_eq_norm, "]"] ["at", ident H],
        convert [] [expr H.1] ["using", 2],
        abel [] [] [] },
      { rw ["[", "<-", expr mul_assoc, ",", expr mul_comm τ, ",", expr mul_assoc, "]"] [],
        refine [expr mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)],
        exact [expr H.2] } },
    { right,
      split,
      { rw ["[", expr dist_eq_norm, ",", "<-", expr smul_sub, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg (inv_nonneg.2 (a.rpos _).le), "]"] [],
        refine [expr mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)],
        rw ["[", expr dist_eq_norm, "]"] ["at", ident H],
        convert [] [expr H.1] ["using", 2],
        abel [] [] [] },
      { rw ["[", "<-", expr mul_assoc, ",", expr mul_comm τ, ",", expr mul_assoc, "]"] [],
        refine [expr mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)],
        exact [expr H.2] } }
  end,
  hlast := λ i hi, begin
    have [ident H] [] [":=", expr a.hlast i hi],
    split,
    { rw ["[", expr dist_eq_norm, ",", "<-", expr smul_sub, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg (inv_nonneg.2 (a.rpos _).le), "]"] [],
      refine [expr mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)],
      rw ["[", expr dist_eq_norm, "]"] ["at", ident H],
      convert [] [expr H.1] ["using", 2],
      abel [] [] [] },
    { rw ["[", "<-", expr mul_assoc, ",", expr mul_comm τ, ",", expr mul_assoc, "]"] [],
      refine [expr mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)],
      exact [expr H.2] }
  end,
  inter := λ i hi, begin
    have [ident H] [] [":=", expr a.inter i hi],
    rw ["[", expr dist_eq_norm, ",", "<-", expr smul_sub, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg (inv_nonneg.2 (a.rpos _).le), ",", "<-", expr mul_add, "]"] [],
    refine [expr mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)],
    rw [expr dist_eq_norm] ["at", ident H],
    convert [] [expr H] ["using", 2],
    abel [] [] []
  end }

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

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any `1`-separated set in the ball of radius `2` has cardinality at most `5 ^ dim`. This is
useful to show that the supremum in the definition of `besicovitch.multiplicity E` is
well behaved. -/
theorem card_le_of_separated
(s : finset E)
(hs : ∀ c «expr ∈ » s, «expr ≤ »(«expr∥ ∥»(c), 2))
(h : ∀
 (c «expr ∈ » s)
 (d «expr ∈ » s), «expr ≠ »(c, d) → «expr ≤ »(1, «expr∥ ∥»(«expr - »(c, d)))) : «expr ≤ »(s.card, «expr ^ »(5, finrank exprℝ() E)) :=
begin
  letI [] [":", expr measurable_space E] [":=", expr borel E],
  letI [] [":", expr borel_space E] [":=", expr ⟨rfl⟩],
  let [ident μ] [":", expr measure E] [":=", expr measure.add_haar],
  let [ident δ] [":", expr exprℝ()] [":=", expr «expr / »((1 : exprℝ()), 2)],
  let [ident ρ] [":", expr exprℝ()] [":=", expr «expr / »((5 : exprℝ()), 2)],
  have [ident ρpos] [":", expr «expr < »(0, ρ)] [":=", expr by norm_num ["[", expr ρ, "]"] []],
  set [] [ident A] [] [":="] [expr «expr⋃ , »((c «expr ∈ » s), ball (c : E) δ)] ["with", ident hA],
  have [ident D] [":", expr set.pairwise (s : set E) «expr on »(disjoint, λ c, ball (c : E) δ)] [],
  { rintros [ident c, ident hc, ident d, ident hd, ident hcd],
    apply [expr ball_disjoint_ball],
    rw [expr dist_eq_norm] [],
    convert [] [expr h c hc d hd hcd] [],
    norm_num [] [] },
  have [ident A_subset] [":", expr «expr ⊆ »(A, ball (0 : E) ρ)] [],
  { refine [expr bUnion_subset (λ x hx, _)],
    apply [expr ball_subset_ball'],
    calc
      «expr ≤ »(«expr + »(δ, dist x 0), «expr + »(δ, 2)) : by { rw [expr dist_zero_right] [],
        exact [expr add_le_add le_rfl (hs x hx)] }
      «expr = »(..., «expr / »(5, 2)) : by norm_num ["[", expr δ, "]"] [] },
  have [ident I] [":", expr «expr ≤ »(«expr * »(«expr * »((s.card : «exprℝ≥0∞»()), ennreal.of_real «expr ^ »(δ, finrank exprℝ() E)), μ (ball 0 1)), «expr * »(ennreal.of_real «expr ^ »(ρ, finrank exprℝ() E), μ (ball 0 1)))] [":=", expr calc
     «expr = »(«expr * »(«expr * »((s.card : «exprℝ≥0∞»()), ennreal.of_real «expr ^ »(δ, finrank exprℝ() E)), μ (ball 0 1)), μ A) : begin
       rw ["[", expr hA, ",", expr measure_bUnion_finset D (λ c hc, measurable_set_ball), "]"] [],
       have [ident I] [":", expr «expr < »(0, δ)] [],
       by norm_num ["[", expr δ, "]"] [],
       simp [] [] ["only"] ["[", expr μ.add_haar_ball_of_pos _ I, ",", expr one_div, ",", expr one_pow, ",", expr finset.sum_const, ",", expr nsmul_eq_mul, ",", expr div_pow, ",", expr mul_assoc, "]"] [] []
     end
     «expr ≤ »(..., μ (ball (0 : E) ρ)) : measure_mono A_subset
     «expr = »(..., «expr * »(ennreal.of_real «expr ^ »(ρ, finrank exprℝ() E), μ (ball 0 1))) : by simp [] [] ["only"] ["[", expr μ.add_haar_ball_of_pos _ ρpos, "]"] [] []],
  have [ident J] [":", expr «expr ≤ »(«expr * »((s.card : «exprℝ≥0∞»()), ennreal.of_real «expr ^ »(δ, finrank exprℝ() E)), ennreal.of_real «expr ^ »(ρ, finrank exprℝ() E))] [":=", expr (ennreal.mul_le_mul_right (μ.add_haar_ball_pos _ zero_lt_one).ne' (μ.add_haar_ball_lt_top _ _).ne).1 I],
  have [ident K] [":", expr «expr ≤ »((s.card : exprℝ()), «expr ^ »((5 : exprℝ()), finrank exprℝ() E))] [],
  by simpa [] [] [] ["[", expr ennreal.to_real_mul, ",", expr div_eq_mul_inv, "]"] [] ["using", expr ennreal.to_real_le_of_le_of_real (pow_nonneg ρpos.le _) J],
  exact_mod_cast [expr K]
end

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

variable (E)

-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
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

variable {E}

theorem card_le_multiplicity_of_δ {s : Finset E} (hs : ∀ c _ : c ∈ s, ∥c∥ ≤ 2)
  (h's : ∀ c _ : c ∈ s d _ : d ∈ s, c ≠ d → 1 - good_δ E ≤ ∥c - d∥) : s.card ≤ multiplicity E :=
  (Classical.some_spec (exists_good_δ E)).2.2 s hs h's

-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
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


-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_normalized_aux1
{N : exprℕ()}
{τ : exprℝ()}
(a : satellite_config E N τ)
(lastr : «expr = »(a.r (last N), 1))
(hτ : «expr ≤ »(1, τ))
(δ : exprℝ())
(hδ1 : «expr ≤ »(τ, «expr + »(1, «expr / »(δ, 4))))
(hδ2 : «expr ≤ »(δ, 1))
(i j : fin N.succ)
(inej : «expr ≠ »(i, j)) : «expr ≤ »(«expr - »(1, δ), «expr∥ ∥»(«expr - »(a.c i, a.c j))) :=
begin
  have [ident ah] [":", expr ∀
   i
   j, «expr ≠ »(i, j) → «expr ∨ »(«expr ∧ »(«expr ≤ »(a.r i, «expr∥ ∥»(«expr - »(a.c i, a.c j))), «expr ≤ »(a.r j, «expr * »(τ, a.r i))), «expr ∧ »(«expr ≤ »(a.r j, «expr∥ ∥»(«expr - »(a.c j, a.c i))), «expr ≤ »(a.r i, «expr * »(τ, a.r j))))] [],
  by simpa [] [] ["only"] ["[", expr dist_eq_norm, "]"] [] ["using", expr a.h],
  have [ident δnonneg] [":", expr «expr ≤ »(0, δ)] [":=", expr by linarith [] ["only"] ["[", expr hτ, ",", expr hδ1, "]"]],
  have [ident D] [":", expr «expr ≤ »(0, «expr - »(1, «expr / »(δ, 4)))] [],
  by linarith [] ["only"] ["[", expr hδ2, "]"],
  have [ident τpos] [":", expr «expr < »(0, τ)] [":=", expr _root_.zero_lt_one.trans_le hτ],
  have [ident I] [":", expr «expr ≤ »(«expr * »(«expr - »(1, «expr / »(δ, 4)), τ), 1)] [":=", expr calc
     «expr ≤ »(«expr * »(«expr - »(1, «expr / »(δ, 4)), τ), «expr * »(«expr - »(1, «expr / »(δ, 4)), «expr + »(1, «expr / »(δ, 4)))) : mul_le_mul_of_nonneg_left hδ1 D
     «expr = »(..., «expr - »(1, «expr / »(«expr ^ »(δ, 2), 16))) : by ring []
     «expr ≤ »(..., 1) : by linarith [] ["only"] ["[", expr sq_nonneg δ, "]"]],
  have [ident J] [":", expr «expr ≤ »(«expr - »(1, δ), «expr - »(1, «expr / »(δ, 4)))] [],
  by linarith [] ["only"] ["[", expr δnonneg, "]"],
  have [ident K] [":", expr «expr ≤ »(«expr - »(1, «expr / »(δ, 4)), «expr ⁻¹»(τ))] [],
  by { rw ["[", expr inv_eq_one_div, ",", expr le_div_iff τpos, "]"] [],
    exact [expr I] },
  suffices [ident L] [":", expr «expr ≤ »(«expr ⁻¹»(τ), «expr∥ ∥»(«expr - »(a.c i, a.c j)))],
  by linarith [] ["only"] ["[", expr J, ",", expr K, ",", expr L, "]"],
  have [ident hτ'] [":", expr ∀ k, «expr ≤ »(«expr ⁻¹»(τ), a.r k)] [],
  { assume [binders (k)],
    rw ["[", expr inv_eq_one_div, ",", expr div_le_iff τpos, ",", "<-", expr lastr, ",", expr mul_comm, "]"] [],
    exact [expr a.hlast' k hτ] },
  rcases [expr ah i j inej, "with", ident H, "|", ident H],
  { apply [expr le_trans _ H.1],
    exact [expr hτ' i] },
  { rw [expr norm_sub_rev] [],
    apply [expr le_trans _ H.1],
    exact [expr hτ' j] }
end

variable [NormedSpace ℝ E]

-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_normalized_aux2
{N : exprℕ()}
{τ : exprℝ()}
(a : satellite_config E N τ)
(lastc : «expr = »(a.c (last N), 0))
(lastr : «expr = »(a.r (last N), 1))
(hτ : «expr ≤ »(1, τ))
(δ : exprℝ())
(hδ1 : «expr ≤ »(τ, «expr + »(1, «expr / »(δ, 4))))
(hδ2 : «expr ≤ »(δ, 1))
(i j : fin N.succ)
(inej : «expr ≠ »(i, j))
(hi : «expr ≤ »(«expr∥ ∥»(a.c i), 2))
(hj : «expr < »(2, «expr∥ ∥»(a.c j))) : «expr ≤ »(«expr - »(1, δ), «expr∥ ∥»(«expr - »(a.c i, «expr • »(«expr / »(2, «expr∥ ∥»(a.c j)), a.c j)))) :=
begin
  have [ident ah] [":", expr ∀
   i
   j, «expr ≠ »(i, j) → «expr ∨ »(«expr ∧ »(«expr ≤ »(a.r i, «expr∥ ∥»(«expr - »(a.c i, a.c j))), «expr ≤ »(a.r j, «expr * »(τ, a.r i))), «expr ∧ »(«expr ≤ »(a.r j, «expr∥ ∥»(«expr - »(a.c j, a.c i))), «expr ≤ »(a.r i, «expr * »(τ, a.r j))))] [],
  by simpa [] [] ["only"] ["[", expr dist_eq_norm, "]"] [] ["using", expr a.h],
  have [ident δnonneg] [":", expr «expr ≤ »(0, δ)] [":=", expr by linarith [] ["only"] ["[", expr hτ, ",", expr hδ1, "]"]],
  have [ident D] [":", expr «expr ≤ »(0, «expr - »(1, «expr / »(δ, 4)))] [],
  by linarith [] ["only"] ["[", expr hδ2, "]"],
  have [ident τpos] [":", expr «expr < »(0, τ)] [":=", expr _root_.zero_lt_one.trans_le hτ],
  have [ident hcrj] [":", expr «expr ≤ »(«expr∥ ∥»(a.c j), «expr + »(a.r j, 1))] [],
  by simpa [] [] ["only"] ["[", expr lastc, ",", expr lastr, ",", expr dist_zero_right, "]"] [] ["using", expr a.inter' j],
  have [ident I] [":", expr «expr ≤ »(a.r i, 2)] [],
  { rcases [expr lt_or_le i (last N), "with", ident H, "|", ident H],
    { apply [expr (a.hlast i H).1.trans],
      simpa [] [] ["only"] ["[", expr dist_eq_norm, ",", expr lastc, ",", expr sub_zero, "]"] [] ["using", expr hi] },
    { have [] [":", expr «expr = »(i, last N)] [":=", expr top_le_iff.1 H],
      rw ["[", expr this, ",", expr lastr, "]"] [],
      exact [expr one_le_two] } },
  have [ident J] [":", expr «expr ≤ »(«expr * »(«expr - »(1, «expr / »(δ, 4)), τ), 1)] [":=", expr calc
     «expr ≤ »(«expr * »(«expr - »(1, «expr / »(δ, 4)), τ), «expr * »(«expr - »(1, «expr / »(δ, 4)), «expr + »(1, «expr / »(δ, 4)))) : mul_le_mul_of_nonneg_left hδ1 D
     «expr = »(..., «expr - »(1, «expr / »(«expr ^ »(δ, 2), 16))) : by ring []
     «expr ≤ »(..., 1) : by linarith [] ["only"] ["[", expr sq_nonneg δ, "]"]],
  have [ident A] [":", expr «expr ≤ »(«expr - »(a.r j, δ), «expr∥ ∥»(«expr - »(a.c i, a.c j)))] [],
  { rcases [expr ah j i inej.symm, "with", ident H, "|", ident H],
    { rw [expr norm_sub_rev] [],
      linarith [] [] ["[", expr H.1, "]"] },
    have [ident C] [":", expr «expr ≤ »(a.r j, 4)] [":=", expr calc
       «expr ≤ »(a.r j, «expr * »(τ, a.r i)) : H.2
       «expr ≤ »(..., «expr * »(τ, 2)) : mul_le_mul_of_nonneg_left I τpos.le
       «expr ≤ »(..., «expr * »(«expr / »(5, 4), 2)) : mul_le_mul_of_nonneg_right (by linarith [] ["only"] ["[", expr hδ1, ",", expr hδ2, "]"]) zero_le_two
       «expr ≤ »(..., 4) : by norm_num [] []],
    calc
      «expr ≤ »(«expr - »(a.r j, δ), «expr - »(a.r j, «expr * »(«expr / »(a.r j, 4), δ))) : begin
        refine [expr sub_le_sub le_rfl _],
        refine [expr mul_le_of_le_one_left δnonneg _],
        linarith [] ["only"] ["[", expr C, "]"]
      end
      «expr = »(..., «expr * »(«expr - »(1, «expr / »(δ, 4)), a.r j)) : by ring []
      «expr ≤ »(..., «expr * »(«expr - »(1, «expr / »(δ, 4)), «expr * »(τ, a.r i))) : mul_le_mul_of_nonneg_left H.2 D
      «expr ≤ »(..., «expr * »(1, a.r i)) : by { rw ["[", "<-", expr mul_assoc, "]"] [],
        apply [expr mul_le_mul_of_nonneg_right J (a.rpos _).le] }
      «expr ≤ »(..., «expr∥ ∥»(«expr - »(a.c i, a.c j))) : by { rw ["[", expr one_mul, "]"] [],
        exact [expr H.1] } },
  set [] [ident d] [] [":="] [expr «expr • »(«expr / »(2, «expr∥ ∥»(a.c j)), a.c j)] ["with", ident hd],
  have [] [":", expr «expr ≤ »(«expr - »(a.r j, δ), «expr + »(«expr∥ ∥»(«expr - »(a.c i, d)), «expr - »(a.r j, 1)))] [":=", expr calc
     «expr ≤ »(«expr - »(a.r j, δ), «expr∥ ∥»(«expr - »(a.c i, a.c j))) : A
     «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr - »(a.c i, d)), «expr∥ ∥»(«expr - »(d, a.c j)))) : by simp [] [] ["only"] ["[", "<-", expr dist_eq_norm, ",", expr dist_triangle, "]"] [] []
     «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr - »(a.c i, d)), «expr - »(a.r j, 1))) : begin
       apply [expr add_le_add_left],
       have [ident A] [":", expr «expr ≤ »(0, «expr - »(1, «expr / »(2, «expr∥ ∥»(a.c j))))] [],
       by simpa [] [] [] ["[", expr div_le_iff (zero_le_two.trans_lt hj), "]"] [] ["using", expr hj.le],
       rw ["[", "<-", expr one_smul exprℝ() (a.c j), ",", expr hd, ",", "<-", expr sub_smul, ",", expr norm_smul, ",", expr norm_sub_rev, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg A, ",", expr sub_mul, "]"] [],
       field_simp [] ["[", expr (zero_le_two.trans_lt hj).ne', "]"] [] [],
       linarith [] ["only"] ["[", expr hcrj, "]"]
     end],
  linarith [] ["only"] ["[", expr this, "]"]
end

-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_normalized_aux3
{N : exprℕ()}
{τ : exprℝ()}
(a : satellite_config E N τ)
(lastc : «expr = »(a.c (last N), 0))
(lastr : «expr = »(a.r (last N), 1))
(hτ : «expr ≤ »(1, τ))
(δ : exprℝ())
(hδ1 : «expr ≤ »(τ, «expr + »(1, «expr / »(δ, 4))))
(i j : fin N.succ)
(inej : «expr ≠ »(i, j))
(hi : «expr < »(2, «expr∥ ∥»(a.c i)))
(hij : «expr ≤ »(«expr∥ ∥»(a.c i), «expr∥ ∥»(a.c j))) : «expr ≤ »(«expr - »(1, δ), «expr∥ ∥»(«expr - »(«expr • »(«expr / »(2, «expr∥ ∥»(a.c i)), a.c i), «expr • »(«expr / »(2, «expr∥ ∥»(a.c j)), a.c j)))) :=
begin
  have [ident ah] [":", expr ∀
   i
   j, «expr ≠ »(i, j) → «expr ∨ »(«expr ∧ »(«expr ≤ »(a.r i, «expr∥ ∥»(«expr - »(a.c i, a.c j))), «expr ≤ »(a.r j, «expr * »(τ, a.r i))), «expr ∧ »(«expr ≤ »(a.r j, «expr∥ ∥»(«expr - »(a.c j, a.c i))), «expr ≤ »(a.r i, «expr * »(τ, a.r j))))] [],
  by simpa [] [] ["only"] ["[", expr dist_eq_norm, "]"] [] ["using", expr a.h],
  have [ident δnonneg] [":", expr «expr ≤ »(0, δ)] [":=", expr by linarith [] ["only"] ["[", expr hτ, ",", expr hδ1, "]"]],
  have [ident τpos] [":", expr «expr < »(0, τ)] [":=", expr _root_.zero_lt_one.trans_le hτ],
  have [ident hcrj] [":", expr «expr ≤ »(«expr∥ ∥»(a.c j), «expr + »(a.r j, 1))] [],
  by simpa [] [] ["only"] ["[", expr lastc, ",", expr lastr, ",", expr dist_zero_right, "]"] [] ["using", expr a.inter' j],
  have [ident A] [":", expr «expr ≤ »(a.r i, «expr∥ ∥»(a.c i))] [],
  { have [] [":", expr «expr < »(i, last N)] [],
    { apply [expr lt_top_iff_ne_top.2],
      assume [binders (iN)],
      change [expr «expr = »(i, last N)] [] ["at", ident iN],
      rw ["[", expr iN, ",", expr lastc, ",", expr norm_zero, "]"] ["at", ident hi],
      exact [expr lt_irrefl _ (zero_le_two.trans_lt hi)] },
    convert [] [expr (a.hlast i this).1] [],
    rw ["[", expr dist_eq_norm, ",", expr lastc, ",", expr sub_zero, "]"] [] },
  have [ident hj] [":", expr «expr < »(2, «expr∥ ∥»(a.c j))] [":=", expr hi.trans_le hij],
  set [] [ident s] [] [":="] [expr «expr∥ ∥»(a.c i)] ["with", ident hs],
  have [ident spos] [":", expr «expr < »(0, s)] [":=", expr zero_lt_two.trans hi],
  set [] [ident d] [] [":="] [expr «expr • »(«expr / »(s, «expr∥ ∥»(a.c j)), a.c j)] ["with", ident hd],
  have [ident I] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(a.c j, a.c i)), «expr + »(«expr - »(«expr∥ ∥»(a.c j), s), «expr∥ ∥»(«expr - »(d, a.c i))))] [":=", expr calc
     «expr ≤ »(«expr∥ ∥»(«expr - »(a.c j, a.c i)), «expr + »(«expr∥ ∥»(«expr - »(a.c j, d)), «expr∥ ∥»(«expr - »(d, a.c i)))) : by simp [] [] [] ["[", "<-", expr dist_eq_norm, ",", expr dist_triangle, "]"] [] []
     «expr = »(..., «expr + »(«expr - »(«expr∥ ∥»(a.c j), «expr∥ ∥»(a.c i)), «expr∥ ∥»(«expr - »(d, a.c i)))) : begin
       nth_rewrite [0] ["<-", expr one_smul exprℝ() (a.c j)] [],
       rw ["[", expr add_left_inj, ",", expr hd, ",", "<-", expr sub_smul, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg, ",", expr sub_mul, ",", expr one_mul, ",", expr div_mul_cancel _ (zero_le_two.trans_lt hj).ne', "]"] [],
       rwa ["[", expr sub_nonneg, ",", expr div_le_iff (zero_lt_two.trans hj), ",", expr one_mul, "]"] []
     end],
  have [ident J] [":", expr «expr ≤ »(«expr - »(a.r j, «expr∥ ∥»(«expr - »(a.c j, a.c i))), «expr * »(«expr / »(s, 2), δ))] [":=", expr calc
     «expr ≤ »(«expr - »(a.r j, «expr∥ ∥»(«expr - »(a.c j, a.c i))), «expr * »(s, «expr - »(τ, 1))) : begin
       rcases [expr ah j i inej.symm, "with", ident H, "|", ident H],
       { calc
           «expr ≤ »(«expr - »(a.r j, «expr∥ ∥»(«expr - »(a.c j, a.c i))), 0) : sub_nonpos.2 H.1
           «expr ≤ »(..., «expr * »(s, «expr - »(τ, 1))) : mul_nonneg spos.le (sub_nonneg.2 hτ) },
       { rw [expr norm_sub_rev] ["at", ident H],
         calc
           «expr ≤ »(«expr - »(a.r j, «expr∥ ∥»(«expr - »(a.c j, a.c i))), «expr - »(«expr * »(τ, a.r i), a.r i)) : sub_le_sub H.2 H.1
           «expr = »(..., «expr * »(a.r i, «expr - »(τ, 1))) : by ring []
           «expr ≤ »(..., «expr * »(s, «expr - »(τ, 1))) : mul_le_mul_of_nonneg_right A (sub_nonneg.2 hτ) }
     end
     «expr ≤ »(..., «expr * »(s, «expr / »(δ, 2))) : mul_le_mul_of_nonneg_left (by linarith [] ["only"] ["[", expr δnonneg, ",", expr hδ1, "]"]) spos.le
     «expr = »(..., «expr * »(«expr / »(s, 2), δ)) : by ring []],
  have [ident invs_nonneg] [":", expr «expr ≤ »(0, «expr / »(2, s))] [":=", expr div_nonneg zero_le_two (zero_le_two.trans hi.le)],
  calc
    «expr = »(«expr - »(1, δ), «expr * »(«expr / »(2, s), «expr - »(«expr / »(s, 2), «expr * »(«expr / »(s, 2), δ)))) : by { field_simp [] ["[", expr spos.ne', "]"] [] [],
      ring [] }
    «expr ≤ »(..., «expr * »(«expr / »(2, s), «expr∥ ∥»(«expr - »(d, a.c i)))) : mul_le_mul_of_nonneg_left (by linarith [] ["only"] ["[", expr hcrj, ",", expr I, ",", expr J, ",", expr hi, "]"]) invs_nonneg
    «expr = »(..., «expr∥ ∥»(«expr - »(«expr • »(«expr / »(2, s), a.c i), «expr • »(«expr / »(2, «expr∥ ∥»(a.c j)), a.c j)))) : begin
      conv_lhs [] [] { rw ["[", expr norm_sub_rev, ",", "<-", expr abs_of_nonneg invs_nonneg, "]"] },
      rw ["[", "<-", expr real.norm_eq_abs, ",", "<-", expr norm_smul, ",", expr smul_sub, ",", expr hd, ",", expr smul_smul, "]"] [],
      congr' [3] [],
      field_simp [] ["[", expr spos.ne', "]"] [] []
    end
end

-- error in MeasureTheory.Covering.BesicovitchVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_normalized
{N : exprℕ()}
{τ : exprℝ()}
(a : satellite_config E N τ)
(lastc : «expr = »(a.c (last N), 0))
(lastr : «expr = »(a.r (last N), 1))
(hτ : «expr ≤ »(1, τ))
(δ : exprℝ())
(hδ1 : «expr ≤ »(τ, «expr + »(1, «expr / »(δ, 4))))
(hδ2 : «expr ≤ »(δ, 1)) : «expr∃ , »((c' : fin N.succ → E), «expr ∧ »(∀
  n, «expr ≤ »(«expr∥ ∥»(c' n), 2), ∀
  i j, «expr ≠ »(i, j) → «expr ≤ »(«expr - »(1, δ), «expr∥ ∥»(«expr - »(c' i, c' j))))) :=
begin
  let [ident c'] [":", expr fin N.succ → E] [":=", expr λ
   i, if «expr ≤ »(«expr∥ ∥»(a.c i), 2) then a.c i else «expr • »(«expr / »(2, «expr∥ ∥»(a.c i)), a.c i)],
  have [ident norm_c'_le] [":", expr ∀ i, «expr ≤ »(«expr∥ ∥»(c' i), 2)] [],
  { assume [binders (i)],
    simp [] [] ["only"] ["[", expr c', "]"] [] [],
    split_ifs [] [],
    { exact [expr h] },
    by_cases [expr hi, ":", expr «expr = »(«expr∥ ∥»(a.c i), 0)]; field_simp [] ["[", expr norm_smul, ",", expr hi, "]"] [] [] },
  refine [expr ⟨c', λ n, norm_c'_le n, λ i j inej, _⟩],
  wlog [ident hij] [":", expr «expr ≤ »(«expr∥ ∥»(a.c i), «expr∥ ∥»(a.c j))] [":=", expr le_total «expr∥ ∥»(a.c i) «expr∥ ∥»(a.c j)] ["using", "[", ident i, ident j, ",", ident j, ident i, "]"] tactic.skip,
  swap,
  { assume [binders (i_ne_j)],
    rw [expr norm_sub_rev] [],
    exact [expr this i_ne_j.symm] },
  rcases [expr le_or_lt «expr∥ ∥»(a.c j) 2, "with", ident Hj, "|", ident Hj],
  { simp_rw ["[", expr c', ",", expr Hj, ",", expr hij.trans Hj, ",", expr if_true, "]"] [],
    exact [expr exists_normalized_aux1 a lastr hτ δ hδ1 hδ2 i j inej] },
  { have [ident H'j] [":", expr «expr ↔ »(«expr ≤ »(«expr∥ ∥»(a.c j), 2), false)] [],
    by simpa [] [] ["only"] ["[", expr not_le, ",", expr iff_false, "]"] [] ["using", expr Hj],
    rcases [expr le_or_lt «expr∥ ∥»(a.c i) 2, "with", ident Hi, "|", ident Hi],
    { simp_rw ["[", expr c', ",", expr Hi, ",", expr if_true, ",", expr H'j, ",", expr if_false, "]"] [],
      exact [expr exists_normalized_aux2 a lastc lastr hτ δ hδ1 hδ2 i j inej Hi Hj] },
    { have [ident H'i] [":", expr «expr ↔ »(«expr ≤ »(«expr∥ ∥»(a.c i), 2), false)] [],
      by simpa [] [] ["only"] ["[", expr not_le, ",", expr iff_false, "]"] [] ["using", expr Hi],
      simp_rw ["[", expr c', ",", expr H'i, ",", expr if_false, ",", expr H'j, ",", expr if_false, "]"] [],
      exact [expr exists_normalized_aux3 a lastc lastr hτ δ hδ1 i j inej Hi hij] } }
end

end SatelliteConfig

variable (E) [NormedSpace ℝ E] [FiniteDimensional ℝ E]

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

