import Mathbin.Analysis.Calculus.MeanValue

/-!
# L'Hôpital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hopital's rule" for computing 0/0
indeterminate forms. The proof of `has_deriv_at.lhopital_zero_right_on_Ioo`
is based on the one given in the corresponding
[Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule)
chapter, and all other statements are derived from this one by composing by
carefully chosen functions.

Note that the filter `f'/g'` tends to isn't required to be one of `𝓝 a`,
`at_top` or `at_bot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `ℝ`.

Each statement is available in a `has_deriv_at` form and a `deriv` form, which
is denoted by each statement being in either the `has_deriv_at` or the `deriv`
namespace.

## Tags

L'Hôpital's rule, L'Hopital's rule
-/


open Filter Set

open_locale Filter TopologicalSpace Pointwise

variable{a b : ℝ}(hab : a < b){l : Filter ℝ}{f f' g g' : ℝ → ℝ}

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' ≠ 0`) have
to be satisfied on an explicitly-provided interval.
-/


namespace HasDerivAt

include hab

theorem lhopital_zero_right_on_Ioo (hff' : ∀ x _ : x ∈ Ioo a b, HasDerivAt f (f' x) x)
  (hgg' : ∀ x _ : x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x _ : x ∈ Ioo a b, g' x ≠ 0)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 0)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 0))
  (hdiv : tendsto (fun x => f' x / g' x) (𝓝[Ioi a] a) l) : tendsto (fun x => f x / g x) (𝓝[Ioi a] a) l :=
  by 
    have sub : ∀ x _ : x ∈ Ioo a b, Ioo a x ⊆ Ioo a b := fun x hx => Ioo_subset_Ioo (le_reflₓ a) (le_of_ltₓ hx.2)
    have hg : ∀ x _ : x ∈ Ioo a b, g x ≠ 0
    ·
      intro x hx h 
      have  : tendsto g (𝓝[Iio x] x) (𝓝 0)
      ·
        rw [←h, ←nhds_within_Ioo_eq_nhds_within_Iio hx.1]
        exact ((hgg' x hx).ContinuousAt.ContinuousWithinAt.mono$ sub x hx).Tendsto 
      obtain ⟨y, hyx, hy⟩ : ∃ (c : _)(_ : c ∈ Ioo a x), g' c = 0 
      exact exists_has_deriv_at_eq_zero' hx.1 hga this fun y hy => hgg' y$ sub x hx hy 
      exact hg' y (sub x hx hyx) hy 
    have  : ∀ x _ : x ∈ Ioo a b, ∃ (c : _)(_ : c ∈ Ioo a x), (f x*g' c) = g x*f' c
    ·
      intro x hx 
      rw [←sub_zero (f x), ←sub_zero (g x)]
      exact
        exists_ratio_has_deriv_at_eq_ratio_slope' g g' hx.1 f f' (fun y hy => hgg' y$ sub x hx hy)
          (fun y hy => hff' y$ sub x hx hy) hga hfa
          (tendsto_nhds_within_of_tendsto_nhds (hgg' x hx).ContinuousAt.Tendsto)
          (tendsto_nhds_within_of_tendsto_nhds (hff' x hx).ContinuousAt.Tendsto)
    choose! c hc using this 
    have  : ∀ x _ : x ∈ Ioo a b, ((fun x' => f' x' / g' x') ∘ c) x = f x / g x
    ·
      intro x hx 
      rcases hc x hx with ⟨h₁, h₂⟩
      fieldSimp [hg x hx, hg' (c x) ((sub x hx) h₁)]
      simp only [h₂]
      rwa [mul_commₓ]
    have cmp : ∀ x _ : x ∈ Ioo a b, a < c x ∧ c x < x 
    exact fun x hx => (hc x hx).1
    rw [←nhds_within_Ioo_eq_nhds_within_Ioi hab]
    apply tendsto_nhds_within_congr this 
    simp only 
    apply hdiv.comp 
    refine'
      tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
        (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_nhds_within_of_tendsto_nhds tendsto_id)
          _ _)
        _ 
    all_goals 
      apply eventually_nhds_with_of_forall 
      intro x hx 
      have  := cmp x hx 
      try 
        simp 
      linarith [this]

theorem lhopital_zero_right_on_Ico (hff' : ∀ x _ : x ∈ Ioo a b, HasDerivAt f (f' x) x)
  (hgg' : ∀ x _ : x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ico a b)) (hcg : ContinuousOn g (Ico a b))
  (hg' : ∀ x _ : x ∈ Ioo a b, g' x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
  (hdiv : tendsto (fun x => f' x / g' x) (nhdsWithin a (Ioi a)) l) :
  tendsto (fun x => f x / g x) (nhdsWithin a (Ioi a)) l :=
  by 
    refine' lhopital_zero_right_on_Ioo hab hff' hgg' hg' _ _ hdiv
    ·
      rw [←hfa, ←nhds_within_Ioo_eq_nhds_within_Ioi hab]
      exact ((hcf a$ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto
    ·
      rw [←hga, ←nhds_within_Ioo_eq_nhds_within_Ioi hab]
      exact ((hcg a$ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto

theorem lhopital_zero_left_on_Ioo (hff' : ∀ x _ : x ∈ Ioo a b, HasDerivAt f (f' x) x)
  (hgg' : ∀ x _ : x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x _ : x ∈ Ioo a b, g' x ≠ 0)
  (hfb : tendsto f (nhdsWithin b (Iio b)) (𝓝 0)) (hgb : tendsto g (nhdsWithin b (Iio b)) (𝓝 0))
  (hdiv : tendsto (fun x => f' x / g' x) (nhdsWithin b (Iio b)) l) :
  tendsto (fun x => f x / g x) (nhdsWithin b (Iio b)) l :=
  by 
    have hdnf : ∀ x _ : x ∈ -Ioo a b, HasDerivAt (f ∘ Neg.neg) (f' (-x)*-1) x 
    exact fun x hx => comp x (hff' (-x) hx) (has_deriv_at_neg x)
    have hdng : ∀ x _ : x ∈ -Ioo a b, HasDerivAt (g ∘ Neg.neg) (g' (-x)*-1) x 
    exact fun x hx => comp x (hgg' (-x) hx) (has_deriv_at_neg x)
    rw [preimage_neg_Ioo] at hdnf 
    rw [preimage_neg_Ioo] at hdng 
    have  :=
      lhopital_zero_right_on_Ioo (neg_lt_neg hab) hdnf hdng
        (by 
          intro x hx h 
          apply
            hg' _
              (by 
                rw [←preimage_neg_Ioo] at hx 
                exact hx)
          rwa [mul_commₓ, ←neg_eq_neg_one_mul, neg_eq_zero] at h)
        (hfb.comp tendsto_neg_nhds_within_Ioi_neg) (hgb.comp tendsto_neg_nhds_within_Ioi_neg)
        (by 
          simp only [neg_div_neg_eq, mul_oneₓ, mul_neg_eq_neg_mul_symm]
          exact (tendsto_congr$ fun x => rfl).mp (hdiv.comp tendsto_neg_nhds_within_Ioi_neg))
    have  := this.comp tendsto_neg_nhds_within_Iio 
    unfold Function.comp  at this 
    simpa only [neg_negₓ]

theorem lhopital_zero_left_on_Ioc (hff' : ∀ x _ : x ∈ Ioo a b, HasDerivAt f (f' x) x)
  (hgg' : ∀ x _ : x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ioc a b)) (hcg : ContinuousOn g (Ioc a b))
  (hg' : ∀ x _ : x ∈ Ioo a b, g' x ≠ 0) (hfb : f b = 0) (hgb : g b = 0)
  (hdiv : tendsto (fun x => f' x / g' x) (nhdsWithin b (Iio b)) l) :
  tendsto (fun x => f x / g x) (nhdsWithin b (Iio b)) l :=
  by 
    refine' lhopital_zero_left_on_Ioo hab hff' hgg' hg' _ _ hdiv
    ·
      rw [←hfb, ←nhds_within_Ioo_eq_nhds_within_Iio hab]
      exact ((hcf b$ right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).Tendsto
    ·
      rw [←hgb, ←nhds_within_Ioo_eq_nhds_within_Iio hab]
      exact ((hcg b$ right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).Tendsto

omit hab

theorem lhopital_zero_at_top_on_Ioi (hff' : ∀ x _ : x ∈ Ioi a, HasDerivAt f (f' x) x)
  (hgg' : ∀ x _ : x ∈ Ioi a, HasDerivAt g (g' x) x) (hg' : ∀ x _ : x ∈ Ioi a, g' x ≠ 0) (hftop : tendsto f at_top (𝓝 0))
  (hgtop : tendsto g at_top (𝓝 0)) (hdiv : tendsto (fun x => f' x / g' x) at_top l) :
  tendsto (fun x => f x / g x) at_top l :=
  by 
    obtain ⟨a', haa', ha'⟩ : ∃ a', a < a' ∧ 0 < a' :=
      ⟨1+max a 0,
        ⟨lt_of_le_of_ltₓ (le_max_leftₓ a 0) (lt_one_add _), lt_of_le_of_ltₓ (le_max_rightₓ a 0) (lt_one_add _)⟩⟩
    have fact1 : ∀ x : ℝ, x ∈ Ioo 0 (a'⁻¹) → x ≠ 0 := fun _ hx => (ne_of_ltₓ hx.1).symm 
    have fact2 : ∀ x _ : x ∈ Ioo 0 (a'⁻¹), a < x⁻¹
    exact fun _ hx => lt_transₓ haa' ((lt_inv ha' hx.1).mpr hx.2)
    have hdnf : ∀ x _ : x ∈ Ioo 0 (a'⁻¹), HasDerivAt (f ∘ HasInv.inv) (f' (x⁻¹)*-(x^2)⁻¹) x 
    exact fun x hx => comp x (hff' (x⁻¹)$ fact2 x hx) (has_deriv_at_inv$ fact1 x hx)
    have hdng : ∀ x _ : x ∈ Ioo 0 (a'⁻¹), HasDerivAt (g ∘ HasInv.inv) (g' (x⁻¹)*-(x^2)⁻¹) x 
    exact fun x hx => comp x (hgg' (x⁻¹)$ fact2 x hx) (has_deriv_at_inv$ fact1 x hx)
    have  :=
      lhopital_zero_right_on_Ioo (inv_pos.mpr ha') hdnf hdng
        (by 
          intro x hx 
          refine' mul_ne_zero _ (neg_ne_zero.mpr$ inv_ne_zero$ pow_ne_zero _$ fact1 x hx)
          exact hg' _ (fact2 x hx))
        (hftop.comp tendsto_inv_zero_at_top) (hgtop.comp tendsto_inv_zero_at_top)
        (by 
          refine' (tendsto_congr' _).mp (hdiv.comp tendsto_inv_zero_at_top)
          rw [eventually_eq_iff_exists_mem]
          use Ioi 0, self_mem_nhds_within 
          intro x hx 
          unfold Function.comp 
          erw [mul_div_mul_right]
          refine' neg_ne_zero.mpr (inv_ne_zero$ pow_ne_zero _$ ne_of_gtₓ hx))
    have  := this.comp tendsto_inv_at_top_zero' 
    unfold Function.comp  at this 
    simpa only [inv_inv₀]

theorem lhopital_zero_at_bot_on_Iio (hff' : ∀ x _ : x ∈ Iio a, HasDerivAt f (f' x) x)
  (hgg' : ∀ x _ : x ∈ Iio a, HasDerivAt g (g' x) x) (hg' : ∀ x _ : x ∈ Iio a, g' x ≠ 0) (hfbot : tendsto f at_bot (𝓝 0))
  (hgbot : tendsto g at_bot (𝓝 0)) (hdiv : tendsto (fun x => f' x / g' x) at_bot l) :
  tendsto (fun x => f x / g x) at_bot l :=
  by 
    have hdnf : ∀ x _ : x ∈ -Iio a, HasDerivAt (f ∘ Neg.neg) (f' (-x)*-1) x 
    exact fun x hx => comp x (hff' (-x) hx) (has_deriv_at_neg x)
    have hdng : ∀ x _ : x ∈ -Iio a, HasDerivAt (g ∘ Neg.neg) (g' (-x)*-1) x 
    exact fun x hx => comp x (hgg' (-x) hx) (has_deriv_at_neg x)
    rw [preimage_neg_Iio] at hdnf 
    rw [preimage_neg_Iio] at hdng 
    have  :=
      lhopital_zero_at_top_on_Ioi hdnf hdng
        (by 
          intro x hx h 
          apply
            hg' _
              (by 
                rw [←preimage_neg_Iio] at hx 
                exact hx)
          rwa [mul_commₓ, ←neg_eq_neg_one_mul, neg_eq_zero] at h)
        (hfbot.comp tendsto_neg_at_top_at_bot) (hgbot.comp tendsto_neg_at_top_at_bot)
        (by 
          simp only [mul_oneₓ, mul_neg_eq_neg_mul_symm, neg_div_neg_eq]
          exact (tendsto_congr$ fun x => rfl).mp (hdiv.comp tendsto_neg_at_top_at_bot))
    have  := this.comp tendsto_neg_at_bot_at_top 
    unfold Function.comp  at this 
    simpa only [neg_negₓ]

end HasDerivAt

namespace deriv

include hab

theorem lhopital_zero_right_on_Ioo (hdf : DifferentiableOn ℝ f (Ioo a b)) (hg' : ∀ x _ : x ∈ Ioo a b, deriv g x ≠ 0)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 0)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[Ioi a] a) l) : tendsto (fun x => f x / g x) (𝓝[Ioi a] a) l :=
  by 
    have hdf : ∀ x _ : x ∈ Ioo a b, DifferentiableAt ℝ f x 
    exact fun x hx => (hdf x hx).DifferentiableAt (Ioo_mem_nhds hx.1 hx.2)
    have hdg : ∀ x _ : x ∈ Ioo a b, DifferentiableAt ℝ g x 
    exact fun x hx => Classical.by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiable_at h)
    exact
      HasDerivAt.lhopital_zero_right_on_Ioo hab (fun x hx => (hdf x hx).HasDerivAt) (fun x hx => (hdg x hx).HasDerivAt)
        hg' hfa hga hdiv

theorem lhopital_zero_right_on_Ico (hdf : DifferentiableOn ℝ f (Ioo a b)) (hcf : ContinuousOn f (Ico a b))
  (hcg : ContinuousOn g (Ico a b)) (hg' : ∀ x _ : x ∈ Ioo a b, (deriv g) x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) (nhdsWithin a (Ioi a)) l) :
  tendsto (fun x => f x / g x) (nhdsWithin a (Ioi a)) l :=
  by 
    refine' lhopital_zero_right_on_Ioo hab hdf hg' _ _ hdiv
    ·
      rw [←hfa, ←nhds_within_Ioo_eq_nhds_within_Ioi hab]
      exact ((hcf a$ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto
    ·
      rw [←hga, ←nhds_within_Ioo_eq_nhds_within_Ioi hab]
      exact ((hcg a$ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto

theorem lhopital_zero_left_on_Ioo (hdf : DifferentiableOn ℝ f (Ioo a b)) (hg' : ∀ x _ : x ∈ Ioo a b, (deriv g) x ≠ 0)
  (hfb : tendsto f (nhdsWithin b (Iio b)) (𝓝 0)) (hgb : tendsto g (nhdsWithin b (Iio b)) (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) (nhdsWithin b (Iio b)) l) :
  tendsto (fun x => f x / g x) (nhdsWithin b (Iio b)) l :=
  by 
    have hdf : ∀ x _ : x ∈ Ioo a b, DifferentiableAt ℝ f x 
    exact fun x hx => (hdf x hx).DifferentiableAt (Ioo_mem_nhds hx.1 hx.2)
    have hdg : ∀ x _ : x ∈ Ioo a b, DifferentiableAt ℝ g x 
    exact fun x hx => Classical.by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiable_at h)
    exact
      HasDerivAt.lhopital_zero_left_on_Ioo hab (fun x hx => (hdf x hx).HasDerivAt) (fun x hx => (hdg x hx).HasDerivAt)
        hg' hfb hgb hdiv

omit hab

theorem lhopital_zero_at_top_on_Ioi (hdf : DifferentiableOn ℝ f (Ioi a)) (hg' : ∀ x _ : x ∈ Ioi a, (deriv g) x ≠ 0)
  (hftop : tendsto f at_top (𝓝 0)) (hgtop : tendsto g at_top (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) at_top l) : tendsto (fun x => f x / g x) at_top l :=
  by 
    have hdf : ∀ x _ : x ∈ Ioi a, DifferentiableAt ℝ f x 
    exact fun x hx => (hdf x hx).DifferentiableAt (Ioi_mem_nhds hx)
    have hdg : ∀ x _ : x ∈ Ioi a, DifferentiableAt ℝ g x 
    exact fun x hx => Classical.by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiable_at h)
    exact
      HasDerivAt.lhopital_zero_at_top_on_Ioi (fun x hx => (hdf x hx).HasDerivAt) (fun x hx => (hdg x hx).HasDerivAt) hg'
        hftop hgtop hdiv

theorem lhopital_zero_at_bot_on_Iio (hdf : DifferentiableOn ℝ f (Iio a)) (hg' : ∀ x _ : x ∈ Iio a, (deriv g) x ≠ 0)
  (hfbot : tendsto f at_bot (𝓝 0)) (hgbot : tendsto g at_bot (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) at_bot l) : tendsto (fun x => f x / g x) at_bot l :=
  by 
    have hdf : ∀ x _ : x ∈ Iio a, DifferentiableAt ℝ f x 
    exact fun x hx => (hdf x hx).DifferentiableAt (Iio_mem_nhds hx)
    have hdg : ∀ x _ : x ∈ Iio a, DifferentiableAt ℝ g x 
    exact fun x hx => Classical.by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiable_at h)
    exact
      HasDerivAt.lhopital_zero_at_bot_on_Iio (fun x hx => (hdf x hx).HasDerivAt) (fun x hx => (hdg x hx).HasDerivAt) hg'
        hfbot hgbot hdiv

end deriv

/-!
## Generic versions

The following statements no longer any explicit interval, as they only require
conditions holding eventually.
-/


namespace HasDerivAt

/-- L'Hôpital's rule for approaching a real from the right, `has_deriv_at` version -/
theorem lhopital_zero_nhds_right (hff' : ∀ᶠx in 𝓝[Ioi a] a, HasDerivAt f (f' x) x)
  (hgg' : ∀ᶠx in 𝓝[Ioi a] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠx in 𝓝[Ioi a] a, g' x ≠ 0)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 0)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 0))
  (hdiv : tendsto (fun x => f' x / g' x) (𝓝[Ioi a] a) l) : tendsto (fun x => f x / g x) (𝓝[Ioi a] a) l :=
  by 
    rw [eventually_iff_exists_mem] at *
    rcases hff' with ⟨s₁, hs₁, hff'⟩
    rcases hgg' with ⟨s₂, hs₂, hgg'⟩
    rcases hg' with ⟨s₃, hs₃, hg'⟩
    let s := s₁ ∩ s₂ ∩ s₃ 
    have hs : s ∈ 𝓝[Ioi a] a := inter_mem (inter_mem hs₁ hs₂) hs₃ 
    rw [mem_nhds_within_Ioi_iff_exists_Ioo_subset] at hs 
    rcases hs with ⟨u, hau, hu⟩
    refine' lhopital_zero_right_on_Ioo hau _ _ _ hfa hga hdiv <;>
      intro x hx <;>
        applyAssumption <;>
          first |
            exact (hu hx).1.1|
            exact (hu hx).1.2|
            exact (hu hx).2

/-- L'Hôpital's rule for approaching a real from the left, `has_deriv_at` version -/
theorem lhopital_zero_nhds_left (hff' : ∀ᶠx in 𝓝[Iio a] a, HasDerivAt f (f' x) x)
  (hgg' : ∀ᶠx in 𝓝[Iio a] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠx in 𝓝[Iio a] a, g' x ≠ 0)
  (hfa : tendsto f (𝓝[Iio a] a) (𝓝 0)) (hga : tendsto g (𝓝[Iio a] a) (𝓝 0))
  (hdiv : tendsto (fun x => f' x / g' x) (𝓝[Iio a] a) l) : tendsto (fun x => f x / g x) (𝓝[Iio a] a) l :=
  by 
    rw [eventually_iff_exists_mem] at *
    rcases hff' with ⟨s₁, hs₁, hff'⟩
    rcases hgg' with ⟨s₂, hs₂, hgg'⟩
    rcases hg' with ⟨s₃, hs₃, hg'⟩
    let s := s₁ ∩ s₂ ∩ s₃ 
    have hs : s ∈ 𝓝[Iio a] a := inter_mem (inter_mem hs₁ hs₂) hs₃ 
    rw [mem_nhds_within_Iio_iff_exists_Ioo_subset] at hs 
    rcases hs with ⟨l, hal, hl⟩
    refine' lhopital_zero_left_on_Ioo hal _ _ _ hfa hga hdiv <;>
      intro x hx <;>
        applyAssumption <;>
          first |
            exact (hl hx).1.1|
            exact (hl hx).1.2|
            exact (hl hx).2

/-- L'Hôpital's rule for approaching a real, `has_deriv_at` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds' (hff' : ∀ᶠx in 𝓝[univ \ {a}] a, HasDerivAt f (f' x) x)
  (hgg' : ∀ᶠx in 𝓝[univ \ {a}] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠx in 𝓝[univ \ {a}] a, g' x ≠ 0)
  (hfa : tendsto f (𝓝[univ \ {a}] a) (𝓝 0)) (hga : tendsto g (𝓝[univ \ {a}] a) (𝓝 0))
  (hdiv : tendsto (fun x => f' x / g' x) (𝓝[univ \ {a}] a) l) : tendsto (fun x => f x / g x) (𝓝[univ \ {a}] a) l :=
  by 
    have  : univ \ {a} = Iio a ∪ Ioi a
    ·
      ext 
      rw [mem_diff_singleton, eq_true_intro$ mem_univ x, true_andₓ, ne_iff_lt_or_gtₓ]
      rfl 
    simp only [this, nhds_within_union, tendsto_sup, eventually_sup] at *
    exact
      ⟨lhopital_zero_nhds_left hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1,
        lhopital_zero_nhds_right hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2⟩

/-- **L'Hôpital's rule** for approaching a real, `has_deriv_at` version -/
theorem lhopital_zero_nhds (hff' : ∀ᶠx in 𝓝 a, HasDerivAt f (f' x) x) (hgg' : ∀ᶠx in 𝓝 a, HasDerivAt g (g' x) x)
  (hg' : ∀ᶠx in 𝓝 a, g' x ≠ 0) (hfa : tendsto f (𝓝 a) (𝓝 0)) (hga : tendsto g (𝓝 a) (𝓝 0))
  (hdiv : tendsto (fun x => f' x / g' x) (𝓝 a) l) : tendsto (fun x => f x / g x) (𝓝[univ \ {a}] a) l :=
  by 
    apply @lhopital_zero_nhds' _ _ _ f' _ g' <;>
      first |
          apply eventually_nhds_within_of_eventually_nhds|
          apply tendsto_nhds_within_of_tendsto_nhds <;>
        assumption

/-- L'Hôpital's rule for approaching +∞, `has_deriv_at` version -/
theorem lhopital_zero_at_top (hff' : ∀ᶠx in at_top, HasDerivAt f (f' x) x) (hgg' : ∀ᶠx in at_top, HasDerivAt g (g' x) x)
  (hg' : ∀ᶠx in at_top, g' x ≠ 0) (hftop : tendsto f at_top (𝓝 0)) (hgtop : tendsto g at_top (𝓝 0))
  (hdiv : tendsto (fun x => f' x / g' x) at_top l) : tendsto (fun x => f x / g x) at_top l :=
  by 
    rw [eventually_iff_exists_mem] at *
    rcases hff' with ⟨s₁, hs₁, hff'⟩
    rcases hgg' with ⟨s₂, hs₂, hgg'⟩
    rcases hg' with ⟨s₃, hs₃, hg'⟩
    let s := s₁ ∩ s₂ ∩ s₃ 
    have hs : s ∈ at_top := inter_mem (inter_mem hs₁ hs₂) hs₃ 
    rw [mem_at_top_sets] at hs 
    rcases hs with ⟨l, hl⟩
    have hl' : Ioi l ⊆ s := fun x hx => hl x (le_of_ltₓ hx)
    refine' lhopital_zero_at_top_on_Ioi _ _ (fun x hx => hg' x$ (hl' hx).2) hftop hgtop hdiv <;>
      intro x hx <;>
        applyAssumption <;>
          first |
            exact (hl' hx).1.1|
            exact (hl' hx).1.2

/-- L'Hôpital's rule for approaching -∞, `has_deriv_at` version -/
theorem lhopital_zero_at_bot (hff' : ∀ᶠx in at_bot, HasDerivAt f (f' x) x) (hgg' : ∀ᶠx in at_bot, HasDerivAt g (g' x) x)
  (hg' : ∀ᶠx in at_bot, g' x ≠ 0) (hfbot : tendsto f at_bot (𝓝 0)) (hgbot : tendsto g at_bot (𝓝 0))
  (hdiv : tendsto (fun x => f' x / g' x) at_bot l) : tendsto (fun x => f x / g x) at_bot l :=
  by 
    rw [eventually_iff_exists_mem] at *
    rcases hff' with ⟨s₁, hs₁, hff'⟩
    rcases hgg' with ⟨s₂, hs₂, hgg'⟩
    rcases hg' with ⟨s₃, hs₃, hg'⟩
    let s := s₁ ∩ s₂ ∩ s₃ 
    have hs : s ∈ at_bot := inter_mem (inter_mem hs₁ hs₂) hs₃ 
    rw [mem_at_bot_sets] at hs 
    rcases hs with ⟨l, hl⟩
    have hl' : Iio l ⊆ s := fun x hx => hl x (le_of_ltₓ hx)
    refine' lhopital_zero_at_bot_on_Iio _ _ (fun x hx => hg' x$ (hl' hx).2) hfbot hgbot hdiv <;>
      intro x hx <;>
        applyAssumption <;>
          first |
            exact (hl' hx).1.1|
            exact (hl' hx).1.2

end HasDerivAt

namespace deriv

/-- **L'Hôpital's rule** for approaching a real from the right, `deriv` version -/
theorem lhopital_zero_nhds_right (hdf : ∀ᶠx in 𝓝[Ioi a] a, DifferentiableAt ℝ f x)
  (hg' : ∀ᶠx in 𝓝[Ioi a] a, deriv g x ≠ 0) (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 0)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[Ioi a] a) l) : tendsto (fun x => f x / g x) (𝓝[Ioi a] a) l :=
  by 
    have hdg : ∀ᶠx in 𝓝[Ioi a] a, DifferentiableAt ℝ g x 
    exact
      hg'.mp
        (eventually_of_forall$
          fun _ hg' => Classical.by_contradiction fun h => hg' (deriv_zero_of_not_differentiable_at h))
    have hdf' : ∀ᶠx in 𝓝[Ioi a] a, HasDerivAt f (deriv f x) x 
    exact hdf.mp (eventually_of_forall$ fun _ => DifferentiableAt.has_deriv_at)
    have hdg' : ∀ᶠx in 𝓝[Ioi a] a, HasDerivAt g (deriv g x) x 
    exact hdg.mp (eventually_of_forall$ fun _ => DifferentiableAt.has_deriv_at)
    exact HasDerivAt.lhopital_zero_nhds_right hdf' hdg' hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real from the left, `deriv` version -/
theorem lhopital_zero_nhds_left (hdf : ∀ᶠx in 𝓝[Iio a] a, DifferentiableAt ℝ f x)
  (hg' : ∀ᶠx in 𝓝[Iio a] a, deriv g x ≠ 0) (hfa : tendsto f (𝓝[Iio a] a) (𝓝 0)) (hga : tendsto g (𝓝[Iio a] a) (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[Iio a] a) l) : tendsto (fun x => f x / g x) (𝓝[Iio a] a) l :=
  by 
    have hdg : ∀ᶠx in 𝓝[Iio a] a, DifferentiableAt ℝ g x 
    exact
      hg'.mp
        (eventually_of_forall$
          fun _ hg' => Classical.by_contradiction fun h => hg' (deriv_zero_of_not_differentiable_at h))
    have hdf' : ∀ᶠx in 𝓝[Iio a] a, HasDerivAt f (deriv f x) x 
    exact hdf.mp (eventually_of_forall$ fun _ => DifferentiableAt.has_deriv_at)
    have hdg' : ∀ᶠx in 𝓝[Iio a] a, HasDerivAt g (deriv g x) x 
    exact hdg.mp (eventually_of_forall$ fun _ => DifferentiableAt.has_deriv_at)
    exact HasDerivAt.lhopital_zero_nhds_left hdf' hdg' hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `deriv` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds' (hdf : ∀ᶠx in 𝓝[univ \ {a}] a, DifferentiableAt ℝ f x)
  (hg' : ∀ᶠx in 𝓝[univ \ {a}] a, deriv g x ≠ 0) (hfa : tendsto f (𝓝[univ \ {a}] a) (𝓝 0))
  (hga : tendsto g (𝓝[univ \ {a}] a) (𝓝 0)) (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[univ \ {a}] a) l) :
  tendsto (fun x => f x / g x) (𝓝[univ \ {a}] a) l :=
  by 
    have  : univ \ {a} = Iio a ∪ Ioi a
    ·
      ext 
      rw [mem_diff_singleton, eq_true_intro$ mem_univ x, true_andₓ, ne_iff_lt_or_gtₓ]
      rfl 
    simp only [this, nhds_within_union, tendsto_sup, eventually_sup] at *
    exact
      ⟨lhopital_zero_nhds_left hdf.1 hg'.1 hfa.1 hga.1 hdiv.1, lhopital_zero_nhds_right hdf.2 hg'.2 hfa.2 hga.2 hdiv.2⟩

/-- **L'Hôpital's rule** for approaching a real, `deriv` version -/
theorem lhopital_zero_nhds (hdf : ∀ᶠx in 𝓝 a, DifferentiableAt ℝ f x) (hg' : ∀ᶠx in 𝓝 a, deriv g x ≠ 0)
  (hfa : tendsto f (𝓝 a) (𝓝 0)) (hga : tendsto g (𝓝 a) (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝 a) l) : tendsto (fun x => f x / g x) (𝓝[univ \ {a}] a) l :=
  by 
    apply lhopital_zero_nhds' <;>
      first |
          apply eventually_nhds_within_of_eventually_nhds|
          apply tendsto_nhds_within_of_tendsto_nhds <;>
        assumption

/-- **L'Hôpital's rule** for approaching +∞, `deriv` version -/
theorem lhopital_zero_at_top (hdf : ∀ᶠx : ℝ in at_top, DifferentiableAt ℝ f x) (hg' : ∀ᶠx : ℝ in at_top, deriv g x ≠ 0)
  (hftop : tendsto f at_top (𝓝 0)) (hgtop : tendsto g at_top (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) at_top l) : tendsto (fun x => f x / g x) at_top l :=
  by 
    have hdg : ∀ᶠx in at_top, DifferentiableAt ℝ g x 
    exact
      hg'.mp
        (eventually_of_forall$
          fun _ hg' => Classical.by_contradiction fun h => hg' (deriv_zero_of_not_differentiable_at h))
    have hdf' : ∀ᶠx in at_top, HasDerivAt f (deriv f x) x 
    exact hdf.mp (eventually_of_forall$ fun _ => DifferentiableAt.has_deriv_at)
    have hdg' : ∀ᶠx in at_top, HasDerivAt g (deriv g x) x 
    exact hdg.mp (eventually_of_forall$ fun _ => DifferentiableAt.has_deriv_at)
    exact HasDerivAt.lhopital_zero_at_top hdf' hdg' hg' hftop hgtop hdiv

/-- **L'Hôpital's rule** for approaching -∞, `deriv` version -/
theorem lhopital_zero_at_bot (hdf : ∀ᶠx : ℝ in at_bot, DifferentiableAt ℝ f x) (hg' : ∀ᶠx : ℝ in at_bot, deriv g x ≠ 0)
  (hfbot : tendsto f at_bot (𝓝 0)) (hgbot : tendsto g at_bot (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) at_bot l) : tendsto (fun x => f x / g x) at_bot l :=
  by 
    have hdg : ∀ᶠx in at_bot, DifferentiableAt ℝ g x 
    exact
      hg'.mp
        (eventually_of_forall$
          fun _ hg' => Classical.by_contradiction fun h => hg' (deriv_zero_of_not_differentiable_at h))
    have hdf' : ∀ᶠx in at_bot, HasDerivAt f (deriv f x) x 
    exact hdf.mp (eventually_of_forall$ fun _ => DifferentiableAt.has_deriv_at)
    have hdg' : ∀ᶠx in at_bot, HasDerivAt g (deriv g x) x 
    exact hdg.mp (eventually_of_forall$ fun _ => DifferentiableAt.has_deriv_at)
    exact HasDerivAt.lhopital_zero_at_bot hdf' hdg' hg' hfbot hgbot hdiv

end deriv

