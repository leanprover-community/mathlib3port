/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Analysis.Calculus.MeanValue

/-!
# L'HΓ΄pital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hopital's rule" for computing 0/0
indeterminate forms. The proof of `has_deriv_at.lhopital_zero_right_on_Ioo`
is based on the one given in the corresponding
[Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule)
chapter, and all other statements are derived from this one by composing by
carefully chosen functions.

Note that the filter `f'/g'` tends to isn't required to be one of `π a`,
`at_top` or `at_bot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `β`.

Each statement is available in a `has_deriv_at` form and a `deriv` form, which
is denoted by each statement being in either the `has_deriv_at` or the `deriv`
namespace.

## Tags

L'HΓ΄pital's rule, L'Hopital's rule
-/


open Filter Set

open Filter TopologicalSpace Pointwise

variable {a b : β} (hab : a < b) {l : Filter β} {f f' g g' : β β β}

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' β  0`) have
to be satisfied on an explicitly-provided interval.
-/


namespace HasDerivAt

include hab

theorem lhopital_zero_right_on_Ioo (hff' : β, β x β Ioo a b, β, HasDerivAt f (f' x) x)
    (hgg' : β, β x β Ioo a b, β, HasDerivAt g (g' x) x) (hg' : β, β x β Ioo a b, β, g' x β  0)
    (hfa : Tendsto f (π[>] a) (π 0)) (hga : Tendsto g (π[>] a) (π 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (π[>] a) l) : Tendsto (fun x => f x / g x) (π[>] a) l := by
  have sub : β, β x β Ioo a b, β, Ioo a x β Ioo a b := fun x hx => Ioo_subset_Ioo (le_reflβ a) (le_of_ltβ hx.2)
  have hg : β, β x β Ioo a b, β, g x β  0 := by
    intro x hx h
    have : tendsto g (π[<] x) (π 0) := by
      rw [β h, β nhds_within_Ioo_eq_nhds_within_Iio hx.1]
      exact ((hgg' x hx).ContinuousAt.ContinuousWithinAt.mono <| sub x hx).Tendsto
    obtain β¨y, hyx, hyβ© : β c β Ioo a x, g' c = 0
    exact exists_has_deriv_at_eq_zero' hx.1 hga this fun y hy => hgg' y <| sub x hx hy
    exact hg' y (sub x hx hyx) hy
  have : β, β x β Ioo a b, β, β c β Ioo a x, f x * g' c = g x * f' c := by
    intro x hx
    rw [β sub_zero (f x), β sub_zero (g x)]
    exact
      exists_ratio_has_deriv_at_eq_ratio_slope' g g' hx.1 f f' (fun y hy => hgg' y <| sub x hx hy)
        (fun y hy => hff' y <| sub x hx hy) hga hfa
        (tendsto_nhds_within_of_tendsto_nhds (hgg' x hx).ContinuousAt.Tendsto)
        (tendsto_nhds_within_of_tendsto_nhds (hff' x hx).ContinuousAt.Tendsto)
  choose! c hc using this
  have : β, β x β Ioo a b, β, ((fun x' => f' x' / g' x') β c) x = f x / g x := by
    intro x hx
    rcases hc x hx with β¨hβ, hββ©
    field_simp [β hg x hx, β hg' (c x) ((sub x hx) hβ)]
    simp only [β hβ]
    rwa [mul_comm]
  have cmp : β, β x β Ioo a b, β, a < c x β§ c x < x := fun x hx => (hc x hx).1
  rw [β nhds_within_Ioo_eq_nhds_within_Ioi hab]
  apply tendsto_nhds_within_congr this
  simp only
  apply hdiv.comp
  refine'
    tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_nhds_within_of_tendsto_nhds tendsto_id) _
        _)
      _
  all_goals
    apply eventually_nhds_within_of_forall
    intro x hx
    have := cmp x hx
    try
      simp
    linarith [this]

theorem lhopital_zero_right_on_Ico (hff' : β, β x β Ioo a b, β, HasDerivAt f (f' x) x)
    (hgg' : β, β x β Ioo a b, β, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ico a b))
    (hcg : ContinuousOn g (Ico a b)) (hg' : β, β x β Ioo a b, β, g' x β  0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x => f' x / g' x) (nhdsWithin a (Ioi a)) l) :
    Tendsto (fun x => f x / g x) (nhdsWithin a (Ioi a)) l := by
  refine' lhopital_zero_right_on_Ioo hab hff' hgg' hg' _ _ hdiv
  Β· rw [β hfa, β nhds_within_Ioo_eq_nhds_within_Ioi hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto
    
  Β· rw [β hga, β nhds_within_Ioo_eq_nhds_within_Ioi hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto
    

theorem lhopital_zero_left_on_Ioo (hff' : β, β x β Ioo a b, β, HasDerivAt f (f' x) x)
    (hgg' : β, β x β Ioo a b, β, HasDerivAt g (g' x) x) (hg' : β, β x β Ioo a b, β, g' x β  0)
    (hfb : Tendsto f (nhdsWithin b (Iio b)) (π 0)) (hgb : Tendsto g (nhdsWithin b (Iio b)) (π 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (nhdsWithin b (Iio b)) l) :
    Tendsto (fun x => f x / g x) (nhdsWithin b (Iio b)) l := by
  -- Here, we essentially compose by `has_neg.neg`. The following is mostly technical details.
  have hdnf : β, β x β -Ioo a b, β, HasDerivAt (f β Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (has_deriv_at_neg x)
  have hdng : β, β x β -Ioo a b, β, HasDerivAt (g β Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (has_deriv_at_neg x)
  rw [preimage_neg_Ioo] at hdnf
  rw [preimage_neg_Ioo] at hdng
  have :=
    lhopital_zero_right_on_Ioo (neg_lt_neg hab) hdnf hdng
      (by
        intro x hx h
        apply
          hg' _
            (by
              rw [β preimage_neg_Ioo] at hx
              exact hx)
        rwa [mul_comm, β neg_eq_neg_one_mul, neg_eq_zero] at h)
      (hfb.comp tendsto_neg_nhds_within_Ioi_neg) (hgb.comp tendsto_neg_nhds_within_Ioi_neg)
      (by
        simp only [β neg_div_neg_eq, β mul_oneβ, β mul_neg]
        exact (tendsto_congr fun x => rfl).mp (hdiv.comp tendsto_neg_nhds_within_Ioi_neg))
  have := this.comp tendsto_neg_nhds_within_Iio
  unfold Function.comp  at this
  simpa only [β neg_negβ]

theorem lhopital_zero_left_on_Ioc (hff' : β, β x β Ioo a b, β, HasDerivAt f (f' x) x)
    (hgg' : β, β x β Ioo a b, β, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ioc a b))
    (hcg : ContinuousOn g (Ioc a b)) (hg' : β, β x β Ioo a b, β, g' x β  0) (hfb : f b = 0) (hgb : g b = 0)
    (hdiv : Tendsto (fun x => f' x / g' x) (nhdsWithin b (Iio b)) l) :
    Tendsto (fun x => f x / g x) (nhdsWithin b (Iio b)) l := by
  refine' lhopital_zero_left_on_Ioo hab hff' hgg' hg' _ _ hdiv
  Β· rw [β hfb, β nhds_within_Ioo_eq_nhds_within_Iio hab]
    exact ((hcf b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).Tendsto
    
  Β· rw [β hgb, β nhds_within_Ioo_eq_nhds_within_Iio hab]
    exact ((hcg b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).Tendsto
    

omit hab

theorem lhopital_zero_at_top_on_Ioi (hff' : β, β x β Ioi a, β, HasDerivAt f (f' x) x)
    (hgg' : β, β x β Ioi a, β, HasDerivAt g (g' x) x) (hg' : β, β x β Ioi a, β, g' x β  0)
    (hftop : Tendsto f atTop (π 0)) (hgtop : Tendsto g atTop (π 0)) (hdiv : Tendsto (fun x => f' x / g' x) atTop l) :
    Tendsto (fun x => f x / g x) atTop l := by
  obtain β¨a', haa', ha'β© : β a', a < a' β§ 0 < a' :=
    β¨1 + max a 0,
      β¨lt_of_le_of_ltβ (le_max_leftβ a 0) (lt_one_add _), lt_of_le_of_ltβ (le_max_rightβ a 0) (lt_one_add _)β©β©
  have fact1 : β x : β, x β Ioo 0 a'β»ΒΉ β x β  0 := fun _ hx => (ne_of_ltβ hx.1).symm
  have fact2 : β, β x β Ioo 0 a'β»ΒΉ, β, a < xβ»ΒΉ := fun _ hx => lt_transβ haa' ((lt_inv ha' hx.1).mpr hx.2)
  have hdnf : β, β x β Ioo 0 a'β»ΒΉ, β, HasDerivAt (f β Inv.inv) (f' xβ»ΒΉ * -(x ^ 2)β»ΒΉ) x := fun x hx =>
    comp x (hff' xβ»ΒΉ <| fact2 x hx) (has_deriv_at_inv <| fact1 x hx)
  have hdng : β, β x β Ioo 0 a'β»ΒΉ, β, HasDerivAt (g β Inv.inv) (g' xβ»ΒΉ * -(x ^ 2)β»ΒΉ) x := fun x hx =>
    comp x (hgg' xβ»ΒΉ <| fact2 x hx) (has_deriv_at_inv <| fact1 x hx)
  have :=
    lhopital_zero_right_on_Ioo (inv_pos.mpr ha') hdnf hdng
      (by
        intro x hx
        refine' mul_ne_zero _ (neg_ne_zero.mpr <| inv_ne_zero <| pow_ne_zero _ <| fact1 x hx)
        exact hg' _ (fact2 x hx))
      (hftop.comp tendsto_inv_zero_at_top) (hgtop.comp tendsto_inv_zero_at_top)
      (by
        refine' (tendsto_congr' _).mp (hdiv.comp tendsto_inv_zero_at_top)
        rw [eventually_eq_iff_exists_mem]
        use Ioi 0, self_mem_nhds_within
        intro x hx
        unfold Function.comp
        erw [mul_div_mul_right]
        refine' neg_ne_zero.mpr (inv_ne_zero <| pow_ne_zero _ <| ne_of_gtβ hx))
  have := this.comp tendsto_inv_at_top_zero'
  unfold Function.comp  at this
  simpa only [β inv_invβ]

theorem lhopital_zero_at_bot_on_Iio (hff' : β, β x β Iio a, β, HasDerivAt f (f' x) x)
    (hgg' : β, β x β Iio a, β, HasDerivAt g (g' x) x) (hg' : β, β x β Iio a, β, g' x β  0)
    (hfbot : Tendsto f atBot (π 0)) (hgbot : Tendsto g atBot (π 0)) (hdiv : Tendsto (fun x => f' x / g' x) atBot l) :
    Tendsto (fun x => f x / g x) atBot l := by
  -- Here, we essentially compose by `has_neg.neg`. The following is mostly technical details.
  have hdnf : β, β x β -Iio a, β, HasDerivAt (f β Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (has_deriv_at_neg x)
  have hdng : β, β x β -Iio a, β, HasDerivAt (g β Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (has_deriv_at_neg x)
  rw [preimage_neg_Iio] at hdnf
  rw [preimage_neg_Iio] at hdng
  have :=
    lhopital_zero_at_top_on_Ioi hdnf hdng
      (by
        intro x hx h
        apply
          hg' _
            (by
              rw [β preimage_neg_Iio] at hx
              exact hx)
        rwa [mul_comm, β neg_eq_neg_one_mul, neg_eq_zero] at h)
      (hfbot.comp tendsto_neg_at_top_at_bot) (hgbot.comp tendsto_neg_at_top_at_bot)
      (by
        simp only [β mul_oneβ, β mul_neg, β neg_div_neg_eq]
        exact (tendsto_congr fun x => rfl).mp (hdiv.comp tendsto_neg_at_top_at_bot))
  have := this.comp tendsto_neg_at_bot_at_top
  unfold Function.comp  at this
  simpa only [β neg_negβ]

end HasDerivAt

namespace deriv

include hab

theorem lhopital_zero_right_on_Ioo (hdf : DifferentiableOn β f (Ioo a b)) (hg' : β, β x β Ioo a b, β, deriv g x β  0)
    (hfa : Tendsto f (π[>] a) (π 0)) (hga : Tendsto g (π[>] a) (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (π[>] a) l) : Tendsto (fun x => f x / g x) (π[>] a) l := by
  have hdf : β, β x β Ioo a b, β, DifferentiableAt β f x := fun x hx =>
    (hdf x hx).DifferentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : β, β x β Ioo a b, β, DifferentiableAt β g x := fun x hx =>
    Classical.by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiable_at h)
  exact
    HasDerivAt.lhopital_zero_right_on_Ioo hab (fun x hx => (hdf x hx).HasDerivAt) (fun x hx => (hdg x hx).HasDerivAt)
      hg' hfa hga hdiv

theorem lhopital_zero_right_on_Ico (hdf : DifferentiableOn β f (Ioo a b)) (hcf : ContinuousOn f (Ico a b))
    (hcg : ContinuousOn g (Ico a b)) (hg' : β, β x β Ioo a b, β, (deriv g) x β  0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (nhdsWithin a (Ioi a)) l) :
    Tendsto (fun x => f x / g x) (nhdsWithin a (Ioi a)) l := by
  refine' lhopital_zero_right_on_Ioo hab hdf hg' _ _ hdiv
  Β· rw [β hfa, β nhds_within_Ioo_eq_nhds_within_Ioi hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto
    
  Β· rw [β hga, β nhds_within_Ioo_eq_nhds_within_Ioi hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto
    

theorem lhopital_zero_left_on_Ioo (hdf : DifferentiableOn β f (Ioo a b)) (hg' : β, β x β Ioo a b, β, (deriv g) x β  0)
    (hfb : Tendsto f (nhdsWithin b (Iio b)) (π 0)) (hgb : Tendsto g (nhdsWithin b (Iio b)) (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (nhdsWithin b (Iio b)) l) :
    Tendsto (fun x => f x / g x) (nhdsWithin b (Iio b)) l := by
  have hdf : β, β x β Ioo a b, β, DifferentiableAt β f x := fun x hx =>
    (hdf x hx).DifferentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : β, β x β Ioo a b, β, DifferentiableAt β g x := fun x hx =>
    Classical.by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiable_at h)
  exact
    HasDerivAt.lhopital_zero_left_on_Ioo hab (fun x hx => (hdf x hx).HasDerivAt) (fun x hx => (hdg x hx).HasDerivAt) hg'
      hfb hgb hdiv

omit hab

theorem lhopital_zero_at_top_on_Ioi (hdf : DifferentiableOn β f (Ioi a)) (hg' : β, β x β Ioi a, β, (deriv g) x β  0)
    (hftop : Tendsto f atTop (π 0)) (hgtop : Tendsto g atTop (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop l) : Tendsto (fun x => f x / g x) atTop l := by
  have hdf : β, β x β Ioi a, β, DifferentiableAt β f x := fun x hx => (hdf x hx).DifferentiableAt (Ioi_mem_nhds hx)
  have hdg : β, β x β Ioi a, β, DifferentiableAt β g x := fun x hx =>
    Classical.by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiable_at h)
  exact
    HasDerivAt.lhopital_zero_at_top_on_Ioi (fun x hx => (hdf x hx).HasDerivAt) (fun x hx => (hdg x hx).HasDerivAt) hg'
      hftop hgtop hdiv

theorem lhopital_zero_at_bot_on_Iio (hdf : DifferentiableOn β f (Iio a)) (hg' : β, β x β Iio a, β, (deriv g) x β  0)
    (hfbot : Tendsto f atBot (π 0)) (hgbot : Tendsto g atBot (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot l) : Tendsto (fun x => f x / g x) atBot l := by
  have hdf : β, β x β Iio a, β, DifferentiableAt β f x := fun x hx => (hdf x hx).DifferentiableAt (Iio_mem_nhds hx)
  have hdg : β, β x β Iio a, β, DifferentiableAt β g x := fun x hx =>
    Classical.by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiable_at h)
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

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- L'HΓ΄pital's rule for approaching a real from the right, `has_deriv_at` version -/
theorem lhopital_zero_nhds_right (hff' : βαΆ  x in π[>] a, HasDerivAt f (f' x) x)
    (hgg' : βαΆ  x in π[>] a, HasDerivAt g (g' x) x) (hg' : βαΆ  x in π[>] a, g' x β  0) (hfa : Tendsto f (π[>] a) (π 0))
    (hga : Tendsto g (π[>] a) (π 0)) (hdiv : Tendsto (fun x => f' x / g' x) (π[>] a) l) :
    Tendsto (fun x => f x / g x) (π[>] a) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with β¨sβ, hsβ, hff'β©
  rcases hgg' with β¨sβ, hsβ, hgg'β©
  rcases hg' with β¨sβ, hsβ, hg'β©
  let s := sβ β© sβ β© sβ
  have hs : s β π[>] a := inter_mem (inter_mem hsβ hsβ) hsβ
  rw [mem_nhds_within_Ioi_iff_exists_Ioo_subset] at hs
  rcases hs with β¨u, hau, huβ©
  refine' lhopital_zero_right_on_Ioo hau _ _ _ hfa hga hdiv <;>
    intro x hx <;>
      apply_assumption <;>
        first |
          exact (hu hx).1.1|
          exact (hu hx).1.2|
          exact (hu hx).2

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- L'HΓ΄pital's rule for approaching a real from the left, `has_deriv_at` version -/
theorem lhopital_zero_nhds_left (hff' : βαΆ  x in π[<] a, HasDerivAt f (f' x) x)
    (hgg' : βαΆ  x in π[<] a, HasDerivAt g (g' x) x) (hg' : βαΆ  x in π[<] a, g' x β  0) (hfa : Tendsto f (π[<] a) (π 0))
    (hga : Tendsto g (π[<] a) (π 0)) (hdiv : Tendsto (fun x => f' x / g' x) (π[<] a) l) :
    Tendsto (fun x => f x / g x) (π[<] a) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with β¨sβ, hsβ, hff'β©
  rcases hgg' with β¨sβ, hsβ, hgg'β©
  rcases hg' with β¨sβ, hsβ, hg'β©
  let s := sβ β© sβ β© sβ
  have hs : s β π[<] a := inter_mem (inter_mem hsβ hsβ) hsβ
  rw [mem_nhds_within_Iio_iff_exists_Ioo_subset] at hs
  rcases hs with β¨l, hal, hlβ©
  refine' lhopital_zero_left_on_Ioo hal _ _ _ hfa hga hdiv <;>
    intro x hx <;>
      apply_assumption <;>
        first |
          exact (hl hx).1.1|
          exact (hl hx).1.2|
          exact (hl hx).2

/-- L'HΓ΄pital's rule for approaching a real, `has_deriv_at` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds' (hff' : βαΆ  x in π[univ \ {a}] a, HasDerivAt f (f' x) x)
    (hgg' : βαΆ  x in π[univ \ {a}] a, HasDerivAt g (g' x) x) (hg' : βαΆ  x in π[univ \ {a}] a, g' x β  0)
    (hfa : Tendsto f (π[univ \ {a}] a) (π 0)) (hga : Tendsto g (π[univ \ {a}] a) (π 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (π[univ \ {a}] a) l) : Tendsto (fun x => f x / g x) (π[univ \ {a}] a) l := by
  have : univ \ {a} = Iio a βͺ Ioi a := by
    ext
    rw [mem_diff_singleton, eq_true_intro <| mem_univ x, true_andβ, ne_iff_lt_or_gtβ]
    rfl
  simp only [β this, β nhds_within_union, β tendsto_sup, β eventually_sup] at *
  exact
    β¨lhopital_zero_nhds_left hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1,
      lhopital_zero_nhds_right hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2β©

/-- **L'HΓ΄pital's rule** for approaching a real, `has_deriv_at` version -/
theorem lhopital_zero_nhds (hff' : βαΆ  x in π a, HasDerivAt f (f' x) x) (hgg' : βαΆ  x in π a, HasDerivAt g (g' x) x)
    (hg' : βαΆ  x in π a, g' x β  0) (hfa : Tendsto f (π a) (π 0)) (hga : Tendsto g (π a) (π 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (π a) l) : Tendsto (fun x => f x / g x) (π[univ \ {a}] a) l := by
  apply @lhopital_zero_nhds' _ _ _ f' _ g' <;>
    first |
        apply eventually_nhds_within_of_eventually_nhds|
        apply tendsto_nhds_within_of_tendsto_nhds <;>
      assumption

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- L'HΓ΄pital's rule for approaching +β, `has_deriv_at` version -/
theorem lhopital_zero_at_top (hff' : βαΆ  x in at_top, HasDerivAt f (f' x) x)
    (hgg' : βαΆ  x in at_top, HasDerivAt g (g' x) x) (hg' : βαΆ  x in at_top, g' x β  0) (hftop : Tendsto f atTop (π 0))
    (hgtop : Tendsto g atTop (π 0)) (hdiv : Tendsto (fun x => f' x / g' x) atTop l) :
    Tendsto (fun x => f x / g x) atTop l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with β¨sβ, hsβ, hff'β©
  rcases hgg' with β¨sβ, hsβ, hgg'β©
  rcases hg' with β¨sβ, hsβ, hg'β©
  let s := sβ β© sβ β© sβ
  have hs : s β at_top := inter_mem (inter_mem hsβ hsβ) hsβ
  rw [mem_at_top_sets] at hs
  rcases hs with β¨l, hlβ©
  have hl' : Ioi l β s := fun x hx => hl x (le_of_ltβ hx)
  refine' lhopital_zero_at_top_on_Ioi _ _ (fun x hx => hg' x <| (hl' hx).2) hftop hgtop hdiv <;>
    intro x hx <;>
      apply_assumption <;>
        first |
          exact (hl' hx).1.1|
          exact (hl' hx).1.2

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- L'HΓ΄pital's rule for approaching -β, `has_deriv_at` version -/
theorem lhopital_zero_at_bot (hff' : βαΆ  x in at_bot, HasDerivAt f (f' x) x)
    (hgg' : βαΆ  x in at_bot, HasDerivAt g (g' x) x) (hg' : βαΆ  x in at_bot, g' x β  0) (hfbot : Tendsto f atBot (π 0))
    (hgbot : Tendsto g atBot (π 0)) (hdiv : Tendsto (fun x => f' x / g' x) atBot l) :
    Tendsto (fun x => f x / g x) atBot l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with β¨sβ, hsβ, hff'β©
  rcases hgg' with β¨sβ, hsβ, hgg'β©
  rcases hg' with β¨sβ, hsβ, hg'β©
  let s := sβ β© sβ β© sβ
  have hs : s β at_bot := inter_mem (inter_mem hsβ hsβ) hsβ
  rw [mem_at_bot_sets] at hs
  rcases hs with β¨l, hlβ©
  have hl' : Iio l β s := fun x hx => hl x (le_of_ltβ hx)
  refine' lhopital_zero_at_bot_on_Iio _ _ (fun x hx => hg' x <| (hl' hx).2) hfbot hgbot hdiv <;>
    intro x hx <;>
      apply_assumption <;>
        first |
          exact (hl' hx).1.1|
          exact (hl' hx).1.2

end HasDerivAt

namespace deriv

/-- **L'HΓ΄pital's rule** for approaching a real from the right, `deriv` version -/
theorem lhopital_zero_nhds_right (hdf : βαΆ  x in π[>] a, DifferentiableAt β f x) (hg' : βαΆ  x in π[>] a, deriv g x β  0)
    (hfa : Tendsto f (π[>] a) (π 0)) (hga : Tendsto g (π[>] a) (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (π[>] a) l) : Tendsto (fun x => f x / g x) (π[>] a) l := by
  have hdg : βαΆ  x in π[>] a, DifferentiableAt β g x :=
    hg'.mp
      (eventually_of_forall fun _ hg' =>
        Classical.by_contradiction fun h => hg' (deriv_zero_of_not_differentiable_at h))
  have hdf' : βαΆ  x in π[>] a, HasDerivAt f (deriv f x) x :=
    hdf.mp (eventually_of_forall fun _ => DifferentiableAt.has_deriv_at)
  have hdg' : βαΆ  x in π[>] a, HasDerivAt g (deriv g x) x :=
    hdg.mp (eventually_of_forall fun _ => DifferentiableAt.has_deriv_at)
  exact HasDerivAt.lhopital_zero_nhds_right hdf' hdg' hg' hfa hga hdiv

/-- **L'HΓ΄pital's rule** for approaching a real from the left, `deriv` version -/
theorem lhopital_zero_nhds_left (hdf : βαΆ  x in π[<] a, DifferentiableAt β f x) (hg' : βαΆ  x in π[<] a, deriv g x β  0)
    (hfa : Tendsto f (π[<] a) (π 0)) (hga : Tendsto g (π[<] a) (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (π[<] a) l) : Tendsto (fun x => f x / g x) (π[<] a) l := by
  have hdg : βαΆ  x in π[<] a, DifferentiableAt β g x :=
    hg'.mp
      (eventually_of_forall fun _ hg' =>
        Classical.by_contradiction fun h => hg' (deriv_zero_of_not_differentiable_at h))
  have hdf' : βαΆ  x in π[<] a, HasDerivAt f (deriv f x) x :=
    hdf.mp (eventually_of_forall fun _ => DifferentiableAt.has_deriv_at)
  have hdg' : βαΆ  x in π[<] a, HasDerivAt g (deriv g x) x :=
    hdg.mp (eventually_of_forall fun _ => DifferentiableAt.has_deriv_at)
  exact HasDerivAt.lhopital_zero_nhds_left hdf' hdg' hg' hfa hga hdiv

/-- **L'HΓ΄pital's rule** for approaching a real, `deriv` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds' (hdf : βαΆ  x in π[univ \ {a}] a, DifferentiableAt β f x)
    (hg' : βαΆ  x in π[univ \ {a}] a, deriv g x β  0) (hfa : Tendsto f (π[univ \ {a}] a) (π 0))
    (hga : Tendsto g (π[univ \ {a}] a) (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (π[univ \ {a}] a) l) :
    Tendsto (fun x => f x / g x) (π[univ \ {a}] a) l := by
  have : univ \ {a} = Iio a βͺ Ioi a := by
    ext
    rw [mem_diff_singleton, eq_true_intro <| mem_univ x, true_andβ, ne_iff_lt_or_gtβ]
    rfl
  simp only [β this, β nhds_within_union, β tendsto_sup, β eventually_sup] at *
  exact
    β¨lhopital_zero_nhds_left hdf.1 hg'.1 hfa.1 hga.1 hdiv.1, lhopital_zero_nhds_right hdf.2 hg'.2 hfa.2 hga.2 hdiv.2β©

/-- **L'HΓ΄pital's rule** for approaching a real, `deriv` version -/
theorem lhopital_zero_nhds (hdf : βαΆ  x in π a, DifferentiableAt β f x) (hg' : βαΆ  x in π a, deriv g x β  0)
    (hfa : Tendsto f (π a) (π 0)) (hga : Tendsto g (π a) (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (π a) l) : Tendsto (fun x => f x / g x) (π[univ \ {a}] a) l :=
  by
  apply lhopital_zero_nhds' <;>
    first |
        apply eventually_nhds_within_of_eventually_nhds|
        apply tendsto_nhds_within_of_tendsto_nhds <;>
      assumption

/-- **L'HΓ΄pital's rule** for approaching +β, `deriv` version -/
theorem lhopital_zero_at_top (hdf : βαΆ  x : β in at_top, DifferentiableAt β f x)
    (hg' : βαΆ  x : β in at_top, deriv g x β  0) (hftop : Tendsto f atTop (π 0)) (hgtop : Tendsto g atTop (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop l) : Tendsto (fun x => f x / g x) atTop l := by
  have hdg : βαΆ  x in at_top, DifferentiableAt β g x :=
    hg'.mp
      (eventually_of_forall fun _ hg' =>
        Classical.by_contradiction fun h => hg' (deriv_zero_of_not_differentiable_at h))
  have hdf' : βαΆ  x in at_top, HasDerivAt f (deriv f x) x :=
    hdf.mp (eventually_of_forall fun _ => DifferentiableAt.has_deriv_at)
  have hdg' : βαΆ  x in at_top, HasDerivAt g (deriv g x) x :=
    hdg.mp (eventually_of_forall fun _ => DifferentiableAt.has_deriv_at)
  exact HasDerivAt.lhopital_zero_at_top hdf' hdg' hg' hftop hgtop hdiv

/-- **L'HΓ΄pital's rule** for approaching -β, `deriv` version -/
theorem lhopital_zero_at_bot (hdf : βαΆ  x : β in at_bot, DifferentiableAt β f x)
    (hg' : βαΆ  x : β in at_bot, deriv g x β  0) (hfbot : Tendsto f atBot (π 0)) (hgbot : Tendsto g atBot (π 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot l) : Tendsto (fun x => f x / g x) atBot l := by
  have hdg : βαΆ  x in at_bot, DifferentiableAt β g x :=
    hg'.mp
      (eventually_of_forall fun _ hg' =>
        Classical.by_contradiction fun h => hg' (deriv_zero_of_not_differentiable_at h))
  have hdf' : βαΆ  x in at_bot, HasDerivAt f (deriv f x) x :=
    hdf.mp (eventually_of_forall fun _ => DifferentiableAt.has_deriv_at)
  have hdg' : βαΆ  x in at_bot, HasDerivAt g (deriv g x) x :=
    hdg.mp (eventually_of_forall fun _ => DifferentiableAt.has_deriv_at)
  exact HasDerivAt.lhopital_zero_at_bot hdf' hdg' hg' hfbot hgbot hdiv

end deriv

