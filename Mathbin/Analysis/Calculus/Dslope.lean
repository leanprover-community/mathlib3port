/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.Deriv
import Mathbin.LinearAlgebra.AffineSpace.Slope

/-!
# Slope of a differentiable function

Given a function `f : ๐ โ E` from a nondiscrete normed field to a normed space over this field,
`dslope f a b` is defined as `slope f a b = (b - a)โปยน โข (f b - f a)` for `a โ  b` and as `deriv f a`
for `a = b`.

In this file we define `dslope` and prove some basic lemmas about its continuity and
differentiability.
-/


open Classical TopologicalSpace Filter

open Function Set Filter

variable {๐ E : Type _} [NondiscreteNormedField ๐] [NormedGroup E] [NormedSpace ๐ E]

/-- `dslope f a b` is defined as `slope f a b = (b - a)โปยน โข (f b - f a)` for `a โ  b` and
`deriv f a` for `a = b`. -/
noncomputable def dslope (f : ๐ โ E) (a : ๐) : ๐ โ E :=
  update (slope f a) a (deriv f a)

@[simp]
theorem dslope_same (f : ๐ โ E) (a : ๐) : dslope f a a = deriv f a :=
  update_same _ _ _

variable {f : ๐ โ E} {a b : ๐} {s : Set ๐}

theorem dslope_of_ne (f : ๐ โ E) (h : b โ  a) : dslope f a b = slope f a b :=
  update_noteq h _ _

theorem ContinuousLinearMap.dslope_comp {F : Type _} [NormedGroup F] [NormedSpace ๐ F] (f : E โL[๐] F) (g : ๐ โ E)
    (a b : ๐) (H : a = b โ DifferentiableAt ๐ g a) : dslope (f โ g) a b = f (dslope g a b) := by
  rcases eq_or_ne b a with (rfl | hne)
  ยท simp only [โ dslope_same]
    exact (f.has_fderiv_at.comp_has_deriv_at b (H rfl).HasDerivAt).deriv
    
  ยท simpa only [โ dslope_of_ne _ hne] using f.to_linear_map.slope_comp g a b
    

theorem eq_on_dslope_slope (f : ๐ โ E) (a : ๐) : EqOn (dslope f a) (slope f a) ({a}แถ) := fun b => dslope_of_ne f

theorem dslope_eventually_eq_slope_of_ne (f : ๐ โ E) (h : b โ  a) : dslope f a =แถ [๐ b] slope f a :=
  (eq_on_dslope_slope f a).eventually_eq_of_mem (is_open_ne.mem_nhds h)

theorem dslope_eventually_eq_slope_punctured_nhds (f : ๐ โ E) : dslope f a =แถ [๐[โ ] a] slope f a :=
  (eq_on_dslope_slope f a).eventually_eq_of_mem self_mem_nhds_within

@[simp]
theorem sub_smul_dslope (f : ๐ โ E) (a b : ๐) : (b - a) โข dslope f a b = f b - f a := by
  rcases eq_or_ne b a with (rfl | hne) <;> simp [โ dslope_of_ne, *]

theorem dslope_sub_smul_of_ne (f : ๐ โ E) (h : b โ  a) : dslope (fun x => (x - a) โข f x) a b = f b := by
  rw [dslope_of_ne _ h, slope_sub_smul _ h.symm]

theorem eq_on_dslope_sub_smul (f : ๐ โ E) (a : ๐) : EqOn (dslope (fun x => (x - a) โข f x) a) f ({a}แถ) := fun b =>
  dslope_sub_smul_of_ne f

theorem dslope_sub_smul [DecidableEq ๐] (f : ๐ โ E) (a : ๐) :
    dslope (fun x => (x - a) โข f x) a = update f a (deriv (fun x => (x - a) โข f x) a) :=
  eq_update_iff.2 โจdslope_same _ _, eq_on_dslope_sub_smul f aโฉ

@[simp]
theorem continuous_at_dslope_same : ContinuousAt (dslope f a) a โ DifferentiableAt ๐ f a := by
  simp only [โ dslope, โ continuous_at_update_same, has_deriv_at_deriv_iff, โ has_deriv_at_iff_tendsto_slope]

theorem ContinuousWithinAt.of_dslope (h : ContinuousWithinAt (dslope f a) s b) : ContinuousWithinAt f s b := by
  have : ContinuousWithinAt (fun x => (x - a) โข dslope f a x + f a) s b :=
    ((continuous_within_at_id.sub continuous_within_at_const).smul h).add continuous_within_at_const
  simpa only [โ sub_smul_dslope, โ sub_add_cancel] using this

theorem ContinuousAt.of_dslope (h : ContinuousAt (dslope f a) b) : ContinuousAt f b :=
  (continuous_within_at_univ _ _).1 h.ContinuousWithinAt.of_dslope

theorem ContinuousOn.of_dslope (h : ContinuousOn (dslope f a) s) : ContinuousOn f s := fun x hx => (h x hx).of_dslope

theorem continuous_within_at_dslope_of_ne (h : b โ  a) :
    ContinuousWithinAt (dslope f a) s b โ ContinuousWithinAt f s b := by
  refine' โจContinuousWithinAt.of_dslope, fun hc => _โฉ
  simp only [โ dslope, โ continuous_within_at_update_of_ne h]
  exact
    ((continuous_within_at_id.sub continuous_within_at_const).invโ (sub_ne_zero.2 h)).smul
      (hc.sub continuous_within_at_const)

theorem continuous_at_dslope_of_ne (h : b โ  a) : ContinuousAt (dslope f a) b โ ContinuousAt f b := by
  simp only [continuous_within_at_univ, โ continuous_within_at_dslope_of_ne h]

theorem continuous_on_dslope (h : s โ ๐ a) : ContinuousOn (dslope f a) s โ ContinuousOn f s โง DifferentiableAt ๐ f a :=
  by
  refine' โจfun hc => โจhc.of_dslope, continuous_at_dslope_same.1 <| hc.ContinuousAt hโฉ, _โฉ
  rintro โจhc, hdโฉ x hx
  rcases eq_or_ne x a with (rfl | hne)
  exacts[(continuous_at_dslope_same.2 hd).ContinuousWithinAt, (continuous_within_at_dslope_of_ne hne).2 (hc x hx)]

theorem DifferentiableWithinAt.of_dslope (h : DifferentiableWithinAt ๐ (dslope f a) s b) :
    DifferentiableWithinAt ๐ f s b := by
  simpa only [โ id, โ sub_smul_dslope f a, โ sub_add_cancel] using
    ((differentiable_within_at_id.sub_const a).smul h).AddConst (f a)

theorem DifferentiableAt.of_dslope (h : DifferentiableAt ๐ (dslope f a) b) : DifferentiableAt ๐ f b :=
  differentiable_within_at_univ.1 h.DifferentiableWithinAt.of_dslope

theorem DifferentiableOn.of_dslope (h : DifferentiableOn ๐ (dslope f a) s) : DifferentiableOn ๐ f s := fun x hx =>
  (h x hx).of_dslope

theorem differentiable_within_at_dslope_of_ne (h : b โ  a) :
    DifferentiableWithinAt ๐ (dslope f a) s b โ DifferentiableWithinAt ๐ f s b := by
  refine' โจDifferentiableWithinAt.of_dslope, fun hd => _โฉ
  refine'
    (((differentiable_within_at_id.sub_const a).inv (sub_ne_zero.2 h)).smul (hd.sub_const (f a))).congr_of_eventually_eq
      _ (dslope_of_ne _ h)
  refine' (eq_on_dslope_slope _ _).eventually_eq_of_mem _
  exact mem_nhds_within_of_mem_nhds (is_open_ne.mem_nhds h)

theorem differentiable_on_dslope_of_nmem (h : a โ s) : DifferentiableOn ๐ (dslope f a) s โ DifferentiableOn ๐ f s :=
  forall_congrโ fun x => forall_congrโ fun hx => differentiable_within_at_dslope_of_ne <| ne_of_mem_of_not_mem hx h

theorem differentiable_at_dslope_of_ne (h : b โ  a) : DifferentiableAt ๐ (dslope f a) b โ DifferentiableAt ๐ f b := by
  simp only [differentiable_within_at_univ, โ differentiable_within_at_dslope_of_ne h]

