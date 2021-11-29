import Mathbin.Analysis.Analytic.Basic

/-!
# Linear functions are analytic

In this file we prove that a `continuous_linear_map` defines an analytic function with
the formal power series `f x = f a + f (x - a)`.
-/


variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜 E]{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]{G : Type _}[NormedGroup G][NormedSpace 𝕜 G]

open_locale TopologicalSpace Classical BigOperators Nnreal Ennreal

open Set Filter Asymptotics

noncomputable theory

namespace ContinuousLinearMap

/-- Formal power series of a continuous linear map `f : E →L[𝕜] F` at `x : E`:
`f y = f x + f (y - x)`. -/
@[simp]
def fpower_series (f : E →L[𝕜] F) (x : E) : FormalMultilinearSeries 𝕜 E F
| 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x)
| 1 => (continuousMultilinearCurryFin1 𝕜 E F).symm f
| _ => 0

@[simp]
theorem fpower_series_apply_add_two (f : E →L[𝕜] F) (x : E) (n : ℕ) : f.fpower_series x (n+2) = 0 :=
  rfl

@[simp]
theorem fpower_series_radius (f : E →L[𝕜] F) (x : E) : (f.fpower_series x).radius = ∞ :=
  (f.fpower_series x).radius_eq_top_of_forall_image_add_eq_zero 2$ fun n => rfl

protected theorem HasFpowerSeriesOnBall (f : E →L[𝕜] F) (x : E) : HasFpowerSeriesOnBall f (f.fpower_series x) x ∞ :=
  { r_le :=
      by 
        simp ,
    r_pos := Ennreal.coe_lt_top,
    HasSum :=
      fun y _ =>
        (has_sum_nat_add_iff' 2).1$
          by 
            simp [Finset.sum_range_succ, ←sub_sub, has_sum_zero] }

protected theorem HasFpowerSeriesAt (f : E →L[𝕜] F) (x : E) : HasFpowerSeriesAt f (f.fpower_series x) x :=
  ⟨∞, f.has_fpower_series_on_ball x⟩

protected theorem AnalyticAt (f : E →L[𝕜] F) (x : E) : AnalyticAt 𝕜 f x :=
  (f.has_fpower_series_at x).AnalyticAt

/-- Reinterpret a bilinear map `f : E →L[𝕜] F →L[𝕜] G` as a multilinear map
`(E × F) [×2]→L[𝕜] G`. This multilinear map is the second term in the formal
multilinear series expansion of `uncurry f`. It is given by
`f.uncurry_bilinear ![(x, y), (x', y')] = f x y'`. -/
def uncurry_bilinear (f : E →L[𝕜] F →L[𝕜] G) : «expr [× ]→L[ ] » (E × F) 2 𝕜 G :=
  @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _$
    («expr↑ » (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F →L[𝕜] G) →L[𝕜] _).comp$
      f.bilinear_comp (fst _ _ _) (snd _ _ _)

@[simp]
theorem uncurry_bilinear_apply (f : E →L[𝕜] F →L[𝕜] G) (m : Finₓ 2 → E × F) :
  f.uncurry_bilinear m = f (m 0).1 (m 1).2 :=
  rfl

/-- Formal multilinear series expansion of a bilinear function `f : E →L[𝕜] F →L[𝕜] G`. -/
@[simp]
def fpower_series_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : FormalMultilinearSeries 𝕜 (E × F) G
| 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x.1 x.2)
| 1 => (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
| 2 => f.uncurry_bilinear
| _ => 0

@[simp]
theorem fpower_series_bilinear_radius (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : (f.fpower_series_bilinear x).radius = ∞ :=
  (f.fpower_series_bilinear x).radius_eq_top_of_forall_image_add_eq_zero 3$ fun n => rfl

-- error in Analysis.Analytic.Linear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem has_fpower_series_on_ball_bilinear
(f : «expr →L[ ] »(E, 𝕜, «expr →L[ ] »(F, 𝕜, G)))
(x : «expr × »(E, F)) : has_fpower_series_on_ball (λ
 x : «expr × »(E, F), f x.1 x.2) (f.fpower_series_bilinear x) x «expr∞»() :=
{ r_le := by simp [] [] [] [] [] [],
  r_pos := ennreal.coe_lt_top,
  has_sum := λ
  y
  _, «expr $ »((has_sum_nat_add_iff' 3).1, begin
     simp [] [] ["only"] ["[", expr finset.sum_range_succ, ",", expr finset.sum_range_one, ",", expr prod.fst_add, ",", expr prod.snd_add, ",", expr f.map_add₂, "]"] [] [],
     dsimp [] [] [] [],
     simp [] [] ["only"] ["[", expr add_comm, ",", expr sub_self, ",", expr has_sum_zero, "]"] [] []
   end) }

-- error in Analysis.Analytic.Linear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem has_fpower_series_at_bilinear
(f : «expr →L[ ] »(E, 𝕜, «expr →L[ ] »(F, 𝕜, G)))
(x : «expr × »(E, F)) : has_fpower_series_at (λ x : «expr × »(E, F), f x.1 x.2) (f.fpower_series_bilinear x) x :=
⟨«expr∞»(), f.has_fpower_series_on_ball_bilinear x⟩

-- error in Analysis.Analytic.Linear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem analytic_at_bilinear
(f : «expr →L[ ] »(E, 𝕜, «expr →L[ ] »(F, 𝕜, G)))
(x : «expr × »(E, F)) : analytic_at 𝕜 (λ x : «expr × »(E, F), f x.1 x.2) x :=
(f.has_fpower_series_at_bilinear x).analytic_at

end ContinuousLinearMap

